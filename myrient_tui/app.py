"""Main Textual App class — MyrientTUI."""
from __future__ import annotations

import atexit
import concurrent.futures
import datetime
import hashlib
import itertools
import json
import logging
import operator
import os
import re
import shutil
import subprocess
import threading
import time
import urllib.parse
import urllib.request
from urllib.parse import quote, unquote, urljoin
import uuid
import xml.etree.ElementTree as ET
from collections import Counter, deque
from pathlib import Path
from typing import Any, Iterator

from bs4 import BeautifulSoup
from rich.markup import escape as _escape_markup
from rich.text import Text
from textual import events, on, work
from textual.app import App, ComposeResult
from textual.containers import Container, Horizontal, Vertical
from textual.events import Key
from textual.timer import Timer
from textual.widgets import (
    Button, DataTable, Footer, Header, Input,
    Label, ListItem, ListView, ProgressBar, RichLog, Select,
    Static, Switch, Tree,
)

from panes import BrowsePane, DownloadsPane, GameSearchInput, LibraryPane, SettingsPane, LogsPane

from .constants import (
    _CHD_TIMEOUT, _DATA_DIR,
    _DAT_AUDITABLE_EXTS, _DAT_INDEX_STRAINER, _DAT_SEARCH_PREFIXES,
    _DOWNLOAD_EXTS, _FLUSH_INTERVAL, _GAME_EXTS, _HASH_CHUNK_BYTES,
    _LOW_PRIO_POPEN, _OS, _PROGRESS_DONE_STATES, _PS2_PATCH_EXTS,
    _SCRAPE_CONCURRENCY, _SEARCH_DEBOUNCE,
    _SESSION_LOG_MAX_FILES, _SIZE_MULTIPLIERS, _SIZE_UNITS,
    _TREE_AMBER, _TREE_DIM, _TREE_GREEN,
    _TREE_RED, _TREE_YELLOW, _WATCH_DEBOUNCE, CUE_BIN_REGEX,
    DAT_CACHE_DIR, DISC_REGEX, SESSION_LOG_DIR, SIZE_REGEX,
)
from .types import ConsoleItem, DataListItem, GameItem, QueueItem
from .messages import (
    BatchComplete, ConsolesLoaded, DownloadComplete, DownloadProgress,
    GamesLoaded, LibraryProgress, LibraryTreeReady, LibraryWatchEvent,
    RatingsLoaded, SystemLog,
)
from .config import ConfigManager
from .library_status import LibraryStatus
from .ratings import RatingsProvider
from .scraper import MyrientScraper
from .toolchain import Toolchain
from .download import DownloadWorker, EngineState, TokenBucket
from .library_ops import LibraryOperation
from .commands import LibraryCommand, OrganizeCommand, RefreshCommand, ConvertCommand, DatAuditCommand
from .utils import normalize_game_title, normalize_game_title_keep_disc, strip_extension, extract_region, extract_revision
from .modals import ConfirmDeleteScreen, ConfirmDownloadScreen, HelpModal

# ── Optional watchdog import for filesystem watch mode ───────────────────────
try:
    from watchdog.observers import Observer as _WatchdogObserver
    from watchdog.events import FileSystemEventHandler as _FSEventHandler
    _WATCHDOG_AVAILABLE = True
except ImportError:
    _WATCHDOG_AVAILABLE = False
    _WatchdogObserver = None   # type: ignore[assignment,misc]
    _FSEventHandler   = object # type: ignore[assignment,misc]


class MyrientTUI(App):
    TITLE = "MYRIENT"
    SUB_TITLE = "ROM Library Manager"

    CSS_PATH = "../tui_dl.tcss"

    BINDINGS = [
        ("ctrl+q", "quit",           "Quit"),
        ("ctrl+d", "toggle_dark",    "Theme"),
        ("ctrl+r", "refresh_browser","Refresh"),
        ("ctrl+j", "jump_to_console","Jump→Browser"),
        ("ctrl+enter", "start_downloads", "Start DL"),   # U6
        ("ctrl+p",     "pause_downloads", "Pause DL"),   # U6
        ("escape",  "escape_input",  "Escape"),
        ("question_mark", "show_help", "Help"),
        ("1", "nav_pane('pane-browse')",    "Browse"),
        ("2", "nav_pane('pane-downloads')", "Downloads"),
        ("3", "nav_pane('pane-library')",   "Library"),
        ("4", "nav_pane('pane-settings')",  "Settings"),
        ("5", "nav_pane('pane-logs')",      "Logs"),
    ]

    def __init__(self):
        super().__init__()
        self.state = ConfigManager()
        self._lib_status = LibraryStatus()

        # ── Extracted subsystems ───────────────────────────────────────────────
        # MyrientScraper owns the TTL link cache; MyrientTUI only calls
        # self.scraper.scrape_links() / self.scraper.clear_cache().
        self.scraper = MyrientScraper(self.post_message)
        self._all_consoles_data: list[ConsoleItem] = []
        self._all_games_data:    list[GameItem] = []
        self._games_lookup:      dict[str, GameItem] = {}

        self.selected_console: dict[str, str] | None = None

        self.proc_lock      = threading.Lock()
        self.active_processes: set[subprocess.Popen] = set()
        self.chd_lock       = threading.Lock()

        # Engine Control State — declared early so Toolchain can receive the
        # actual cancel_flag object (not a dummy Event created by hasattr guard).
        self._engine_state  = EngineState.IDLE
        self._engine_lock   = threading.Lock()
        self.cancel_flag    = threading.Event()   # download workers
        self._lib_cancel    = threading.Event()   # library operations
        self._progress_lock = threading.Lock()
        # Initialise progress counters early — _update_global_statusbar reads
        # these under _progress_lock and would raise AttributeError if they
        # didn't exist yet (race between engine_state → RUNNING and the first
        # assignment inside start_download_engine).
        self.global_completed: int = 0
        self.global_total:     int = 0

        # ── Toolchain subsystem ───────────────────────────────────────────────
        # Owns binary discovery, package-manager install, chdman conversion, and
        # PS2 Master Disc Patcher invocation.  MyrientTUI delegates all tool calls
        # to self.toolchain.* so it never spawns chdman/ps2_master directly.
        self.toolchain = Toolchain(
            post_message_fn    = self.post_message,
            cancel_flag        = self.cancel_flag,
            register_process   = self._register_process,
            unregister_process = self._unregister_process,
            chd_lock           = self.chd_lock,
        )

        # Game / filter selection state
        self._selected_games:      set[str] = set()
        self._filter_include_sel:  set[str] = set()
        self._filter_exclude_sel:  set[str] = set()

        # IGDB ratings state
        self._ratings_provider: RatingsProvider | None = None
        self._ratings_cancel = threading.Event()
        self._game_metadata: dict[str, dict] = {}   # clean_name → GameMetadata
        self._browse_sort_key: str = "name"          # "name" | "rating" | "popularity" | "size"
        self._browse_sort_reverse: bool = False
        self._browse_active_tags: set[str] = set()
        self._browse_available_tags: list[str] = []
        self._last_loaded_console: str = ""

        # Separate debounce timers per search box
        self._consoles_search_timer: Timer | None = None
        self._games_search_timer:    Timer | None = None

        # Track which progress containers are mounted — avoids exception-as-control-flow
        self._active_progress_containers: set[str] = set()

        # Periodic config flush timer
        self._flush_timer: Timer | None = None

        # Session log — opened in on_mount, closed in on_unmount.
        # All _log() calls are mirrored here as plain text with full timestamps.
        self._session_log_file: Any = None

        # Watchdog observer for library filesystem watch mode
        self._watch_observer: Any = None   # _WatchdogObserver instance or None
        self._watch_debounce_timer: Timer | None = None

        # Cached LibraryTreeReady for detail panel

        # (batch succeeded/failed counts are computed locally inside
        # start_download_engine — no shared state needed)

        # Cache external-tool availability once at startup.
        # shutil.which() is a filesystem probe — calling it on every download
        # attempt (per retry, per concurrent worker) is wasteful and noisy.
        self._wget_available:  bool = bool(shutil.which("wget"))
        self._unzip_available: bool = bool(shutil.which("unzip"))

        # ── Redesign state ────────────────────────────────────────────────────
        # Active nav pane ID (used to sync highlight on restore)
        self._current_pane: str = "pane-browse"

        # Log filtering / search
        self._log_filter: str = "all"           # "all" | "err"
        self._log_buffer: deque[tuple[Any, bool]] = deque(maxlen=2000)  # (Text, is_error)
        self._log_search_text: str = ""
        self._log_search_timer: Timer | None = None

        # Queue multi-select state
        self._queue_selected: set[str] = set()

        # Download scheduling
        self._scheduled_time: str = ""  # HH:MM format, empty = immediate
        self._schedule_timer: Timer | None = None

        # Global search state
        self._global_search_results: dict[str, str] = {}  # key → console_name
        self._global_search_timer: Timer | None = None

        # F1: Per-worker speed tracking for aggregate display
        self._worker_speeds: dict[str, float] = {}

        # N6: Queue range selection — last toggled index
        self._last_queue_selected_idx: int = -1

        # N1: Library search
        self._lib_search_timer: Timer | None = None
        self._lib_search_text: str = ""
        self._last_lib_tree_data: LibraryTreeReady | None = None

        # F3: In-library path set (populated on library scan)
        self._library_game_names: set[str] = set()

    # ── Dynamic source URLs ───────────────────────────────────────────────
    @property
    def _active_base_url(self) -> str:
        return self.state.get_active_source()["browse_url"]

    @property
    def _active_dat_url(self) -> str:
        return self.state.get_active_source().get("dat_url", "")

    # ── Console detection ────────────────────────────────────────────────
    _SKIP_NAMES: frozenset[str] = frozenset({
        "files", "donate", "upload", "faq", "contact", "login", "register",
    })

    def _filter_console_items(self, items: list[ConsoleItem]) -> list[ConsoleItem]:
        """Filter scraped links to those that look like console directories.

        Works with both Apache/nginx directory listings (trailing ``/``) and
        non-directory-listing sites (links that are direct children of the
        browse URL with no file extension).
        """
        base_path = urllib.parse.urlparse(self._active_base_url).path.rstrip("/")
        consoles: list[ConsoleItem] = []
        for i in items:
            url = i["url_part"]
            name_lower = i["name"].strip("/").lower()
            if name_lower in self._SKIP_NAMES or not name_lower:
                continue
            # Directory-listing style: trailing slash means directory
            if url.endswith("/"):
                consoles.append(i)
                continue
            # Non-directory site: accept direct child paths without download extensions
            if url.startswith("/"):
                child = url.rstrip("/")
                if child.startswith(base_path + "/"):
                    relative = child[len(base_path) + 1:]
                    if "/" not in relative and not any(
                        child.lower().endswith(ext) for ext in _DOWNLOAD_EXTS
                    ):
                        consoles.append(i)
        return consoles

    # ── S4: Helper factory ───────────────────────────────────────────────
    def _make_queue_item(self, console_name: str, game_name: str,
                         game_url: str, dest_path: str, size_str: str) -> QueueItem:
        """S4: Canonical queue-item factory — eliminates copy-paste across 8 sites."""
        return {
            "id": f"dl_{uuid.uuid4().hex[:8]}",
            "name": f"{console_name} / {game_name}",
            "game_url": game_url,
            "dest_path": dest_path,
            "size_str": size_str,
        }

    def action_escape_input(self) -> None:
        """Escape: blur the focused Input widget so pane-nav keys work again."""
        if isinstance(self.focused, Input):
            self.focused.blur()

    def action_start_downloads(self) -> None:
        """U6: Ctrl+Enter — start download engine from any pane."""
        if self.state.get_active_queue() and not self.engine_running:
            self.start_download_engine()

    def action_pause_downloads(self) -> None:
        """U6: Ctrl+P — pause downloads from any pane."""
        if self.engine_running:
            self._handle_pause_dl()

    @property
    def engine_running(self) -> bool:
        """Backward-compatible check — True when the download engine is active."""
        return self._engine_state in (EngineState.RUNNING, EngineState.PAUSING)

    def _flash_nav_button(self, button_id: str, duration: float = 1.5) -> None:
        """Briefly highlight a nav button (e.g. after queuing items)."""
        try:
            btn = self.query_one(f"#{button_id}", Button)
            btn.add_class("--nav-flash")
            self.set_timer(duration, lambda: btn.remove_class("--nav-flash"))
        except Exception:
            pass

    def action_refresh_browser(self) -> None:
        """Ctrl+R: re-scrape console list (bypasses cache)."""
        self.scraper.clear_cache()
        self._all_games_data = []
        self._games_lookup = {}
        self._selected_games.clear()
        self._update_selection_count()
        try:
            self.query_one("#game-list", DataTable).clear()
        except Exception as e:
            logging.debug("Clear game list failed: %s", e)
        self.fetch_consoles()

    def action_toggle_dark(self) -> None:
        """Override default toggle_dark to persist the theme choice."""
        super().action_toggle_dark()
        try:
            self.state.set_setting("theme", "dark" if self.dark else "light", immediate=False)
        except AttributeError:
            pass  # .dark reactive not available in this Textual build

    def action_jump_to_console(self) -> None:
        """Ctrl+J: from a selected queue row, open the browser tab and highlight the console."""
        try:
            table = self.query_one("#queue-table", DataTable)
            rows = list(table.ordered_rows)
            if not rows or table.cursor_row is None:
                return
            if table.cursor_row >= len(rows):
                return
            item_id = rows[table.cursor_row].key.value
            # Find queue item by id to get the console name
            current_queue = self.state.get_active_queue()
            item = next((i for i in current_queue if i["id"] == item_id), None)
            if not item:
                return
            # Item name format: "Console Name / game.zip"
            console_name_raw = item["name"].split(" / ")[0].strip()
            # Switch to browse pane
            self._nav_switch("pane-browse")
            # Search for the console
            search_input = self.query_one("#search-consoles", Input)
            search_input.value = console_name_raw
            self._render_consoles(console_name_raw)
        except Exception as e:
            logging.debug("Jump to console failed: %s", e)

    def _register_process(self, proc: subprocess.Popen) -> None:
        with self.proc_lock:
            self.active_processes.add(proc)

    def _unregister_process(self, proc: subprocess.Popen) -> None:
        with self.proc_lock:
            self.active_processes.discard(proc)

    def cleanup_subprocesses(self) -> None:
        """Safely tears down background tasks, enforcing a hard kill to prevent OS memory leaks."""
        # Snapshot and clear under lock, then release — blocking wait/kill must not hold the lock
        with self.proc_lock:
            procs = list(self.active_processes)
            self.active_processes.clear()
        for proc in procs:
            try:
                proc.terminate()
                proc.wait(timeout=1)
            except subprocess.TimeoutExpired:
                proc.kill()
                try:
                    proc.wait(timeout=1)   # reap zombie — POSIX requires wait() after kill()
                except Exception as e:
                    logging.debug("Zombie reap failed after kill: %s", e)
            except Exception as e:
                logging.debug("Subprocess cleanup failed: %s", e)

    @work(exclusive=True, thread=True)
    def setup_chdman_auto(self) -> None:
        """Delegate chdman setup to Toolchain."""
        self.toolchain.setup_chdman_auto()

    @work(exclusive=True, thread=True)
    def setup_ps2mdp_auto(self) -> None:
        """Delegate PS2 patcher setup to Toolchain."""
        self.toolchain.setup_ps2mdp_auto()

    @work(exclusive=True, thread=True)
    def run_ps2_master_disc_patch(self) -> None:
        """Patch PS2 ISO/BIN images as Master Discs for MechaPwn.

        Scope is determined by _ps2mdp_target (set in on_button_pressed from
        the tree cursor before calling this worker):
          Path == library root  → scan all PS2 console folders in the library
          Path == console dir   → patch that console only
          Path == game dir      → patch that one game only

        The patcher modifies the ISO in-place and writes a DVD_Sectors.Bin
        sidecar file alongside it. Re-runs skip any game dir that already
        contains DVD_Sectors.Bin.
        Originals are never deleted.
        """
        self._lib_cancel.clear()
        # Resolve locally — same race-safety rationale as run_lib_convert.
        ps2mdp = self.toolchain.ps2mdp_path or Toolchain.find_ps2mdp()
        if not ps2mdp:
            self.post_message(SystemLog(
                "[bold red]ps2_master not found.[/bold red] "
                "Run 'Setup PS2 Patcher' first.", True
            ))
            return

        library  = Path(self.state.settings["library_root"])
        scope_path: Path = getattr(self, "_ps2mdp_target", library)

        # ── Build the list of game dirs to process ───────────────────────────
        if scope_path == library:
            scope_label = "full library (PS2 only)"
            # Collect PS2 console dirs first, then walk the library once and
            # filter — avoids a full O(n) walk per PS2 console (was O(n × k)).
            ps2_console_dirs = {
                d for d in library.iterdir()
                if d.is_dir() and not d.name.startswith('.')
                and "PlayStation 2" in d.name
            }
            game_dirs = [
                gd
                for _, gd, _ in self._walk_library_game_dirs(library, self._lib_status)
                if any(gd.is_relative_to(d) for d in ps2_console_dirs)
            ]
        elif scope_path.parent == library:
            scope_label = scope_path.name
            game_dirs = [
                gd for _, gd, _ in self._walk_library_game_dirs(library, self._lib_status)
                if gd.is_relative_to(scope_path)
            ]
        else:
            scope_label = scope_path.name
            # If scope is a multi-disc grouping folder (no game files itself,
            # but contains disc subdirs), expand to the individual disc dirs.
            try:
                disc_subdirs = sorted(
                    (d for d in scope_path.iterdir()
                     if d.is_dir() and DISC_REGEX.search(d.name)),
                    key=lambda d: d.name,
                )
            except (PermissionError, OSError):
                disc_subdirs = []
            game_dirs = disc_subdirs if disc_subdirs else [scope_path]

        if not game_dirs:
            self.post_message(SystemLog(
                f"PS2 Master Disc: No game directories found in [{scope_label}].\n"
                "Make sure the selected node is a PS2 console or game, and the library is populated."
            ))
            return

        self.post_message(SystemLog(
            f"PS2 Master Disc: Patching {len(game_dirs)} game dir(s) in [{scope_label}]…"
        ))

        patched = skipped = failed = 0
        total = len(game_dirs)

        for i, game_dir in enumerate(game_dirs, 1):
            if self._lib_cancel.is_set():
                self.post_message(SystemLog("[yellow]PS2 Master Disc patching cancelled.[/]"))
                break

            self.post_message(LibraryProgress(
                f"PS2 MD Patch ({i}/{total})", game_dir.name, i, total
            ))

            try:
                # ps2_master creates a DVD_Sectors.Bin sidecar next to the ISO
                # when patching succeeds — use its presence as the already-patched
                # indicator so re-runs skip files that were previously processed.
                candidates = [
                    f for f in game_dir.iterdir()
                    if f.is_file()
                    and f.suffix.lower() in _PS2_PATCH_EXTS
                    and not (f.parent / "DVD_Sectors.Bin").exists()
                ]
            except PermissionError:
                failed += 1
                continue

            if not candidates:
                skipped += 1
                continue

            for src_file in candidates:
                if self._lib_cancel.is_set():
                    break

                self.post_message(SystemLog(f"PS2 MD: Patching [bold]{_escape_markup(src_file.name)}[/bold]…"))
                try:
                    # Run from the game directory so DVD_Sectors.Bin lands there.
                    # ps2_master patches the image in-place and writes DVD_Sectors.Bin
                    # as a sector backup alongside the ISO.
                    proc = subprocess.Popen(
                        [ps2mdp, str(src_file)],
                        cwd=str(game_dir),
                        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                    )
                    self._register_process(proc)
                    stdout_b, stderr_b = proc.communicate(timeout=300)
                    self._unregister_process(proc)

                    if proc.returncode == 0:
                        patched += 1
                        self.post_message(SystemLog(
                            f"[green]PS2 MD: ✓ Patched[/green] {_escape_markup(src_file.name)}"
                        ))
                    else:
                        failed += 1
                        err_msg = (stdout_b + stderr_b).decode("utf-8", errors="replace").strip()
                        self.post_message(SystemLog(
                            f"[red]PS2 MD: Patcher failed[/red] for {_escape_markup(src_file.name)} "
                            f"(exit {proc.returncode}):\n{_escape_markup(err_msg)}",
                            True,
                        ))
                except subprocess.TimeoutExpired:
                    proc.kill()
                    proc.wait()            # reap zombie to avoid resource leak
                    self._unregister_process(proc)
                    failed += 1
                    self.post_message(SystemLog(
                        f"[red]PS2 MD: Timeout[/red] patching {_escape_markup(src_file.name)}", True
                    ))
                except Exception as e:
                    failed += 1
                    self.post_message(SystemLog(
                        f"[red]PS2 MD: Error[/red] patching {_escape_markup(src_file.name)}: {_escape_markup(str(e))}", True
                    ))

        self.post_message(LibraryProgress("PS2 MD Patch", "Complete", total, total))
        self.post_message(SystemLog(
            f"PS2 Master Disc Patch complete — "
            f"[bold green]{patched}[/] patched, "
            f"[bold yellow]{skipped}[/] skipped, "
            f"[bold red]{failed}[/] failed.\n"
            "Images are patched in-place. Directories with a [dim]DVD_Sectors.Bin[/dim] "
            "file will be skipped on future runs."
        ))

    @work(exclusive=True, thread=True)
    def run_ps2_master_disc_unpatch(self) -> None:
        """Restore PS2 ISO/BIN images to their original pre-patched state.

        Re-runs ps2_master on games that have a DVD_Sectors.Bin sidecar file.
        ps2_master detects the sidecar and restores the original sectors, then
        removes DVD_Sectors.Bin on success.
        """
        self._lib_cancel.clear()
        ps2mdp = self.toolchain.ps2mdp_path or Toolchain.find_ps2mdp()
        if not ps2mdp:
            self.post_message(SystemLog(
                "[bold red]ps2_master not found.[/bold red] "
                "Run 'Setup PS2 Patcher' first.", True
            ))
            return

        library = Path(self.state.settings["library_root"])
        scope_path: Path = getattr(self, "_ps2mdp_target", library)

        # ── Build the list of game dirs to process ───────────────────────────
        if scope_path == library:
            scope_label = "full library (PS2 only)"
            ps2_console_dirs = {
                d for d in library.iterdir()
                if d.is_dir() and not d.name.startswith('.')
                and "PlayStation 2" in d.name
            }
            game_dirs = [
                gd
                for _, gd, _ in self._walk_library_game_dirs(library, self._lib_status)
                if any(gd.is_relative_to(d) for d in ps2_console_dirs)
            ]
        elif scope_path.parent == library:
            scope_label = scope_path.name
            game_dirs = [
                gd for _, gd, _ in self._walk_library_game_dirs(library, self._lib_status)
                if gd.is_relative_to(scope_path)
            ]
        else:
            scope_label = scope_path.name
            try:
                disc_subdirs = sorted(
                    (d for d in scope_path.iterdir()
                     if d.is_dir() and DISC_REGEX.search(d.name)),
                    key=lambda d: d.name,
                )
            except (PermissionError, OSError):
                disc_subdirs = []
            game_dirs = disc_subdirs if disc_subdirs else [scope_path]

        # Filter to only dirs that have DVD_Sectors.Bin (i.e. previously patched)
        game_dirs = [
            gd for gd in game_dirs
            if (gd / "DVD_Sectors.Bin").exists()
        ]

        if not game_dirs:
            self.post_message(SystemLog(
                f"PS2 Unpatch: No patched games found in [{scope_label}].\n"
                "Only games with a [dim]DVD_Sectors.Bin[/dim] sidecar can be unpatched."
            ))
            return

        self.post_message(SystemLog(
            f"PS2 Unpatch: Restoring {len(game_dirs)} game dir(s) in [{scope_label}]…"
        ))

        restored = failed = 0
        total = len(game_dirs)

        for i, game_dir in enumerate(game_dirs, 1):
            if self._lib_cancel.is_set():
                self.post_message(SystemLog("[yellow]PS2 unpatch cancelled.[/]"))
                break

            self.post_message(LibraryProgress(
                f"PS2 Unpatch ({i}/{total})", game_dir.name, i, total
            ))

            # Find the ISO/BIN that was patched
            try:
                candidates = [
                    f for f in game_dir.iterdir()
                    if f.is_file() and f.suffix.lower() in _PS2_PATCH_EXTS
                ]
            except PermissionError:
                failed += 1
                continue

            if not candidates:
                failed += 1
                self.post_message(SystemLog(
                    f"[red]PS2 Unpatch:[/red] No ISO/BIN found in "
                    f"{_escape_markup(game_dir.name)} to restore.", True
                ))
                continue

            for src_file in candidates:
                if self._lib_cancel.is_set():
                    break

                self.post_message(SystemLog(
                    f"PS2 Unpatch: Restoring [bold]{_escape_markup(src_file.name)}[/bold]…"
                ))
                try:
                    proc = subprocess.Popen(
                        [ps2mdp, str(src_file)],
                        cwd=str(game_dir),
                        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                    )
                    self._register_process(proc)
                    stdout_b, stderr_b = proc.communicate(timeout=300)
                    self._unregister_process(proc)

                    sidecar = game_dir / "DVD_Sectors.Bin"
                    if proc.returncode == 0:
                        # ps2_master should remove DVD_Sectors.Bin on restore;
                        # if it didn't, clean up manually.
                        if sidecar.exists():
                            try:
                                sidecar.unlink()
                            except OSError:
                                pass
                        restored += 1
                        self.post_message(SystemLog(
                            f"[green]PS2 Unpatch: ✓ Restored[/green] "
                            f"{_escape_markup(src_file.name)}"
                        ))
                    else:
                        failed += 1
                        err_msg = (stdout_b + stderr_b).decode(
                            "utf-8", errors="replace"
                        ).strip()
                        self.post_message(SystemLog(
                            f"[red]PS2 Unpatch: Failed[/red] for "
                            f"{_escape_markup(src_file.name)} "
                            f"(exit {proc.returncode}):\n"
                            f"{_escape_markup(err_msg)}",
                            True,
                        ))
                except subprocess.TimeoutExpired:
                    proc.kill()
                    proc.wait()
                    self._unregister_process(proc)
                    failed += 1
                    self.post_message(SystemLog(
                        f"[red]PS2 Unpatch: Timeout[/red] restoring "
                        f"{_escape_markup(src_file.name)}", True
                    ))
                except Exception as e:
                    failed += 1
                    self.post_message(SystemLog(
                        f"[red]PS2 Unpatch: Error[/red] restoring "
                        f"{_escape_markup(src_file.name)}: "
                        f"{_escape_markup(str(e))}", True
                    ))

        self.post_message(LibraryProgress("PS2 Unpatch", "Complete", total, total))
        self.post_message(SystemLog(
            f"PS2 Unpatch complete — "
            f"[bold green]{restored}[/] restored, "
            f"[bold red]{failed}[/] failed."
        ))

    @staticmethod
    def _format_size(size_bytes: int) -> str:
        if size_bytes <= 0:
            return "0 B"
        size_float = float(size_bytes)
        for unit in _SIZE_UNITS[:-1]:   # stop before the last unit and use it as fallback
            if size_float < 1024.0:
                return f"{size_float:.2f} {unit}"
            size_float /= 1024.0
        return f"{size_float:.2f} {_SIZE_UNITS[-1]}"

    def compose(self) -> ComposeResult:
        yield Header(show_clock=True)

        with Horizontal(id="app-body"):

            # ── Left navigation sidebar ───────────────────────────────────
            with Vertical(id="nav-sidebar"):
                yield Label("◈  MYRIENT", id="nav-logo")
                yield Button("◈  Browse",     id="nav-btn-browse",    classes="nav-btn")
                yield Button("▶  Downloads",  id="nav-btn-downloads", classes="nav-btn")
                yield Button("⊞  Library",    id="nav-btn-library",   classes="nav-btn")
                yield Button("◎  Settings",   id="nav-btn-settings",  classes="nav-btn")
                yield Button("≡  Logs",        id="nav-btn-logs",      classes="nav-btn")
                yield Label("", id="nav-status")

            # ── Content area: one pane per section ───────────────────────
            with Vertical(id="content-area"):
                yield BrowsePane(id="pane-browse", classes="content-pane")
                yield DownloadsPane(id="pane-downloads", classes="content-pane")
                yield LibraryPane(id="pane-library", classes="content-pane")
                yield SettingsPane(id="pane-settings", classes="content-pane")
                yield LogsPane(id="pane-logs", classes="content-pane")

        # ── Global status bar (always visible, above Footer) ─────────────
        with Horizontal(id="global-statusbar"):
            yield Label("●  Idle", id="gs-engine")
            yield Label("", id="gs-speed")
            yield Label("", id="gs-queue")

        yield Footer()

    def on_mount(self) -> None:
        # Queue table — Status column replaces dest_path
        table = self.query_one("#queue-table", DataTable)
        table.add_columns("Game", "Size", "Status")
        table.cursor_type = "row"

        # B1: History table
        htable = self.query_one("#history-table", DataTable)
        htable.add_columns("Game", "Console", "Size", "Date")
        htable.cursor_type = "row"
        self._refresh_history_table()

        # Game browser table — columns recreated with dynamic widths in
        # _render_games(); headers are visible and clickable for sorting.
        game_table = self.query_one("#game-list", DataTable)
        game_table.add_column("", key="sel", width=self._GAME_COL_SEL_W)
        game_table.add_column("Game", key="name", width=45)
        game_table.add_column("Rating", key="rating", width=self._GAME_COL_RATING_W)
        game_table.add_column("Size", key="size", width=self._GAME_COL_SIZE_W)
        game_table.show_header = True
        # Start with empty state visible, game view hidden
        self._show_browse_game_view(False)
        self._browse_global_mode = False

        # F3: Filter tags are configurable via settings, with sensible defaults
        inc_tags = self.state.settings.get("include_tags", ["USA", "Europe", "Japan", "World"])
        exc_tags = self.state.settings.get("exclude_tags", ["Demo", "Beta", "Proto"])
        _INCLUDE_OPTS = [(t, t) for t in inc_tags]
        _EXCLUDE_OPTS = [(t, t) for t in exc_tags]
        for tbl_id, opts in (("set-include", _INCLUDE_OPTS), ("set-exclude", _EXCLUDE_OPTS)):
            tbl = self.query_one(f"#{tbl_id}", DataTable)
            tbl.add_column("", key="sel", width=3)
            tbl.add_column("Tag", key="name")
            tbl.show_header = False
            for label, value in opts:
                tbl.add_row(Text(" ", style="dim"), Text(label, style="dim"), key=value)

        # Initial toolbar state — show root-level operations
        self._update_lib_toolbar(None)

        # Hide IGDB sort/tag rows until credentials are configured
        self._update_igdb_ui_visibility()

        self._refresh_queue_dropdown()
        self._refresh_queue_table()
        self._load_settings_toggles()
        self._populate_source_select()
        self.fetch_consoles()
        # Load library status store before scanning so the tree renders correctly.
        self._lib_status.load(Path(self.state.settings['library_root']), db=self.state._db)
        self.run_lib_status_scan()
        # Flush deferred config writes every 3 s — catches any dirty state from
        # in-progress downloads without hammering the disk on every completion.
        self._flush_timer = self.set_interval(_FLUSH_INTERVAL, self.state.flush_if_dirty)

        # Resolve chdman path once at startup via Toolchain
        self.toolchain.refresh_chdman()
        if not self.toolchain.chdman_path:
            self._log(
                "[yellow]chdman not found.[/yellow] "
                "CHD conversion is disabled. Use [bold]'Setup chdman'[/bold] in Settings to install.",
                is_error=False,
            )

        # Resolve PS2 Master Disc Patcher path once at startup via Toolchain
        self.toolchain.refresh_ps2mdp()
        if not self.toolchain.ps2mdp_path:
            self._log(
                "[yellow]ps2_master not found.[/yellow] "
                "PS2 Master Disc patching disabled. Use [bold]'Setup PS2 Patcher'[/bold] in Settings to install.",
                is_error=False,
            )

        # Probe wget and unzip at startup so users see a clear message before
        # the first download attempt fails with a cryptic OS error.
        if not self._wget_available:
            self._log(
                "[yellow]wget not found.[/yellow] "
                "Downloads will use urllib fallback only. "
                "Install wget for better resumable-download support.",
                is_error=False,
            )
        if not self._unzip_available:
            self._log(
                "[yellow]unzip not found.[/yellow] "
                "ZIP extraction will use Python's built-in zipfile module instead. "
                "Install unzip if you encounter extraction problems.",
                is_error=False,
            )

        # ── Restore theme preference ───────────────────────────────────────
        saved_theme = self.state.settings.get("theme", "dark")
        try:
            if saved_theme == "light" and self.dark:
                self.dark = False
            elif saved_theme == "dark" and not self.dark:
                self.dark = True
        except AttributeError:
            pass  # .dark reactive not available in this Textual build

        # ── Populate filter preset dropdown ───────────────────────────────
        self._refresh_preset_dropdown()

        # ── Populate per-queue settings from stored overrides ──────────────
        q_settings = self.state.get_queue_settings(self.state.active_queue_name)
        try:
            self.query_one("#input-queue-speed-limit", Input).value = \
                str(q_settings.get("speed_limit_mbps", 0))
            mc = q_settings.get("max_concurrent")
            self.query_one("#input-queue-max-concurrent", Input).value = \
                str(mc) if mc is not None else ""
        except Exception as e:
            logging.debug("Populate per-queue settings failed: %s", e)

        # ── Start watchdog observer if enabled ────────────────────────────
        if self.state.settings.get("watch_library", False):
            self._start_watchdog()

        # ── Open session log ──────────────────────────────────────────────
        try:
            SESSION_LOG_DIR.mkdir(parents=True, exist_ok=True)
            now = datetime.datetime.now()
            ts = now.strftime("%Y%m%d_%H%M%S")
            log_path = SESSION_LOG_DIR / f"myrient_{ts}.log"
            self._session_log_file = open(log_path, 'w', encoding='utf-8', buffering=1)
            self._session_log_file.write(
                f"# Myrient session log — started {now.isoformat()}\n"
            )
            # B11: Safety net — flush and close session log on abnormal termination
            def _atexit_close_log(fh=self._session_log_file):
                try:
                    if not fh.closed:
                        fh.flush()
                        fh.close()
                except OSError:
                    pass
            atexit.register(_atexit_close_log)
            # Prune old session logs — keep only the most recent _SESSION_LOG_MAX_FILES.
            self._prune_session_logs()
        except OSError as e:
            self._session_log_file = None
            self._log(f"Could not open session log file: {e}", is_error=True)

        # Populate the session log viewer list
        self._refresh_session_log_list()

        # ── Activate initial pane (Browse) and init log filter btn ───────
        self._nav_switch("pane-browse")
        try:
            self.query_one("#log-filter-all", Button).add_class("--log-active")
        except Exception as e:
            logging.debug("Init log filter button failed: %s", e)
        # Show breadcrumb placeholder
        self._update_breadcrumb()
        # Initial global statusbar state
        self._update_global_statusbar()

    # ═══════════════════════════════════════════════════════════════════════
    # Navigation helpers
    # ═══════════════════════════════════════════════════════════════════════

    def _nav_switch(self, pane_id: str) -> None:
        """Show the requested content pane and update sidebar nav highlights."""
        for pid in self._NAV_PANE_IDS:
            try:
                self.query_one(f"#{pid}").display = (pid == pane_id)
            except Exception as e:
                logging.debug("Nav pane toggle %s failed: %s", pid, e)
        for pid, bid in self._NAV_BTN_MAP.items():
            try:
                btn = self.query_one(f"#{bid}", Button)
                if pid == pane_id:
                    btn.add_class("--nav-active")
                else:
                    btn.remove_class("--nav-active")
            except Exception as e:
                logging.debug("Nav button toggle %s failed: %s", bid, e)
        self._current_pane = pane_id

    def action_nav_pane(self, pane_id: str) -> None:
        """1–5: switch nav pane directly (only when no text Input is focused)."""
        focused = self.focused
        if isinstance(focused, Input):
            return  # let the digit go to the input widget
        self._nav_switch(pane_id)

    def on_resize(self, event) -> None:
        """Adjust layouts when terminal size changes."""
        try:
            grid = self.query_one("#progress-grid", Container)
            cols = 2 if self.size.width >= 120 else 1
            grid.styles.grid_size_columns = cols
        except Exception as e:
            logging.debug("Resize progress grid failed: %s", e)
        # Re-render game table so dynamic column widths track the new size
        if self._all_games_data:
            try:
                query = self.query_one("#search-games", Input).value
            except Exception:
                query = ""
            self._render_games(query)

    def action_show_help(self) -> None:
        """? — open the keyboard shortcut help modal."""
        self.push_screen(HelpModal())

    def _update_breadcrumb(self, console_name: str = "", game_count: int = 0) -> None:
        """Update the Browse pane breadcrumb trail."""
        try:
            lbl = self.query_one("#breadcrumb", Label)
            if not console_name:
                lbl.update(Text(""))
                return
            t = Text()
            t.append(self.state.get_active_source()["name"] or "Source", style="#3d4451")
            t.append("  ›  ", style="dim #1c2333")
            t.append(console_name, style="#9aa0aa")
            if game_count > 0:
                t.append(f"  ({game_count:,})", style="dim #3d4451")
            # U1: Show active filter indicator
            active_filters = []
            if self._filter_include_sel:
                active_filters.append(", ".join(sorted(self._filter_include_sel)))
            if self._filter_exclude_sel:
                active_filters.append("-" + ", -".join(sorted(self._filter_exclude_sel)))
            if active_filters:
                t.append("  [", style="dim")
                t.append(" ".join(active_filters), style="italic #e6b73e")
                t.append("]", style="dim")
            lbl.update(t)
        except Exception as e:
            logging.debug("Update breadcrumb failed: %s", e)

    def _show_browse_game_view(self, show: bool) -> None:
        """Toggle between the game table and the empty-state placeholder."""
        try:
            self.query_one("#game-list", DataTable).display = show
            self.query_one("#browse-empty-state", Label).display = not show
        except Exception:
            pass

    def _select_all_visible(self) -> None:
        """Select every currently visible row in the game browser."""
        try:
            game_table = self.query_one("#game-list", DataTable)
            for row in game_table.ordered_rows:
                url_part = row.key.value
                if url_part and url_part not in ("LOADING", "EMPTY"):
                    self._selected_games.add(url_part)
            current_query = ""
            try:
                current_query = self.query_one("#search-games", Input).value
            except Exception as e:
                logging.debug("Get search-games input failed: %s", e)
            self._render_games(current_query)
            self._update_selection_count()
        except Exception as e:
            logging.debug("Select all visible failed: %s", e)

    def _update_global_statusbar(self) -> None:
        """Refresh the persistent one-line status bar at the bottom of the screen."""
        try:
            engine_lbl = self.query_one("#gs-engine", Label)
            queue_lbl  = self.query_one("#gs-queue",  Label)
            state = self._engine_state
            if state == EngineState.RUNNING:
                engine_lbl.update(Text.assemble(
                    ("●  ", "bold #3fb950"), ("Downloading", "#9aa0aa")
                ))
            elif state == EngineState.PAUSING:
                engine_lbl.update(Text.assemble(
                    ("●  ", "bold #d29922"), ("Pausing…", "#d29922")
                ))
            elif state == EngineState.PAUSED:
                engine_lbl.update(Text.assemble(
                    ("●  ", "bold #e6b73e"), ("Paused", "#e6b73e")
                ))
            else:
                engine_lbl.update(Text("●  Idle", style="#3d4451"))
            q_len = self.state.active_queue_length()
            if q_len > 0:
                queue_lbl.update(Text(
                    f"{q_len} queued · {self.state.active_queue_name}",
                    style="#3d4451",
                ))
            else:
                queue_lbl.update(Text(""))
            # C5: Lock queue dropdown while engine is active
            try:
                qs = self.query_one("#queue-select", Select)
                qs.disabled = state in (EngineState.RUNNING, EngineState.PAUSING)
            except Exception as e:
                logging.debug("Queue select disable toggle failed: %s", e)
            # C1: Nav-sidebar status summary
            nav_status = self.query_one("#nav-status", Label)
            parts: list[tuple[str, str]] = []
            if state in (EngineState.RUNNING, EngineState.PAUSING):
                with self._progress_lock:
                    done, total = self.global_completed, self.global_total
                parts.append((f"↓ {done}/{total}", "#3fb950"))
            elif state == EngineState.PAUSED:
                parts.append(("⏸ Paused", "#e6b73e"))
            if q_len > 0 and state not in (EngineState.RUNNING, EngineState.PAUSING):
                parts.append((f"◈ {q_len} queued", "#3d4451"))
            if parts:
                nav_status.update(Text.assemble(*[(t + "  ", s) for t, s in parts]))
            else:
                nav_status.update(Text(""))
        except Exception as e:
            logging.debug("Update global statusbar failed: %s", e)
        # F2: Keep queue total size label in sync
        self._update_queue_total_size()

    def _set_log_filter(self, filter_id: str) -> None:
        """Switch active log severity filter and re-render the log widget."""
        level_map = {"log-filter-all": "all", "log-filter-err": "err"}
        self._log_filter = level_map.get(filter_id, "all")
        for btn_id in ("log-filter-all", "log-filter-err"):
            try:
                btn = self.query_one(f"#{btn_id}", Button)
                if btn_id == filter_id:
                    btn.add_class("--log-active")
                else:
                    btn.remove_class("--log-active")
            except Exception as e:
                logging.debug("Log filter button toggle failed: %s", e)
        self._rerender_log()

    def _rerender_log(self) -> None:
        """Re-populate the log widget from the in-memory buffer, honouring
        the current filter level and search string.
        """
        try:
            log_widget = self.query_one("#sys-log", RichLog)
            log_widget.clear()
            for line, is_error in self._log_buffer:
                if self._log_filter == "err" and not is_error:
                    continue
                if self._log_search_text and self._log_search_text not in line.plain.lower():
                    continue
                log_widget.write(line)
        except Exception as e:
            logging.debug("Rerender log failed: %s", e)

    def _log(self, msg: str, is_error: bool = False) -> None:
        # Capture timestamp once — used for both the TUI widget and the file mirror.
        now = datetime.datetime.now()
        ts = now.strftime("%H:%M:%S")
        line = Text()
        line.append(ts, style="dim #3d4451")
        line.append("  ")
        if is_error:
            line.append("ERR", style="bold #f85149")
        else:
            line.append("INF", style="dim #606878")
        line.append("  ")
        try:
            line.append_text(Text.from_markup(msg))
        except Exception:
            line.append(msg)

        # Buffer for re-render on filter/search change (deque maxlen=2000 auto-evicts)
        self._log_buffer.append((line, is_error))

        # Only write to widget if it passes the current filter + search
        try:
            should_show = True
            if self._log_filter == "err" and not is_error:
                should_show = False
            if should_show and self._log_search_text:
                if self._log_search_text not in line.plain.lower():
                    should_show = False
            if should_show:
                self.query_one("#sys-log", RichLog).write(line)
        except Exception:
            # Widget not mounted yet (startup) or already unmounted — normal lifecycle.
            pass

        # Mirror to session log — strip markup to plain text for readability.
        # _log is always invoked on the main thread (via on_system_log message
        # dispatch), so no lock is needed for file writes here.
        if self._session_log_file is not None:
            try:
                full_ts = now.strftime("%Y-%m-%d %H:%M:%S")
                level   = "ERR" if is_error else "INF"
                try:
                    plain_msg = Text.from_markup(msg).plain
                except Exception:
                    plain_msg = msg
                self._session_log_file.write(f"{full_ts}  {level}  {plain_msg}\n")
            except OSError as e:
                logging.debug("Session log write failed: %s", e)

    def on_system_log(self, message: SystemLog) -> None: 
        self._log(message.message, message.is_error)

    def _prune_session_logs(self) -> None:
        """Delete the oldest session log files when the count exceeds _SESSION_LOG_MAX_FILES.
        Called once at startup after the new log file has been opened.
        """
        try:
            log_files = sorted(
                SESSION_LOG_DIR.glob("myrient_*.log"),
                key=lambda p: p.stat().st_mtime,
            )
            excess = len(log_files) - _SESSION_LOG_MAX_FILES
            if excess > 0:
                for old_log in log_files[:excess]:
                    try:
                        old_log.unlink()
                    except OSError:
                        pass
        except OSError:
            pass

    def on_library_tree_ready(self, message: LibraryTreeReady) -> None:
        """Runs on the main thread — safe to touch the widget tree.
        Uses rich.text.Text objects for all user-controlled labels so that
        brackets in game/console names (e.g. [USA], [SLES-00867]) are NEVER
        parsed as markup tags.
        """
        def _game_label(name: str, status: str, has_chd: bool = False,
                        region: str = "", revision: str = "",
                        has_ps2_patch: bool = False) -> Text:
            t = Text(no_wrap=True, overflow="ellipsis")
            if status == "validated":
                t.append("✓ ", style=_TREE_GREEN)
                t.append(name, style=_TREE_GREEN)
            elif status == "corrupted":
                t.append("✗ ", style=_TREE_RED)
                t.append(name, style=_TREE_RED)
            else:
                t.append("~ ", style=_TREE_YELLOW)
                t.append(name, style=_TREE_YELLOW)
            if region:
                t.append(" │ ", style="dim #00ffbb")
                t.append(f"({region})", style="dim #d2a8ff")
            if revision:
                t.append(" │ ", style="dim #00ffbb")
                t.append(revision, style="dim #e0a458")
            if has_chd:
                t.append(" │ ", style="dim #00ffbb")
                t.append("CHD", style="dim #58a6ff")
            if has_ps2_patch:
                t.append(" │ ", style="dim #00ffbb")
                t.append("PS2P", style="dim #f78166")
            return t

        def _console_label(name: str, n_ok: int, n_bad: int, n_inc: int,
                           disk_bytes: int = 0) -> Text:
            t = Text(no_wrap=True)
            t.append(name, style=f"bold {_TREE_AMBER}")
            if n_ok:
                t.append(f" {n_ok}✓", style=_TREE_GREEN)
            if n_bad:
                t.append(f" {n_bad}✗", style=_TREE_RED)
            if n_inc:
                t.append(f" {n_inc}~", style=_TREE_YELLOW)
            if disk_bytes > 0:
                t.append(f" [{MyrientTUI._format_size(disk_bytes)}]", style=_TREE_DIM)
            return t

        self._last_lib_tree_data = message
        search_text = self._lib_search_text

        try:
            tree = self.query_one("#lib-tree", Tree)
            tree.clear()
            library = message.library_path
            root_name = library.name if library.exists() else "Library"
            root_label = Text(root_name, style=f"bold {_TREE_AMBER}", no_wrap=True)
            tree.root.label = root_label

            for console_name, (console_path, games) in message.structure.items():
                counts = Counter(s for _, s, _, _ in games)
                n_ok  = counts["validated"]
                n_bad = counts["corrupted"]
                n_inc = counts["incomplete"]
                # Use pre-computed disk usage from the worker thread — avoids
                # blocking the main thread with heavy I/O on large libraries.
                disk_bytes = message.disk_usage.get(console_name, 0)
                # C6+A2: Group multi-disc games into inline labels
                # Partition into disc entries (keyed by base name) and singles
                # disc_groups values: (game_dir, status, disc_label_str, has_chd)
                disc_groups: dict[str, list[tuple[Path, str, str, bool, bool]]] = {}
                singles: dict[str, tuple[Path, str, bool, bool]] = {}
                for game_dir, status, has_chd, has_ps2_patch in games:
                    m = DISC_REGEX.search(game_dir.name)
                    if m:
                        base = DISC_REGEX.sub('', game_dir.name).strip()
                        disc_label = m.group(0).strip()  # e.g. "(Disc 1)"
                        disc_groups.setdefault(base, []).append((game_dir, status, disc_label, has_chd, has_ps2_patch))
                    else:
                        singles[game_dir.name] = (game_dir, status, has_chd, has_ps2_patch)

                # Build unified sorted list: (sort_key, label, data_path)
                tree_entries: list[tuple[str, Text, Path]] = []

                for name, (game_dir, status, has_chd, has_ps2_patch) in singles.items():
                    if name in disc_groups:
                        continue  # rendered as disc group instead
                    clean = normalize_game_title(name)
                    region = extract_region(name)
                    revision = extract_revision(name)
                    tree_entries.append((clean.lower(), _game_label(clean, status, has_chd, region, revision, has_ps2_patch), game_dir))

                for base_name, discs in disc_groups.items():
                    clean_base = normalize_game_title(base_name)
                    region = extract_region(base_name)
                    revision = extract_revision(base_name)
                    discs.sort(key=lambda d: d[2])  # sort by disc label
                    t = Text(no_wrap=True, overflow="ellipsis")
                    # Aggregate status for leading icon + game name
                    statuses = {s for _, s, _, _, _ in discs}
                    if statuses == {"validated"}:
                        t.append("✓ ", style=_TREE_GREEN)
                        t.append(clean_base, style=_TREE_GREEN)
                    elif "corrupted" in statuses:
                        t.append("✗ ", style=_TREE_RED)
                        t.append(clean_base, style=_TREE_RED)
                    else:
                        t.append("~ ", style=_TREE_YELLOW)
                        t.append(clean_base, style=_TREE_YELLOW)
                    # Region tag
                    if region:
                        t.append(" │ ", style="dim #00ffbb")
                        t.append(f"({region})", style="dim #d2a8ff")
                    # Revision tag
                    if revision:
                        t.append(" │ ", style="dim #00ffbb")
                        t.append(revision, style="dim #e0a458")
                    # CHD indicator if any disc is in CHD format
                    any_chd = any(c for _, _, _, c, _ in discs)
                    if any_chd:
                        t.append(" │ ", style="dim #00ffbb")
                        t.append("CHD", style="dim #58a6ff")
                    # PS2 patch indicator if any disc is patched
                    any_ps2_patch = any(p for _, _, _, _, p in discs)
                    if any_ps2_patch:
                        t.append(" │ ", style="dim #00ffbb")
                        t.append("PS2P", style="dim #f78166")
                    # Dim pipe separator before per-disc status
                    t.append(" │ ", style="dim #00ffbb")
                    # Per-disc status: dim grey number + small colored icon
                    for i, (_, st, dlbl, _, _) in enumerate(discs):
                        num_m = re.search(r'\d+', dlbl)
                        dnum = num_m.group(0) if num_m else dlbl
                        if i > 0:
                            t.append(" ", style="dim")
                        t.append(f"({dnum})", style="dim #6e7681")
                        if st == "validated":
                            t.append("✓", style="dim green")
                        elif st == "corrupted":
                            t.append("✗", style="dim red")
                        else:
                            t.append("~", style="dim yellow")
                    group_path = discs[0][0].parent
                    tree_entries.append((clean_base.lower(), t, group_path))

                # N1: Filter by library search text
                if search_text:
                    tree_entries = [
                        e for e in tree_entries if search_text in e[0]
                    ]
                    # Skip entire console if no games match and console name doesn't match
                    if not tree_entries and search_text not in console_name.lower():
                        continue

                console_node = tree.root.add(
                    _console_label(console_name, n_ok, n_bad, n_inc, disk_bytes),
                    data=console_path,
                )

                # Render all entries in alphabetical order
                tree_entries.sort(key=lambda e: e[0])
                for _, label, data_path in tree_entries:
                    console_node.add_leaf(label, data=data_path)

            if not message.structure:
                no_games = Text("No consoles found — check library path in Settings", style=_TREE_DIM)
                tree.root.add_leaf(no_games)

            tree.root.expand_all()
            self.query_one("#lib-status-label", Label).update("[dim]Scan complete[/dim]")
            self.query_one("#lib-progress-bar", ProgressBar).display = False

            # Update merged summary bar
            try:
                all_statuses = [s for _, games in message.structure.values() for _, s, _, _ in games]
                total_ok  = all_statuses.count("validated")
                total_bad = all_statuses.count("corrupted")
                total_inc = all_statuses.count("incomplete")
                n_cons    = len(message.structure)
                total_bytes = sum(message.disk_usage.values())
                t = Text()
                t.append(f"{n_cons} console(s)", style="#3d4451")
                t.append("   ", style="")
                t.append(f"{total_ok}", style="#3fb950")
                t.append("✓", style="bold green")
                t.append("ok", style="dim #606878")
                t.append("  ", style="")
                t.append(f"{total_bad}", style="#f85149")
                t.append("✗", style="bold red")
                t.append("bad", style="dim #606878")
                t.append("  ", style="")
                t.append(f"{total_inc}", style="#d29922")
                t.append("~", style="yellow")
                t.append("inc", style="dim #606878")
                if total_bytes > 0:
                    t.append("   ", style="")
                    t.append(self._format_size(total_bytes), style="#9aa0aa")
                try:
                    free = shutil.disk_usage(library).free
                    if free > 0:
                        t.append("   ", style="")
                        t.append(f"{self._format_size(free)} free", style="#3fb950")
                except OSError:
                    pass
                self.query_one("#lib-summary-bar", Label).update(t)
            except Exception as e:
                logging.debug("Update lib summary bar failed: %s", e)

            # Reset toolbar to root-level operations
            self._update_lib_toolbar(tree.root)
        except Exception as e:
            self._log(f"Tree build error: {e}", is_error=True)

    def _filter_library_tree(self) -> None:
        """Re-render the library tree applying the current search filter."""
        if self._last_lib_tree_data is not None:
            self.on_library_tree_ready(self._last_lib_tree_data)

    # ── Library detail panel — contextual toolbar + file detail view ─────

    def on_tree_node_highlighted(self, event: Tree.NodeHighlighted) -> None:
        """Update toolbar and status bar when the library tree cursor moves."""
        if event.control.id != "lib-tree":
            return
        self._update_lib_toolbar(event.node)
        self._update_lib_selection_status(event.node)

    async def on_click(self, event: events.Click) -> None:
        """Handle clicks on header label controls (library)."""
        widget = event.widget
        if not isinstance(widget, Label):
            return
        wid = widget.id or ""
        if wid == "btn-lib-delete":
            self._lib_delete_selected()

    def on_data_table_header_selected(self, event: DataTable.HeaderSelected) -> None:
        """Sort the game list when a column header is clicked."""
        if event.data_table.id != "game-list":
            return
        key_map = {"name": "name", "rating": "rating", "size": "size"}
        sort_key = key_map.get(event.column_key.value)
        if sort_key:
            self._apply_sort(sort_key)

    def _apply_sort(self, new_key: str) -> None:
        """Apply a sort key, toggle direction, and re-render the game table."""
        if self._browse_sort_key == new_key:
            self._browse_sort_reverse = not self._browse_sort_reverse
        else:
            self._browse_sort_key = new_key
            self._browse_sort_reverse = (new_key != "name")
        if new_key == "rating" and not self._game_metadata:
            self.notify("No IGDB data — configure credentials in Settings", severity="warning")
        try:
            query = self.query_one("#search-games", Input).value
        except Exception:
            query = ""
        self._render_games(query)

    async def action_toggle_chip(self, prefix: str, tag: str) -> None:
        """Handle [@click] actions from tag chip markup."""
        if prefix == "tag":
            if tag in self._browse_active_tags:
                self._browse_active_tags.discard(tag)
            else:
                self._browse_active_tags.add(tag)
            await self._render_tags_panel()
            try:
                query = self.query_one("#search-games", Input).value
            except Exception:
                query = ""
            self._render_games(query)
        elif prefix in ("inc", "exc"):
            is_include = prefix == "inc"
            sel_set = self._filter_include_sel if is_include else self._filter_exclude_sel
            if tag in sel_set:
                sel_set.discard(tag)
            else:
                sel_set.add(tag)
            key = "filter_include" if is_include else "filter_exclude"
            self.state.update_settings({key: sorted(sel_set)})
            tbl_id = "set-include" if is_include else "set-exclude"
            try:
                tbl = self.query_one(f"#{tbl_id}", DataTable)
                self._refresh_filter_row(tbl, tag, sel_set)
            except Exception:
                pass
            await self._render_tags_panel()
            if self.selected_console:
                self.fetch_games(self.selected_console)

    def _update_lib_toolbar(self, node: Any) -> None:
        """Show/hide toolbar buttons based on tree selection context."""
        library = Path(self.state.settings["library_root"])
        node_path = getattr(node, "data", None) if node else None

        if node_path is None or not isinstance(node_path, Path):
            level = "root"
        elif node_path == library or node_path.parent == library:
            level = "console" if node_path != library else "root"
        else:
            level = "game"

        _vis: dict[str, set[str]] = {
            "btn-lib-dat-audit":      {"root", "console"},
            "btn-lib-convert":        {"root", "console", "game"},
            "btn-lib-chd-to-orig":    {"root", "console", "game"},
            "btn-lib-refresh":        {"root"},
            "btn-ps2-md-patch":       {"console", "game"},
            "btn-ps2-md-unpatch":     {"console", "game"},
            "btn-requeue-failed":     {"root"},
            "btn-requeue-console":    {"console"},
        }
        for btn_id, levels in _vis.items():
            try:
                btn = self.query_one(f"#{btn_id}", Button)
                if level in levels:
                    btn.remove_class("--lib-hidden")
                else:
                    btn.add_class("--lib-hidden")
            except Exception:
                pass

    def _update_lib_selection_status(self, node: Any) -> None:
        """Show the selected node name in the status bar."""
        try:
            status_label = self.query_one("#lib-status-label", Label)
            progress_bar = self.query_one("#lib-progress-bar", ProgressBar)
            # Don't overwrite active operation progress
            if progress_bar.display:
                return
        except Exception:
            return
        node_path = getattr(node, "data", None) if node else None
        if node_path is None or not isinstance(node_path, Path):
            status_label.update(Text("Library root", style="dim"))
            return
        library = Path(self.state.settings["library_root"])
        t = Text()
        t.append("Selected: ", style="dim")
        if node_path == library:
            t.append("Library root", style="#9aa0aa")
        elif node_path.parent == library:
            t.append(node_path.name, style="bold #e6b73e")
        else:
            # Check if this is a multi-disc grouping folder
            disc_subdirs: list[Path] = []
            try:
                disc_subdirs = [
                    d for d in node_path.iterdir()
                    if d.is_dir() and DISC_REGEX.search(d.name)
                ]
            except (PermissionError, OSError):
                pass

            if disc_subdirs:
                # Multi-disc grouping folder — aggregate status from disc subdirs
                statuses = {self._lib_status.get(d) for d in disc_subdirs}
                if statuses == {"validated"}:
                    t.append("✓ ", style="bold green")
                elif "corrupted" in statuses:
                    t.append("✗ ", style="bold red")
                else:
                    t.append("~ ", style="yellow")
                t.append(node_path.name, style="#c9d1d9")
                t.append(f"  {len(disc_subdirs)} disc(s)", style="dim")
                try:
                    total_files = 0
                    total_size = 0
                    for d in disc_subdirs:
                        for f in d.iterdir():
                            if f.is_file() and not f.name.startswith('.'):
                                total_files += 1
                                total_size += f.stat().st_size
                    if total_files:
                        t.append(f"  {total_files} file(s)", style="dim")
                        t.append(f"  {MyrientTUI._format_size(total_size)}", style="dim #9aa0aa")
                except (PermissionError, OSError):
                    pass
            else:
                status = self._lib_status.get(node_path)
                if status == "validated":
                    t.append("✓ ", style="bold green")
                elif status == "corrupted":
                    t.append("✗ ", style="bold red")
                else:
                    t.append("~ ", style="yellow")
                t.append(node_path.name, style="#c9d1d9")
                try:
                    files = [f for f in node_path.iterdir() if f.is_file() and not f.name.startswith('.')]
                    if files:
                        total_size = sum(f.stat().st_size for f in files)
                        t.append(f"  {len(files)} file(s)", style="dim")
                        t.append(f"  {MyrientTUI._format_size(total_size)}", style="dim #9aa0aa")
                except (PermissionError, OSError):
                    pass
        status_label.update(t)

    def on_library_progress(self, message: LibraryProgress) -> None:
        try:
            progress_bar = self.query_one("#lib-progress-bar", ProgressBar)
            status_label = self.query_one("#lib-status-label", Label)

            is_done = message.current_item.lower() in _PROGRESS_DONE_STATES

            # Truncate current item name so it fits on one line next to the bar
            item_display = message.current_item
            if len(item_display) > 60:
                item_display = item_display[:57] + "…"

            if is_done:
                progress_bar.display = False
                done_text = Text.assemble(
                    (message.task_name, "bold #e6b73e"),
                    ("  ", ""),
                    (message.current_item, "dim"),
                )
                status_label.update(done_text)
            else:
                progress_bar.display = True
                progress_bar.update(total=message.total, progress=message.completed)
                status_text = Text.assemble(
                    (message.task_name, "bold #e6b73e"),
                    ("  ", ""),
                    (f"{message.completed}/{message.total}  ", "dim"),
                    (item_display, "#9aa0aa"),
                )
                status_label.update(status_text)
        except Exception as e:
            logging.debug("Update library progress UI failed: %s", e)

    # --- Fuzzy Search Engine & Highlighter ---
    @staticmethod
    def _fuzzy_spans(query: str, text: str) -> list[tuple[int, int]] | None:
        """Return ordered (start, end) match spans for each query character in text,
        or None if any character cannot be found.  O(n·m) with no backtracking risk —
        replaces the prior lru_cache+regex approach that had O(2^n) worst-case behaviour
        for long queries due to interleaved (.*?) capture groups.
        """
        text_lower = text.lower()
        query_lower = query.lower()
        spans: list[tuple[int, int]] = []
        pos = 0
        for ch in query_lower:
            idx = text_lower.find(ch, pos)
            if idx == -1:
                return None
            spans.append((idx, idx + 1))
            pos = idx + 1
        return spans

    @staticmethod
    def fuzzy_match(query: str, text: str) -> bool:
        if not query:
            return True
        return MyrientTUI._fuzzy_spans(query, text) is not None

    @staticmethod
    def _build_highlight_text(text: str, spans: list[tuple[int, int]]) -> Text:
        """Construct a Text object with matched characters highlighted in red."""
        result = Text(no_wrap=True, overflow="ellipsis")
        last = 0
        for start, end in spans:
            if start > last:
                result.append(text[last:start], style="white")
            result.append(text[start:end], style="bold red")
            last = end
        if last < len(text):
            result.append(text[last:], style="white")
        return result

    def fuzzy_highlight_fast(self, text: str, query: str) -> Text:
        """Return a Text object with fuzzy-matched characters highlighted.
        Safe against all input — Text never interprets brackets as markup.
        """
        if not query:
            return Text(text, style="white", no_wrap=True)
        spans = self._fuzzy_spans(query, text)
        if spans is None:
            return Text(text, style="white", no_wrap=True)
        return self._build_highlight_text(text, spans)

    # --- GameSearchInput message handlers ---
    def on_game_search_input_nav_up(self, _: GameSearchInput.NavUp) -> None:
        try:
            t = self.query_one("#game-list", DataTable)
            if t.row_count:
                t.move_cursor(row=max((t.cursor_row or 0) - 1, 0))
        except Exception as e:
            logging.debug("Game list nav up failed: %s", e)

    def on_game_search_input_nav_down(self, _: GameSearchInput.NavDown) -> None:
        try:
            t = self.query_one("#game-list", DataTable)
            if t.row_count:
                t.move_cursor(row=min((t.cursor_row or 0) + 1, t.row_count - 1))
        except Exception as e:
            logging.debug("Game list nav down failed: %s", e)

    def on_game_search_input_toggle_at_cursor(self, _: GameSearchInput.ToggleAtCursor) -> None:
        self._toggle_game_at_cursor()

    def on_game_search_input_queue_selected(self, _: GameSearchInput.QueueSelected) -> None:
        self._add_selected_to_queue()

    def on_key(self, event: Key) -> None:
        """Handles keys for game-list and filter tables.
        search-games keys (↑↓/Tab/Enter) are handled by GameSearchInput._on_key
        before they bubble, so they never reach here.
        """
        focused = self.focused
        fid = getattr(focused, "id", None)

        if fid == "game-list":
            if event.key == "space":
                self._toggle_game_at_cursor()
                event.prevent_default()
                event.stop()
            elif event.key in ("q", "enter"):
                self._add_selected_to_queue()
                event.prevent_default()
                event.stop()

        elif fid in ("set-include", "set-exclude"):
            if event.key == "space":
                self._toggle_filter_at_cursor(fid)
                event.prevent_default()
                event.stop()

        elif fid == "console-list":
            if event.key == "f":
                self._toggle_console_favorite()
                event.prevent_default()
                event.stop()

        elif fid == "queue-table":
            if event.key == "space":
                self._queue_toggle_selection()
                event.prevent_default()
                event.stop()
            elif event.key == "shift+space":
                # N6: Queue range selection
                try:
                    table = self.query_one("#queue-table", DataTable)
                    cursor = table.cursor_row
                    if cursor is not None and self._last_queue_selected_idx >= 0:
                        rows = table.ordered_rows
                        lo = min(self._last_queue_selected_idx, cursor)
                        hi = max(self._last_queue_selected_idx, cursor)
                        for i in range(lo, min(hi + 1, len(rows))):
                            item_id = rows[i].key.value
                            self._queue_selected.add(item_id)
                            self._refresh_queue_row_visual(table, item_id)
                    if cursor is not None:
                        self._last_queue_selected_idx = cursor
                except Exception:
                    pass
                event.prevent_default()
                event.stop()
            elif event.key == "delete":
                self._remove_selected_queue_items()
                event.prevent_default()
                event.stop()
            elif event.key == "shift+up":
                self._move_queue_item(-1)
                event.prevent_default()
                event.stop()
            elif event.key == "shift+down":
                self._move_queue_item(1)
                event.prevent_default()
                event.stop()

    def _toggle_game_at_cursor(self) -> None:
        """Toggle selection on the currently highlighted DataTable row."""
        try:
            game_table = self.query_one("#game-list", DataTable)
            cursor = game_table.cursor_row
            if cursor is None:
                return
            # Access the row directly by position — no full list() materialisation needed.
            ordered = game_table.ordered_rows
            if cursor >= len(ordered):
                return
            url_part = ordered[cursor].key.value
            if not url_part or url_part in ("LOADING", "EMPTY"):
                return
            if url_part in self._selected_games:
                self._selected_games.discard(url_part)
            else:
                self._selected_games.add(url_part)
            self._refresh_game_row(game_table, url_part)
            self._update_selection_count()
        except Exception as e:
            logging.debug("Toggle game at cursor failed: %s", e)

    def _refresh_game_row(self, game_table: DataTable, url_part: str) -> None:
        """Update a single row's visual to reflect its current selection state."""
        game_data = self._games_lookup.get(url_part)
        if not game_data:
            return
        selected = url_part in self._selected_games
        name_str = game_data["name"]
        sel_cell  = Text("✓", style="bold green") if selected else Text(" ", style="dim")
        name_cell = Text(name_str, style="bold green", no_wrap=True) if selected else Text(name_str, style="dim", no_wrap=True)
        try:
            game_table.update_cell(url_part, "sel",  sel_cell,  update_width=False)
            game_table.update_cell(url_part, "name", name_cell, update_width=False)
        except Exception as e:
            logging.debug("Refresh game row failed: %s", e)

    def _update_selection_count(self) -> None:
        count = len(self._selected_games)
        try:
            lbl = self.query_one("#game-selection-count", Label)
            if count == 0:
                lbl.update(Text(""))
            else:
                noun = "game" if count == 1 else "games"
                lbl.update(Text.assemble((f"{count} {noun} selected", "bold green")))
        except Exception as e:
            logging.debug("Update selection count failed: %s", e)

    def _toggle_filter_at_cursor(self, table_id: str) -> None:
        """Toggle a filter tag selection at the current cursor row."""
        sel_set = self._filter_include_sel if table_id == "set-include" else self._filter_exclude_sel
        try:
            tbl = self.query_one(f"#{table_id}", DataTable)
            cursor = tbl.cursor_row
            if cursor is None:
                return
            ordered = tbl.ordered_rows
            if cursor >= len(ordered):
                return
            tag = ordered[cursor].key.value
            if not tag:
                return
            if tag in sel_set:
                sel_set.discard(tag)
            else:
                sel_set.add(tag)
            self._refresh_filter_row(tbl, tag, sel_set)
            self.call_later(self._render_tags_panel)
        except Exception as e:
            logging.debug("Toggle filter at cursor failed: %s", e)

    def _refresh_filter_row(self, tbl: DataTable, tag: str, sel_set: set) -> None:
        """Re-render a single filter row to reflect its current selection state."""
        selected = tag in sel_set
        sel_cell  = Text("✓", style="bold cyan") if selected else Text(" ", style="dim")
        name_cell = Text(tag, style="bold cyan") if selected else Text(tag, style="dim")
        try:
            tbl.update_cell(tag, "sel",  sel_cell,  update_width=False)
            tbl.update_cell(tag, "name", name_cell, update_width=False)
        except Exception as e:
            logging.debug("Refresh filter row failed: %s", e)

    def on_input_changed(self, event: Input.Changed) -> None:
        """Debounces search input to prevent UI stutter during rapid typing.
        Each search box has its own timer so they never cancel each other.
        """
        if event.input.id == "search-consoles":
            if self._consoles_search_timer is not None:
                self._consoles_search_timer.stop()
            self._consoles_search_timer = self.set_timer(
                _SEARCH_DEBOUNCE, lambda: self._render_consoles(event.value)
            )
        elif event.input.id == "search-games":
            if getattr(self, "_browse_global_mode", False):
                if self._global_search_timer is not None:
                    self._global_search_timer.stop()
                val = event.value.strip()
                if len(val) >= 3:
                    self._global_search_timer = self.set_timer(
                        0.5, lambda: self.run_global_search(val)
                    )
            else:
                if self._games_search_timer is not None:
                    self._games_search_timer.stop()
                self._games_search_timer = self.set_timer(
                    _SEARCH_DEBOUNCE, lambda: self._render_games(event.value)
                )
        elif event.input.id == "lib-search":
            self._lib_search_text = event.value.lower().strip()
            if self._lib_search_timer is not None:
                self._lib_search_timer.stop()
            self._lib_search_timer = self.set_timer(
                _SEARCH_DEBOUNCE, self._filter_library_tree
            )
        elif event.input.id == "log-search":
            self._log_search_text = event.value.lower().strip()
            if self._log_search_timer is not None:
                self._log_search_timer.stop()
            self._log_search_timer = self.set_timer(
                _SEARCH_DEBOUNCE, self._rerender_log
            )

    def _render_consoles(self, query: str = "") -> None:
        list_view = self.query_one("#console-list", ListView)
        list_view.clear()

        filtered_consoles = [c for c in self._all_consoles_data if self.fuzzy_match(query, c["name"])]

        # N2: Partition into favorites and non-favorites, render favorites first
        fav_set = set(self.state.settings.get("favorite_consoles", []))
        favorites = [c for c in filtered_consoles if c["name"].strip('/') in fav_set]
        non_favorites = [c for c in filtered_consoles if c["name"].strip('/') not in fav_set]
        ordered_consoles = favorites + non_favorites

        new_items = []

        for console in ordered_consoles:
            console_label = console["name"].strip('/')
            is_fav = console_label in fav_set
            # U8: Highlight the currently selected console
            is_active = (
                self.selected_console is not None
                and console["url_part"] == self.selected_console["url_part"]
            )
            if is_active:
                prefix = "\u2605 " if is_fav else ""
                highlighted_name = Text(f"{prefix}{console_label} \u25c2", style="bold #e6b73e")
            else:
                if is_fav:
                    highlighted_name = Text(f"\u2605 {console_label}", style="#e6b73e")
                else:
                    highlighted_name = self.fuzzy_highlight_fast(console_label, query)
            item = DataListItem(Label(highlighted_name), data=console)  # C2
            new_items.append(item)

        if new_items:
            list_view.extend(new_items)

        # Update console count
        try:
            total = len(self._all_consoles_data)
            shown = len(filtered_consoles)
            if query and shown != total:
                self.query_one("#console-count", Label).update(
                    Text(f"{shown}/{total}", style="#3d4451")
                )
            else:
                self.query_one("#console-count", Label).update(
                    Text(f"{total}", style="#3d4451")
                )
        except Exception:
            pass

    def _toggle_console_favorite(self) -> None:
        """Toggle the highlighted console in/out of favorites and re-render."""
        try:
            lv = self.query_one("#console-list", ListView)
            idx = lv.index
            if idx is None or idx >= len(lv.children):
                return
            item = lv.children[idx]
            data = getattr(item, "data", None)  # C2: DataListItem.data
            if not data:
                return
            console_name = data["name"].strip('/')
            favs = list(self.state.settings.get("favorite_consoles", []))
            if console_name in favs:
                favs.remove(console_name)
            else:
                favs.append(console_name)
            self.state.set_setting("favorite_consoles", favs)
            query = self.query_one("#search-consoles", Input).value
            self._render_consoles(query)
        except Exception as e:
            logging.debug("Toggle console favorite failed: %s", e)

    _GAME_COL_SEL_W = 2
    _GAME_COL_RATING_W = 7
    _GAME_COL_SIZE_W = 9
    # Fixed width: column content widths + cell padding (2 per col × 4 cols = 8)
    _GAME_COL_FIXED = _GAME_COL_SEL_W + _GAME_COL_RATING_W + _GAME_COL_SIZE_W + 8  # 26

    def _render_games(self, query: str = "") -> None:
        """
        Repopulate the game DataTable, preserving selection state across searches.
        DataTable is virtualised — clearing and re-adding 1000+ rows is fast because
        only visible rows are actually rendered.
        Uses _fuzzy_spans for a single-pass match+highlight (no double regex).
        """
        game_table = self.query_one("#game-list", DataTable)
        # Dynamically size the Game column so Rating + Size anchor to the right edge
        tw = game_table.content_size.width
        name_w = max(20, tw - self._GAME_COL_FIXED) if tw > 0 else 45
        # Column headers double as sort controls — show arrow on active sort key
        sort_key = self._browse_sort_key
        rev = self._browse_sort_reverse
        def _hdr(label: str, key: str) -> str:
            if sort_key == key:
                return f"{label} ▲" if not rev else f"{label} ▼"
            return label
        game_table.clear(columns=True)
        game_table.add_column("", key="sel", width=self._GAME_COL_SEL_W)
        game_table.add_column(_hdr("Game", "name"), key="name", width=name_w)
        game_table.add_column(_hdr("Rating", "rating"), key="rating", width=self._GAME_COL_RATING_W)
        game_table.add_column(_hdr("Size", "size"), key="size", width=self._GAME_COL_SIZE_W)

        if not self._all_games_data:
            return

        has_metadata = bool(self._game_metadata)
        active_tags = self._browse_active_tags

        # Build filtered list of (game, clean_name, display_name, spans)
        filtered: list[tuple[dict, str, str, list | None]] = []
        for game in self._all_games_data:
            name = game["name"]
            clean_name = normalize_game_title(name)
            display_name = strip_extension(name)

            if query:
                spans = self._fuzzy_spans(query, display_name)
                if spans is None:
                    spans = self._fuzzy_spans(query, name)
                    if spans is None:
                        continue
                    spans = None  # show without highlight rather than wrong offsets
            else:
                spans = None

            # Tag filtering: if tags are active, only show games that match ALL tags
            if active_tags and has_metadata:
                meta = self._game_metadata.get(clean_name)
                if meta is None:
                    continue  # unmatched games hidden when tags active
                game_tags = set(meta.get("genres", []))
                game_tags.update(meta.get("themes", []))
                game_tags.update(meta.get("game_modes", []))
                if not active_tags.issubset(game_tags):
                    continue

            filtered.append((game, clean_name, display_name, spans))

        # Sort
        if sort_key == "name":
            filtered.sort(key=lambda e: e[2].lower(), reverse=rev)
        elif sort_key == "rating" and has_metadata:
            filtered.sort(
                key=lambda e: self._game_metadata.get(e[1], {}).get("rating", -1),
                reverse=rev,
            )
        elif sort_key == "popularity" and has_metadata:
            filtered.sort(
                key=lambda e: self._game_metadata.get(e[1], {}).get("popularity", 0),
                reverse=rev,
            )
        elif sort_key == "size":
            filtered.sort(
                key=lambda e: self._parse_size_bytes(e[0]["size_str"]),
                reverse=rev,
            )

        found = 0
        for game, clean_name, display_name, spans in filtered:
            url_part = game["url_part"]
            selected = url_part in self._selected_games
            bare_name = strip_extension(game["name"])
            in_library = bare_name in self._library_game_names

            if selected:
                sel_cell = Text("✓", style="bold green")
            elif in_library:
                sel_cell = Text("★", style="bold #3fb950")
            else:
                sel_cell = Text(" ", style="dim")

            if selected:
                name_cell = Text(display_name, style="bold green", no_wrap=True, overflow="ellipsis")
            elif in_library and spans is None:
                name_cell = Text(display_name, style="#3fb950", no_wrap=True, overflow="ellipsis")
            elif spans is not None:
                name_cell = self._build_highlight_text(display_name, spans)
            else:
                name_cell = Text(display_name, style="dim", no_wrap=True, overflow="ellipsis")

            # Rating cell
            if has_metadata:
                meta = self._game_metadata.get(clean_name)
                rating = meta.get("rating", -1) if meta else -1
                if rating >= 80:
                    rating_cell = Text(f"{rating:.0f}", style="bold #3fb950")
                elif rating >= 60:
                    rating_cell = Text(f"{rating:.0f}", style="#e6b73e")
                elif rating >= 0:
                    rating_cell = Text(f"{rating:.0f}", style="#9aa0aa")
                else:
                    rating_cell = Text("—", style="#6e7681")
            else:
                rating_cell = Text("")

            # Already in library indicator
            if in_library:
                size_cell = Text(game["size_str"], style="bold #3fb950")
            else:
                size_cell = Text(game["size_str"])

            game_table.add_row(sel_cell, name_cell, rating_cell, size_cell, key=url_part)
            found += 1

        if found == 0 and self._all_games_data:
            game_table.add_row("", Text("No matches found.", style="dim"), "", "", key="EMPTY")

        # Update breadcrumb with visible count
        if self.selected_console:
            console_name = self.selected_console["name"].strip('/')
            self._update_breadcrumb(console_name, found)

    # --- Queue & Settings Managers ---
    def _refresh_queue_dropdown(self) -> None:
        selector = self.query_one("#queue-select", Select)
        selector.set_options([(k, k) for k in self.state.queues.keys()])
        
        if self.state.active_queue_name in self.state.queues:
            selector.value = self.state.active_queue_name

    def _refresh_queue_table(self) -> None:
        """Full rebuild of the queue DataTable — used when switching profiles or
        after bulk mutations where row keys have changed.  For single-item removal
        during active downloads, use _remove_queue_row() instead."""
        table = self.query_one("#queue-table", DataTable)
        table.clear()
        queue = self.state.get_active_queue()
        # Visual disc grouping: detect consecutive items with the same base name
        prev_base = ""
        for item in queue:
            raw_name = item["name"]
            # Strip console prefix for display: "Console / Game.zip" → "Game.zip"
            game_part = raw_name.split(" / ", 1)[-1] if " / " in raw_name else raw_name
            m = DISC_REGEX.search(game_part)
            if m:
                base = normalize_game_title(game_part)
                if base != prev_base:
                    # Insert a dim group header for the multi-disc set
                    table.add_row(
                        Text(f"  ▸ {base}", style="dim #58a6ff"),
                        "", "", key=f"_grp_{item['id']}",
                    )
                prev_base = base
                # Indent disc entries with clean title keeping disc info
                disc_display = normalize_game_title_keep_disc(game_part)
                display_name = Text(f"    {disc_display}", style="#9aa0aa")
            else:
                prev_base = ""
                display_name = normalize_game_title(game_part)
            table.add_row(display_name, item['size_str'], "Queued", key=item['id'])
        # F2: Update queue total size indicator
        self._update_queue_total_size(queue)
        self._update_global_statusbar()

    def _update_queue_total_size(self, queue: list | None = None) -> None:
        """Compute and display total queue size in the #queue-total-size label."""
        try:
            if queue is None:
                queue = self.state.get_active_queue()
            total_bytes = sum(self._parse_size_bytes(item['size_str']) for item in queue)
            count = len(queue)
            if count > 0:
                size_str = self._format_size(total_bytes)
                self.query_one("#queue-total-size", Label).update(
                    Text(f"{count} item{'s' if count != 1 else ''} \u00b7 {size_str}", style="#3d4451")
                )
            else:
                self.query_one("#queue-total-size", Label).update(Text(""))
        except Exception as e:
            logging.debug("Update queue total size failed: %s", e)

    def _remove_queue_row(self, item_id: str) -> None:
        """Remove a single row by item id without touching the rest of the table.
        Avoids the O(n) clear+re-add cost on every download completion callback.
        Falls back to a full rebuild if the surgical remove fails (e.g. row not found).
        """
        try:
            self.query_one("#queue-table", DataTable).remove_row(item_id)
        except Exception:
            self._refresh_queue_table()

    def _refresh_history_table(self) -> None:
        """Rebuild the download history DataTable from persisted data."""
        try:
            htable = self.query_one("#history-table", DataTable)
            htable.clear()
            for entry in reversed(self.state.download_history):
                htable.add_row(
                    entry.get("name", ""),
                    entry.get("console", ""),
                    entry.get("size", ""),
                    entry.get("timestamp", ""),
                )
        except Exception as e:
            logging.debug("Refresh history table failed: %s", e)

    def _load_settings_toggles(self) -> None:
        # Each try/except guards a single widget query.  During early startup the
        # compose() tree may not yet be fully mounted; catching here prevents a
        # crash while still loading all toggles that are ready.

        # ── Input values (SettingsPane doesn't have access to self.state) ──
        _input_vals = {
            "set-lib-path":    self.state.settings["library_root"],
            "set-threads":     str(self.state.settings["max_concurrent"]),
            "set-speed-limit": str(self.state.settings.get("speed_limit_mbps", 0)),
            "set-dat-ttl":     str(self.state.settings.get("dat_cache_ttl_hours", 168)),
            "set-igdb-client-id":     self.state.settings.get("igdb_client_id", ""),
            "set-igdb-client-secret":  self.state.settings.get("igdb_client_secret", ""),
        }
        for wid, val in _input_vals.items():
            try:
                self.query_one(f"#{wid}", Input).value = val
            except Exception as e:
                logging.debug("Load settings input %s failed: %s", wid, e)

        # ── Switch toggles ─────────────────────────────────────────────────
        try:
            self.query_one("#set-auto-chd", Switch).value = \
                self.state.settings.get("auto_convert_chd", False)
        except Exception as e:
            logging.debug("Load set-auto-chd toggle failed: %s", e)
        try:
            self.query_one("#set-watch-library", Switch).value = \
                self.state.settings.get("watch_library", False)
        except Exception as e:
            logging.debug("Load set-watch-library toggle failed: %s", e)
        try:
            self.query_one("#set-notify-batch", Switch).value = \
                self.state.settings.get("notify_on_batch_complete", True)
        except Exception as e:
            logging.debug("Load set-notify-batch toggle failed: %s", e)
        try:
            self.query_one("#set-verify-dl", Switch).value = \
                self.state.settings.get("verify_after_download", False)
        except Exception as e:
            logging.debug("Load set-verify-dl toggle failed: %s", e)
        # Restore filter selections from saved settings into the Python sets and DataTable rows
        self._filter_include_sel = set(self.state.settings.get("filter_include", []))
        self._filter_exclude_sel = set(self.state.settings.get("filter_exclude", []))
        try:
            inc_tbl = self.query_one("#set-include", DataTable)
            for row in inc_tbl.ordered_rows:
                self._refresh_filter_row(inc_tbl, row.key.value, self._filter_include_sel)
            exc_tbl = self.query_one("#set-exclude", DataTable)
            for row in exc_tbl.ordered_rows:
                self._refresh_filter_row(exc_tbl, row.key.value, self._filter_exclude_sel)
        except Exception as e:
            logging.debug("Restore filter selections failed: %s", e)
        self.call_later(self._render_tags_panel)

    def on_select_changed(self, event: Select.Changed) -> None:
        if event.control.id == "queue-select" and event.value != Select.BLANK:
            self.state.set_active_queue(str(event.value))
            self._refresh_queue_table()
            self.notify(f"Switched to: {event.value}")
            # Reflect this queue's per-queue settings in the input fields
            q_settings = self.state.get_queue_settings(str(event.value))
            try:
                self.query_one("#input-queue-speed-limit", Input).value = \
                    str(q_settings.get("speed_limit_mbps", 0))
                mc = q_settings.get("max_concurrent")
                self.query_one("#input-queue-max-concurrent", Input).value = \
                    str(mc) if mc is not None else ""
            except Exception as e:
                logging.debug("Reflect queue settings on select failed: %s", e)

        elif event.control.id == "set-active-source" and event.value != Select.BLANK:
            # Populate edit fields with the selected source's data
            sources = self.state.settings.get("sources", [])
            for s in sources:
                if s["name"] == str(event.value):
                    try:
                        self.query_one("#src-name", Input).value = s.get("name", "")
                        self.query_one("#src-browse-url", Input).value = s.get("browse_url", "")
                        self.query_one("#src-dat-url", Input).value = s.get("dat_url", "")
                    except Exception:
                        pass
                    break

    _NAV_PANE_IDS: tuple[str, ...] = (
        "pane-browse", "pane-downloads", "pane-library",
        "pane-settings", "pane-logs",
    )
    _NAV_BTN_MAP: dict[str, str] = {
        "pane-browse":     "nav-btn-browse",
        "pane-downloads":  "nav-btn-downloads",
        "pane-library":    "nav-btn-library",
        "pane-settings":   "nav-btn-settings",
        "pane-logs":       "nav-btn-logs",
    }

    # Button-ID → method-name dispatch table.  Defined once at class level so it is
    # not re-allocated on every button press.  getattr is used at call time so that
    # @work-decorated methods are looked up fresh each invocation (they return new
    # Worker objects and must not be cached as bound methods).
    _BUTTON_DISPATCH: dict[str, str] = {
        "btn-add-queue":            "_add_selected_to_queue",
        "btn-lib-refresh":          "run_lib_refresh",
        "btn-setup-chdman":         "setup_chdman_auto",
        "btn-setup-ps2mdp":         "setup_ps2mdp_auto",
        "btn-requeue-failed":       "requeue_failed_games",
        "btn-prefetch-consoles":    "prefetch_all_consoles",
        "btn-refresh-session-logs": "_refresh_session_log_list",
        "btn-schedule-dl":          "_schedule_download",
    }

    async def on_button_pressed(self, event: Button.Pressed) -> None:
        button_id = event.button.id

        # ── Sidebar navigation ────────────────────────────────────────────
        if button_id and button_id.startswith("nav-btn-"):
            pane_map = {
                "nav-btn-browse":    "pane-browse",
                "nav-btn-downloads": "pane-downloads",
                "nav-btn-library":   "pane-library",
                "nav-btn-settings":  "pane-settings",
                "nav-btn-logs":      "pane-logs",
            }
            target = pane_map.get(button_id)
            if target:
                self._nav_switch(target)
            return

        # ── Log filter buttons ────────────────────────────────────────────
        if button_id in ("log-filter-all", "log-filter-err"):
            self._set_log_filter(button_id)
            return

        if button_id in self._BUTTON_DISPATCH:
            getattr(self, self._BUTTON_DISPATCH[button_id])()
            return

        if button_id == "btn-clear-igdb-cache":
            # Cancel any in-progress IGDB fetch
            self._ratings_cancel.set()
            self.state._db.clear_igdb_cache()
            self._game_metadata = {}
            self._browse_available_tags = []
            self._browse_active_tags = set()
            await self._render_tags_panel()
            self.notify("IGDB cache cleared")
            # Re-fetch for the currently displayed console
            if self.selected_console and self._all_games_data:
                self._fetch_ratings(
                    self.selected_console["name"].strip("/"),
                    self._all_games_data,
                )
            return

        if button_id == "btn-clear-igdb-misses":
            self._ratings_cancel.set()
            count = self.state._db.clear_igdb_misses()
            self._game_metadata = {}
            self._browse_available_tags = []
            self._browse_active_tags = set()
            await self._render_tags_panel()
            self.notify(f"Cleared {count} IGDB miss entries")
            if self.selected_console and self._all_games_data:
                self._fetch_ratings(
                    self.selected_console["name"].strip("/"),
                    self._all_games_data,
                )
            return

        if button_id == "btn-batch-import":
            try:
                path = self.query_one("#input-batch-import-path", Input).value.strip()
                if path:
                    self.run_batch_import(path)
                else:
                    self.notify("Enter a file path first", severity="warning")
            except Exception:
                pass
            return

        if button_id == "btn-toggle-global":
            self._handle_toggle_global()
            return

        if button_id == "btn-refresh-games" and self.selected_console:
            self.fetch_games(self.selected_console)

        elif button_id == "btn-select-all":
            self._select_all_visible()

        elif button_id == "btn-queue-up":
            self._move_queue_item(-1)

        elif button_id == "btn-queue-down":
            self._move_queue_item(1)

        elif button_id == "btn-apply-queue-settings":
            try:
                val_str = self.query_one("#input-queue-speed-limit", Input).value.strip()
                speed   = max(0.0, float(val_str) if val_str else 0.0)
                mc_str  = self.query_one("#input-queue-max-concurrent", Input).value.strip()
                overrides: dict[str, Any] = {"speed_limit_mbps": speed}
                if mc_str:
                    overrides["max_concurrent"] = max(1, min(10, int(mc_str)))
                self.state.set_queue_settings(
                    self.state.active_queue_name, overrides
                )
                self.notify(f"Queue settings applied (speed={speed} MB/s)")
            except Exception as e:
                self.notify(f"Invalid queue setting: {e}", severity="warning")
            
        elif button_id == "btn-save-preset":
            try:
                name = self.query_one("#input-preset-name", Input).value.strip()
                if name:
                    self._save_current_preset(name)
                else:
                    self.notify("Enter a preset name first.", severity="warning")
            except Exception as e:
                logging.debug("Save preset failed: %s", e)

        elif button_id == "btn-load-preset":
            try:
                sel = self.query_one("#preset-select", Select)
                if sel.value != Select.BLANK:
                    self._load_preset(str(sel.value))
                else:
                    self.notify("Select a preset from the dropdown first.", severity="warning")
            except Exception as e:
                logging.debug("Load preset failed: %s", e)

        elif button_id == "btn-del-preset":
            try:
                sel = self.query_one("#preset-select", Select)
                if sel.value != Select.BLANK:
                    self._delete_preset(str(sel.value))
                else:
                    self.notify("Select a preset to delete.", severity="warning")
            except Exception as e:
                logging.debug("Delete preset failed: %s", e)

        elif button_id == "btn-create-queue":
            input_box = self.query_one("#input-new-queue", Input)
            if input_box.value and self.state.create_queue(input_box.value):
                input_box.value = ""
                self._refresh_queue_dropdown()
                self._refresh_queue_table()
                self.notify("Queue Created")
                
        elif button_id == "btn-delete-queue":
            # Delete the queue currently selected in the dropdown (which may or may
            # not be the active queue).  delete_queue() handles re-pointing the
            # active queue if needed and blocks deletion of the last queue.
            try:
                selected_name = str(self.query_one("#queue-select", Select).value)
            except Exception:
                selected_name = self.state.active_queue_name
            if self.state.delete_queue(selected_name):
                self._refresh_queue_dropdown()
                self._refresh_queue_table()
                self.notify(f"Queue '{selected_name}' deleted")
            else:
                self.notify("Cannot delete the only remaining queue.", severity="warning")
                
        elif button_id == "btn-remove-items":
            self._remove_selected_queue_items()

        elif button_id == "btn-clear-queue":
            if self.engine_running:
                self.notify("Cannot clear queue while downloads are active", severity="warning")
            else:
                self.state.update_active_queue([])
                self._queue_selected.clear()
                self._refresh_queue_table()
                self.notify("Queue cleared")

        elif button_id == "btn-start-dl":
            queue = self.state.get_active_queue()
            if queue:
                # U3: Confirm before starting large downloads (>10 items)
                if len(queue) > 10:
                    total_bytes = sum(self._parse_size_bytes(it["size_str"]) for it in queue)
                    size_str = self._format_size(total_bytes) if total_bytes > 0 else "unknown"
                    self.push_screen(
                        ConfirmDownloadScreen(len(queue), size_str),
                        callback=lambda ok: self.start_download_engine() if ok else None,
                    )
                else:
                    self.start_download_engine()
                
        elif button_id == "btn-pause-dl":
            self._handle_pause_dl()
                
        elif button_id == "btn-clear-filters":
            self._filter_include_sel.clear()
            self._filter_exclude_sel.clear()
            try:
                for tbl_id, sel_set in (("set-include", self._filter_include_sel),
                                        ("set-exclude", self._filter_exclude_sel)):
                    tbl = self.query_one(f"#{tbl_id}", DataTable)
                    for row in tbl.ordered_rows:
                        self._refresh_filter_row(tbl, row.key.value, sel_set)
            except Exception as e:
                logging.debug("Clear filter table visuals failed: %s", e)
            self.state.update_settings({"filter_include": [], "filter_exclude": []})
            self.call_later(self._render_tags_panel)
            self.notify("Filters cleared")

        elif button_id == "btn-save-settings":
            self._handle_save_settings()

        elif button_id == "btn-save-source":
            self._handle_save_source()

        elif button_id == "btn-delete-source":
            self._handle_delete_source()

        elif button_id == "btn-export-queue":
            try:
                io_input = self.query_one("#input-queue-io-path", Input)
                custom = io_input.value.strip()
                if custom:
                    export_path = Path(custom).expanduser().resolve()
                else:
                    export_path = _DATA_DIR / f"queue_export_{self.state.active_queue_name}.json"
                queue = self.state.get_active_queue()
                export_path.parent.mkdir(parents=True, exist_ok=True)
                with open(export_path, 'w', encoding='utf-8') as f:
                    json.dump(queue, f, indent=2)
                io_input.value = str(export_path)
                self.notify(f"Queue exported to {export_path}")
                self.post_message(SystemLog(f"Queue exported: {export_path}"))
            except Exception as e:
                self.notify(f"Export failed: {e}", severity="error")

        elif button_id == "btn-import-queue":
            try:
                io_input = self.query_one("#input-queue-io-path", Input)
                custom = io_input.value.strip()
                if custom:
                    import_path = Path(custom).expanduser().resolve()
                else:
                    import_path = _DATA_DIR / f"queue_export_{self.state.active_queue_name}.json"
                if not import_path.exists():
                    candidates = list(_DATA_DIR.glob("queue_export_*.json"))
                    if candidates:
                        import_path = candidates[0]
                    else:
                        self.notify("No queue export file found in data dir.", severity="warning")
                        return
                with open(import_path, 'r', encoding='utf-8') as f:
                    imported = json.load(f)
                if not isinstance(imported, list):
                    self.notify("Invalid queue file format.", severity="error")
                    return
                current = self.state.get_active_queue()
                existing_ids = {i["id"] for i in current}
                added = 0
                for item in imported:
                    if isinstance(item, dict) and item.get("id") not in existing_ids:
                        current.append(item)
                        existing_ids.add(item["id"])
                        added += 1
                if added:
                    self.state.update_active_queue(current, immediate=True)
                    self._refresh_queue_table()
                io_input.value = str(import_path)
                self.notify(f"Imported {added} item(s) from {import_path}")
            except Exception as e:
                self.notify(f"Import failed: {e}", severity="error")

        elif button_id == "btn-clear-history":
            self.state.clear_history()
            self._refresh_history_table()
            self.notify("Download history cleared")

        elif button_id == "btn-requeue-console":
            # Read tree cursor on the main thread before dispatching worker.
            tree = self.query_one("#lib-tree", Tree)
            node = tree.cursor_node
            if not node or not isinstance(getattr(node, 'data', None), Path):
                self.notify("Select a console or game in the tree first.", severity="warning")
                return
            library = Path(self.state.settings['library_root'])
            node_path: Path = node.data
            # Resolve to console level — if a game leaf is selected, walk up one level.
            # Console nodes are direct children of the library root (depth 1).
            if node_path.parent == library:
                console_path = node_path
            elif node_path.parent.parent == library:
                console_path = node_path.parent
            else:
                # Deeper nesting (multi-disc grandchild) — go up two levels
                console_path = node_path.parent.parent
            if not console_path.is_dir():
                self.notify("Could not resolve a console folder from the selected node.", severity="warning")
                return
            self.requeue_console_games(console_path.name, console_path)

        elif button_id in ("btn-lib-convert", "btn-lib-chd-to-orig", "btn-ps2-md-patch",
                           "btn-ps2-md-unpatch", "btn-lib-dat-audit"):
            # All scoped operations use the tree cursor when one is selected,
            # or fall back to the full library when nothing is highlighted.
            tree = self.query_one("#lib-tree", Tree)
            node = tree.cursor_node
            library = Path(self.state.settings["library_root"])

            if node and isinstance(getattr(node, "data", None), Path):
                node_path: Path = node.data
                if node_path == library:
                    scope = library
                elif node_path.parent == library:
                    scope = node_path          # console node
                else:
                    scope = node_path          # game dir at any depth
            else:
                scope = library               # nothing selected → full library

            if button_id == "btn-lib-convert":
                self.run_lib_convert(scope)
            elif button_id == "btn-lib-chd-to-orig":
                self.run_chd_to_original(scope)
            elif button_id == "btn-lib-dat-audit":
                self.run_bulk_dat_audit(scope)
            elif button_id == "btn-ps2-md-patch":
                self._ps2mdp_target = scope
                self.run_ps2_master_disc_patch()
            elif button_id == "btn-ps2-md-unpatch":
                self._ps2mdp_target = scope
                self.run_ps2_master_disc_unpatch()



    # ── S1: Extracted button handlers ──────────────────────────────────
    def _handle_toggle_global(self) -> None:
        """Toggle between local and global search mode."""
        self._browse_global_mode = not getattr(self, "_browse_global_mode", False)
        try:
            btn = self.query_one("#btn-toggle-global", Button)
            search_input = self.query_one("#search-games", Input)
            if self._browse_global_mode:
                btn.variant = "primary"
                btn.label = "\u2715 Local"
                search_input.placeholder = "  search all consoles\u2026 (min 3 chars)"
                search_input.value = ""
                search_input.focus()
            else:
                btn.variant = "default"
                btn.label = "Global"
                search_input.placeholder = "  search games\u2026"
                search_input.value = ""
                self._global_search_results = {}
                if self.selected_console:
                    self._render_games("")
                    self._show_browse_game_view(True)
                else:
                    self._show_browse_game_view(False)
        except Exception:
            pass

    def _handle_pause_dl(self) -> None:
        """Pause downloads or cancel a running library operation."""
        with self._engine_lock:
            if self._engine_state == EngineState.RUNNING:
                self._engine_state = EngineState.PAUSING
            elif self._engine_state != EngineState.PAUSING:
                self._lib_cancel.set()
                self.post_message(SystemLog("[bold yellow]Cancel signal sent to library operation.[/]"))
                return
        self.post_message(SystemLog("[bold yellow]Pause signal sent. Suspending threads and preserving partial files...[/]"))
        self._update_global_statusbar()
        self.cancel_flag.set()
        self.cleanup_subprocesses()

    def _handle_save_settings(self) -> None:
        """Read all settings widgets, persist to config, and apply side effects."""
        try:
            new_path = Path(self.query_one("#set-lib-path", Input).value).expanduser().resolve()

            threads_input = self.query_one("#set-threads", Input).value.strip()
            try:
                thread_count = int(threads_input)
            except ValueError:
                thread_count = 4

            speed_str = self.query_one("#set-speed-limit", Input).value.strip()
            try:
                speed_limit = max(0.0, float(speed_str) if speed_str else 0.0)
            except ValueError:
                speed_limit = self.state.settings.get("speed_limit_mbps", 0)

            dat_ttl_str = self.query_one("#set-dat-ttl", Input).value.strip()
            try:
                dat_ttl_hours = max(0, int(dat_ttl_str) if dat_ttl_str else 168)
            except ValueError:
                dat_ttl_hours = self.state.settings.get("dat_cache_ttl_hours", 168)

            try:
                custom_inc = self.query_one("#set-custom-include", Input).value.strip()
            except Exception:
                custom_inc = self.state.settings.get("custom_include_regex", "")
            try:
                custom_exc = self.query_one("#set-custom-exclude", Input).value.strip()
            except Exception:
                custom_exc = self.state.settings.get("custom_exclude_regex", "")

            try:
                igdb_cid = self.query_one("#set-igdb-client-id", Input).value.strip()
            except Exception:
                igdb_cid = self.state.settings.get("igdb_client_id", "")
            try:
                igdb_csec = self.query_one("#set-igdb-client-secret", Input).value.strip()
            except Exception:
                igdb_csec = self.state.settings.get("igdb_client_secret", "")

            try:
                src_val = self.query_one("#set-active-source", Select).value
                active_src = str(src_val) if src_val != Select.BLANK else self.state.get_active_source()["name"]
            except Exception:
                active_src = self.state.get_active_source()["name"]

            prev_settings = dict(self.state.settings)

            self.state.update_settings({
                "library_root":             str(new_path),
                "max_concurrent":           max(1, min(10, thread_count)),
                "speed_limit_mbps":         speed_limit,
                "dat_cache_ttl_hours":      dat_ttl_hours,
                "auto_convert_chd":         self.query_one("#set-auto-chd", Switch).value,
                "watch_library":            self.query_one("#set-watch-library", Switch).value,
                "notify_on_batch_complete": self.query_one("#set-notify-batch", Switch).value,
                "verify_after_download":    self.query_one("#set-verify-dl", Switch).value,
                "filter_include":           sorted(self._filter_include_sel),
                "filter_exclude":           sorted(self._filter_exclude_sel),
                "custom_include_regex":     custom_inc,
                "custom_exclude_regex":     custom_exc,
                "active_source":            active_src,
                "igdb_client_id":           igdb_cid,
                "igdb_client_secret":       igdb_csec,
            })

            # Source switch side effects — clear cached data and re-fetch
            old_source = prev_settings.get("active_source", "")
            new_source = self.state.settings.get("active_source", "")
            if old_source != new_source:
                self.scraper.clear_cache()
                self.selected_console = None
                self._all_games_data = []
                self._games_lookup = {}
                self._selected_games.clear()
                try:
                    self.query_one("#game-list", DataTable).clear()
                except Exception:
                    pass
                self.fetch_consoles()

            # Invalidate ratings provider if credentials changed
            if self._ratings_provider and (
                self._ratings_provider.client_id != igdb_cid
                or self._ratings_provider.client_secret != igdb_csec
            ):
                self._ratings_provider = None
            self._update_igdb_ui_visibility()

            new_path.mkdir(parents=True, exist_ok=True)
            self._lib_status.load(new_path, db=self.state._db)
            self.run_lib_status_scan()
            self.notify("Settings saved")

            if self.state.settings.get("watch_library", False):
                self._start_watchdog()
            else:
                if self._watch_observer is not None:
                    try:
                        self._watch_observer.stop()
                    except Exception as e:
                        logging.debug("Stop watchdog observer failed: %s", e)
                    self._watch_observer = None

            if self.selected_console:
                self.fetch_games(self.selected_console)

        except Exception as err:
            self.notify(f"Error saving settings: {err}", severity="error")

    def _populate_source_select(self) -> None:
        """Populate the active-source Select and edit fields from settings."""
        try:
            sources = self.state.settings.get("sources", [])
            sel = self.query_one("#set-active-source", Select)
            sel.set_options([(s["name"], s["name"]) for s in sources])
            active = self.state.get_active_source()
            sel.value = active["name"]
            # Fill edit fields with active source data
            try:
                self.query_one("#src-name", Input).value = active.get("name", "")
                self.query_one("#src-browse-url", Input).value = active.get("browse_url", "")
                self.query_one("#src-dat-url", Input).value = active.get("dat_url", "")
            except Exception:
                pass
        except Exception:
            pass

    def _handle_save_source(self) -> None:
        """Save or update a source from the edit fields."""
        try:
            name = self.query_one("#src-name", Input).value.strip()
            browse_url = self.query_one("#src-browse-url", Input).value.strip()
            dat_url = self.query_one("#src-dat-url", Input).value.strip()
            if not name or not browse_url:
                self.notify("Source name and browse URL are required", severity="error")
                return
            if not browse_url.endswith("/"):
                browse_url += "/"
            if dat_url and not dat_url.endswith("/"):
                dat_url += "/"
            sources = list(self.state.settings.get("sources", []))
            # Upsert: update existing or append new
            found = False
            for i, s in enumerate(sources):
                if s["name"] == name:
                    sources[i] = {"name": name, "browse_url": browse_url, "dat_url": dat_url}
                    found = True
                    break
            if not found:
                sources.append({"name": name, "browse_url": browse_url, "dat_url": dat_url})
            old_source = self.state.get_active_source()["name"]
            self.state.update_settings({"sources": sources, "active_source": name})
            self._populate_source_select()
            self.notify(f"Source '{name}' saved")
            # Switch side effects — clear cache and re-fetch console list
            if old_source != name:
                self.scraper.clear_cache()
                self.selected_console = None
                self._all_games_data = []
                self._games_lookup = {}
                self._selected_games.clear()
                try:
                    self.query_one("#game-list", DataTable).clear()
                except Exception:
                    pass
            self.fetch_consoles()
        except Exception as err:
            self.notify(f"Error saving source: {err}", severity="error")

    def _handle_delete_source(self) -> None:
        """Delete the source shown in the edit fields."""
        try:
            name = self.query_one("#src-name", Input).value.strip()
            if not name:
                self.notify("No source name specified", severity="error")
                return
            sources = list(self.state.settings.get("sources", []))
            if len(sources) <= 1:
                self.notify("Cannot delete the only source", severity="error")
                return
            active = self.state.get_active_source()["name"]
            if name == active:
                self.notify("Cannot delete the active source — switch first", severity="error")
                return
            sources = [s for s in sources if s["name"] != name]
            self.state.update_settings({"sources": sources})
            self._populate_source_select()
            self.notify(f"Source '{name}' deleted")
        except Exception as err:
            self.notify(f"Error deleting source: {err}", severity="error")

    def _add_selected_to_queue(self) -> None:
        # Global search mode: results keyed as "Console/url_part"
        if self._global_search_results and self._selected_games:
            library_root = Path(self.state.settings["library_root"])
            current_queue = self.state.get_active_queue()
            existing_paths = {i["dest_path"] for i in current_queue}
            added_count = 0
            for key in self._selected_games:
                data = self._games_lookup.get(key)
                gs_console = self._global_search_results.get(key)
                if not data or not gs_console:
                    continue
                sub_folder = strip_extension(data['name']).strip()
                clean_base = DISC_REGEX.sub('', sub_folder).strip()
                if clean_base != sub_folder:
                    dest_path = library_root / gs_console / clean_base / sub_folder
                else:
                    dest_path = library_root / gs_console / sub_folder
                if str(dest_path) in existing_paths:
                    continue
                # B10: Use pre-computed URL from global search (avoids double-encoding)
                game_url = data.get("game_url") or urljoin(self._active_base_url, data["url_part"])
                current_queue.append(self._make_queue_item(
                    gs_console, data["name"], game_url, str(dest_path), data["size_str"],
                ))
                existing_paths.add(str(dest_path))
                added_count += 1
            self._selected_games.clear()
            self._update_selection_count()
            self.state.update_active_queue(current_queue)
            self._refresh_queue_table()
            self.notify(f"Queued {added_count} item(s)")
            self._flash_nav_button("nav-btn-downloads")
            self._update_global_statusbar()
            return

        if not self.selected_console or not self._selected_games:
            return

        library_root = Path(self.state.settings["library_root"])
        console_name = self.selected_console["name"].strip('/')
        base_url = urljoin(self._active_base_url, self.selected_console["url_part"])
        current_queue = self.state.get_active_queue()

        # Build a set of already-queued dest_paths to prevent duplicate entries
        existing_paths = {i["dest_path"] for i in current_queue}

        added_count = 0
        for url_part in self._selected_games:
            data = self._games_lookup.get(url_part)
            if not data:
                continue

            sub_folder = strip_extension(data['name']).strip()
            clean_base = DISC_REGEX.sub('', sub_folder).strip()

            # clean_base != sub_folder iff the DISC_REGEX matched — avoids a second .search() call
            if clean_base != sub_folder:
                dest_path = library_root / console_name / clean_base / sub_folder
            else:
                dest_path = library_root / console_name / sub_folder

            # Skip if this exact destination is already queued
            if str(dest_path) in existing_paths:
                continue

            current_queue.append(self._make_queue_item(
                console_name, data["name"], urljoin(base_url, data["url_part"]),
                str(dest_path), data["size_str"],
            ))
            existing_paths.add(str(dest_path))
            added_count += 1

        # Clear selections and re-render so green highlights are removed
        self._selected_games.clear()
        self._update_selection_count()
        self._render_games(self.query_one("#search-games", Input).value)
        self.state.update_active_queue(current_queue)
        self._refresh_queue_table()
        self.notify(f"Queued {added_count} item(s)")
        self._flash_nav_button("nav-btn-downloads")
        self._update_global_statusbar()

    # --- UI Message Receivers ---
    def on_consoles_loaded(self, message: ConsolesLoaded) -> None:
        self._all_consoles_data = message.consoles
        self._render_consoles(self.query_one("#search-consoles", Input).value)

    def on_games_loaded(self, message: GamesLoaded) -> None:
        self._all_games_data = message.games
        # RAM Optimization: Store active dictionary for O(1) queue lookups instead of JSON parsing
        self._games_lookup = {g["url_part"]: g for g in message.games}
        # Only clear IGDB metadata/tags when the console actually changes,
        # not when filters change for the same console.
        console_name = self.selected_console["name"] if self.selected_console else ""
        if console_name != self._last_loaded_console:
            self._last_loaded_console = console_name
            self._game_metadata = {}
            self._browse_active_tags = set()
            self._browse_available_tags = []
            # Kick off IGDB metadata fetch in background
            if self.selected_console:
                self._fetch_ratings(self.selected_console["name"].strip("/"), message.games)
        self._render_games(self.query_one("#search-games", Input).value)
        # Focus the search box so the user can immediately type to filter
        # and use ↑↓/Space/Enter without clicking anything.
        try:
            self.query_one("#search-games", Input).focus()
        except Exception as e:
            logging.debug("Focus search-games input failed: %s", e)

    # ── IGDB ratings integration ─────────────────────────────────────────

    def _get_ratings_provider(self) -> RatingsProvider | None:
        """Lazy-init the RatingsProvider from current settings."""
        cid = self.state.get_setting("igdb_client_id", "")
        csec = self.state.get_setting("igdb_client_secret", "")
        if not cid or not csec:
            return None
        if (
            self._ratings_provider is None
            or self._ratings_provider.client_id != cid
            or self._ratings_provider.client_secret != csec
        ):
            self._ratings_provider = RatingsProvider(
                db=self.state._db, client_id=cid, client_secret=csec,
            )
        return self._ratings_provider

    @work(thread=True, group="ratings")
    def _fetch_ratings(self, console_name: str, games: list) -> None:
        """Background: fetch IGDB metadata for current console's games."""
        self._ratings_cancel.clear()
        provider = self._get_ratings_provider()
        if provider is None or not provider.configured:
            self.post_message(SystemLog(
                "[dim]IGDB: skipped — no credentials configured[/dim]"
            ))
            return
        from .ratings import CONSOLE_PLATFORM_MAP
        if console_name not in CONSOLE_PLATFORM_MAP:
            self.post_message(SystemLog(
                f"[dim]IGDB: no platform mapping for '{console_name}' — ratings unavailable[/dim]"
            ))
            return
        clean_names = list(dict.fromkeys(
            normalize_game_title(g["name"]) for g in games
        ))
        self.post_message(SystemLog(
            f"[dim]IGDB: fetching ratings for {len(clean_names)} games…[/dim]"
        ))

        def _on_progress(done: int, total: int) -> None:
            self.post_message(SystemLog(
                f"[dim]IGDB: fetched {done}/{total} games…[/dim]"
            ))

        def _on_log(msg: str) -> None:
            self.post_message(SystemLog(f"[dim]{msg}[/dim]"))

        try:
            metadata = provider.fetch_console(
                console_name, clean_names,
                cancel=self._ratings_cancel,
                on_progress=_on_progress,
                on_log=_on_log,
            )
        except Exception as exc:
            self.post_message(SystemLog(f"IGDB fetch failed: {exc}", is_error=True))
            return
        if self._ratings_cancel.is_set():
            self.post_message(SystemLog("[dim]IGDB: fetch cancelled[/dim]"))
            return
        if metadata:
            matched = sum(1 for m in metadata.values() if m.get("igdb_id", 0) != 0)
            self.post_message(SystemLog(
                f"[dim]IGDB: matched {matched}/{len(clean_names)} games[/dim]"
            ))
            self.post_message(RatingsLoaded(metadata))
        else:
            self.post_message(SystemLog("[dim]IGDB: no matches found[/dim]"))

    def _update_igdb_ui_visibility(self) -> None:
        """Re-render the tags panel when IGDB state changes."""
        self.call_later(self._render_tags_panel)

    async def _render_tags_panel(self) -> None:
        """Populate the tags & filters panel with IGDB tags and region filter chips."""
        try:
            panel = self.query_one("#browse-tags-panel")
        except Exception:
            return
        await panel.remove_children()

        def _build_chip_markup(tags: list[str], active_set: set[str],
                              action_prefix: str, active_style: str) -> str:
            """Build a Textual markup string with clickable, comma-separated tag chips."""
            inactive_style = "#6e7681"
            parts: list[str] = []
            for tag in tags:
                active = tag in active_set
                style = active_style if active else inactive_style
                safe = tag.replace('"', '\\"').replace('[', '\\[')
                display = tag.replace('[', '\\[')
                action = f'app.toggle_chip("{action_prefix}", "{safe}")'
                parts.append(f"[{style} @click={action}]{display}[/]")
            return ", ".join(parts)

        # ── IGDB genre/theme/mode tags ─────────────────────────────────────
        if self._browse_available_tags:
            panel.mount(Label("Genres", classes="tag-section-label"))
            ordered = sorted(self._browse_available_tags,
                             key=lambda t: (t not in self._browse_active_tags, t))
            chip_markup = _build_chip_markup(ordered, self._browse_active_tags, "tag", "bold #00d4aa")
            s = Static(chip_markup, classes="tag-chip-line")
            s.auto_links = False
            panel.mount(s)

        # ── Include region filters ─────────────────────────────────────────
        inc_tags = self.state.settings.get("include_tags", ["USA", "Europe", "Japan", "World"])
        panel.mount(Label("Regions", classes="tag-section-label"))
        chip_markup = _build_chip_markup(inc_tags, self._filter_include_sel, "inc", "bold #3fb950")
        s = Static(chip_markup, classes="tag-chip-line")
        s.auto_links = False
        panel.mount(s)

        # ── Exclude filters ───────────────────────────────────────────────
        exc_tags = self.state.settings.get("exclude_tags", ["Demo", "Beta", "Proto"])
        panel.mount(Label("Exclude", classes="tag-section-label"))
        chip_markup = _build_chip_markup(exc_tags, self._filter_exclude_sel, "exc", "bold #f85149")
        s = Static(chip_markup, classes="tag-chip-line")
        s.auto_links = False
        panel.mount(s)

    @on(RatingsLoaded)
    async def on_ratings_loaded(self, message: RatingsLoaded) -> None:
        """Merge IGDB metadata and re-render the browse table."""
        try:
            self._game_metadata = message.metadata
            rated = sum(1 for m in message.metadata.values() if m.get("rating", -1) >= 0)
            self.post_message(SystemLog(
                f"[dim]IGDB: loaded {len(message.metadata)} entries ({rated} with ratings) — re-rendering[/dim]"
            ))
            # Compute available tags from the metadata
            tags: set[str] = set()
            for meta in message.metadata.values():
                tags.update(meta.get("genres", []))
                tags.update(meta.get("themes", []))
                tags.update(meta.get("game_modes", []))
            self._browse_available_tags = sorted(tags)
            await self._render_tags_panel()
            # Re-render with metadata (adds rating column, respects current sort)
            try:
                query = self.query_one("#search-games", Input).value
            except Exception:
                query = ""
            self._render_games(query)
        except Exception as exc:
            self.post_message(SystemLog(f"IGDB render failed: {exc}", is_error=True))
            logging.exception("on_ratings_loaded failed")

    # --- Async Background Workers ---
    @work(exclusive=True, thread=True)
    def fetch_consoles(self) -> None:
        def _show_loading() -> None:
            try:
                lv = self.query_one("#console-list", ListView)
                lv.clear()
                lv.append(ListItem(Label(Text("Loading consoles…", style="dim italic"))))
            except Exception as e:
                logging.debug("Show console loading indicator failed: %s", e)
        self.call_from_thread(_show_loading)
        self.post_message(SystemLog("Scraping console list..."))
        items = self.scraper.scrape_links(self._active_base_url)
        consoles = self._filter_console_items(items)
        self.post_message(ConsolesLoaded(consoles))  # type: ignore[arg-type]

    @work(exclusive=True, thread=True)
    def prefetch_all_consoles(self) -> None:
        """Concurrently scrape all console game pages and warm the link cache."""
        self._lib_cancel.clear()
        items = self.scraper.scrape_links(self._active_base_url)
        consoles = self._filter_console_items(items)
        if not consoles:
            return

        semaphore = threading.Semaphore(_SCRAPE_CONCURRENCY)
        total     = len(consoles)

        def _fetch_one(console: ConsoleItem, idx: int) -> None:
            with semaphore:
                if self._lib_cancel.is_set():
                    return
                url = urljoin(self._active_base_url, console["url_part"])
                self.post_message(LibraryProgress(
                    "Pre-caching", console["name"].strip('/'), idx, total
                ))
                self.scraper.scrape_links(url)

        with concurrent.futures.ThreadPoolExecutor(max_workers=_SCRAPE_CONCURRENCY) as ex:
            futures = [ex.submit(_fetch_one, c, i) for i, c in enumerate(consoles, 1)]  # type: ignore[arg-type]
            for f in concurrent.futures.as_completed(futures):
                try:
                    f.result()
                except Exception as e:
                    logging.debug("Pre-cache console fetch failed: %s", e)

        self.post_message(LibraryProgress("Pre-caching", "Done", total, total))
        self.post_message(SystemLog(
            f"[dim]Console cache warm — {total} console(s) pre-fetched.[/dim]"
        ))

    @work(exclusive=True, thread=True)
    def fetch_games(self, console_data: ConsoleItem) -> None:
        url = urljoin(self._active_base_url, console_data["url_part"])
        # C2: Show loading indicator in breadcrumb
        def _show_loading() -> None:
            try:
                lbl = self.query_one("#breadcrumb", Label)
                t = Text()
                t.append(self.state.get_active_source()["name"] or "Source", style="#3d4451")
                t.append("  ›  ", style="dim #1c2333")
                t.append(console_data["name"], style="#9aa0aa")
                t.append("  ⟳ Loading…", style="italic #d29922")
                lbl.update(t)
            except Exception as e:
                logging.debug("Show game loading breadcrumb failed: %s", e)
        self.call_from_thread(_show_loading)
        self.post_message(SystemLog(f"Listing games for {console_data['name']}..."))
        items = self.scraper.scrape_links(url)

        inc_filters = self.state.settings["filter_include"]
        exc_filters = self.state.settings["filter_exclude"]

        # Build combined include regex: tag-based presets + custom regex
        inc_parts: list[str] = [re.escape(t) for t in inc_filters]
        custom_inc = self.state.settings.get("custom_include_regex", "").strip()
        if custom_inc:
            inc_parts.append(custom_inc)
        try:
            inc_rx = re.compile('|'.join(inc_parts), re.IGNORECASE) if inc_parts else None
        except re.error:
            inc_rx = re.compile('|'.join(re.escape(t) for t in inc_filters), re.IGNORECASE) if inc_filters else None

        exc_parts: list[str] = [re.escape(t) for t in exc_filters]
        custom_exc = self.state.settings.get("custom_exclude_regex", "").strip()
        if custom_exc:
            exc_parts.append(custom_exc)
        try:
            exc_rx = re.compile('|'.join(exc_parts), re.IGNORECASE) if exc_parts else None
        except re.error:
            exc_rx = re.compile('|'.join(re.escape(t) for t in exc_filters), re.IGNORECASE) if exc_filters else None

        filtered_games: list[GameItem] = []
        for game in items:
            # B6: Accept all downloadable file types, not just .zip
            url_lower = game["url_part"].lower()
            if not any(url_lower.endswith(ext) for ext in _DOWNLOAD_EXTS):
                continue
            if inc_rx and not inc_rx.search(game["name"]):
                continue
            if exc_rx and exc_rx.search(game["name"]):
                continue
            filtered_games.append(game)  # type: ignore[arg-type]

        self.post_message(GamesLoaded(filtered_games))

    @work(exclusive=True, thread=True)
    def start_download_engine(self) -> None:
        # Atomic check-and-set: prevents a second invocation from slipping through
        # the gap between checking engine state and setting it.
        with self._engine_lock:
            if self._engine_state in (EngineState.RUNNING, EngineState.PAUSING):
                return
            self._engine_state = EngineState.RUNNING

        # Clear cancel flag immediately after acquiring the engine — a prior
        # cancelled run leaves the flag set, which would cause every new worker
        # to bail out instantly if we only clear it after the queue check.
        self.cancel_flag.clear()
        self._active_progress_containers.clear()   # fresh slate for this batch

        # Remove any leftover "Paused" progress containers from the previous run.
        def _clear_paused_containers() -> None:
            try:
                grid = self.query_one("#progress-grid")
                for child in list(grid.children):
                    if hasattr(child, 'id') and child.id and child.id.startswith("cont_pb_"):
                        child.remove()
            except Exception as e:
                logging.debug("Clear paused progress containers failed: %s", e)
        self.call_from_thread(_clear_paused_containers)

        queue = self.state.get_active_queue()  # already returns a fresh list copy
        q_settings = self.state.get_queue_settings(self.state.active_queue_name)
        max_threads = q_settings.get("max_concurrent",
                                     self.state.settings.get("max_concurrent", 4))

        if not queue:
            with self._engine_lock:
                self._engine_state = EngineState.IDLE
            return

        # B6: Pre-flight disk space check + N3: Batch size estimate (B9: compute once)
        total_bytes = sum(self._parse_size_bytes(it["size_str"]) for it in queue)
        try:
            library_root = Path(self.state.settings["library_root"])
            library_root.mkdir(parents=True, exist_ok=True)
            free = shutil.disk_usage(library_root).free
            if total_bytes > 0 and total_bytes > free:
                self.post_message(SystemLog(
                    f"[bold red]Insufficient disk space![/bold red] "
                    f"Need {self._format_size(total_bytes)}, only {self._format_size(free)} free.", True
                ))
                with self._engine_lock:
                    self._engine_state = EngineState.IDLE
                self.call_from_thread(self._update_global_statusbar)
                return
        except OSError:
            pass  # best-effort; proceed if we can't stat the filesystem

        if total_bytes > 0:
            self.post_message(SystemLog(
                f"Batch estimate: {len(queue)} items, {self._format_size(total_bytes)}"
            ))

        with self._progress_lock:
            self.global_total     = len(queue)
            self.global_completed = 0
        
        def init_global_pb() -> None:
            try:
                pb = self.query_one("#global-progress", ProgressBar)
                pb.display = True
                pb.update(total=self.global_total, progress=0)
                self.query_one("#lbl-global-progress", Label).update(
                    Text.assemble(
                        ("▸ DOWNLOAD PROGRESS", "dim"),
                        "  ",
                        (f"0 / {self.global_total}", "#e6b73e"),
                    )
                )
            except Exception as e:
                logging.debug("Init global progress bar failed: %s", e)

        self.call_from_thread(init_global_pb)
        self.call_from_thread(self._update_global_statusbar)
        # A8: Global bandwidth cap — shared across all download threads
        global_speed = int(q_settings.get("speed_limit_mbps", 0) or
                           self.state.settings.get("speed_limit_mbps", 0))
        self._bandwidth_bucket = TokenBucket(int(global_speed * 1024 * 1024))

        self.post_message(SystemLog(f"Engine Online. Dispatching {max_threads} Threads..."))

        # Count results on the worker thread so BatchComplete gets accurate
        # totals without racing against main-thread message processing.
        _batch_ok = _batch_fail = 0
        with concurrent.futures.ThreadPoolExecutor(max_workers=max_threads) as executor:
            futures = {executor.submit(self._download_worker, item): item for item in queue}
            for future in concurrent.futures.as_completed(futures):
                try:
                    result = future.result()
                    if result.get("success"):
                        _batch_ok += 1
                    elif not result.get("cancelled"):
                        _batch_fail += 1
                    self.post_message(DownloadComplete(
                        futures[future],
                        result.get("success", False),
                        result.get("cancelled", False)
                    ))
                except Exception as err:
                    _batch_fail += 1
                    self.post_message(SystemLog(f"Thread crash {futures[future]['name']}: {err}", True))
                    self.post_message(DownloadComplete(futures[future], False))
                    
        with self._engine_lock:
            if self.cancel_flag.is_set():
                self._engine_state = EngineState.PAUSED
            else:
                self._engine_state = EngineState.IDLE

        def _finish_ui() -> None:
            # F1: Clear aggregate speed tracking
            self._worker_speeds.clear()
            try:
                self.query_one("#global-progress", ProgressBar).display = False
                self.query_one("#lbl-global-progress", Label).update(
                    Text.assemble(("▸ DOWNLOAD PROGRESS", "dim"), ("  idle", "dim"))
                )
                # Clear speed indicator
                self.query_one("#gs-speed", Label).update(Text(""))
            except Exception as e:
                logging.debug("Finish download UI update failed: %s", e)
            self._update_global_statusbar()

        if self.cancel_flag.is_set():
            self.post_message(SystemLog("[bold yellow]Downloads Successfully Paused[/]"))
            self.call_from_thread(_finish_ui)
        else:
            self.post_message(SystemLog("[bold green]Batch Queue Finished[/]"))
            self.state.flush_if_dirty()
            self.call_from_thread(_finish_ui)
            # Post BatchComplete so the handler can send a desktop notification
            self.post_message(BatchComplete(
                total=self.global_total,
                succeeded=_batch_ok,
                failed=_batch_fail,
            ))

    def _download_worker(self, item: QueueItem) -> dict[str, Any]:
        """Delegate to :class:`DownloadWorker` (A3 extraction)."""
        return DownloadWorker(self, item).run()

    def _convert_to_chd(self, dest_dir: Path, silent: bool = False,
                         cancel: threading.Event | None = None) -> tuple[int, int]:
        """Thin shim → Toolchain.convert_to_chd().

        *cancel* is forwarded to the Toolchain so library operations and
        download auto-CHD can use independent cancellation signals.
        """
        return self.toolchain.convert_to_chd(dest_dir, silent=silent, cancel=cancel)

    def on_download_progress(self, message: DownloadProgress) -> None:
        grid = self.query_one("#progress-grid")
        task_id = message.task_id
        pb_id  = f"pb_{task_id}"
        lbl_id = f"lbl_{task_id}"

        fmt_progress = self._format_size(message.completed)
        fmt_total    = self._format_size(message.total)

        # Row 1: action + game name + size
        status_line = Text()
        status_line.append(message.action, style="bold #e6b73e")
        status_line.append("  ")
        name_display = message.item_name
        if " / " in name_display:
            name_display = name_display.split(" / ", 1)[1]
        name_display = normalize_game_title_keep_disc(name_display)
        if len(name_display) > 50:
            name_display = name_display[:47] + "…"
        status_line.append(name_display, style="#c9d1d9")
        status_line.append(f"  {fmt_progress}/{fmt_total}", style="dim")

        # Row 2 speed label: speed + ETA (displayed next to progress bar)
        speed_text = Text()
        if message.speed_bps > 0:
            speed_str = f"{self._format_size(int(message.speed_bps))}/s"
            speed_text.append(speed_str, style="bold #3fb950")
            self._worker_speeds[message.task_id] = message.speed_bps
            try:
                agg_speed = sum(self._worker_speeds.values())
                agg_str = f"{self._format_size(int(agg_speed))}/s"
                self.query_one("#gs-speed", Label).update(
                    Text(agg_str, style="#3fb950")
                )
            except Exception as e:
                logging.debug("Update speed indicator failed: %s", e)
        elif message.action in ("Extracting ZIP", "Converting CHD"):
            speed_text.append(f"⟳ {message.action}…", style="italic #d29922")
            try:
                self.query_one("#gs-speed", Label).update(
                    Text(f"⟳ {message.action}…", style="italic #d29922")
                )
            except Exception as e:
                logging.debug("Update action phase label failed: %s", e)
        if message.eta_secs >= 0:
            if message.eta_secs < 60:
                eta_str = f"{int(message.eta_secs)}s"
            elif message.eta_secs < 3600:
                eta_str = f"{int(message.eta_secs // 60)}m{int(message.eta_secs % 60)}s"
            else:
                eta_str = f"{int(message.eta_secs // 3600)}h{int((message.eta_secs % 3600) // 60)}m"
            if speed_text.plain:
                speed_text.append("  ")
            speed_text.append(f"ETA {eta_str}", style="dim #58a6ff")

        # U4: Update queue table status cell with action + percentage
        try:
            pct = ""
            if message.total > 0:
                pct = f" {message.completed * 100 // message.total}%"
            self.query_one("#queue-table", DataTable).update_cell(
                message.task_id, "Status", f"{message.action}{pct}"
            )
        except Exception:
            pass

        speed_lbl_id = f"spd_{task_id}"
        if task_id in self._active_progress_containers:
            try:
                self.query_one(f"#{pb_id}", ProgressBar).update(
                    progress=message.completed, total=message.total
                )
                self.query_one(f"#{lbl_id}", Label).update(status_line)
                self.query_one(f"#{speed_lbl_id}", Label).update(speed_text)
            except Exception as e:
                logging.debug("Update download progress widget failed: %s", e)
        else:
            self._active_progress_containers.add(task_id)
            grid.mount(
                Container(
                    Label(status_line, id=lbl_id),
                    Horizontal(
                        ProgressBar(id=pb_id, total=message.total, show_eta=False),
                        Label(speed_text, id=speed_lbl_id, classes="speed-label"),
                        classes="progress-bar-row",
                    ),
                    classes="progress-container", id=f"cont_{pb_id}",
                )
            )

    def on_download_complete(self, message: DownloadComplete) -> None:
        # F1: Remove completed worker from aggregate speed tracking
        self._worker_speeds.pop(message.item["id"], None)

        if message.success:
            with self._progress_lock:
                self.global_completed   += 1
                completed_snap           = self.global_completed
                total_snap               = self.global_total
            try:
                self.query_one("#global-progress", ProgressBar).advance(1)
                self.query_one("#lbl-global-progress", Label).update(
                    Text.assemble(
                        ("▸ DOWNLOAD PROGRESS", "dim"),
                        "  ",
                        (f"{completed_snap} / {total_snap}", "#e6b73e"),
                    )
                )
            except Exception as e:
                logging.debug("Update global progress on completion failed: %s", e)

            # Deferred save: mark dirty instead of flushing to disk on every
            # completion — the periodic flush timer (every 3 s) handles persistence.
            current_queue = self.state.get_active_queue()
            self.state.update_active_queue(
                [i for i in current_queue if i["id"] != message.item["id"]],
                immediate=False,
            )
            # Surgical single-row removal — no full clear+rebuild cost
            self._remove_queue_row(message.item["id"])
            self._update_global_statusbar()

            # Discard tracking id unconditionally — must happen regardless of
            # whether the DOM remove succeeds so the set stays consistent.
            self._active_progress_containers.discard(message.item["id"])
            try:
                self.query_one(f"#cont_pb_{message.item['id']}").remove()
            except Exception as e:
                logging.debug("Remove completed progress container failed: %s", e)

        elif message.cancelled:
            self._active_progress_containers.discard(message.item["id"])
            try:
                lbl_id = f"lbl_{message.item['id']}"
                self.query_one(f"#{lbl_id}", Label).update(
                    Text.assemble(("■ Paused  ", "yellow"), (message.item['name'], "dim"))
                )
                self.query_one(f"#pb_{message.item['id']}", ProgressBar).display = False
            except Exception:
                pass
            # Keep the cancelled item in the queue so the user can resume it by
            # pressing Start again.  The progress row is left visible as a "Paused"
            # indicator — it will be cleaned up when a new batch starts.

        else:
            # Download failed — mark label as failed, hide bar, then remove
            # the container after a short delay so the user can see the failure.
            self._active_progress_containers.discard(message.item["id"])
            item_id = message.item["id"]
            try:
                lbl_id = f"lbl_{item_id}"
                self.query_one(f"#{lbl_id}", Label).update(
                    Text.assemble(("✗ Failed  ", "bold red"), (message.item['name'], "dim"))
                )
                self.query_one(f"#pb_{item_id}", ProgressBar).display = False
            except Exception:
                pass
            # Remove the failed container after 5 s — gives the user time to see
            # the failure without leaving it on screen permanently.
            def _remove_failed(cid: str = item_id) -> None:
                try:
                    self.query_one(f"#cont_pb_{cid}").remove()
                except Exception:
                    pass
            self.set_timer(5.0, _remove_failed)

    # ── Generic library command dispatcher ──────────────────────────────

    @work(exclusive=True, thread=True)
    def run_library_command(self, cmd: LibraryCommand) -> None:
        """Execute any LibraryCommand on a worker thread.

        Creates the LibraryOperation context, then delegates to cmd.execute().
        All library operations (organize, convert, audit) go through here.
        """
        op = LibraryOperation(self, cmd.scope)
        cmd.execute(op, self)

    # Convenience wrappers — keep the old call-site API working.

    def run_lib_refresh(self) -> None:
        self.run_library_command(RefreshCommand())

    # ── DAT audit helpers ────────────────────────────────────────────────

    def _dat_fetch_index(
        self, op: LibraryOperation,
    ) -> dict[str, str] | None:
        """Fetch the DAT index page and return a {filename: href} mapping.

        Returns ``None`` on failure (already logged).
        """
        if not self._active_dat_url:
            op.log("DAT audit skipped — active source has no DAT URL configured.")
            return None
        op.progress("DAT Audit", "Fetching DAT index...", 0, 100)
        try:
            try:
                index_html = subprocess.check_output(
                    ["wget", "-qO-", self._active_dat_url],
                    text=True, errors="ignore", timeout=30,
                )
            except Exception:
                req = urllib.request.Request(
                    self._active_dat_url,
                    headers={'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'},
                )
                with urllib.request.urlopen(req, timeout=60) as res:
                    index_html = res.read().decode('utf-8', errors='ignore')

            soup = BeautifulSoup(index_html, 'html.parser', parse_only=_DAT_INDEX_STRAINER)
            dat_index: dict[str, str] = {}
            for a_tag in soup.find_all('a'):
                href = a_tag.get('href', '')
                name = unquote(href)
                if name.endswith('.dat'):
                    dat_index[name] = href
            return dat_index
        except Exception as err:
            op.log(f"DAT Audit: Failed to fetch DAT index: {err}", True)
            op.progress("DAT Audit", "Failed", 0, 100)
            return None

    def _dat_resolve_dat_file(
        self, console_name: str, dat_index: dict[str, str],
        dat_ttl: float, op: LibraryOperation,
    ) -> Path | None:
        """Find the matching DAT for *console_name*, download if needed.

        Returns the local path to the cached DAT, or ``None`` if unavailable.
        """
        standard_prefix = f"{console_name} - Datfile"
        extra_prefixes = _DAT_SEARCH_PREFIXES.get(console_name, [])
        prefixes_to_try = [standard_prefix] + extra_prefixes

        dat_href: str | None = None
        matched_prefix: str = ""
        for prefix in prefixes_to_try:
            dat_href = next(
                (href for name, href in dat_index.items()
                 if name.startswith(prefix)),
                None,
            )
            if dat_href:
                matched_prefix = prefix
                break

        if not dat_href:
            op.log(
                f"DAT Audit [{console_name}]: No matching DAT found at source — skipping.\n"
                f"  (Tried prefixes: {', '.join(prefixes_to_try)})"
            )
            return None

        if matched_prefix != standard_prefix:
            op.log(
                f"DAT Audit [{_escape_markup(console_name)}]: Using alternate DAT format "
                f"[bold]{_escape_markup(Path(unquote(dat_href)).name)}[/bold]"
            )

        # Download if not cached or stale
        dat_dir = DAT_CACHE_DIR / console_name
        dat_dir.mkdir(parents=True, exist_ok=True)
        dat_filename = Path(unquote(dat_href)).name
        dat_path = dat_dir / dat_filename

        _dat_is_stale = False
        if dat_path.exists():
            try:
                age = time.time() - dat_path.stat().st_mtime
                if age > dat_ttl:
                    _dat_is_stale = True
                    op.log(
                        f"DAT Audit [{console_name}]: Cached DAT is "
                        f"{int(age // 86400)}d old — refreshing."
                    )
            except OSError:
                pass

        if not dat_path.exists() or _dat_is_stale:
            dat_url = urljoin(self._active_dat_url, dat_href)
            op.log(f"DAT Audit [{console_name}]: Downloading DAT...")
            dat_tmp = dat_path.with_suffix('.tmp')
            try:
                proc = subprocess.run(
                    ["wget", "-q", "-O", str(dat_tmp), dat_url],
                    timeout=120,
                )
                if proc.returncode != 0:
                    raise RuntimeError("wget failed")
                dat_tmp.replace(dat_path)
            except Exception:
                dat_tmp.unlink(missing_ok=True)
                try:
                    req = urllib.request.Request(
                        dat_url,
                        headers={'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'},
                    )
                    with urllib.request.urlopen(req, timeout=30) as res, open(dat_tmp, 'wb') as f:
                        shutil.copyfileobj(res, f)
                    dat_tmp.replace(dat_path)
                except Exception as err:
                    dat_tmp.unlink(missing_ok=True)
                    op.log(
                        f"DAT Audit [{console_name}]: Could not download DAT: {err}", True
                    )
                    return None

        return dat_path

    @staticmethod
    def _dat_parse_xml(
        dat_path: Path,
    ) -> tuple[dict[str, dict[str, str]], set[str], set[str]] | None:
        """Parse a DAT XML file into lookup structures.

        Returns ``(dat_by_sha1, ambiguous_sha1s, dat_all_games)`` or ``None``
        on parse failure.  SHA-1 keys are lowercased.

        *dat_by_sha1* maps unique SHA-1 → ``{"name": rom_name, "game": game_name}``.
        SHA-1 values seen in more than one game are placed in *ambiguous_sha1s*
        instead (e.g. identical silent audio tracks shared across PS1 titles).
        """
        dat_by_sha1: dict[str, dict[str, str]] = {}
        ambiguous_sha1s: set[str] = set()
        dat_all_games: set[str] = set()
        try:
            context = ET.iterparse(dat_path, events=('start', 'end'))
            _, xml_root = next(context)
            current_game = "Unknown"
            for event, elem in context:
                if event == 'start' and elem.tag == 'game':
                    current_game = elem.get('name', 'Unknown')
                    dat_all_games.add(current_game)
                elif event == 'end' and elem.tag == 'rom':
                    sha1_val = elem.get('sha1')
                    rom_name = elem.get('name')
                    if sha1_val and rom_name:
                        sha1_lower = sha1_val.lower()
                        if sha1_lower in ambiguous_sha1s:
                            pass
                        elif sha1_lower in dat_by_sha1:
                            ambiguous_sha1s.add(sha1_lower)
                            del dat_by_sha1[sha1_lower]
                        else:
                            dat_by_sha1[sha1_lower] = {
                                "name": rom_name, "game": current_game,
                            }
                    elem.clear()
                elif event == 'end' and elem.tag == 'game':
                    xml_root.clear()
        except Exception as exc:
            logging.error("DAT XML parse failed for %s: %s", dat_path, exc)
            return None
        return dat_by_sha1, ambiguous_sha1s, dat_all_games

    def _dat_audit_one_console(
        self, console_dir: Path, library: Path,
        dat_by_sha1: dict[str, dict[str, str]],
        ambiguous_sha1s: set[str],
        dat_disc_groups: dict[str, set[str]],
        dry_run: bool, op: LibraryOperation,
    ) -> tuple[int, int, int, int]:
        """Run the DAT audit for a single console directory.

        Returns ``(perfect, misnamed, ambiguous, bad)`` counts.
        """
        console_name = console_dir.name

        # ── Collect auditable files ──────────────────────────────────────
        game_dirs: dict[Path, list[Path]] = {}
        for ext in _DAT_AUDITABLE_EXTS:
            for item in console_dir.rglob(f'*{ext}'):
                if (not item.name.startswith('.')
                        and not any(p.name.startswith('.') for p in item.parents)):
                    game_dirs.setdefault(item.parent, []).append(item)

        if not game_dirs:
            op.log(f"DAT Audit [{console_name}]: No auditable files found.")
            return (0, 0, 0, 0)

        # ── Load SHA-1 sidecar cache ─────────────────────────────────────
        sha1_cache_path = DAT_CACHE_DIR / console_name / ".sha1_cache.json"
        sha1_cache: dict[str, dict[str, Any]] = {}
        try:
            if sha1_cache_path.exists():
                with open(sha1_cache_path, 'r', encoding='utf-8') as cf:
                    loaded = json.load(cf)
                migrated: dict[str, dict[str, Any]] = {}
                for k, v in loaded.items():
                    p = Path(k)
                    if p.is_absolute():
                        try:
                            rel = p.relative_to(console_dir).as_posix()
                        except ValueError:
                            continue
                        migrated[rel] = v
                    else:
                        migrated[k] = v
                sha1_cache = migrated
        except (json.JSONDecodeError, OSError):
            sha1_cache = {}

        # ── Hash files and match against DAT ─────────────────────────────
        op.lib_status.defer_flushes(True)
        con_perfect = con_misnamed = con_bad = con_ambiguous = 0
        all_files = [(gd, fp) for gd, fps in game_dirs.items() for fp in fps]
        total_files = len(all_files)
        hash_results: dict[Path, bool] = {}
        cache_dirty = False
        renamed_old_dirs: set[Path] = set()

        # Parallel hashing
        _hash_idx = itertools.count(1)
        hash_lock = threading.Lock()

        def _hash_file(pair: tuple[Path, Path]) -> tuple[Path, Path, str | None]:
            game_dir_h, file_path_h = pair
            if op.cancelled:
                return (game_dir_h, file_path_h, None)
            idx = next(_hash_idx)
            op.progress(
                f"Hashing {console_name} ({idx}/{total_files})",
                file_path_h.name, idx, total_files,
            )
            file_hash_h: str | None = None
            try:
                stat = file_path_h.stat()
                key = file_path_h.relative_to(console_dir).as_posix()
                cached = sha1_cache.get(key)
                if (cached
                        and cached.get("mtime") == stat.st_mtime
                        and cached.get("size") == stat.st_size):
                    file_hash_h = cached["sha1"]
                else:
                    sha1_obj = hashlib.sha1(usedforsecurity=False)
                    with open(file_path_h, 'rb') as fh:
                        while chunk := fh.read(_HASH_CHUNK_BYTES):
                            sha1_obj.update(chunk)
                    file_hash_h = sha1_obj.hexdigest().lower()
                    with hash_lock:
                        sha1_cache[key] = {
                            "mtime": stat.st_mtime,
                            "size": stat.st_size,
                            "sha1": file_hash_h,
                        }
                        nonlocal cache_dirty
                        cache_dirty = True
            except Exception:
                pass
            return (game_dir_h, file_path_h, file_hash_h)

        with concurrent.futures.ThreadPoolExecutor(max_workers=4) as hash_pool:
            hash_results_raw = list(hash_pool.map(_hash_file, all_files))

        # Sequential matching / renaming
        for game_dir, file_path, file_hash in hash_results_raw:
            if op.cancelled:
                break

            if file_hash is None:
                con_bad += 1
                hash_results[file_path] = False
                logging.debug("DAT audit hash returned None: %s", file_path)
                continue

            try:
                if file_hash in ambiguous_sha1s:
                    con_ambiguous += 1
                    hash_results[file_path] = True

                elif file_hash in dat_by_sha1:
                    expected_name = dat_by_sha1[file_hash]['name']
                    expected_game = dat_by_sha1[file_hash]['game']

                    if file_path.name == expected_name:
                        con_perfect += 1
                        hash_results[file_path] = True
                    else:
                        con_misnamed += 1
                        clean_game = DISC_REGEX.sub('', expected_game).strip()
                        if clean_game != expected_game:
                            correct_dir = console_dir / clean_game / expected_game
                        else:
                            correct_dir = console_dir / expected_game
                        correct_path = correct_dir / expected_name

                        if dry_run:
                            hash_results[file_path] = True
                            op.log(
                                f"[cyan][DRY-RUN][/cyan] Would rename: "
                                f"[dim]{_escape_markup(file_path.name)}[/dim]"
                                f" → [bold]{_escape_markup(str(correct_path.relative_to(library)))}[/bold]"
                            )
                        else:
                            try:
                                correct_dir.mkdir(parents=True, exist_ok=True)
                                shutil.move(file_path, correct_path)
                                old_cache_key = file_path.relative_to(console_dir).as_posix()
                                if old_cache_key in sha1_cache:
                                    new_cache_key = correct_path.relative_to(console_dir).as_posix()
                                    sha1_cache[new_cache_key] = sha1_cache.pop(old_cache_key)
                                    cache_dirty = True
                                hash_results[correct_path] = True
                                op.lib_status.set_status(correct_dir, "validated")
                                renamed_old_dirs.add(game_dir)
                                op.log(
                                    f"Fixed [{console_name}]: "
                                    f"'{file_path.name}' → '{correct_dir.name}/{expected_name}'"
                                )
                            except Exception as rename_err:
                                hash_results[file_path] = True
                                logging.exception(
                                    "DAT audit rename failed: %s → %s", file_path, correct_path,
                                )
                                op.log(
                                    f"Rename failed [{console_name}]: "
                                    f"'{file_path.name}': {rename_err}", True,
                                )
                else:
                    con_bad += 1
                    op.log(
                        f"Bad/Unknown [{console_name}]: "
                        f"'{file_path.name}' (SHA1: {file_hash})"
                    )
                    hash_results[file_path] = False

            except Exception as err:
                con_bad += 1
                hash_results[file_path] = False
                logging.exception("DAT audit read error: %s", file_path)
                op.log(
                    f"Read error [{console_name}]: '{file_path.name}': {err}", True,
                )

        # ── Persist SHA-1 cache ──────────────────────────────────────────
        if cache_dirty:
            sha1_cache = {
                k: v for k, v in sha1_cache.items()
                if (console_dir / k).exists()
            }
            try:
                sha1_cache_path.parent.mkdir(parents=True, exist_ok=True)
                tmp_cache = sha1_cache_path.with_suffix('.tmp')
                with open(tmp_cache, 'w', encoding='utf-8') as cf:
                    json.dump(sha1_cache, cf)
                tmp_cache.replace(sha1_cache_path)
            except OSError:
                pass

        # ── Write validation markers ─────────────────────────────────────
        try:
            if not dry_run:
                for game_dir, files in game_dirs.items():
                    if game_dir in renamed_old_dirs:
                        op.lib_status.remove(game_dir)
                    else:
                        dir_ok = all(hash_results.get(fp, False) for fp in files)
                        if dir_ok:
                            op.lib_status.set_status(game_dir, "validated")
                        else:
                            op.lib_status.set_status(game_dir, "corrupted")

                # Multi-disc completeness check
                incomplete_parents: set[Path] = set()
                for game_dir in game_dirs:
                    dir_name = game_dir.name
                    base_name = DISC_REGEX.sub('', dir_name).strip()
                    if base_name == dir_name:
                        continue
                    if base_name not in dat_disc_groups:
                        continue
                    expected_discs = dat_disc_groups[base_name]
                    parent_dir = game_dir.parent
                    for disc_name in expected_discs:
                        disc_dir = parent_dir / disc_name
                        if not disc_dir.exists() or not any(
                            f.suffix.lower() in _DAT_AUDITABLE_EXTS
                            for f in disc_dir.iterdir() if f.is_file()
                        ):
                            incomplete_parents.add(parent_dir)
                            break

                for parent_dir in incomplete_parents:
                    for child in parent_dir.iterdir():
                        if child.is_dir() and op.lib_status.get(child) == "validated":
                            op.lib_status.remove(child)
                    op.log(
                        f"Incomplete [{console_name}]: "
                        f"'{parent_dir.name}' — missing disc(s)"
                    )
        finally:
            op.lib_status.defer_flushes(False)

        return (con_perfect, con_misnamed, con_ambiguous, con_bad)

    def run_bulk_dat_audit(self, scope: Path | None = None) -> None:
        self.run_library_command(DatAuditCommand(scope))



    def run_lib_convert(self, scope: Path | None = None) -> None:
        self.run_library_command(ConvertCommand(scope, toolchain=self.toolchain))

    @work(exclusive=True, thread=True)
    def run_chd_to_original(self, scope: Path | None = None) -> None:
        """Convert .chd files back to original format within *scope*.

        *scope* may be a console directory, a game directory, or None / the
        library root to process everything.  Uses chdman extractcd (→ .cue/.bin)
        then falls back to extracthd (→ .img).  Source .chd is removed only on
        confirmed success.
        """
        op = LibraryOperation(self, scope)
        library = op.library
        scope_label = op.scope_label()
        # Resolve locally — same race-safety rationale as run_lib_convert.
        chdman = self.toolchain.chdman_path or Toolchain.find_chdman()
        if not chdman:
            op.log(
                "[bold red]chdman not found.[/bold red] "
                "Run 'Setup chdman' first, or install it manually.", True
            )
            return

        if scope is None or scope == library:
            scope = library

        op.log(f"CHD → Original: Scanning {scope_label}\u2026")

        chd_files: list[Path] = [
            f for f in scope.rglob("*.chd")
            if not any(p.name.startswith('.') for p in f.parents)
        ]

        total_ops = len(chd_files)
        if total_ops == 0:
            op.log(f"CHD → Original: No .chd files found in {scope_label}.")
            op.progress("CHD → Original", "Done", 100, 100)
            return

        op.log(f"CHD → Original: Extracting {total_ops} file(s)...")
        converted = failed = 0

        for i, chd_path in enumerate(chd_files, 1):
            if op.cancelled:
                op.log("[yellow]CHD extraction cancelled.[/]")
                break

            op.progress(f"Extracting ({i}/{total_ops})", chd_path.name, i, total_ops)
            op.log(f"Extracting: {chd_path.name}")

            dest_dir = chd_path.parent

            # Try extractcd first (CD images); fall back to extracthd (hard-disk/DVD).
            # extracthd outputs .iso (not .img) to match Redump DAT naming.
            #
            # For extractcd: if the original .cue was preserved during convert_to_chd,
            # we extract to a temp .cue, then rename the chdman-generated bin files to
            # match the names referenced in the original .cue.  This ensures the .cue
            # SHA1 matches the DAT exactly (line endings, track names, etc.).
            # If no preserved .cue exists, we use --splitbin and CRLF-convert the
            # generated .cue as a best-effort fallback.
            success = False
            for subcommand, output_suffix in [("extractcd", ".cue"), ("extracthd", ".iso")]:
                original_cue = chd_path.with_suffix(".cue")
                has_preserved_cue = subcommand == "extractcd" and original_cue.exists()

                if has_preserved_cue:
                    # Extract to a temp .cue so the original is not overwritten
                    tmp_cue = chd_path.with_suffix(".cue.tmp")
                    output_file = tmp_cue
                else:
                    output_file = chd_path.with_suffix(output_suffix)

                cmd = [chdman, subcommand,
                       "-i", str(chd_path),
                       "-o", str(output_file)]
                if subcommand == "extractcd":
                    cmd.append("--splitbin")
                try:
                    proc = subprocess.Popen(
                        cmd,
                        stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
                        **_LOW_PRIO_POPEN,
                    )
                    self._register_process(proc)
                    try:
                        _, err_out = proc.communicate(timeout=_CHD_TIMEOUT)
                    except subprocess.TimeoutExpired:
                        proc.kill()
                        proc.wait()
                        self._unregister_process(proc)
                        op.log(
                            f"CHD Extract [{chd_path.name}] {subcommand} timed out — killed.", True
                        )
                        break
                    self._unregister_process(proc)

                    if proc.returncode == 0:
                        success = True
                        converted += 1

                        if subcommand == "extractcd" and has_preserved_cue:
                            # Read the bin names from both the original .cue and the generated .cue,
                            # then rename the extracted bins to match the original .cue references.
                            try:
                                with open(original_cue, "r", encoding="utf-8", errors="ignore") as f:
                                    orig_bins = CUE_BIN_REGEX.findall(f.read())
                                with open(tmp_cue, "r", encoding="utf-8", errors="ignore") as f:
                                    gen_bins = CUE_BIN_REGEX.findall(f.read())
                                for gen_name, orig_name in zip(gen_bins, orig_bins):
                                    gen_path = dest_dir / gen_name
                                    orig_path = dest_dir / orig_name
                                    if gen_path.exists() and gen_name != orig_name:
                                        gen_path.rename(orig_path)
                            except Exception as e:
                                logging.error("CHD extract: bin rename failed: %s", e)
                            # Remove the temp .cue — the original is already in place
                            try:
                                tmp_cue.unlink()
                            except OSError:
                                pass
                        elif subcommand == "extractcd" and output_file.exists():
                            # No preserved .cue — CRLF-convert the generated one as best-effort
                            try:
                                raw = output_file.read_bytes()
                                if b'\r\n' not in raw and b'\n' in raw:
                                    output_file.write_bytes(raw.replace(b'\n', b'\r\n'))
                            except OSError:
                                pass

                        # Remove source .chd only after confirmed successful extraction
                        try:
                            chd_path.unlink()
                        except OSError:
                            pass
                        # Update validation status — game is now incomplete until re-verified
                        op.lib_status.remove(dest_dir)
                        break

                    # Extraction failed — discard any partial output before trying next subcommand
                    if output_file.exists():
                        # For extractcd --splitbin, also remove generated .bin track files
                        if subcommand == "extractcd":
                            try:
                                with open(output_file, "r", encoding="utf-8", errors="ignore") as cf:
                                    for bin_name in CUE_BIN_REGEX.findall(cf.read()):
                                        bp = output_file.parent / bin_name
                                        if bp.exists():
                                            bp.unlink()
                            except OSError:
                                pass
                        try:
                            output_file.unlink()
                        except OSError:
                            pass
                    # If extractcd fails it's probably an HD image — try next subcommand
                except Exception as e:
                    op.log(
                        f"CHD Extract [{chd_path.name}] {subcommand} error: {e}", True
                    )
                    break

            if not success:
                failed += 1
                op.log(
                    f"[red]Failed to extract:[/red] {_escape_markup(chd_path.name)} "
                    "(not a CD or HD image, or chdman error)", True
                )

        op.progress("CHD → Original", "Complete", total_ops, total_ops)
        op.log(
            f"CHD → Original complete: "
            f"[bold green]{converted}[/] extracted, [bold red]{failed}[/] failed."
        )
        if converted:
            self.run_lib_status_scan()

    # ── Batch completion notification ─────────────────────────────────────────

    def on_batch_complete(self, message: BatchComplete) -> None:
        """Refresh the library tree and send a desktop notification when a batch finishes."""
        # Refresh the library tree so newly downloaded games (including
        # multi-disc titles) reflect their current status immediately.
        if message.succeeded:
            self.run_lib_status_scan()
            self._refresh_history_table()

        if not self.state.settings.get("notify_on_batch_complete", True):
            return
        title = "Myrient: Downloads Finished"
        body  = (f"{message.succeeded} succeeded"
                 + (f", {message.failed} failed" if message.failed else ""))
        self._send_desktop_notification(title, body)

    @staticmethod
    def _send_desktop_notification(title: str, body: str) -> None:
        """Best-effort desktop notification via notify-send (Linux) or osascript (macOS)."""
        try:
            if _OS == "linux" and shutil.which("notify-send"):
                subprocess.run(
                    ["notify-send", "-t", "8000", title, body],
                    stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                    timeout=5,
                )
            elif _OS == "darwin":
                # Escape backslashes and double quotes to prevent AppleScript injection
                safe_body  = body.replace("\\", "\\\\").replace('"', '\\"')
                safe_title = title.replace("\\", "\\\\").replace('"', '\\"')
                script = (
                    f'display notification "{safe_body}" with title "{safe_title}"'
                )
                subprocess.run(
                    ["osascript", "-e", script],
                    stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                    timeout=5,
                )
        except Exception:
            pass   # notifications are best-effort — never crash the app

    # ── Queue reorder helpers ─────────────────────────────────────────────────

    def _move_queue_item(self, direction: int) -> None:
        """Move the selected queue row up (-1) or down (+1)."""
        try:
            table = self.query_one("#queue-table", DataTable)
            rows  = list(table.ordered_rows)
            cursor = table.cursor_row
            if cursor is None or not rows:
                return
            if cursor >= len(rows):
                return
            item_id = rows[cursor].key.value
            current_queue = self.state.get_active_queue()
            idx = next((i for i, q in enumerate(current_queue) if q["id"] == item_id), None)
            if idx is None:
                return
            new_idx = idx + direction
            if new_idx < 0 or new_idx >= len(current_queue):
                return
            current_queue[idx], current_queue[new_idx] = current_queue[new_idx], current_queue[idx]
            self.state.update_active_queue(current_queue)
            self._refresh_queue_table()
            # Move cursor to follow the item
            new_cursor = max(0, min(cursor + direction, len(rows) - 1))
            table.move_cursor(row=new_cursor)
        except Exception as exc:
            logging.debug("Queue item move failed: %s", exc)

    # ── Watchdog filesystem watch ─────────────────────────────────────────────

    def _start_watchdog(self) -> None:
        """Start a watchdog observer on the library root (if watchdog is available)."""
        if not _WATCHDOG_AVAILABLE:
            self._log(
                "[yellow]watchdog not installed.[/yellow] "
                "Library watch mode requires: pip install watchdog",
                is_error=False,
            )
            return
        library = Path(self.state.settings["library_root"])
        if not library.exists():
            return
        if self._watch_observer is not None:
            try:
                self._watch_observer.stop()
                self._watch_observer.join(timeout=2)
            except Exception:
                pass

        app_ref = self   # capture for closure

        class _Handler(_FSEventHandler):  # type: ignore[misc]
            def on_any_event(self, event: Any) -> None:  # noqa: ANN001
                app_ref.post_message(LibraryWatchEvent())

        observer = _WatchdogObserver()   # type: ignore[misc]
        observer.schedule(_Handler(), str(library), recursive=True)
        observer.start()
        self._watch_observer = observer
        self._log(f"[dim]Library watch active:[/dim] {library}", is_error=False)

    def on_library_watch_event(self, _: LibraryWatchEvent) -> None:
        """Debounce rapid FS events and trigger a library rescan after quiet period."""
        if self._watch_debounce_timer is not None:
            self._watch_debounce_timer.stop()
        self._watch_debounce_timer = self.set_timer(
            _WATCH_DEBOUNCE, self.run_lib_status_scan
        )

    # ── Session log viewer ────────────────────────────────────────────────────

    def _refresh_session_log_list(self) -> None:
        """Populate the session log ListView with available log files (newest first)."""
        try:
            log_list = self.query_one("#session-log-list", ListView)
            log_list.clear()
            if not SESSION_LOG_DIR.exists():
                return
            log_files = sorted(
                SESSION_LOG_DIR.glob("myrient_*.log"),
                key=lambda p: p.stat().st_mtime,
                reverse=True,
            )
            for lf in log_files:
                item = DataListItem(Label(lf.name), data=lf)  # C2
                log_list.append(item)
        except Exception:
            pass

    def on_list_view_selected(self, event: ListView.Selected) -> None:  # C1
        list_id = getattr(event.list_view, "id", None)

        if list_id == "console-list":
            data = getattr(event.item, 'data', None)  # C2: DataListItem.data
            if data:
                self.selected_console = data
                self._selected_games.clear()
                self._global_search_results = {}
                self._browse_global_mode = False
                self._update_selection_count()
                self._show_browse_game_view(True)
                try:
                    btn = self.query_one("#btn-toggle-global", Button)
                    btn.variant = "default"
                    search_input = self.query_one("#search-games", Input)
                    search_input.placeholder = "  search games…"
                except Exception:
                    pass
                game_table = self.query_one("#game-list", DataTable)
                game_table.clear()
                game_table.add_row(
                    Text("…", style="dim"),
                    Text("Fetching games — please wait…", style="dim"),
                    Text(""), Text(""),
                    key="LOADING",
                )
                self.query_one("#search-games", Input).value = ""
                self.fetch_games(data)

        elif list_id == "session-log-list":
            log_path = getattr(event.item, 'data', None)  # C2: DataListItem.data
            if log_path and isinstance(log_path, Path):
                self._load_session_log(log_path)

    def _load_session_log(self, log_path: Path) -> None:
        """Display contents of a session log file in the viewer."""
        try:
            viewer = self.query_one("#session-log-view", RichLog)
            viewer.clear()
            try:
                text = log_path.read_text(encoding="utf-8", errors="replace")
            except OSError as e:
                viewer.write(f"Error reading {log_path.name}: {e}")
                return
            for line in text.splitlines():
                viewer.write(line)
        except Exception:
            pass

    def _lib_delete_selected(self) -> None:
        """Delete the currently selected game/console from the library tree."""
        tree = self.query_one("#lib-tree", Tree)
        if not tree.cursor_node or not isinstance(tree.cursor_node.data, Path):
            self.notify("Select a game or console folder first.", severity="warning")
            return
        target_path: Path = tree.cursor_node.data

        def check_delete(confirm: bool) -> None:
            if confirm and target_path:
                try:
                    library = Path(self.state.settings['library_root'])
                    self._lib_status.remove(target_path)
                    self._lib_status.prune(library)
                    if target_path.is_dir():
                        shutil.rmtree(target_path)
                    else:
                        target_path.unlink()
                    # Clean up empty parent grouping folder (multi-disc case)
                    parent = target_path.parent
                    if (parent.exists()
                            and parent != library
                            and parent.parent != library):
                        try:
                            if not any(parent.iterdir()):
                                self._lib_status.remove(parent)
                                parent.rmdir()
                                self.post_message(SystemLog(
                                    f"Cleaned up empty grouping folder: {parent.name}"
                                ))
                        except OSError:
                            pass
                    self.run_lib_status_scan()
                except Exception as err:
                    self.notify(f"Error during deletion: {err}", severity="error")
        self.push_screen(ConfirmDeleteScreen(target_path.name), check_delete)

    # ── Queue multi-select ───────────────────────────────────────────────────

    def _queue_toggle_selection(self) -> None:
        """Toggle selection on the current queue row for bulk operations."""
        try:
            table = self.query_one("#queue-table", DataTable)
            cursor = table.cursor_row
            if cursor is None:
                return
            rows = table.ordered_rows
            if cursor >= len(rows):
                return
            item_id = rows[cursor].key.value
            if item_id in self._queue_selected:
                self._queue_selected.discard(item_id)
            else:
                self._queue_selected.add(item_id)
            self._refresh_queue_row_visual(table, item_id)
            # N6: Track last toggled index for range selection
            self._last_queue_selected_idx = cursor
        except Exception:
            pass

    def _refresh_queue_row_visual(self, table: DataTable, item_id: str) -> None:
        """Update a queue row's visual to reflect multi-select state."""
        try:
            # P2: Use targeted lookup instead of copying the entire queue
            item = self.state.get_queue_item(item_id)
            if not item:
                return
            selected = item_id in self._queue_selected
            name_cell = Text(item["name"], style="bold cyan" if selected else "")
            table.update_cell(item_id, "Game", name_cell, update_width=False)
        except Exception:
            pass

    def _remove_selected_queue_items(self) -> None:
        """Remove all multi-selected queue items (or the cursor item if none selected)."""
        try:
            table = self.query_one("#queue-table", DataTable)
            if self._queue_selected:
                ids_to_remove = set(self._queue_selected)
                self._queue_selected.clear()
            else:
                # Fall back to cursor item
                rows = list(table.ordered_rows)
                if table.cursor_row is not None and table.cursor_row < len(rows):
                    ids_to_remove = {rows[table.cursor_row].key.value}
                else:
                    return
            current_queue = self.state.get_active_queue()
            new_queue = [i for i in current_queue if i["id"] not in ids_to_remove]
            if len(new_queue) < len(current_queue):
                self.state.update_active_queue(new_queue)
                self._refresh_queue_table()
        except Exception as e:
            logging.error("Queue multi-remove error: %s", e)

    # ── Preset filter profile management ─────────────────────────────────────

    def _refresh_preset_dropdown(self) -> None:
        presets = self.state.settings.get("filter_presets", {})
        try:
            sel = self.query_one("#preset-select", Select)
            sel.set_options([(k, k) for k in presets.keys()])
        except Exception:
            pass

    def _save_current_preset(self, name: str) -> None:
        if not name.strip():
            return
        preset_data = {
            "include": sorted(self._filter_include_sel),
            "exclude": sorted(self._filter_exclude_sel),
        }
        self.state.mutate_settings(
            lambda s: s.setdefault("filter_presets", {}).__setitem__(name, preset_data)
        )
        self._refresh_preset_dropdown()
        self.notify(f"Preset '{name}' saved")

    def _load_preset(self, name: str) -> None:
        presets = self.state.settings.get("filter_presets", {})
        preset  = presets.get(name)
        if not preset:
            self.notify(f"Preset '{name}' not found", severity="warning")
            return
        self._filter_include_sel = set(preset.get("include", []))
        self._filter_exclude_sel = set(preset.get("exclude", []))
        # Refresh filter table visuals
        try:
            inc_tbl = self.query_one("#set-include", DataTable)
            for row in inc_tbl.ordered_rows:
                self._refresh_filter_row(inc_tbl, row.key.value, self._filter_include_sel)
            exc_tbl = self.query_one("#set-exclude", DataTable)
            for row in exc_tbl.ordered_rows:
                self._refresh_filter_row(exc_tbl, row.key.value, self._filter_exclude_sel)
        except Exception:
            pass
        self.call_later(self._render_tags_panel)
        self.notify(f"Preset '{name}' loaded")
        # A7: Auto-refresh game list with new filters
        if self.selected_console:
            self.fetch_games(self.selected_console)

    def _delete_preset(self, name: str) -> None:
        presets = self.state.settings.get("filter_presets", {})
        if name not in presets:
            return
        self.state.mutate_settings(
            lambda s: s.get("filter_presets", {}).pop(name, None)
        )
        self._refresh_preset_dropdown()
        self.notify(f"Preset '{name}' deleted")


    # ── Library disk usage helper ─────────────────────────────────────────────

    @staticmethod
    def _console_disk_usage(console_path: Path) -> int:
        """Return total bytes used by all files under *console_path*.
        Uses os.scandir for performance — avoids repeatedly calling stat() via pathlib.
        """
        total = 0
        try:
            stack = [str(console_path)]
            while stack:
                current = stack.pop()
                try:
                    with os.scandir(current) as it:
                        for entry in it:
                            if entry.is_file(follow_symlinks=False):
                                try:
                                    total += entry.stat(follow_symlinks=False).st_size
                                except OSError:
                                    pass
                            elif entry.is_dir(follow_symlinks=False):
                                stack.append(entry.path)
                except PermissionError:
                    pass
        except Exception:
            pass
        return total

    # ── Shared library-traversal helpers ─────────────────────────────────────

    @staticmethod
    def _classify_game_dir(d: Path, lib_status: LibraryStatus) -> str | None:
        """Classify a candidate game directory.

        Returns ``'validated'``, ``'corrupted'``, ``'incomplete'``, or ``None``
        (not a recognised game dir — caller should skip it).
        Status is read from *lib_status* — no marker files are checked.

        A completely empty directory (no files *and* no subdirs) returns
        ``None`` — it is either an orphaned multi-disc grouping folder or a
        download that was interrupted before any data landed.  In both cases
        the directory is not a recognisable game and should be invisible in
        the library tree.  The Organize command cleans these up on request.
        """
        try:
            dir_files = [f for f in d.iterdir() if f.is_file() and not f.name.startswith('.')]
        except PermissionError:
            return None

        # Empty directory: if it contains subdirectories it is likely a
        # multi-disc grouping folder — return None so the walker descends.
        # If it has NO subdirs either, it is an orphaned/interrupted dir —
        # also return None so it doesn't pollute the tree as "incomplete".
        if not dir_files:
            return None

        # _GAME_EXTS is a module-level frozenset — O(1) membership test
        has_game = has_zip = False
        for f in dir_files:
            ext = f.suffix.lower()
            if ext in _GAME_EXTS:
                has_game = True
            elif ext == '.zip':
                has_zip = True
            if has_game and has_zip:
                break
        if not (has_game or has_zip):
            return None
        stored = lib_status.get(d)
        if stored in ("validated", "corrupted"):
            return stored
        return "incomplete"

    @staticmethod
    def _walk_library_game_dirs(library: Path, lib_status: LibraryStatus) -> Iterator[tuple[str, Path, str]]:
        """Yield ``(console_name, game_dir, status)`` for every recognised game
        directory under *library* at depth-1 (direct games) and depth-2 (multi-disc
        grouping folders).  Implemented as a generator — no list allocation, constant
        memory regardless of library size.  Handles PermissionError at every level.
        """
        if not library.exists():
            return

        _by_name = operator.attrgetter('name')   # built once per call, not per sorted()

        try:
            console_entries = sorted(
                (e for e in library.iterdir() if e.is_dir() and not e.name.startswith('.')),
                key=_by_name,
            )
        except PermissionError:
            return

        for console_dir in console_entries:
            console_name = console_dir.name
            try:
                depth1 = sorted(
                    (e for e in console_dir.iterdir() if e.is_dir() and not e.name.startswith('.')),
                    key=_by_name,
                )
            except PermissionError:
                continue

            for child in depth1:
                status = MyrientTUI._classify_game_dir(child, lib_status)
                if status is not None:
                    yield (console_name, child, status)
                else:
                    # May be a grouping folder (multi-disc base) — check its children
                    try:
                        for grandchild in sorted(
                            (e for e in child.iterdir() if e.is_dir() and not e.name.startswith('.')),
                            key=_by_name,
                        ):
                            gs = MyrientTUI._classify_game_dir(grandchild, lib_status)
                            if gs is not None:
                                yield (console_name, grandchild, gs)
                    except PermissionError:
                        pass

    @work(exclusive=True, thread=True)
    def run_lib_status_scan(self) -> None:
        """Scans the library and posts LibraryTreeReady for main-thread Tree rebuild."""
        library = Path(self.state.settings['library_root'])
        self.post_message(LibraryProgress("Library Scan", "Scanning…", 0, 1))

        # structure: {console_name: (console_path, [(game_dir, status_str, has_chd, has_ps2_patch), ...])}
        structure: dict[str, tuple[Path, list[tuple[Path, str, bool, bool]]]] = {}
        for console_name, game_dir, status in self._walk_library_game_dirs(library, self._lib_status):
            # Detect .chd files and PS2 patch sidecar — lightweight checks on already-listed dir
            try:
                dir_files = [f for f in game_dir.iterdir() if f.is_file()]
                has_chd = any(f.suffix.lower() == '.chd' for f in dir_files)
                has_ps2_patch = any(f.name == 'DVD_Sectors.Bin' for f in dir_files)
            except PermissionError:
                has_chd = False
                has_ps2_patch = False
            if console_name not in structure:
                structure[console_name] = (library / console_name, [])
            structure[console_name][1].append((game_dir, status, has_chd, has_ps2_patch))

        # F3: Build set of validated game directory names for browser indicator
        validated_names: set[str] = set()
        for _cname, (_cpath, games_list) in structure.items():
            for game_dir, status, _has_chd, _has_patch in games_list:
                if status == "validated":
                    validated_names.add(game_dir.name)
        self.call_from_thread(setattr, self, "_library_game_names", validated_names)

        # P4/P7: Compute disk usage in parallel across consoles
        disk_usage: dict[str, int] = {}
        with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
            futs = {
                pool.submit(self._console_disk_usage, cp): cn
                for cn, (cp, _) in structure.items()
            }
            for f in concurrent.futures.as_completed(futs):
                disk_usage[futs[f]] = f.result()

        self.post_message(LibraryTreeReady(structure, library, disk_usage))

    def _find_source_game(self, console_name: str, dir_name: str) -> tuple[str, str, str] | None:
        """Find a game on the active source by matching its directory name against the console listing.

        Returns ``(game_name, game_url, size_str)`` on hit, or *None* if not found.
        """
        try:
            console_url = self._active_base_url + quote(console_name, safe="") + "/"
            games = self.scraper.scrape_links(console_url)
            for g in games:
                if strip_extension(g["name"]) == dir_name:
                    return g["name"], urljoin(console_url, g["url_part"]), g.get("size_str", "N/A")
        except Exception as exc:
            logging.debug("_find_source_game failed for %s/%s: %s", console_name, dir_name, exc)
        return None

    def _find_disc_variants(self, console_name: str, base_name: str) -> list[GameItem]:
        """Scrape the console page on the active source and return disc-specific entries
        whose base name (with the disc suffix stripped) matches *base_name*.

        Used by the requeue methods to expand multi-disc parent folders into
        individual per-disc queue items.
        """
        console_url = self._active_base_url + quote(console_name, safe="") + "/"
        all_games = self.scraper.scrape_links(console_url)
        variants: list[GameItem] = []
        for g in all_games:
            name: str = g["name"]  # e.g. "Resident Evil 2 (USA) (Disc 1).zip"
            folder_name = strip_extension(name)
            if folder_name == name:
                continue  # no recognized extension — skip
            disc_base = DISC_REGEX.sub("", folder_name).strip()
            if disc_base == base_name and DISC_REGEX.search(folder_name):
                variants.append(g)  # type: ignore[arg-type]
        return variants

    def _queue_disc_variants(
        self,
        console_name: str,
        game_dir: Path,
        status: str,
        library: Path,
        current_queue: list[QueueItem],
        existing_paths: set[str],
        include_status_label: bool = False,
    ) -> int:
        """Expand a multi-disc parent *game_dir* into individual disc queue items.

        Returns the number of items added.  Mutates *current_queue* and
        *existing_paths* in place.
        """
        variants = self._find_disc_variants(console_name, game_dir.name)
        if not variants:
            return 0

        added = 0
        console_url = self._active_base_url + quote(console_name, safe="") + "/"
        for g in variants:
            disc_folder = strip_extension(g["name"])
            disc_dest = library / console_name / game_dir.name / disc_folder
            if str(disc_dest) in existing_paths:
                continue
            self._lib_status.remove(disc_dest)
            disc_url = urljoin(console_url, g["url_part"])
            game_label = g["name"]
            if include_status_label:
                plain = "corrupted" if status == "corrupted" else "incomplete"
                game_label += f" ({plain})"
            current_queue.append(self._make_queue_item(
                console_name, game_label, disc_url, str(disc_dest), g.get("size_str", "N/A"),
            ))
            existing_paths.add(str(disc_dest))
            added += 1

        # Clean up the empty parent folder now that disc items are queued
        try:
            if game_dir.exists() and not any(game_dir.iterdir()):
                game_dir.rmdir()
        except OSError:
            pass

        return added

    @work(exclusive=True, thread=True)
    def requeue_failed_games(self) -> None:
        """Finds corrupted and incomplete game dirs and adds them to the queue.

        Multi-disc parent folders (e.g. ``Resident Evil 2 (USA)/`` with no disc
        subfolders) are detected automatically: the console page is scraped to
        find matching disc entries and each disc is queued individually.
        """
        library = Path(self.state.settings['library_root'])
        if not library.exists():
            self.post_message(SystemLog("Re-queue: Library path not found.", True))
            return

        targets = [
            (cn, gd, s)
            for cn, gd, s in self._walk_library_game_dirs(library, self._lib_status)
            if s != "validated"
        ]

        if not targets:
            self.post_message(SystemLog("Re-queue: No incomplete or corrupted games found. Library looks clean!"))
            return

        current_queue  = self.state.get_active_queue()
        existing_paths = {i["dest_path"] for i in current_queue}
        added = n_corrupted = n_incomplete = 0

        for console_name, game_dir, status in targets:
            if str(game_dir) in existing_paths:
                continue
            # Clear status so the download worker doesn't fast-skip on a stale
            # "validated" entry (can happen when _classify_game_dir correctly
            # returns "incomplete" for an empty dir but lib_status JSON still
            # carries the old "validated" value from a previous download).
            self._lib_status.remove(game_dir)

            # ── Multi-disc detection ────────────────────────────────────────
            # Case A: dir name has NO disc suffix → grouping folder whose disc
            #   subfolders were deleted.  Scrape to find disc zips.
            # Case B: dir name HAS a disc suffix AND status is incomplete →
            #   some sibling discs may be missing.  Scrape to find all disc
            #   variants and queue whichever ones are absent or incomplete.
            if DISC_REGEX.search(game_dir.name) is None:
                disc_added = self._queue_disc_variants(
                    console_name, game_dir, status, library,
                    current_queue, existing_paths, include_status_label=True,
                )
                if disc_added:
                    added += disc_added
                    if status == "corrupted":
                        n_corrupted += disc_added
                    else:
                        n_incomplete += disc_added
                    continue
                # No disc variants found — queue as a normal single-file game
            elif status == "incomplete":
                # Disc-suffixed dir is incomplete — check for missing siblings
                base_name = DISC_REGEX.sub('', game_dir.name).strip()
                parent_dir = game_dir.parent
                variants = self._find_disc_variants(console_name, base_name)
                if variants:
                    console_url = self._active_base_url + quote(console_name, safe="") + "/"
                    sibling_added = 0
                    for g in variants:
                        disc_folder = strip_extension(g["name"])
                        disc_dest = parent_dir / disc_folder
                        if str(disc_dest) in existing_paths:
                            continue
                        # Queue if the disc dir doesn't exist or isn't validated
                        disc_status = self._lib_status.get(disc_dest)
                        if disc_dest.exists() and disc_status == "validated":
                            continue
                        self._lib_status.remove(disc_dest)
                        disc_url = urljoin(console_url, g["url_part"])
                        current_queue.append(self._make_queue_item(
                            console_name, f"{g['name']} (incomplete)",
                            disc_url, str(disc_dest), g.get("size_str", "N/A"),
                        ))
                        existing_paths.add(str(disc_dest))
                        sibling_added += 1
                    if sibling_added:
                        added += sibling_added
                        n_incomplete += sibling_added
                        continue
                # Fall through to single-file queue if no variants found

            # Look up the actual remote filename from the scrape cache.
            match = self._find_source_game(console_name, game_dir.name)
            if not match:
                continue
            game_name, game_url, size_str = match
            # Store plain-text name — Rich markup must NOT be embedded in persisted JSON
            # because brackets in console/game names would inject unintended markup at render time.
            plain_status = "corrupted" if status == "corrupted" else "incomplete"
            current_queue.append(self._make_queue_item(
                console_name, f"{game_name} ({plain_status})",
                game_url, str(game_dir), size_str,
            ))
            existing_paths.add(str(game_dir))
            added += 1
            # Tally while iterating — avoids a second full pass over targets
            if status == "corrupted":
                n_corrupted += 1
            else:
                n_incomplete += 1

        if added:
            self.state.update_active_queue(current_queue, immediate=True)
            self.call_from_thread(self._refresh_queue_table)
            # Switch to the downloads pane so the user can see what was added
            self.call_from_thread(lambda: self._nav_switch("pane-downloads"))

        self.post_message(SystemLog(
            f"Re-queued [bold]{added}[/bold] game(s): "
            f"{n_corrupted} corrupted, {n_incomplete} incomplete."
        ))

    @work(exclusive=True, thread=True)
    def requeue_console_games(self, console_name: str, console_path: Path) -> None:
        """Queue every game directory under *console_path* for re-download.
        Clears any existing validated/corrupted status so the download worker
        does not fast-skip games that were previously marked validated.
        Already-queued entries are skipped to avoid duplicates.

        URL reconstruction carries the same caveat as ``requeue_failed_games``:
        URLs are built from the on-disk directory name; manually renamed directories
        will produce URLs that 404.
        """
        if not console_path.exists():
            self.post_message(SystemLog(
                f"Re-queue Console: path not found: {console_path}", True
            ))
            return

        # Walk from the library root but filter to just this console — reuses
        # the shared walker so grouping-folder / multi-disc handling is consistent.
        targets = [
            (cn, gd, s)
            for cn, gd, s in self._walk_library_game_dirs(console_path.parent, self._lib_status)
            if cn == console_name
        ]

        if not targets:
            self.post_message(SystemLog(
                f"Re-queue Console [{console_name}]: No game directories found."
            ))
            return

        current_queue  = self.state.get_active_queue()
        existing_paths = {i["dest_path"] for i in current_queue}
        added = skipped = 0

        library = Path(self.state.settings['library_root'])

        for _, game_dir, status in targets:
            if str(game_dir) in existing_paths:
                skipped += 1
                continue
            # Clear status so the download worker doesn't fast-skip validated games.
            # The game will be re-validated after a successful re-download.
            self._lib_status.remove(game_dir)

            # ── Multi-disc parent detection (same logic as requeue_failed_games)
            if DISC_REGEX.search(game_dir.name) is None:
                disc_added = self._queue_disc_variants(
                    console_name, game_dir, status, library,
                    current_queue, existing_paths,
                )
                if disc_added:
                    added += disc_added
                    continue

            match = self._find_source_game(console_name, game_dir.name)
            if not match:
                continue
            game_name, game_url, size_str = match
            current_queue.append(self._make_queue_item(
                console_name, game_name, game_url, str(game_dir), size_str,
            ))
            existing_paths.add(str(game_dir))
            added += 1

        if added:
            self.state.update_active_queue(current_queue, immediate=True)
            self.call_from_thread(self._refresh_queue_table)
            self.call_from_thread(lambda: self._nav_switch("pane-downloads"))

        self.post_message(SystemLog(
            f"Re-queue Console [{_escape_markup(console_name)}]: "
            f"queued [bold]{added}[/bold] game(s)"
            + (f", skipped {skipped} already in queue." if skipped else ".")
        ))

    # ── Global cross-console search (2A) ──────────────────────────────────────

    @work(exclusive=True, thread=True)
    def run_global_search(self, query: str) -> None:
        """Search all consoles for games matching *query*. Uses prefetch cache."""
        if not query or len(query) < 3:
            return
        self._lib_cancel.clear()

        def _show_searching():
            try:
                lbl = self.query_one("#breadcrumb", Label)
                t = Text()
                t.append("Global Search", style="#58a6ff")
                t.append("  Searching\u2026", style="italic #d29922")
                lbl.update(t)
            except Exception:
                pass
        self.call_from_thread(_show_searching)

        self.post_message(SystemLog(f"Global search: \"{_escape_markup(query)}\"…"))

        items = self.scraper.scrape_links(self._active_base_url)
        consoles = [i for i in items if i["url_part"].endswith('/')]
        if not consoles:
            self.post_message(SystemLog("Global search: no consoles found.", True))
            return

        results: list[tuple[str, GameItem]] = []
        semaphore = threading.Semaphore(_SCRAPE_CONCURRENCY)
        lock = threading.Lock()

        def _search_one(console: ConsoleItem, idx: int) -> None:
            with semaphore:
                if self._lib_cancel.is_set():
                    return
                url = urljoin(self._active_base_url, console["url_part"])
                self.post_message(LibraryProgress(
                    "Searching", console["name"].strip('/'), idx, len(consoles)
                ))
                games = self.scraper.scrape_links(url)
                for g in games:
                    # B6: Accept all downloadable file types
                    gl = g["url_part"].lower()
                    if not any(gl.endswith(ext) for ext in _DOWNLOAD_EXTS):
                        continue
                    if self._fuzzy_spans(query, g["name"]) is not None:
                        # B10: Pre-compute the full game URL using urljoin
                        # so _add_selected_to_queue doesn't double-encode.
                        g["game_url"] = urljoin(url, g["url_part"])
                        with lock:
                            results.append((console["name"].strip('/'), g))  # type: ignore[arg-type]

        with concurrent.futures.ThreadPoolExecutor(max_workers=_SCRAPE_CONCURRENCY) as ex:
            futures = [ex.submit(_search_one, c, i) for i, c in enumerate(consoles, 1)]
            for f in concurrent.futures.as_completed(futures):
                try:
                    f.result()
                except Exception:
                    pass

        # Populate game table with results
        def _show_results() -> None:
            try:
                self._show_browse_game_view(True)
                gt = self.query_one("#game-list", DataTable)
                gt.clear()
                self._all_games_data = []
                self._games_lookup = {}
                self._global_search_results = {}
                for console_name, game in results:
                    key = f"{console_name}/{game['url_part']}"
                    game_item: GameItem = game  # type: ignore[assignment]
                    self._all_games_data.append(game_item)
                    self._games_lookup[key] = game_item
                    self._global_search_results[key] = console_name
                    name_text = Text(no_wrap=True)
                    name_text.append(f"[{console_name}] ", style="dim #58a6ff")
                    spans = self._fuzzy_spans(query, game["name"])
                    if spans:
                        name_text.append_text(self._build_highlight_text(game["name"], spans))
                    else:
                        name_text.append(game["name"], style="#9aa0aa")
                    gt.add_row(Text(" "), name_text, Text("", style="dim"), game["size_str"], key=key)
                if not results:
                    gt.add_row("", Text("No matches found.", style="dim"), "", "", key="EMPTY")
                lbl = self.query_one("#breadcrumb", Label)
                t = Text()
                t.append("Global Search", style="#58a6ff")
                t.append(f"  ({len(results)} results)", style="dim #606878")
                lbl.update(t)
            except Exception as e:
                logging.debug("Global search UI update failed: %s", e)
        self.call_from_thread(_show_results)

        self.post_message(SystemLog(
            f"Global search: found [bold]{len(results)}[/bold] match(es) across {len(consoles)} consoles."
        ))


    # ── Batch queue import (2E) ───────────────────────────────────────────────

    @work(exclusive=True, thread=True)
    def run_batch_import(self, file_path: str) -> None:
        """Import game URLs or names from a text file into the download queue."""
        path = Path(file_path.strip())
        if not path.exists():
            self.post_message(SystemLog(f"Batch import: file not found: {path}", True))
            return

        try:
            lines = path.read_text(encoding="utf-8", errors="ignore").strip().splitlines()
        except OSError as e:
            self.post_message(SystemLog(f"Batch import: read error: {e}", True))
            return

        lines = [l.strip() for l in lines if l.strip() and not l.strip().startswith('#')]
        if not lines:
            self.post_message(SystemLog("Batch import: file is empty or all comments."))
            return

        library_root = Path(self.state.settings["library_root"])
        current_queue = self.state.get_active_queue()
        existing_paths = {i["dest_path"] for i in current_queue}
        added = 0

        for line in lines:
            if self._lib_cancel.is_set():
                return
            if line.startswith(("http://", "https://")):
                try:
                    parsed = urllib.parse.urlparse(line)
                    parts = [unquote(p) for p in parsed.path.strip('/').split('/') if p]
                    if len(parts) >= 3:
                        console_name = parts[-2]
                        game_zip = parts[-1]
                        game_name = strip_extension(game_zip).strip()
                        clean_base = DISC_REGEX.sub('', game_name).strip()
                        if clean_base != game_name:
                            dest_path = library_root / console_name / clean_base / game_name
                        else:
                            dest_path = library_root / console_name / game_name
                        if str(dest_path) not in existing_paths:
                            current_queue.append(self._make_queue_item(
                                console_name, game_zip, line, str(dest_path), "N/A",
                            ))
                            existing_paths.add(str(dest_path))
                            added += 1
                except Exception:
                    continue
            elif " / " in line:
                parts = line.split(" / ", 1)
                console_name = parts[0].strip()
                game_entry = parts[1].strip()
                game_name = strip_extension(game_entry)
                if game_name == game_entry:
                    # No recognized extension — look up actual filename on Myrient
                    match = self._find_source_game(console_name, game_entry)
                    if not match:
                        continue
                    game_entry, game_url, size_str = match
                    game_name = strip_extension(game_entry)
                else:
                    game_url = self._active_base_url + quote(console_name, safe="") + "/" + quote(game_entry, safe="")
                    size_str = "N/A"
                clean_base = DISC_REGEX.sub('', game_name).strip()
                if clean_base != game_name:
                    dest_path = library_root / console_name / clean_base / game_name
                else:
                    dest_path = library_root / console_name / game_name
                if str(dest_path) not in existing_paths:
                    current_queue.append(self._make_queue_item(
                        console_name, game_entry, game_url, str(dest_path), size_str,
                    ))
                    existing_paths.add(str(dest_path))
                    added += 1

        if added:
            self.state.update_active_queue(current_queue, immediate=True)
            self.call_from_thread(self._refresh_queue_table)

        self.post_message(SystemLog(
            f"Batch import: queued [bold]{added}[/bold] item(s) from {len(lines)} line(s)."
        ))

    # ── Download scheduling (2F) ─────────────────────────────────────────────

    def _schedule_download(self) -> None:
        """Schedule downloads to start at the configured time."""
        try:
            time_input = self.query_one("#input-schedule-time", Input).value.strip()
        except Exception:
            time_input = ""

        if not time_input:
            self.notify("Enter a time in HH:MM format", severity="warning")
            return

        try:
            hour, minute = map(int, time_input.split(":"))
            if not (0 <= hour <= 23 and 0 <= minute <= 59):
                raise ValueError
        except (ValueError, AttributeError):
            self.notify("Invalid time format. Use HH:MM (24h)", severity="warning")
            return

        now = datetime.datetime.now()
        target = now.replace(hour=hour, minute=minute, second=0, microsecond=0)
        if target <= now:
            target += datetime.timedelta(days=1)

        delay = (target - now).total_seconds()
        self._scheduled_time = time_input

        if self._schedule_timer is not None:
            self._schedule_timer.stop()

        def _start_at_time() -> None:
            self._scheduled_time = ""
            self._schedule_timer = None
            self.start_download_engine()
            self.notify("Scheduled download started!")

        self._schedule_timer = self.set_timer(delay, _start_at_time)
        self.notify(f"Downloads scheduled for {time_input} ({delay/3600:.1f}h from now)")
        self.post_message(SystemLog(
            f"Download engine scheduled for {time_input} ({delay/3600:.1f} hours from now)."
        ))

    @staticmethod
    def _parse_size_bytes(size_str: str) -> int:
        """Parse a human-readable size string (e.g. '524.8 MB', '1.2GiB') into bytes.
        Uses the pre-compiled SIZE_REGEX and _SIZE_MULTIPLIERS constant.

        Unit mapping: only the first character of the matched unit is used as the
        dict key ('KB'→'K', 'MiB'→'M', 'GB'→'G', etc.).  SI and IEC units both
        map to the same binary multipliers (1 KB = 1 KiB = 1024 bytes) — this is
        intentional: Myrient displays sizes with mixed conventions and the
        difference is negligible for progress display purposes.
        """
        if not size_str or size_str == "N/A":
            return 0
        match = SIZE_REGEX.search(size_str)
        if not match:
            return 0
        try:
            value    = float(match.group(1))
            unit_raw = match.group(2).upper()
            # All SI prefixes (K, M, G, T) are exactly one character — take only the first.
            unit_key = unit_raw[0]
            return int(value * _SIZE_MULTIPLIERS.get(unit_key, 1))
        except (ValueError, TypeError):
            return 0

    async def on_unmount(self) -> None:
        try:
            self.cleanup_subprocesses()
        finally:
            try:
                # Always flush config even if subprocess cleanup fails — prevents
                # losing queue state / settings on unclean shutdown.
                self.state.flush_if_dirty()
            finally:
                # Stop watchdog observer if running — must happen even if
                # flush_if_dirty() raises so the observer thread doesn't
                # outlive the app process.
                if self._watch_observer is not None:
                    try:
                        self._watch_observer.stop()
                        self._watch_observer.join(timeout=2)
                    except Exception:
                        pass
                if self._session_log_file is not None:
                    try:
                        self._session_log_file.write(
                            f"# Session ended {datetime.datetime.now().isoformat()}\n"
                        )
                        self._session_log_file.close()
                    except OSError as e:
                        logging.error("Failed to close session log: %s", e)


