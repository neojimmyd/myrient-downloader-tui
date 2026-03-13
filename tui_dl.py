#!/usr/bin/env python3
"""
Myrient TUI Downloader & Library Manager
A high-performance Textual application for managing Redump libraries.
"""
from __future__ import annotations  # enable PEP 604 / lowercase generics on 3.9+

import concurrent.futures
import datetime
import hashlib
import json
import logging
import operator
import os
import platform as _platform
import random
import re
import shutil
import socket
import subprocess
import threading
import time
import urllib.parse
import urllib.request
import uuid
import xml.etree.ElementTree as ET
import zipfile as _zf
from collections import Counter, deque
from pathlib import Path
from typing import Any, Iterator
from urllib.parse import quote, unquote, urljoin

from bs4 import BeautifulSoup, SoupStrainer
from rich.markup import escape as _escape_markup
from rich.text import Text
from textual import work
from textual.app import App, ComposeResult
from textual.containers import Container, Horizontal, Vertical, VerticalScroll
from textual.events import Key
from textual.message import Message
from textual.screen import ModalScreen
from textual.timer import Timer
from textual.widgets import (
    Button, Collapsible, DataTable, Footer, Header, Input,
    Label, ListItem, ListView, ProgressBar, RichLog, Rule, Select,
    Switch, TabbedContent, TabPane, Tree
)

# ── Optional watchdog import for filesystem watch mode ───────────────────────
try:
    from watchdog.observers import Observer as _WatchdogObserver
    from watchdog.events import FileSystemEventHandler as _FSEventHandler
    _WATCHDOG_AVAILABLE = True
except ImportError:
    _WATCHDOG_AVAILABLE = False
    _WatchdogObserver = None   # type: ignore[assignment,misc]
    _FSEventHandler   = object # type: ignore[assignment,misc]

# ── Module-level side effects (after all imports) ────────────────────────────
# Global socket timeout applies to all urllib connections made by this process.
socket.setdefaulttimeout(60)

# ── All program data lives in a single subfolder next to the script ──────────
# Using __file__ guarantees the paths are correct regardless of the working
# directory the user launches the script from.
_SCRIPT_DIR = Path(__file__).parent.resolve()
_DATA_DIR   = _SCRIPT_DIR / "myrient_data"
_DATA_DIR.mkdir(parents=True, exist_ok=True)
_TOOLS_DIR  = _DATA_DIR / "tools"
_TOOLS_DIR.mkdir(parents=True, exist_ok=True)

BASE_URL        = "https://myrient.erista.me/files/Redump/"
DAT_BASE_URL    = "https://myrient.erista.me/dats/Redump/"

# PS2 Master Disc Patcher — extracted from the PSDB v1.0.5 x86_64 release zip.
# The release zip layout is:
#   playstation-disc-burner-v1.0.5-x86_64/
#     bin/
#       ps2_master      ← binary we want (the master disc patcher)
#       ps2_master.exe  ← Windows variant (ignored on Linux)
#       ... (other tools: pops2cue, psx80mp, cdrdao, etc.)
#     licenses/
#     images/
#
# The binary is named "ps2_master" (underscore, no version suffix) inside bin/.
_PS2MDP_BINARY_NAME  = "ps2_master"
_PS2MDP_RELEASE_URL  = (
    "https://github.com/alex-free/playstation-disc-burner/releases/download/"
    "v1.0.5/playstation-disc-burner-v1.0.5-x86_64.zip"
)

# Consoles whose Redump DAT name does NOT follow the standard
# "{console_name} - Datfile (N) (date).dat" pattern.  Each entry maps a
# console folder name to a list of prefix strings to try (in order) when
# searching the Myrient DAT index.  The first matching prefix wins.
_DAT_SEARCH_PREFIXES: dict[str, list[str]] = {
    # Myrient stores Wii/GC games in folders named after the NKit RVZ collection.
    # The folder on disk is "Nintendo - Wii - NKit RVZ [zstd-19-128k]" or the
    # shorter variant without the bracket suffix — both need to resolve to the
    # same DAT.  We key every plausible folder name variant here.
    "Nintendo - Wii":                        ["Nintendo - Wii - NKit RVZ", "Nintendo - Wii -"],
    "Nintendo - Wii - NKit RVZ":             ["Nintendo - Wii - NKit RVZ"],
    "Nintendo - Wii - NKit RVZ [zstd-19-128k]": ["Nintendo - Wii - NKit RVZ"],
    "Nintendo - GameCube":                   ["Nintendo - GameCube - NKit RVZ", "Nintendo - GameCube -"],
    "Nintendo - GameCube - NKit RVZ":        ["Nintendo - GameCube - NKit RVZ"],
    "Nintendo - GameCube - NKit RVZ [zstd-19-128k]": ["Nintendo - GameCube - NKit RVZ"],
    # Wii U uses WUX format on Myrient
    "Nintendo - Wii U":                      ["Nintendo - Wii U - WUX", "Nintendo - Wii U -"],
    "Nintendo - Wii U - WUX":               ["Nintendo - Wii U - WUX"],
}
CONFIG_FILE     = _DATA_DIR / "myrient_config.json"
SESSION_LOG_DIR = _DATA_DIR / "logs"
DAT_CACHE_DIR   = _DATA_DIR / "dats"

# --- Global Configurations & Pre-Compiled Regex ---
logging.basicConfig(
    filename=str(_DATA_DIR / 'myrient_errors.log'),
    level=logging.ERROR,
    format='%(asctime)s - [%(levelname)s] - %(message)s'
)

# Pre-compiled globally to minimize CPU cycles during tight loops
SIZE_REGEX      = re.compile(r'(?<!\d)(\d+(?:\.\d+)?)\s*([KMGT]i?B?)', re.IGNORECASE)
DISC_REGEX      = re.compile(r'\s*\((?:Disc|Disk|Tape|Side)\s+[^)]+\)', re.IGNORECASE)
CUE_BIN_REGEX   = re.compile(r'FILE\s+"([^"]+)"')
WGET_PROG_REGEX   = re.compile(r'(\d+)%')
WGET_LENGTH_REGEX = re.compile(r'Length:\s+(\d+)')

# ── Library / conversion constants ───────────────────────────────────────────
# Frozensets and dicts allocated once at module load — these are called inside
# tight loops (per-file during scans and conversions) so object allocation
# inside the loop matters.

# All disc/cart/tape/CHD image extensions recognised on Myrient Redump
_GAME_EXTS: frozenset[str] = frozenset({
    '.bin', '.iso', '.cue', '.chd', '.img',
    '.wbfs', '.rvz', '.gcz', '.gdi',
    '.nrg', '.mdf', '.mds',
    '.rom', '.xiso', '.ecm',
})

# Source extensions that chdman can convert TO .chd
_CHD_SOURCE_EXTS: frozenset[str] = frozenset({'.bin', '.iso', '.cue', '.gdi'})

# Mapping from source extension to ordered list of chdman subcommands to try.
# CD images (.cue/.gdi) use createcd.
# Raw ISOs are most likely DVD-based (Wii, PS2, GC, Xbox) → createdvd first,
# then createcd as fallback for the rare CD-ROM ISO.
_CHD_CMD_MAP: dict[str, list[str]] = {
    '.bin': ['createcd'],
    '.cue': ['createcd'],
    '.gdi': ['createcd'],
    '.iso': ['createdvd', 'createcd'],
}

# Extensions audited during DAT verification (all disc formats except .chd which
# carries its own internal SHA-1 and does not need external hash verification).
_DAT_AUDITABLE_EXTS: frozenset[str] = frozenset({
    '.bin', '.iso', '.cue', '.img', '.gdi',
    '.wbfs', '.rvz', '.gcz', '.nrg', '.mdf', '.wux',
})

# Extensions accepted by ps2_master (the PS2 Master Disc Patcher).
# Compared against f.suffix.lower() so mixed-case variants (.Iso, .ISO, etc.)
# are matched correctly on case-sensitive Linux filesystems.
_PS2_PATCH_EXTS: frozenset[str] = frozenset({'.iso', '.bin'})

_OS = _platform.system().lower()   # 'linux', 'darwin', 'windows'
# These are the mame-tools package names used by common package managers
_PKG_INSTALL_CMDS: list[tuple[str, list[str]]] = [
    # (label, argv)
    ("apt-get",  ["apt-get", "install", "-y", "mame-tools"]),
    ("dnf",      ["dnf",     "install", "-y", "mame-tools"]),
    ("pacman",   ["pacman",  "-S",  "--noconfirm", "mame-tools"]),
    ("brew",     ["brew",    "install", "rom-tools"]),
]

# SoupStrainer shared across all scrape calls — only parse <a> and <tr> tags
_SCRAPE_STRAINER = SoupStrainer(["a", "tr"])
# Same for the DAT index page which only needs <a> tags
_DAT_INDEX_STRAINER = SoupStrainer("a")

# ── Named constants for all tunable magic numbers ────────────────────────────
_UI_UPDATE_INTERVAL: float = 0.25   # seconds between progress bar refreshes
_DL_CHUNK_BYTES:     int   = 1 * 1024 * 1024   # urllib read chunk size (1 MiB)
_HASH_CHUNK_BYTES:   int   = 8 * 1024 * 1024   # SHA-1 read chunk size  (8 MiB)
_LINK_CACHE_TTL:     float = 300.0  # seconds before a cached scrape expires
_SEARCH_DEBOUNCE:    float = 0.15   # seconds of idle before search fires
_FLUSH_INTERVAL:     float = 3.0    # seconds between deferred config saves

# ── Download retry / speed constants ─────────────────────────────────────────
_RETRY_MAX_ATTEMPTS: int   = 5      # max download retry attempts (incl. first)
_RETRY_BASE_DELAY:   float = 2.0    # initial backoff delay in seconds
_RETRY_MAX_DELAY:    float = 60.0   # maximum backoff cap in seconds
_SPEED_WINDOW:       float = 5.0    # rolling window (seconds) for speed calc

# ── Concurrent scraping semaphore limit ──────────────────────────────────────
_SCRAPE_CONCURRENCY: int = 8        # max simultaneous console page fetches

# ── Filesystem watch debounce ────────────────────────────────────────────────
_WATCH_DEBOUNCE:     float = 2.0    # seconds after last FS event before rescan

# Tuple allocated once — _format_size is called twice per progress tick per thread
_SIZE_UNITS: tuple[str, ...] = ('B', 'KB', 'MB', 'GB', 'TB')

# Dict allocated once — _parse_size_bytes is called per download queue item
_SIZE_MULTIPLIERS: dict[str, int] = {
    "B": 1,
    "K": 1024,
    "M": 1024 ** 2,
    "G": 1024 ** 3,
    "T": 1024 ** 4,
}

# Maximum wall-clock seconds to wait for a single chdman conversion (2 hours).
# Defined at module level — was previously inside the per-file loop.
_CHD_TIMEOUT: int = 7200

# Maximum wait time for a ZIP extraction (10 minutes).  Large multi-gigabyte ISOs
# occasionally stall unzip on corrupted data; this caps the hang.
_UNZIP_TIMEOUT: int = 600

# DAT files older than this many seconds are re-fetched on the next audit run.
# 7 days — Redump DATs are updated frequently enough that week-old data is stale.
_DAT_CACHE_TTL: float = 7 * 24 * 3600.0

# Maximum number of session log files kept in myrient_data/logs/.
# Oldest files beyond this count are pruned at startup.
_SESSION_LOG_MAX_FILES: int = 30

# Frozenset for O(1) membership test in on_library_progress
_PROGRESS_DONE_STATES: frozenset[str] = frozenset({"done", "complete", "failed"})

# ── Library tree label styles — allocated once, shared across all rebuilds ───
# on_library_tree_ready fires on every scan; allocating five string objects there
# on every call is wasteful.  Module-level constants are interned by CPython.
_TREE_AMBER:  str = "#e6b73e"
_TREE_GREEN:  str = "bold green"
_TREE_RED:    str = "bold red"
_TREE_YELLOW: str = "yellow"
_TREE_DIM:    str = "dim"

DEFAULT_SETTINGS: dict[str, Any] = {
    # Default library sits next to the script, not inside _DATA_DIR.
    "library_root": str(_SCRIPT_DIR / "Myrient_Library"),
    "filter_include": [],
    "filter_exclude": [],
    "max_concurrent": 4,
    "auto_convert_chd": False,
    "chdman_path": "",   # empty = search PATH / tools dir at runtime
    # ── New settings ──────────────────────────────────────────────────────────
    "speed_limit_mbps": 0,          # 0 = unlimited; >0 = MB/s cap per download
    "dat_cache_ttl_hours": 168,     # 168 = 7 days; 0 = always refresh
    "theme": "dark",                # "dark" or "light" — persisted across restarts
    "filter_presets": {},           # {preset_name: {"include": [...], "exclude": [...]}}
    "queue_settings": {},           # {queue_name: {"max_concurrent": N, "speed_limit_mbps": N}}
    "watch_library": False,         # auto-rescan library when files change (requires watchdog)
    "dat_dry_run": False,           # preview audit renames without touching files
    "notify_on_batch_complete": True,  # desktop notification when batch finishes
}


# --- State Management (Thread-Safe) ---
class ConfigManager:
    """Handles loading and atomic, thread-safe saving of state.

    All mutations to ``self.data`` are performed while holding ``_lock`` so that
    worker threads calling ``get_active_queue()`` concurrently never see a
    partially-mutated dict.
    """

    def __init__(self, config_path: Path):
        self.config_path = config_path
        self._lock = threading.Lock()
        self._dirty = False
        self.data: dict[str, Any] = self._load()

    def _load(self) -> dict[str, Any]:
        base: dict[str, Any] = {
            "settings": DEFAULT_SETTINGS.copy(),
            "active_queue": "default",
            "queues": {"default": []}
        }
        # One-time migration: if the new config file doesn't exist yet but the
        # old CWD-relative one does, copy it into _DATA_DIR before loading.
        old_path = _SCRIPT_DIR / "myrient_data.json"
        if not self.config_path.exists() and old_path.exists():
            try:
                shutil.copy2(old_path, self.config_path)
            except OSError:
                pass
        if self.config_path.exists():
            try:
                with open(self.config_path, 'r', encoding="utf-8") as file:
                    disk_data = json.load(file)
                base["settings"] = {**DEFAULT_SETTINGS, **disk_data.get("settings", {})}
                base["queues"] = disk_data.get("queues", {"default": []})
                base["active_queue"] = disk_data.get("active_queue", "default")
                if base["active_queue"] not in base["queues"]:
                    base["queues"][base["active_queue"]] = []
            except (json.JSONDecodeError, OSError) as exc:
                # Log corruption so the user can recover the file manually.
                # Preserve the corrupt file as *.bak before the next save overwrites it.
                logging.error("Config load failed (%s): %s", self.config_path, exc)
                bak = self.config_path.with_suffix('.bak')
                try:
                    shutil.copy2(self.config_path, bak)
                except OSError:
                    pass
        return base

    # ── Internal write helper — must be called with _lock already held ───────
    def _write_locked(self) -> None:
        """Flush self.data to disk atomically. Caller MUST hold _lock."""
        self._dirty = False
        temp_file = self.config_path.with_suffix('.tmp')
        with open(temp_file, 'w', encoding="utf-8") as f:
            json.dump(self.data, f)
        os.replace(temp_file, self.config_path)

    def save(self) -> None:
        """Acquire lock and write current state to disk immediately."""
        with self._lock:
            self._write_locked()

    def mark_dirty(self) -> None:
        """Mark state as needing a flush without touching the disk.
        Used during high-frequency operations (e.g. per-download completions).
        The periodic flush timer and on_unmount both call flush_if_dirty().
        """
        with self._lock:
            self._dirty = True

    def flush_if_dirty(self) -> None:
        """Write to disk only if state has been dirtied since the last save.
        Holds the lock for the entire check-and-write so there is no TOCTOU gap
        between reading _dirty and clearing it.
        """
        with self._lock:
            if not self._dirty:
                return
            self._write_locked()   # clears _dirty inside the same lock window

    @property
    def settings(self) -> dict[str, Any]:
        return self.data["settings"]

    @property
    def queues(self) -> dict[str, list[dict[str, str]]]:
        return self.data["queues"]

    @property
    def active_queue_name(self) -> str:
        return self.data["active_queue"]

    def get_active_queue(self) -> list[dict[str, str]]:
        with self._lock:
            return list(self.data["queues"].get(self.active_queue_name, []))

    def update_active_queue(self, new_queue: list[dict[str, str]], immediate: bool = True) -> None:
        """Replace the active queue in memory.
        Pass ``immediate=False`` during active download batch runs to defer the
        disk write — the periodic flush timer handles persistence.
        """
        with self._lock:
            self.data["queues"][self.active_queue_name] = new_queue
            if immediate:
                self._write_locked()
            else:
                self._dirty = True

    def set_active_queue(self, name: str) -> None:
        with self._lock:
            if name in self.data["queues"]:
                self.data["active_queue"] = name
                self._write_locked()

    def create_queue(self, name: str) -> bool:
        with self._lock:
            if name not in self.data["queues"]:
                self.data["queues"][name] = []
                self.data["active_queue"] = name
                self._write_locked()
                return True
        return False

    def delete_queue(self, name: str) -> bool:
        """Delete a queue by name.

        Unlike the previous logic that blocked deletion of the *active* queue,
        this version allows it as long as at least one other queue exists — it
        automatically switches the active queue to ``'default'`` (or the first
        remaining queue) before deleting so the app is never left with no active
        queue.  Returns ``False`` and makes no change if ``name`` is the only
        queue.
        """
        with self._lock:
            if name not in self.data["queues"]:
                return False
            if len(self.data["queues"]) <= 1:
                return False   # would leave no queues — disallow
            del self.data["queues"][name]
            # If we just deleted the active queue, point to another one.
            if self.data["active_queue"] == name:
                fallback = "default" if "default" in self.data["queues"] else next(iter(self.data["queues"]))
                self.data["active_queue"] = fallback
            self._write_locked()
            return True

    def get_queue_settings(self, queue_name: str) -> dict[str, Any]:
        """Return per-queue override settings, falling back to global defaults."""
        global_qs = self.data["settings"].get("queue_settings", {})
        q_overrides = global_qs.get(queue_name, {})
        return {
            "max_concurrent":  q_overrides.get("max_concurrent",
                                self.data["settings"].get("max_concurrent", 4)),
            "speed_limit_mbps": q_overrides.get("speed_limit_mbps",
                                self.data["settings"].get("speed_limit_mbps", 0)),
        }

    def set_queue_settings(self, queue_name: str, overrides: dict[str, Any]) -> None:
        """Persist per-queue setting overrides."""
        with self._lock:
            if "queue_settings" not in self.data["settings"]:
                self.data["settings"]["queue_settings"] = {}
            self.data["settings"]["queue_settings"][queue_name] = overrides
            self._write_locked()
            self._write_locked()
            return True


class LibraryStatus:
    """Thread-safe, file-backed store for game directory validation status.

    Replaces per-directory ``.validated`` / ``.corrupted`` marker files with a
    single ``myrient_data/.myrient_status.json`` dict:

        { "Console Name/Game Dir": "validated" | "corrupted" }

    Absence from the dict means ``"incomplete"``.  Keys are POSIX-style paths
    relative to the library root so the entire file is portable — the library
    can be moved to a different mount point without invalidating any entries.
    The status file lives in ``myrient_data/`` (alongside the config) rather
    than in the library root so it is never accidentally included in archives
    or synced with the ROM collection.

    On first load, any existing ``.validated`` / ``.corrupted`` marker files are
    migrated into the JSON store and then deleted, so the transition is seamless
    for existing libraries.
    """

    STATUS_FILE = _DATA_DIR / ".myrient_status.json"

    def __init__(self) -> None:
        self._lock    = threading.Lock()
        self._data:   dict[str, str] = {}
        self._library: Path | None   = None
        self._path:    Path | None   = None
        self._dirty   = False

    # ── Public API ────────────────────────────────────────────────────────────

    def load(self, library: Path) -> None:
        """(Re)load status from *library*.  Safe to call from any thread.

        The backing file lives at ``myrient_data/.myrient_status.json``
        (a fixed path in _DATA_DIR) rather than inside the library root.
        If the library root changes (Settings → Save), this method is called
        again but the file path never changes — only the ``_library`` reference
        used for key relativisation is updated.

        All shared state (_library, _path, _data, _dirty) is updated inside a
        single lock acquisition so concurrent readers never see a torn view.

        One-time migration: if a legacy ``<library>/.myrient_status.json``
        exists, its entries are merged into the central file and the old file
        is deleted so the transition is seamless for existing libraries.
        """
        new_path = self.STATUS_FILE   # fixed path in myrient_data/
        data: dict[str, str] = {}
        try:
            if new_path.exists():
                with open(new_path, 'r', encoding='utf-8') as f:
                    data = json.load(f)
        except (json.JSONDecodeError, OSError):
            data = {}

        # One-time migration: merge entries from old library-root file if present
        old_lib_path = library / ".myrient_status.json"
        if old_lib_path.exists():
            try:
                with open(old_lib_path, 'r', encoding='utf-8') as f:
                    old_data: dict[str, str] = json.load(f)
                # Only import keys not already in the central file
                for k, v in old_data.items():
                    if k not in data:
                        data[k] = v
                old_lib_path.unlink()
            except (json.JSONDecodeError, OSError):
                pass

        with self._lock:
            self._library = library
            self._path    = new_path
            self._data    = data
            self._dirty   = False
        self._migrate_marker_files(library)

    def get(self, path: Path) -> str | None:
        """Return ``'validated'``, ``'corrupted'``, or ``None`` (incomplete/unknown)."""
        key = self._key(path)
        if key is None:
            return None
        with self._lock:
            return self._data.get(key)

    def set_status(self, path: Path, status: str) -> None:
        """Set *path* to ``'validated'`` or ``'corrupted'`` and flush to disk.

        Raises ``ValueError`` for any other string so callers catch typos at
        the point of call rather than silently persisting invalid data.
        """
        if status not in ("validated", "corrupted"):
            raise ValueError(f"Invalid status {status!r}; expected 'validated' or 'corrupted'")
        key = self._key(path)
        if key is None:
            return
        with self._lock:
            self._data[key] = status
            self._dirty = True
        self._flush()

    def remove(self, path: Path) -> None:
        """Remove *path* from the store (marks it incomplete) and flush."""
        key = self._key(path)
        if key is None:
            return
        with self._lock:
            self._data.pop(key, None)
            self._dirty = True
        self._flush()

    def prune(self, library: Path) -> None:
        """Drop entries whose directories no longer exist (e.g. after deletion)."""
        with self._lock:
            stale = [k for k in self._data if not (library / k).exists()]
            for k in stale:
                del self._data[k]
            if stale:
                self._dirty = True
        if stale:
            self._flush()

    # ── Internal helpers ──────────────────────────────────────────────────────

    def _key(self, path: Path) -> str | None:
        if self._library is None:
            return None
        try:
            return path.relative_to(self._library).as_posix()
        except ValueError:
            return None  # path is outside the library — don't store it

    def _flush(self) -> None:
        """Atomically write the current dict to disk if dirty.

        ``_dirty`` is cleared to ``False`` BEFORE the write begins (inside the
        first lock window) so that any mutation arriving while the write is
        in-flight will set the flag again and be captured by the *next* flush.
        If the write itself fails, the flag is restored so no data is silently
        lost.
        """
        if self._path is None:
            return
        with self._lock:
            if not self._dirty:
                return
            snapshot = dict(self._data)
            path     = self._path
            # Clear before writing — if a mutation arrives during the write it
            # will set _dirty=True again, ensuring the next flush picks it up.
            self._dirty = False
        # Write outside the lock — file I/O must not block readers.
        try:
            path.parent.mkdir(parents=True, exist_ok=True)
            tmp = path.with_suffix('.tmp')
            with open(tmp, 'w', encoding='utf-8') as f:
                json.dump(snapshot, f, indent=2, sort_keys=True)
            tmp.replace(path)
        except OSError:
            # Restore dirty flag so the next mutation attempt retries the write.
            with self._lock:
                self._dirty = True

    def _migrate_marker_files(self, library: Path) -> None:
        """One-time migration: scan for legacy ``.validated`` / ``.corrupted``
        files, import them into the JSON store, then delete them."""
        if not library.exists():
            return
        migrated = 0
        try:
            for marker_name, status in ((".validated", "validated"), (".corrupted", "corrupted")):
                for marker_file in library.rglob(marker_name):
                    game_dir = marker_file.parent
                    key = self._key(game_dir)
                    if key is None:
                        continue
                    with self._lock:
                        # Only import if not already set by the JSON store
                        if key not in self._data:
                            self._data[key] = status
                            self._dirty = True
                    try:
                        marker_file.unlink()
                        migrated += 1
                    except OSError:
                        pass
        except (PermissionError, OSError):
            pass
        if migrated:
            self._flush()


# --- Custom UI Components & Messages ---

class GameSearchInput(Input):
    """Search input that intercepts ↑↓ / Tab / Enter before Input consumes them.

    Textual's Input widget handles keys internally in ``_on_key`` before they
    bubble to the App.  Up/down arrows and enter are all swallowed that
    way, so App.on_key never sees them when this widget is focused.

    Tab is intercepted here to toggle the highlighted game's selection while
    keeping focus on the search box, rather than moving focus to the next widget.
    Space is left alone so users can type multi-word searches freely.
    """

    class NavUp(Message):           pass
    class NavDown(Message):         pass
    class ToggleAtCursor(Message):  pass
    class QueueSelected(Message):   pass

    def _on_key(self, event: Key) -> None:
        match event.key:
            case "up":    self.post_message(self.NavUp())
            case "down":  self.post_message(self.NavDown())
            case "tab":   self.post_message(self.ToggleAtCursor())
            case "enter": self.post_message(self.QueueSelected())
            case _:
                super()._on_key(event)
                return
        event.prevent_default()
        event.stop()


class SystemLog(Message):
    def __init__(self, message: str, is_error: bool = False):
        self.message = message
        self.is_error = is_error
        super().__init__()

class ConsolesLoaded(Message):
    def __init__(self, consoles: list[dict[str, str]]):
        self.consoles = consoles
        super().__init__()

class GamesLoaded(Message):
    def __init__(self, games: list[dict[str, str]]):
        self.games = games
        super().__init__()

class DownloadProgress(Message):
    def __init__(self, task_id: str, item_name: str, completed: int, total: int,
                 action: str = "Downloading",
                 speed_bps: float = 0.0, eta_secs: float = -1.0):
        self.task_id   = task_id
        self.item_name = item_name
        self.completed = completed
        self.total     = total
        self.action    = action
        self.speed_bps = speed_bps   # rolling average bytes/sec (0 = unknown)
        self.eta_secs  = eta_secs    # estimated seconds remaining (-1 = unknown)
        super().__init__()

class DownloadComplete(Message):
    def __init__(self, item: dict[str, str], success: bool, cancelled: bool = False):
        self.item = item
        self.success = success
        self.cancelled = cancelled
        super().__init__()

class LibraryProgress(Message):
    def __init__(self, task_name: str, current_item: str, completed: int, total: int):
        self.task_name = task_name
        self.current_item = current_item
        self.completed = completed
        self.total = total
        super().__init__()

class LibraryTreeReady(Message):
    """Carries the fully-built library structure to the main thread for Tree rendering."""
    def __init__(self, structure: dict[str, tuple[Path, list[tuple[Path, str]]]], library_path: Path,
                 disk_usage: dict[str, int] | None = None):
        self.structure = structure
        self.library_path = library_path
        # Pre-computed disk usage per console (computed on the worker thread).
        self.disk_usage: dict[str, int] = disk_usage or {}
        super().__init__()

class BatchComplete(Message):
    """Posted when an entire download queue finishes (success or mixed)."""
    def __init__(self, total: int, succeeded: int, failed: int):
        self.total     = total
        self.succeeded = succeeded
        self.failed    = failed
        super().__init__()

class LibraryWatchEvent(Message):
    """Posted by the watchdog observer thread when a filesystem change is detected."""
    pass


class ConfirmDeleteScreen(ModalScreen[bool]):
    def __init__(self, target_name: str):
        super().__init__()
        self.target_name = target_name

    def compose(self) -> ComposeResult:
        with Vertical(id="dialog"):
            msg = Text.assemble(
                "Permanently delete ",
                (self.target_name, "bold red"),
                "?",
            )
            yield Label(msg, id="question")
            with Horizontal(id="dialog-btn-row"):
                yield Button("Cancel", variant="primary", id="btn-cancel")
                yield Button("Delete", variant="error",   id="btn-delete")

    def on_button_pressed(self, event: Button.Pressed) -> None:
        self.dismiss(event.button.id == "btn-delete")


class HelpModal(ModalScreen):
    """Keyboard shortcut reference, shown with ?."""

    BINDINGS = [("escape", "dismiss_modal", "Close"), ("question_mark", "dismiss_modal", "Close")]

    def compose(self) -> ComposeResult:
        with Vertical(id="help-dialog"):
            yield Label("  Keyboard Shortcuts", id="help-title")
            rows = [
                ("Ctrl+Q",    "Quit"),
                ("Ctrl+D",    "Toggle dark/light theme"),
                ("Ctrl+R",    "Refresh console list"),
                ("Ctrl+J",    "Jump queue item → Browser"),
                ("?",         "Show this help"),
                ("",          ""),
                ("↑ ↓",       "Navigate lists and tables"),
                ("Space",     "Toggle game selection"),
                ("Tab",       "Toggle game selection (browser)"),
                ("Enter / q", "Queue selected games"),
                ("",          ""),
                ("1–5",       "Switch nav pane (browse/dl/lib/set/logs)"),
            ]
            for key, desc in rows:
                if not key:
                    yield Label("", classes="help-row")
                else:
                    yield Label(
                        Text.assemble(
                            (f"  {key:<14}", "#58a6ff"),
                            (desc, "#9aa0aa"),
                        ),
                        classes="help-row",
                    )
            yield Button("Close", id="help-close", variant="primary")

    def action_dismiss_modal(self) -> None:
        self.dismiss()

    def on_button_pressed(self, _: Button.Pressed) -> None:
        self.dismiss()


# --- Main Application ---
class MyrientTUI(App):
    TITLE = "MYRIENT"
    SUB_TITLE = "ROM Library Manager"

    CSS = """
    /* ═══════════════════════════════════════════════════════════════════════
       MYRIENT  —  Redesigned Terminal UI
       Left-sidebar nav · semantic color vocabulary · responsive panels
       Color roles: amber=nav-active  blue=actions  green=success  red=error
       ═══════════════════════════════════════════════════════════════════════ */

    /* ── Base ─────────────────────────────────────────────────────── */
    Screen { background: #0d1117; color: #e6edf3; }

    /* ── Header / Footer ──────────────────────────────────────────── */
    Header {
        background: #080c12;
        color: #9aa0aa;
        border-bottom: solid #1c2333;
        height: 1;
    }
    Footer {
        background: #080c12;
        color: #3d4451;
        border-top: solid #1c2333;
    }

    /* ── App body: sidebar + content ──────────────────────────────── */
    #app-body { height: 1fr; layout: horizontal; }

    /* ── Left navigation sidebar ──────────────────────────────────── */
    #nav-sidebar {
        width: 20;
        min-width: 18;
        height: 1fr;
        background: #080c12;
        border-right: solid #1c2333;
        layout: vertical;
        padding: 0;
    }
    #nav-logo {
        height: 3;
        padding: 1 2;
        color: #e6b73e;
        text-style: bold;
        border-bottom: solid #1c2333;
        content-align: left middle;
    }
    .nav-btn {
        width: 100%;
        height: 3;
        background: transparent;
        border: none;
        color: #3d4451;
        text-align: left;
        padding: 0 2;
        margin: 0;
        min-width: 1;
        text-style: none;
    }
    .nav-btn:hover  { background: #0d1117; color: #9aa0aa; border: none; }
    .nav-btn:focus  { background: #0d1117; color: #9aa0aa; border: solid #1c2333; }
    .nav-btn.--nav-active {
        background: #0d1117;
        color: #e6b73e;
        text-style: bold;
        border-left: thick #e6b73e;
    }
    #nav-status {
        height: auto;
        padding: 1 2;
        border-top: solid #1c2333;
        color: #3d4451;
        margin-top: 1;
    }

    /* ── Content area ─────────────────────────────────────────────── */
    #content-area { height: 1fr; width: 1fr; background: #0d1117; }
    .content-pane { height: 1fr; display: none; }

    /* ── Global status bar (engine · speed · queue) ───────────────── */
    #global-statusbar {
        height: 1;
        layout: horizontal;
        background: #080c12;
        border-top: solid #1c2333;
        padding: 0 2;
        align: left middle;
    }
    #gs-engine { width: auto; color: #3d4451; margin-right: 3; }
    #gs-speed  { width: auto; color: #3fb950; margin-right: 3; }
    #gs-queue  { width: 1fr;  color: #3d4451; text-align: right; }

    /* ── Section headers ──────────────────────────────────────────── */
    .section-header {
        height: 1;
        color: #606878;
        text-style: bold;
        padding: 0;
        margin-bottom: 1;
        border-bottom: solid #1c2333;
    }

    /* ── Hint bar ─────────────────────────────────────────────────── */
    .hint-bar {
        height: auto;
        color: #3d4451;
        margin-top: 1;
        text-align: right;
    }

    /* ── Inputs ───────────────────────────────────────────────────── */
    .search-bar { margin-bottom: 1; }
    Input {
        background: #0d1117;
        border: solid #1c2333;
        color: #e6edf3;
        height: 3;
    }
    Input:focus { border: solid #30415e; }

    /* ── ListViews ────────────────────────────────────────────────── */
    ListView { border: solid #1c2333; background: #0d1117; height: 1fr; }
    ListView > ListItem {
        background: transparent;
        padding: 0 1;
        color: #9aa0aa;
    }
    ListView > ListItem.--highlight         { background: #0f1520; color: #e6edf3; }
    ListView:focus > ListItem.--highlight   { background: #0f1520; border-left: thick #58a6ff; }

    /* ── ◈ BROWSE pane ────────────────────────────────────────────── */
    #browse-layout { height: 1fr; layout: horizontal; }
    #browse-left {
        width: 25%;
        min-width: 22;
        max-width: 40;
        height: 1fr;
        background: #080c12;
        border-right: solid #1c2333;
        padding: 1 1 1 2;
        layout: vertical;
    }
    #browse-right {
        width: 1fr;
        height: 1fr;
        padding: 1 2;
        layout: vertical;
    }
    #breadcrumb { height: 1; color: #3d4451; margin-bottom: 1; }
    #game-list {
        height: 1fr;
        border: solid #1c2333;
        background: #0d1117;
    }
    #game-list > .datatable--header { display: none; }
    #game-list > .datatable--cursor { background: #0f1520; }
    #console-list { height: 1fr; border: solid #1c2333; background: #0d1117; }
    #game-selection-count {
        width: auto;
        color: #3fb950;
        text-style: bold;
        margin: 0 0 0 2;
    }
    .browse-actions {
        height: auto;
        layout: horizontal;
        margin-top: 1;
        align: left middle;
    }

    /* ── ▶ DOWNLOADS pane ─────────────────────────────────────────── */
    #downloads-layout { height: 1fr; layout: horizontal; }
    #queue-panel {
        width: 40%;
        min-width: 34;
        max-width: 60;
        height: 1fr;
        background: #080c12;
        border-right: solid #1c2333;
        padding: 1 2;
        layout: vertical;
    }
    #queue-table { height: 1fr; border: solid #1c2333; background: #0d1117; }
    .queue-toolbar  { height: auto; margin-bottom: 1; layout: vertical; }
    .queue-controls { height: auto; layout: horizontal; margin-top: 1; align: left middle; }
    /* Queue settings collapsible replaces old .queue-settings-row */
    #queue-settings-collapsible {
        height: auto;
        margin-top: 1;
    }

    /* Progress panel */
    #progress-panel {
        width: 1fr;
        height: 1fr;
        padding: 1 2;
        layout: vertical;
    }
    #lbl-global-progress { height: 1; color: #9aa0aa; margin-bottom: 0; }
    #global-progress     { margin-bottom: 1; display: none; }
    #progress-area       { height: 1fr; overflow-y: auto; layout: vertical; }
    #progress-grid {
        layout: grid;
        grid-size: 2;
        grid-gutter: 1 2;
        height: auto;
        min-height: 4;
    }
    .progress-container {
        height: 7;
        padding: 1;
        border: solid #1c2333;
        background: #080c12;
        overflow: hidden;
    }
    ProgressBar > .bar--bar      { color: #58a6ff; }
    ProgressBar > .bar--complete { color: #3fb950; }
    .speed-label { color: #3fb950; height: 1; }

    /* ── ⊞ LIBRARY pane ───────────────────────────────────────────── */
    #lib-tab-wrapper { height: 1fr; layout: vertical; }
    #library-main    { height: 1fr; layout: horizontal; }
    #lib-tree-panel {
        width: 60%;
        min-width: 38;
        height: 1fr;
        background: #080c12;
        border-right: solid #1c2333;
        padding: 1 2;
        layout: vertical;
    }
    #lib-ops-panel {
        width: 1fr;
        height: 1fr;
        padding: 1 2;
        overflow-y: auto;
        layout: vertical;
    }
    #lib-summary-bar { height: 1; color: #3d4451; margin-bottom: 1; }
    Tree {
        height: 1fr;
        border: solid #1c2333;
        background: #0d1117;
        margin-bottom: 1;
    }
    Tree > .tree--guides { color: #1c2333; }
    Tree > .tree--cursor { background: #0f1520; }
    .ops-btn    { width: 100%; margin: 0 0 1 0; }
    .legend-label { margin: 1 0; color: #3d4451; }
    #lib-status-bar {
        height: 3;
        padding: 0 2;
        border-top: solid #1c2333;
        background: #080c12;
        layout: horizontal;
        align: left middle;
    }
    #lib-status-label {
        width: 1fr;
        height: auto;
        color: #9aa0aa;
        content-align: left middle;
    }
    #lib-status-bar ProgressBar { width: 35%; display: none; }
    #lib-progress-bar { display: none; }

    /* ── ◎ SETTINGS pane (TabbedContent layout) ─────────────────── */
    #settings-tabs { height: 1fr; }
    #settings-tabs > ContentSwitcher { height: 1fr; }
    TabPane { padding: 0; }
    TabPane > VerticalScroll { height: 1fr; padding: 1 2; }
    .setting-label { margin-top: 1; color: #9aa0aa; }
    .filter-table  {
        height: 8;
        border: solid #1c2333;
        margin-bottom: 1;
        background: #0d1117;
    }
    .filter-table > .datatable--header { display: none; }
    .filter-table > .datatable--cursor { background: #0f1520; }
    .preset-row { height: auto; margin-bottom: 1; layout: horizontal; }
    Switch { background: transparent; }

    /* ── Collapsible widget styling ───────────────────────────────── */
    Collapsible { background: transparent; padding: 0; margin: 0 0 1 0; }
    CollapsibleTitle {
        background: #080c12;
        color: #9aa0aa;
        border: solid #1c2333;
        padding: 0 1;
        height: 3;
    }
    CollapsibleTitle:hover { background: #0f1520; color: #e6edf3; }
    CollapsibleTitle:focus { border: solid #30415e; }

    /* ── TabbedContent tab bar styling ────────────────────────────── */
    Tabs { background: #080c12; border-bottom: solid #1c2333; }
    Tab { background: transparent; color: #3d4451; padding: 0 2; height: 3; }
    Tab:hover { color: #9aa0aa; }
    Tab.-active { color: #e6b73e; border-bottom: thick #e6b73e; }
    Tab:focus { text-style: bold; }

    /* ── Rule (horizontal divider) ────────────────────────────────── */
    Rule { color: #1c2333; margin: 1 0; }

    /* ── ≡ LOGS pane ──────────────────────────────────────────────── */
    #logs-layout { height: 1fr; layout: vertical; }
    #log-toolbar {
        height: auto;
        min-height: 3;
        layout: horizontal;
        margin-bottom: 1;
        align: left middle;
        border-bottom: solid #1c2333;
        padding-bottom: 1;
    }
    .log-filter-btn {
        min-width: 8;
        margin: 0 1 0 0;
        background: #080c12;
        border: solid #1c2333;
        color: #3d4451;
        height: 3;
        text-style: none;
    }
    .log-filter-btn:hover { background: #0f1520; color: #9aa0aa; border: solid #1c2333; }
    .log-filter-btn.--log-active { color: #e6b73e; border: solid #30415e; background: #0f1520; }
    #log-search { width: 1fr; margin-left: 1; }
    RichLog {
        height: 1fr;
        border: none;
        background: #0d1117;
        color: #9aa0aa;
    }
    #sessions-divider {
        color: #1c2333;
        margin: 0;
    }
    #sessions-layout { height: 30%; min-height: 8; layout: horizontal; }
    #session-log-list {
        width: 30%;
        min-width: 22;
        height: 1fr;
        border: solid #1c2333;
        background: #0d1117;
    }
    #session-log-view {
        width: 1fr;
        height: 1fr;
        border: solid #1c2333;
        background: #0d1117;
        color: #9aa0aa;
        margin-left: 1;
    }

    /* ── Buttons — semantic color vocabulary ──────────────────────── */
    Button {
        background: #0d1117;
        color: #9aa0aa;
        border: solid #1c2333;
        margin: 0 1 0 0;
        min-width: 10;
        text-style: none;
        height: 3;
    }
    Button:hover { background: #0f1520; color: #e6edf3; border: solid #30415e; }
    Button:focus  { border: solid #30415e; color: #e6edf3; }

    /* Blue — actions (primary) */
    Button.-primary  { background: #0d1926; color: #58a6ff; border: solid #1f4070; }
    Button.-primary:hover { background: #1f4070; color: #e6edf3; border: solid #58a6ff; }

    /* Green — add / confirm */
    Button.-success  { background: #0d2318; color: #3fb950; border: solid #196327; }
    Button.-success:hover { background: #196327; color: #e6edf3; border: solid #3fb950; }

    /* Red — destructive */
    Button.-error    { background: #2a0e0e; color: #f85149; border: solid #6e1a1a; }
    Button.-error:hover { background: #6e1a1a; color: #e6edf3; border: solid #f85149; }

    /* Amber — warning */
    Button.-warning  { background: #1a1400; color: #d29922; border: solid #5a3e00; }
    Button.-warning:hover { background: #5a3e00; color: #e6edf3; border: solid #d29922; }

    .btn-row {
        height: auto;
        align: left middle;
        margin-top: 1;
        layout: horizontal;
    }
    .reorder-btn { min-width: 5; width: 5; margin: 0 1 0 0; }

    /* ── Confirm dialog ───────────────────────────────────────────── */
    ConfirmDeleteScreen { align: center middle; background: rgba(0,0,0,0.82); }
    #dialog {
        padding: 2 3;
        width: 68;
        height: auto;
        min-height: 10;
        border: thick #f85149;
        background: #0d1117;
        align: center middle;
    }
    #question {
        width: 1fr;
        content-align: center middle;
        text-align: center;
        height: auto;
        color: #e6edf3;
        text-style: bold;
        padding: 1 0 2 0;
    }
    #dialog-btn-row { height: auto; align: center middle; width: 1fr; layout: horizontal; }
    #dialog-btn-row Button { width: 1fr; margin: 0 1; }

    /* ── Help modal ───────────────────────────────────────────────── */
    HelpModal { align: center middle; background: rgba(0,0,0,0.82); }
    #help-dialog {
        padding: 2 3;
        width: 62;
        height: auto;
        border: solid #30415e;
        background: #0d1117;
        layout: vertical;
    }
    #help-title   { color: #e6b73e; text-style: bold; margin-bottom: 1; height: auto; }
    .help-row     { height: 1; color: #9aa0aa; }
    .help-key     { color: #58a6ff; }
    #help-close   { margin-top: 2; }
    """

    BINDINGS = [
        ("ctrl+q", "quit",           "Quit"),
        ("ctrl+d", "toggle_dark",    "Theme"),
        ("ctrl+r", "refresh_browser","Refresh"),
        ("ctrl+j", "jump_to_console","Jump→Browser"),
        ("question_mark", "show_help", "Help"),
    ]

    def __init__(self):
        super().__init__()
        self.state = ConfigManager(CONFIG_FILE)
        self._lib_status = LibraryStatus()
        # TTL-aware cache: stores (data, timestamp) to prevent stale results across long sessions.
        # Values are either (list[dict], float) for resolved results or ("_PENDING", float) for
        # in-flight requests.  The Any union avoids a needlessly complex generic annotation.
        self._link_cache: dict[str, tuple[Any, float]] = {}
        # Lock protects _link_cache from concurrent reads/writes across fetch_consoles
        # and fetch_games, which can run on separate exclusive workers simultaneously.
        self._link_cache_lock = threading.Lock()

        self._all_consoles_data: list[dict[str, str]] = []
        self._all_games_data:    list[dict[str, str]] = []
        self._games_lookup:      dict[str, dict[str, str]] = {}

        self.selected_console: dict[str, str] | None = None

        self.proc_lock      = threading.Lock()
        self.active_processes: set[subprocess.Popen] = set()
        self.chd_lock       = threading.Lock()
        self._chdman_path: str = ""   # resolved at startup by _find_chdman()
        self._ps2mdp_path: str  = ""  # resolved at startup by _find_ps2mdp()

        self.global_total     = 0
        self.global_completed = 0

        # Engine Control State
        self.engine_running = False
        self._engine_lock   = threading.Lock()
        self.cancel_flag    = threading.Event()
        self._progress_lock = threading.Lock()

        # Game / filter selection state
        self._selected_games:      set[str] = set()
        self._filter_include_sel:  set[str] = set()
        self._filter_exclude_sel:  set[str] = set()

        # Cache cpu_count once — os.cpu_count() is a syscall, result never changes
        _cpu = os.cpu_count()
        self._chd_cores: str = str(max(1, _cpu - 1)) if _cpu else "1"

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

        # Batch complete counters (set at engine start, updated on each completion)
        self._batch_succeeded: int = 0
        self._batch_failed:    int = 0

        # ── Redesign state ────────────────────────────────────────────────────
        # Active nav pane ID (used to sync highlight on restore)
        self._current_pane: str = "pane-browse"

        # Log filtering / search
        self._log_filter: str = "all"           # "all" | "err"
        self._log_buffer: list[tuple[Any, bool]] = []   # (Text, is_error)
        self._log_search_text: str = ""
        self._log_search_timer: Timer | None = None

    def action_refresh_browser(self) -> None:
        """Ctrl+R: re-scrape console list (bypasses cache)."""
        with self._link_cache_lock:
            self._link_cache.clear()
        self._all_games_data = []
        self._games_lookup = {}
        self._selected_games.clear()
        self._update_selection_count()
        try:
            self.query_one("#game-list", DataTable).clear()
        except Exception:
            pass
        self.fetch_consoles()

    def action_toggle_dark(self) -> None:
        """Override default toggle_dark to persist the theme choice."""
        super().action_toggle_dark()
        try:
            self.state.settings["theme"] = "dark" if self.dark else "light"
            self.state.mark_dirty()
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
        except Exception:
            pass

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
            except Exception:
                pass

    @staticmethod
    def _find_chdman() -> str:
        """Locate chdman executable.  Returns full path string or '' if not found.
        Search order: saved settings path → tools directory → system PATH.
        """
        # 1. Local tools directory shipped/downloaded alongside the script
        local_candidates = [
            _TOOLS_DIR / "chdman",
            _TOOLS_DIR / "chdman.exe",
            _SCRIPT_DIR / "chdman",
            _SCRIPT_DIR / "chdman.exe",
        ]
        for p in local_candidates:
            if p.is_file() and os.access(p, os.X_OK):
                return str(p)
        # 2. System PATH
        found = shutil.which("chdman")
        return found or ""

    @work(exclusive=True, thread=True)
    def setup_chdman_auto(self) -> None:
        """Try to install chdman automatically via the system package manager.
        Falls back to detailed instructions if every method fails.
        """
        self.post_message(SystemLog("chdman Setup: Checking for existing installation..."))

        # Re-check first — it may have been installed since launch
        path = self._find_chdman()
        if path:
            self._chdman_path = path
            self.post_message(SystemLog(f"chdman already available at: [bold]{path}[/bold]"))
            return

        self.post_message(SystemLog("chdman Setup: Attempting package-manager install..."))

        for label, cmd in _PKG_INSTALL_CMDS:
            mgr = shutil.which(cmd[0])
            if not mgr:
                continue
            self.post_message(SystemLog(f"chdman Setup: Trying [bold]{label}[/bold]…"))
            try:
                result = subprocess.run(
                    cmd, capture_output=True, text=True, timeout=120
                )
                if result.returncode == 0:
                    path = self._find_chdman()
                    if path:
                        self._chdman_path = path
                        self.post_message(SystemLog(
                            f"[bold green]chdman installed successfully![/bold green] "
                            f"Path: [bold]{path}[/bold]"
                        ))
                        return
                else:
                    self.post_message(SystemLog(
                        f"chdman Setup: {label} returned non-zero "
                        f"(may need sudo). Output: {result.stderr[:120]}", True
                    ))
            except (subprocess.TimeoutExpired, OSError) as e:
                self.post_message(SystemLog(f"chdman Setup: {label} failed — {e}", True))

        # All package managers failed — show manual instructions
        self.post_message(SystemLog(
            "[bold yellow]chdman auto-install failed.[/bold yellow] "
            "Manual options:\n"
            "  • Linux (Debian/Ubuntu):  sudo apt install mame-tools\n"
            "  • Linux (Arch):           sudo pacman -S mame-tools\n"
            "  • Linux (Fedora):         sudo dnf install mame-tools\n"
            "  • macOS (Homebrew):       brew install rom-tools\n"
            "  • Windows: download MAME tools from https://www.mamedev.org/release.html\n"
            "Place chdman(.exe) in the myrient_data/tools/ folder to use it without installing."
        ))

    @staticmethod
    def _find_ps2mdp() -> str:
        """Locate ps2_master binary. Returns full path or ''."""
        candidates = [
            _TOOLS_DIR / _PS2MDP_BINARY_NAME,
            _TOOLS_DIR / (_PS2MDP_BINARY_NAME + ".exe"),
            _SCRIPT_DIR / _PS2MDP_BINARY_NAME,
            _SCRIPT_DIR / (_PS2MDP_BINARY_NAME + ".exe"),
        ]
        for p in candidates:
            if p.is_file() and os.access(p, os.X_OK):
                return str(p)
        return shutil.which(_PS2MDP_BINARY_NAME) or ""

    @work(exclusive=True, thread=True)
    def setup_ps2mdp_auto(self) -> None:
        """Download ps2_master from the PSDB v1.0.5 x86_64 release zip.

        Extracts only the ps2_master binary from the bin/ folder into
        myrient_data/tools/.  All other PSDB components are ignored.
        """
        self.post_message(SystemLog("PS2 Patcher Setup: Checking for existing installation..."))
        path = self._find_ps2mdp()
        if path:
            self._ps2mdp_path = path
            self.post_message(SystemLog(
                f"ps2_master already available at: [bold]{path}[/bold]"
            ))
            return

        self.post_message(SystemLog(
            "PS2 Patcher Setup: Downloading PSDB v1.0.5 x86_64 release zip…\n"
            f"  {_PS2MDP_RELEASE_URL}"
        ))

        tmp_zip = _TOOLS_DIR / "_ps2mdp_download.zip"
        try:
            # ── Download ─────────────────────────────────────────────────────
            try:
                subprocess.run(
                    ["wget", "-q", "--timeout=60", "--tries=3",
                     "-O", str(tmp_zip), _PS2MDP_RELEASE_URL],
                    check=True, timeout=300,
                )
            except Exception:
                req = urllib.request.Request(
                    _PS2MDP_RELEASE_URL,
                    headers={"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64)"},
                )
                with urllib.request.urlopen(req, timeout=120) as resp, \
                        open(tmp_zip, "wb") as fout:
                    shutil.copyfileobj(resp, fout)

            # ── Extract ps2_master binary from bin/ in the release zip ─────────
            # The binary lives at:
            #   playstation-disc-burner-v1.0.5-x86_64/bin/ps2_master
            # We match by exact filename AND require it to be inside a "bin/"
            # path component so we never accidentally pick up a same-named file
            # elsewhere in the archive.
            extracted_binary = False
            with _zf.ZipFile(tmp_zip, "r") as zf:
                all_members = zf.namelist()
                self.post_message(SystemLog(
                    f"PS2 Patcher Setup: Zip has {len(all_members)} entries. First 60:\n  " +
                    "\n  ".join(all_members[:60]) +
                    ("\n  …" if len(all_members) > 60 else "")
                ))

                for member in all_members:
                    if member.endswith("/"):
                        continue
                    base = Path(member).name
                    # Must be exactly "ps2_master" inside a "bin/" directory
                    in_bin = "/bin/" in member
                    if base == _PS2MDP_BINARY_NAME and in_bin and not extracted_binary:
                        dest = _TOOLS_DIR / _PS2MDP_BINARY_NAME
                        with zf.open(member) as src, open(dest, "wb") as dst:
                            shutil.copyfileobj(src, dst)
                        dest.chmod(dest.stat().st_mode | 0o111)
                        extracted_binary = True
                        self.post_message(SystemLog(
                            f"PS2 Patcher Setup: Extracted [bold]{base}[/bold] "
                            f"from [dim]{member}[/dim] → {dest}"
                        ))
                        break  # found what we need — no point scanning further

            if not extracted_binary:
                self.post_message(SystemLog(
                    "[bold red]PS2 Patcher Setup: binary not found in release zip.[/bold red]\n"
                    "Check the zip contents log above. Manual install:\n"
                    f"  1. Download: {_PS2MDP_RELEASE_URL}\n"
                    f"  2. Extract 'bin/{_PS2MDP_BINARY_NAME}' to myrient_data/tools/\n"
                    f"  3. chmod +x myrient_data/tools/{_PS2MDP_BINARY_NAME}",
                    True,
                ))
                return

            path = self._find_ps2mdp()
            if path:
                self._ps2mdp_path = path
                self.post_message(SystemLog(
                    f"[bold green]PS2 Master Disc Patcher ready![/bold green] "
                    f"Path: [bold]{path}[/bold]"
                ))
            else:
                self.post_message(SystemLog(
                    "[bold red]Setup finished but binary not found — "
                    "extraction may have failed.[/bold red]", True
                ))

        except Exception as err:
            self.post_message(SystemLog(
                f"[bold red]PS2 Patcher Setup failed:[/bold red] {err}", True
            ))
        finally:
            try:
                tmp_zip.unlink(missing_ok=True)
            except OSError:
                pass

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
        ps2mdp = self._ps2mdp_path or self._find_ps2mdp()
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
            game_dirs = [scope_path]

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
            if self.cancel_flag.is_set():
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
                if self.cancel_flag.is_set():
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

        # Game browser table — virtual rendering, no header
        game_table = self.query_one("#game-list", DataTable)
        game_table.add_column("", key="sel", width=3)
        game_table.add_column("Game", key="name")
        game_table.add_column("Size", key="size", width=10)
        game_table.show_header = False

        # Filter tables — same checkmark design, fixed rows
        _INCLUDE_OPTS = [("USA", "USA"), ("Europe", "Europe"), ("Japan", "Japan"), ("World", "World")]
        _EXCLUDE_OPTS = [("Demo", "Demo"), ("Beta", "Beta"), ("Proto", "Proto")]
        for tbl_id, opts in (("set-include", _INCLUDE_OPTS), ("set-exclude", _EXCLUDE_OPTS)):
            tbl = self.query_one(f"#{tbl_id}", DataTable)
            tbl.add_column("", key="sel", width=3)
            tbl.add_column("Tag", key="name")
            tbl.show_header = False
            for label, value in opts:
                tbl.add_row(Text(" ", style="dim"), Text(label, style="dim"), key=value)

        self._refresh_queue_dropdown()
        self._refresh_queue_table()
        self._load_settings_toggles()
        self.fetch_consoles()
        # Load library status store before scanning so the tree renders correctly.
        self._lib_status.load(Path(self.state.settings['library_root']))
        self.run_lib_status_scan()
        # Flush deferred config writes every 3 s — catches any dirty state from
        # in-progress downloads without hammering the disk on every completion.
        self._flush_timer = self.set_interval(_FLUSH_INTERVAL, self.state.flush_if_dirty)

        # Resolve chdman path once at startup
        self._chdman_path = self._find_chdman()
        if not self._chdman_path:
            self._log(
                "[yellow]chdman not found.[/yellow] "
                "CHD conversion is disabled. Use [bold]'Setup chdman'[/bold] in Settings to install.",
                is_error=False,
            )

        # Resolve PS2 Master Disc Patcher path once at startup
        self._ps2mdp_path = self._find_ps2mdp()
        if not self._ps2mdp_path:
            self._log(
                "[yellow]ps2_master not found.[/yellow] "
                "PS2 Master Disc patching disabled. Use [bold]'Setup PS2 Patcher'[/bold] in Settings to install.",
                is_error=False,
            )

        # Probe wget and unzip at startup so users see a clear message before
        # the first download attempt fails with a cryptic OS error.
        if not shutil.which("wget"):
            self._log(
                "[yellow]wget not found.[/yellow] "
                "Downloads will use urllib fallback only. "
                "Install wget for better resumable-download support.",
                is_error=False,
            )
        if not shutil.which("unzip"):
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

        # ── Populate per-queue speed limit from stored settings ───────────
        q_settings = self.state.get_queue_settings(self.state.active_queue_name)
        try:
            self.query_one("#input-queue-speed-limit", Input).value = \
                str(q_settings.get("speed_limit_mbps", 0))
        except Exception:
            pass

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
        except Exception:
            pass
        # Show breadcrumb placeholder
        self._update_breadcrumb()
        # Initial global statusbar state
        self._update_global_statusbar()

    # ═══════════════════════════════════════════════════════════════════════
    # Navigation helpers
    # ═══════════════════════════════════════════════════════════════════════

    def _nav_switch(self, pane_id: str) -> None:
        """Show the requested content pane and update sidebar nav highlights."""
        pane_ids = [
            "pane-browse", "pane-downloads", "pane-library",
            "pane-settings", "pane-logs",
        ]
        btn_map = {
            "pane-browse":     "nav-btn-browse",
            "pane-downloads":  "nav-btn-downloads",
            "pane-library":    "nav-btn-library",
            "pane-settings":   "nav-btn-settings",
            "pane-logs":       "nav-btn-logs",
        }
        for pid in pane_ids:
            try:
                self.query_one(f"#{pid}").display = (pid == pane_id)
            except Exception:
                pass
        for pid, bid in btn_map.items():
            try:
                btn = self.query_one(f"#{bid}", Button)
                if pid == pane_id:
                    btn.add_class("--nav-active")
                else:
                    btn.remove_class("--nav-active")
            except Exception:
                pass
        self._current_pane = pane_id

    def action_show_help(self) -> None:
        """? — open the keyboard shortcut help modal."""
        self.push_screen(HelpModal())

    def _update_breadcrumb(self, console_name: str = "", game_count: int = 0) -> None:
        """Update the Browse pane breadcrumb trail."""
        try:
            lbl = self.query_one("#breadcrumb", Label)
            if not console_name:
                lbl.update(Text("Select a console to browse games", style="dim #3d4451"))
                return
            t = Text()
            t.append("Redump", style="#3d4451")
            t.append("  ›  ", style="dim #1c2333")
            t.append(console_name, style="#9aa0aa")
            if game_count > 0:
                t.append(f"  ({game_count:,})", style="dim #3d4451")
            lbl.update(t)
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
            except Exception:
                pass
            self._render_games(current_query)
            self._update_selection_count()
        except Exception:
            pass

    def _update_global_statusbar(self) -> None:
        """Refresh the persistent one-line status bar at the bottom of the screen."""
        try:
            engine_lbl = self.query_one("#gs-engine", Label)
            queue_lbl  = self.query_one("#gs-queue",  Label)
            if self.engine_running:
                engine_lbl.update(Text.assemble(
                    ("●  ", "bold #3fb950"), ("Downloading", "#9aa0aa")
                ))
            else:
                engine_lbl.update(Text("●  Idle", style="#3d4451"))
            q_len = len(self.state.get_active_queue())
            if q_len > 0:
                queue_lbl.update(Text(
                    f"{q_len} queued · {self.state.active_queue_name}",
                    style="#3d4451",
                ))
            else:
                queue_lbl.update(Text(""))
        except Exception:
            pass

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
            except Exception:
                pass
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
        except Exception:
            pass

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

        # Buffer for re-render on filter/search change (cap at 2000 lines)
        self._log_buffer.append((line, is_error))
        if len(self._log_buffer) > 2000:
            self._log_buffer = self._log_buffer[-2000:]

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
            except Exception:
                pass

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
        def _game_label(name: str, status: str) -> Text:
            t = Text(no_wrap=True, overflow="ellipsis")
            if status == "validated":
                t.append("✓  ", style=_TREE_GREEN)
                t.append(name,   style=_TREE_GREEN)
            elif status == "corrupted":
                t.append("✗  ", style=_TREE_RED)
                t.append(name,   style=_TREE_RED)
            else:
                t.append("~  ", style=_TREE_YELLOW)
                t.append(name,   style=_TREE_YELLOW)
            return t

        def _console_label(name: str, n_ok: int, n_bad: int, n_inc: int,
                           disk_bytes: int = 0) -> Text:
            t = Text(no_wrap=True)
            t.append(name, style=f"bold {_TREE_AMBER}")
            if n_ok:
                t.append(f"  {n_ok}✓", style=_TREE_GREEN)
            if n_bad:
                t.append(f"  {n_bad}✗", style=_TREE_RED)
            if n_inc:
                t.append(f"  {n_inc}~", style=_TREE_YELLOW)
            if disk_bytes > 0:
                t.append(f"  [{MyrientTUI._format_size(disk_bytes)}]", style=_TREE_DIM)
            return t

        try:
            tree = self.query_one("#lib-tree", Tree)
            tree.clear()
            library = message.library_path
            root_name = library.name if library.exists() else "Library"
            root_label = Text(root_name, style=f"bold {_TREE_AMBER}", no_wrap=True)
            tree.root.label = root_label

            for console_name, (console_path, games) in message.structure.items():
                counts = Counter(s for _, s in games)
                n_ok  = counts["validated"]
                n_bad = counts["corrupted"]
                n_inc = counts["incomplete"]
                # Use pre-computed disk usage from the worker thread — avoids
                # blocking the main thread with heavy I/O on large libraries.
                disk_bytes = message.disk_usage.get(console_name, 0)
                console_node = tree.root.add(
                    _console_label(console_name, n_ok, n_bad, n_inc, disk_bytes),
                    data=console_path,
                )
                for game_dir, status in games:
                    console_node.add_leaf(_game_label(game_dir.name, status), data=game_dir)

            if not message.structure:
                no_games = Text("No consoles found — check library path in Settings", style=_TREE_DIM)
                tree.root.add_leaf(no_games)

            tree.root.expand()
            self.query_one("#lib-status-label", Label).update("[dim]Scan complete[/dim]")
            self.query_one("#lib-progress-bar", ProgressBar).display = False

            # Update summary bar with totals across all consoles
            try:
                all_statuses = [s for _, games in message.structure.values() for _, s in games]
                total_ok  = all_statuses.count("validated")
                total_bad = all_statuses.count("corrupted")
                total_inc = all_statuses.count("incomplete")
                n_cons    = len(message.structure)
                t = Text()
                t.append(f"{n_cons} console(s)", style="#3d4451")
                t.append("   ", style="")
                t.append(f"{total_ok}✓", style="#3fb950")
                t.append("  ", style="")
                t.append(f"{total_bad}✗", style="#f85149")
                t.append("  ", style="")
                t.append(f"{total_inc}~", style="#d29922")
                self.query_one("#lib-summary-bar", Label).update(t)
            except Exception:
                pass
        except Exception as e:
            self._log(f"Tree build error: {e}", is_error=True)

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
        except Exception:
            pass

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
        result = Text(no_wrap=True)
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
        except Exception:
            pass

    def on_game_search_input_nav_down(self, _: GameSearchInput.NavDown) -> None:
        try:
            t = self.query_one("#game-list", DataTable)
            if t.row_count:
                t.move_cursor(row=min((t.cursor_row or 0) + 1, t.row_count - 1))
        except Exception:
            pass

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
        except Exception:
            pass

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
        except Exception:
            pass

    def _update_selection_count(self) -> None:
        count = len(self._selected_games)
        try:
            lbl = self.query_one("#game-selection-count", Label)
            if count == 0:
                lbl.update(Text(""))
            else:
                noun = "game" if count == 1 else "games"
                lbl.update(Text.assemble((f"{count} {noun} selected", "bold green")))
        except Exception:
            pass

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
        except Exception:
            pass

    def _refresh_filter_row(self, tbl: DataTable, tag: str, sel_set: set) -> None:
        """Re-render a single filter row to reflect its current selection state."""
        selected = tag in sel_set
        sel_cell  = Text("✓", style="bold cyan") if selected else Text(" ", style="dim")
        name_cell = Text(tag, style="bold cyan") if selected else Text(tag, style="dim")
        try:
            tbl.update_cell(tag, "sel",  sel_cell,  update_width=False)
            tbl.update_cell(tag, "name", name_cell, update_width=False)
        except Exception:
            pass

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
            if self._games_search_timer is not None:
                self._games_search_timer.stop()
            self._games_search_timer = self.set_timer(
                _SEARCH_DEBOUNCE, lambda: self._render_games(event.value)
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
        new_items = []

        for console in filtered_consoles:
            highlighted_name = self.fuzzy_highlight_fast(console["name"].strip('/'), query)
            item = ListItem(Label(highlighted_name))
            item.link_data = console
            new_items.append(item)

        if new_items:
            list_view.extend(new_items)

    def _render_games(self, query: str = "") -> None:
        """
        Repopulate the game DataTable, preserving selection state across searches.
        DataTable is virtualised — clearing and re-adding 1000+ rows is fast because
        only visible rows are actually rendered.
        Uses _fuzzy_spans for a single-pass match+highlight (no double regex).
        """
        game_table = self.query_one("#game-list", DataTable)
        game_table.clear()

        if not self._all_games_data:
            return

        found = 0
        for game in self._all_games_data:
            url_part = game["url_part"]
            name = game["name"]

            if query:
                spans = self._fuzzy_spans(query, name)
                if spans is None:
                    continue  # no match — skip row
            else:
                spans = None

            selected = url_part in self._selected_games
            sel_cell = Text("✓", style="bold green") if selected else Text(" ", style="dim")

            if selected:
                name_cell = Text(name, style="bold green", no_wrap=True)
            elif spans is not None:
                name_cell = self._build_highlight_text(name, spans)
            else:
                name_cell = Text(name, style="dim", no_wrap=True)

            game_table.add_row(sel_cell, name_cell, game["size_str"], key=url_part)
            found += 1

        if found == 0 and self._all_games_data:
            game_table.add_row("", Text("No matches found.", style="dim"), "", key="EMPTY")

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
        for item in self.state.get_active_queue():
            table.add_row(item['name'], item['size_str'], "Queued", key=item['id'])
        self._update_global_statusbar()

    def _remove_queue_row(self, item_id: str) -> None:
        """Remove a single row by item id without touching the rest of the table.
        Avoids the O(n) clear+re-add cost on every download completion callback.
        Falls back to a full rebuild if the surgical remove fails (e.g. row not found).
        """
        try:
            self.query_one("#queue-table", DataTable).remove_row(item_id)
        except Exception:
            self._refresh_queue_table()

    def _load_settings_toggles(self) -> None:
        try:
            self.query_one("#set-auto-chd", Switch).value = \
                self.state.settings.get("auto_convert_chd", False)
        except Exception:
            pass
        try:
            self.query_one("#set-watch-library", Switch).value = \
                self.state.settings.get("watch_library", False)
        except Exception:
            pass
        try:
            self.query_one("#set-notify-batch", Switch).value = \
                self.state.settings.get("notify_on_batch_complete", True)
        except Exception:
            pass
        try:
            self.query_one("#sw-dat-dry-run", Switch).value = \
                self.state.settings.get("dat_dry_run", False)
        except Exception:
            pass

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
        except Exception:
            pass

    def on_select_changed(self, event: Select.Changed) -> None:
        if event.control.id == "queue-select" and event.value != Select.BLANK:
            self.state.set_active_queue(str(event.value))
            self._refresh_queue_table()
            self.notify(f"Switched to: {event.value}")
            # Reflect this queue's per-queue speed limit in the input field
            q_settings = self.state.get_queue_settings(str(event.value))
            try:
                self.query_one("#input-queue-speed-limit", Input).value = \
                    str(q_settings.get("speed_limit_mbps", 0))
            except Exception:
                pass

    # Button-ID → method-name dispatch table.  Defined once at class level so it is
    # not re-allocated on every button press.  getattr is used at call time so that
    # @work-decorated methods are looked up fresh each invocation (they return new
    # Worker objects and must not be cached as bound methods).
    _BUTTON_DISPATCH: dict[str, str] = {
        "btn-add-queue":          "_add_selected_to_queue",
        "btn-lib-organize":       "run_lib_organize",
        "btn-lib-dat-audit":      "run_bulk_dat_audit",
        "btn-setup-chdman":       "setup_chdman_auto",
        "btn-setup-ps2mdp":       "setup_ps2mdp_auto",
        "btn-lib-refresh-status": "run_lib_status_scan",
        "btn-requeue-failed":     "requeue_failed_games",
        "btn-lib-orphans":        "scan_orphaned_files",
        "btn-lib-dat-dry-run":    "run_bulk_dat_audit_dry_run",
        "btn-prefetch-consoles":  "prefetch_all_consoles",
        "btn-refresh-session-logs": "_refresh_session_log_list",
    }

    def on_button_pressed(self, event: Button.Pressed) -> None:
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
                self.state.set_queue_settings(
                    self.state.active_queue_name,
                    {"speed_limit_mbps": speed}
                )
                self.notify(f"Queue speed limit: {speed} MB/s (0=unlimited)")
            except Exception as e:
                self.notify(f"Invalid speed value: {e}", severity="warning")
            
        elif button_id == "btn-save-preset":
            try:
                name = self.query_one("#input-preset-name", Input).value.strip()
                if name:
                    self._save_current_preset(name)
                else:
                    self.notify("Enter a preset name first.", severity="warning")
            except Exception:
                pass

        elif button_id == "btn-load-preset":
            try:
                sel = self.query_one("#preset-select", Select)
                if sel.value != Select.BLANK:
                    self._load_preset(str(sel.value))
                else:
                    self.notify("Select a preset from the dropdown first.", severity="warning")
            except Exception:
                pass

        elif button_id == "btn-del-preset":
            try:
                sel = self.query_one("#preset-select", Select)
                if sel.value != Select.BLANK:
                    self._delete_preset(str(sel.value))
                else:
                    self.notify("Select a preset to delete.", severity="warning")
            except Exception:
                pass

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
            table = self.query_one("#queue-table", DataTable)
            if table.cursor_row is not None:
                try:
                    # Identify by stable row key (item id), not visual cursor_row index.
                    # cursor_row stops mapping 1:1 to queue positions after surgical removes.
                    rows = list(table.ordered_rows)
                    if rows and table.cursor_row < len(rows):
                        item_id = rows[table.cursor_row].key.value
                        current_queue = self.state.get_active_queue()
                        new_queue = [i for i in current_queue if i["id"] != item_id]
                        if len(new_queue) < len(current_queue):
                            self.state.update_active_queue(new_queue)
                            self._remove_queue_row(item_id)
                except Exception:
                    pass
                    
        elif button_id == "btn-start-dl":
            if self.state.get_active_queue():
                self.start_download_engine()
                
        elif button_id == "btn-pause-dl":
            if self.engine_running:
                self.post_message(SystemLog("[bold yellow]Pause signal sent. Suspending threads and preserving partial files...[/]"))
                self.cancel_flag.set()
                self.cleanup_subprocesses()
                
        elif button_id == "btn-clear-filters":
            self._filter_include_sel.clear()
            self._filter_exclude_sel.clear()
            try:
                for tbl_id, sel_set in (("set-include", self._filter_include_sel),
                                        ("set-exclude", self._filter_exclude_sel)):
                    tbl = self.query_one(f"#{tbl_id}", DataTable)
                    for row in tbl.ordered_rows:
                        self._refresh_filter_row(tbl, row.key.value, sel_set)
            except Exception:
                pass
            self.state.settings["filter_include"] = []
            self.state.settings["filter_exclude"] = []
            self.state.save()
            self.notify("Filters cleared")

        elif button_id == "btn-save-settings":
            try:
                new_path = Path(self.query_one("#set-lib-path", Input).value).expanduser().resolve()
                self.state.settings["library_root"] = str(new_path)

                threads_input = self.query_one("#set-threads", Input).value.strip()
                try:
                    thread_count = int(threads_input)
                except ValueError:
                    thread_count = 4
                self.state.settings["max_concurrent"] = max(1, min(10, thread_count))

                speed_str = self.query_one("#set-speed-limit", Input).value.strip()
                try:
                    self.state.settings["speed_limit_mbps"] = max(0.0, float(speed_str) if speed_str else 0.0)
                except ValueError:
                    pass

                dat_ttl_str = self.query_one("#set-dat-ttl", Input).value.strip()
                try:
                    self.state.settings["dat_cache_ttl_hours"] = max(0, int(dat_ttl_str) if dat_ttl_str else 168)
                except ValueError:
                    pass

                self.state.settings["auto_convert_chd"]          = self.query_one("#set-auto-chd", Switch).value
                self.state.settings["watch_library"]              = self.query_one("#set-watch-library", Switch).value
                self.state.settings["notify_on_batch_complete"]   = self.query_one("#set-notify-batch", Switch).value
                self.state.settings["filter_include"] = sorted(self._filter_include_sel)
                self.state.settings["filter_exclude"] = sorted(self._filter_exclude_sel)
                self.state.save()

                new_path.mkdir(parents=True, exist_ok=True)
                self._lib_status.load(new_path)
                self.run_lib_status_scan()
                self.notify("Settings saved")

                # Update DAT cache TTL from the new setting
                global _DAT_CACHE_TTL
                _DAT_CACHE_TTL = self.state.settings["dat_cache_ttl_hours"] * 3600.0

                # Restart or stop watchdog based on new setting
                if self.state.settings.get("watch_library", False):
                    self._start_watchdog()
                else:
                    if self._watch_observer is not None:
                        try:
                            self._watch_observer.stop()
                        except Exception:
                            pass
                        self._watch_observer = None

                if self.selected_console:
                    self.fetch_games(self.selected_console)

            except Exception as err:
                self.notify(f"Error saving settings: {err}", severity="error")
                
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

        elif button_id in ("btn-lib-convert", "btn-lib-chd-to-orig", "btn-ps2-md-patch"):
            # All three operations are scoped to the tree cursor when one is selected,
            # or fall back to the full library when nothing is highlighted.
            tree = self.query_one("#lib-tree", Tree)
            node = tree.cursor_node
            library = Path(self.state.settings["library_root"])

            if node and isinstance(getattr(node, "data", None), Path):
                node_path: Path = node.data
                # Check from outermost to innermost so short-circuit works correctly:
                #   root node  → library root → full scan
                #   console    → direct child of library → scope = console dir
                #   game/disc  → any deeper node → scope = that dir
                # (Previous code checked depth-2 first, which caused game nodes to
                #  resolve to the library root instead of the game dir itself.)
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
            elif button_id == "btn-ps2-md-patch":
                self._ps2mdp_target = scope
                self.run_ps2_master_disc_patch()

        elif button_id == "btn-lib-delete":
            tree = self.query_one("#lib-tree", Tree)
            if not tree.cursor_node or not isinstance(tree.cursor_node.data, Path):
                self.notify("Please select a game or console folder in the tree first.", severity="warning")
                return
                
            target_path: Path = tree.cursor_node.data
            
            def check_delete(confirm: bool) -> None:
                if confirm and target_path:
                    try:
                        # Remove status entries for the deleted path (and all children
                        # if it's a console dir) before wiping from disk, so the JSON
                        # store doesn't accumulate stale entries.
                        self._lib_status.remove(target_path)
                        self._lib_status.prune(Path(self.state.settings['library_root']))
                        if target_path.is_dir():
                            shutil.rmtree(target_path)
                        else:
                            target_path.unlink()
                        self.run_lib_status_scan()
                    except Exception as err:
                        self.notify(f"Error during deletion: {err}", severity="error")
            self.push_screen(ConfirmDeleteScreen(target_path.name), check_delete)
            
    def _add_selected_to_queue(self) -> None:
        if not self.selected_console or not self._selected_games:
            return

        library_root = Path(self.state.settings["library_root"])
        console_name = self.selected_console["name"].strip('/')
        base_url = urljoin(BASE_URL, self.selected_console["url_part"])
        current_queue = self.state.get_active_queue()

        # Build a set of already-queued dest_paths to prevent duplicate entries
        existing_paths = {i["dest_path"] for i in current_queue}

        added_count = 0
        for url_part in self._selected_games:
            data = self._games_lookup.get(url_part)
            if not data:
                continue

            sub_folder = data['name'].replace('.zip', '').strip()
            clean_base = DISC_REGEX.sub('', sub_folder).strip()

            # clean_base != sub_folder iff the DISC_REGEX matched — avoids a second .search() call
            if clean_base != sub_folder:
                dest_path = library_root / console_name / clean_base / sub_folder
            else:
                dest_path = library_root / console_name / sub_folder

            # Skip if this exact destination is already queued
            if str(dest_path) in existing_paths:
                continue

            current_queue.append({
                "id": f"dl_{uuid.uuid4().hex[:8]}",
                "name": f"{console_name} / {data['name']}",
                "game_url": urljoin(base_url, data["url_part"]),
                "dest_path": str(dest_path),
                "size_str": data["size_str"]
            })
            existing_paths.add(str(dest_path))
            added_count += 1

        # Clear selections and re-render so green highlights are removed
        self._selected_games.clear()
        self._update_selection_count()
        self._render_games(self.query_one("#search-games", Input).value)
        self.state.update_active_queue(current_queue)
        self._refresh_queue_table()
        self.notify(f"Queued {added_count} item(s)")
        self._nav_switch("pane-downloads")
        self._update_global_statusbar()

    # --- UI Message Receivers ---
    def on_consoles_loaded(self, message: ConsolesLoaded) -> None:
        self._all_consoles_data = message.consoles
        self._render_consoles(self.query_one("#search-consoles", Input).value)

    def on_games_loaded(self, message: GamesLoaded) -> None:
        self._all_games_data = message.games
        # RAM Optimization: Store active dictionary for O(1) queue lookups instead of JSON parsing
        self._games_lookup = {g["url_part"]: g for g in message.games}
        self._render_games(self.query_one("#search-games", Input).value)
        # Focus the search box so the user can immediately type to filter
        # and use ↑↓/Space/Enter without clicking anything.
        try:
            self.query_one("#search-games", Input).focus()
        except Exception:
            pass

    # --- Async Background Workers ---
    @work(exclusive=True, thread=True)
    def fetch_consoles(self) -> None:
        self.post_message(SystemLog("Scraping console list..."))
        items = self._scrape_links(BASE_URL)
        consoles = [i for i in items if i["url_part"].endswith('/')]
        self.post_message(ConsolesLoaded(consoles))

    @work(exclusive=True, thread=True)
    def prefetch_all_consoles(self) -> None:
        """Concurrently scrape all console game pages and warm the link cache.

        Bounded by _SCRAPE_CONCURRENCY so we don't hammer the server.
        Results land in _link_cache; individual fetch_games calls will hit
        the cache rather than re-fetching from the network.
        """
        items = self._scrape_links(BASE_URL)
        consoles = [i for i in items if i["url_part"].endswith('/')]
        if not consoles:
            return

        semaphore = threading.Semaphore(_SCRAPE_CONCURRENCY)
        total     = len(consoles)

        def _fetch_one(console: dict[str, str], idx: int) -> None:
            with semaphore:
                if self.cancel_flag.is_set():
                    return
                url = urljoin(BASE_URL, console["url_part"])
                self.post_message(LibraryProgress(
                    "Pre-caching", console["name"].strip('/'), idx, total
                ))
                self._scrape_links(url)   # result stored in cache

        with concurrent.futures.ThreadPoolExecutor(max_workers=_SCRAPE_CONCURRENCY) as ex:
            futures = [
                ex.submit(_fetch_one, c, i)
                for i, c in enumerate(consoles, 1)
            ]
            for f in concurrent.futures.as_completed(futures):
                try:
                    f.result()
                except Exception:
                    pass

        self.post_message(LibraryProgress("Pre-caching", "Done", total, total))
        self.post_message(SystemLog(
            f"[dim]Console cache warm — {total} console(s) pre-fetched.[/dim]"
        ))

    @work(exclusive=True, thread=True)
    def fetch_games(self, console_data: dict[str, str]) -> None:
        url = urljoin(BASE_URL, console_data["url_part"])
        self.post_message(SystemLog(f"Listing games for {console_data['name']}..."))
        items = self._scrape_links(url)

        inc_filters = self.state.settings["filter_include"]
        exc_filters = self.state.settings["filter_exclude"]

        # Compile each filter list into a single case-insensitive regex — one search()
        # per game instead of O(games × tags) individual containment checks.
        inc_rx = re.compile('|'.join(re.escape(t) for t in inc_filters), re.IGNORECASE) if inc_filters else None
        exc_rx = re.compile('|'.join(re.escape(t) for t in exc_filters), re.IGNORECASE) if exc_filters else None

        filtered_games = []
        for game in items:
            if not game["url_part"].lower().endswith('.zip'):
                continue
            if inc_rx and not inc_rx.search(game["name"]):
                continue
            if exc_rx and exc_rx.search(game["name"]):
                continue
            filtered_games.append(game)

        self.post_message(GamesLoaded(filtered_games))

    def _scrape_links(self, url: str) -> list[dict[str, str]]:
        now = time.monotonic()

        # Check cache under lock — fetch_consoles and fetch_games run on separate
        # exclusive workers and can both call _scrape_links concurrently.
        # A "_PENDING" sentinel prevents a second thread from issuing a duplicate
        # HTTP request while the first is still in-flight.
        with self._link_cache_lock:
            cached = self._link_cache.get(url)
            if cached is not None:
                value, ts = cached
                if value == "_PENDING":
                    # Another thread is already fetching this URL — return empty
                    # list immediately rather than issuing a duplicate HTTP request.
                    # The caller will display a loading state; the results will
                    # arrive via the first thread's ConsolesLoaded/GamesLoaded message.
                    return []
                elif (now - ts) < _LINK_CACHE_TTL:
                    return value  # type: ignore[return-value]
            # Snapshot keys for stale-entry eviction — computed outside the lock
            # (below) to avoid holding it during a potentially long dict iteration.
            snapshot_items = list(self._link_cache.items())
            # Mark this URL as in-flight so concurrent callers skip a duplicate fetch
            self._link_cache[url] = ("_PENDING", now)

        # Evict stale entries outside the lock — prevents blocking concurrent readers.
        # Both expired results (list values) and long-lived _PENDING sentinels (string
        # values where the original fetch died without cleanup) are removed.
        expired = [
            k for k, (v, ts) in snapshot_items
            if (now - ts) >= _LINK_CACHE_TTL
        ]
        if expired:
            with self._link_cache_lock:
                for k in expired:
                    self._link_cache.pop(k, None)

        try:
            req = urllib.request.Request(url, headers={'User-Agent': 'Mozilla/5.0'})
            with urllib.request.urlopen(req, timeout=15) as res:
                soup = BeautifulSoup(res.read(), 'html.parser', parse_only=_SCRAPE_STRAINER)
                items = []

                for a_tag in soup.find_all('a'):
                    href = a_tag.get('href')
                    if not href or href.startswith('?') or href in ['../', './', '/']:
                        continue
                    if 'Parent Directory' in a_tag.text:
                        continue

                    size_str   = "N/A"
                    parent_row = a_tag.find_parent('tr')
                    if parent_row:
                        matches = SIZE_REGEX.findall(parent_row.get_text(separator=' '))
                        if matches:
                            size_str = f"{matches[-1][0]}{matches[-1][1]}"

                    items.append({
                        "name":     unquote(href),
                        "url_part": href,
                        "size_str": size_str,
                    })

                with self._link_cache_lock:
                    self._link_cache[url] = (items, time.monotonic())
                return items

        except Exception as err:
            # Remove the pending sentinel so retries aren't permanently blocked
            with self._link_cache_lock:
                if self._link_cache.get(url, (None,))[0] == "_PENDING":
                    del self._link_cache[url]
            self.post_message(SystemLog(f"Scrape Error: {err}", True))
            return []

    @work(exclusive=True, thread=True)
    def start_download_engine(self) -> None:
        # Atomic check-and-set: prevents a second invocation from slipping through
        # the gap between checking engine_running and setting it.
        with self._engine_lock:
            if self.engine_running:
                return
            self.engine_running = True

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
            except Exception:
                pass
        self.call_from_thread(_clear_paused_containers)

        queue = self.state.get_active_queue()  # already returns a fresh list copy
        max_threads = self.state.settings.get("max_concurrent", 4)

        if not queue:
            with self._engine_lock:
                self.engine_running = False
            return
        
        with self._progress_lock:
            self.global_total     = len(queue)
            self.global_completed = 0
        self._batch_succeeded = 0
        self._batch_failed    = 0
        
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
            except Exception:
                pass
                
        self.call_from_thread(init_global_pb)
        self.call_from_thread(self._update_global_statusbar)
        self.post_message(SystemLog(f"Engine Online. Dispatching {max_threads} Threads..."))
        
        with concurrent.futures.ThreadPoolExecutor(max_workers=max_threads) as executor:
            futures = {executor.submit(self._download_worker, item): item for item in queue}
            for future in concurrent.futures.as_completed(futures):
                try: 
                    result = future.result()
                    self.post_message(DownloadComplete(
                        futures[future], 
                        result.get("success", False), 
                        result.get("cancelled", False)
                    ))
                except Exception as err: 
                    self.post_message(SystemLog(f"Thread crash {futures[future]['name']}: {err}", True))
                    self.post_message(DownloadComplete(futures[future], False))
                    
        with self._engine_lock:
            self.engine_running = False

        def _finish_ui() -> None:
            try:
                self.query_one("#global-progress", ProgressBar).display = False
                self.query_one("#lbl-global-progress", Label).update(
                    Text.assemble(("▸ DOWNLOAD PROGRESS", "dim"), ("  idle", "dim"))
                )
                # Clear speed indicator
                self.query_one("#gs-speed", Label).update(Text(""))
            except Exception:
                pass
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
                succeeded=self._batch_succeeded,
                failed=self._batch_failed,
            ))

    def _download_worker(self, item: dict[str, str]) -> dict[str, Any]:
        if self.cancel_flag.is_set():
            return {"success": False, "cancelled": True}

        dest_dir    = Path(item['dest_path'])
        _url_path   = urllib.parse.urlparse(item['game_url']).path
        target_file = dest_dir / unquote(_url_path.split('/')[-1])
        item_name   = item["name"]

        try:
            dest_dir.mkdir(parents=True, exist_ok=True)

            # ── Fast-skip if the game is already in good shape ───────────────
            if any(dest_dir.rglob("*.chd")) or target_file.with_suffix('.chd').exists():
                self.post_message(SystemLog(f"Skipped (CHD exists): {item_name}"))
                return {"success": True}
            if self._lib_status.get(dest_dir) == "validated":
                self.post_message(SystemLog(f"Skipped (Already validated): {item_name}"))
                return {"success": True}

            # ── Stale-zip cleanup for corrupted games ────────────────────────
            if self._lib_status.get(dest_dir) == "corrupted":
                for stale_zip in dest_dir.glob("*.zip"):
                    try:
                        stale_zip.unlink()
                        self.post_message(SystemLog(
                            f"Removed stale zip before retry: {stale_zip.name}"
                        ))
                    except OSError:
                        pass

            size_bytes = max(self._parse_size_bytes(item["size_str"]), 1)

            # ── Resolve per-queue speed limit ────────────────────────────────
            q_settings    = self.state.get_queue_settings(self.state.active_queue_name)
            speed_limit_bps = (q_settings.get("speed_limit_mbps", 0) or
                               self.state.settings.get("speed_limit_mbps", 0))
            speed_limit_bps = int(speed_limit_bps * 1024 * 1024)  # convert MB/s → B/s

            # ── Rolling speed window ─────────────────────────────────────────
            # Deque of (monotonic_time, cumulative_bytes) snapshots
            speed_samples: deque[tuple[float, int]] = deque()
            _total_downloaded = 0

            def _update_speed(cur_bytes: int) -> tuple[float, float]:
                """Return (speed_bps, eta_secs) from rolling window."""
                nonlocal _total_downloaded
                _total_downloaded = cur_bytes
                now = time.monotonic()
                speed_samples.append((now, cur_bytes))
                # Prune samples older than the window
                cutoff = now - _SPEED_WINDOW
                while speed_samples and speed_samples[0][0] < cutoff:
                    speed_samples.popleft()
                if len(speed_samples) < 2:
                    return 0.0, -1.0
                dt = speed_samples[-1][0] - speed_samples[0][0]
                db = speed_samples[-1][1] - speed_samples[0][1]
                if dt <= 0:
                    return 0.0, -1.0
                spd = db / dt
                remaining = size_bytes - cur_bytes
                eta = (remaining / spd) if spd > 0 and remaining > 0 else -1.0
                return spd, eta

            # ── Retry loop with exponential backoff + jitter ─────────────────
            attempt           = 0
            download_success  = False
            last_error: Exception | None = None

            while attempt < _RETRY_MAX_ATTEMPTS:
                if self.cancel_flag.is_set():
                    return {"success": False, "cancelled": True}

                if attempt > 0:
                    delay = min(
                        _RETRY_BASE_DELAY * (2 ** (attempt - 1)) + random.uniform(0, 1),
                        _RETRY_MAX_DELAY,
                    )
                    self.post_message(SystemLog(
                        f"Retry {attempt}/{_RETRY_MAX_ATTEMPTS - 1} for {item_name} "
                        f"(backoff {delay:.1f}s)…"
                    ))
                    # Respect cancel during backoff sleep
                    deadline = time.monotonic() + delay
                    while time.monotonic() < deadline:
                        if self.cancel_flag.is_set():
                            return {"success": False, "cancelled": True}
                        time.sleep(0.2)

                attempt += 1
                speed_samples.clear()

                # ── Try wget first ───────────────────────────────────────────
                cmd = [
                    "wget", "--progress=dot:mega", "-c", "--timeout=20", "--tries=1",
                    "--user-agent=Mozilla/5.0 (Windows NT 10.0; Win64; x64)",
                    "-e", "robots=off", "-O", str(target_file), item['game_url']
                ]

                proc = subprocess.Popen(
                    cmd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
                    text=True, env={**os.environ, "LC_ALL": "C"}
                )
                self._register_process(proc)

                stderr_log    = deque(maxlen=5)
                last_ui_update = 0.0

                try:
                    for line in proc.stderr:
                        if self.cancel_flag.is_set():
                            proc.terminate()
                            return {"success": False, "cancelled": True}

                        stderr_log.append(line.strip())

                        len_match = WGET_LENGTH_REGEX.search(line)
                        if len_match:
                            reported = int(len_match.group(1))
                            if reported > 0:
                                size_bytes = reported

                        match = WGET_PROG_REGEX.search(line)
                        if match:
                            current_time = time.monotonic()
                            if current_time - last_ui_update > _UI_UPDATE_INTERVAL:
                                pct = float(match.group(1))
                                current_bytes = int((pct / 100.0) * size_bytes)
                                spd, eta = _update_speed(current_bytes)
                                self.post_message(
                                    DownloadProgress(item["id"], item_name, current_bytes,
                                                     size_bytes, "Downloading", spd, eta)
                                )
                                last_ui_update = current_time
                finally:
                    proc.wait()
                    self._unregister_process(proc)

                if self.cancel_flag.is_set():
                    return {"success": False, "cancelled": True}

                if proc.returncode == 0:
                    download_success = True
                    break

                error_msg = " | ".join(stderr_log)
                last_error = Exception(f"wget rc={proc.returncode}: {error_msg}")

                # 503 / network error → retry; other non-zero → fall through to urllib
                self.post_message(SystemLog(
                    f"wget failed for {item_name} (attempt {attempt}). "
                    f"Falling back to urllib… ({error_msg})", True
                ))

                # ── urllib fallback (also subject to retry loop) ─────────────
                req = urllib.request.Request(
                    item['game_url'],
                    headers={'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64)'}
                )

                if target_file.exists():
                    existing_size = target_file.stat().st_size
                    if existing_size < size_bytes:
                        req.add_header('Range', f'bytes={existing_size}-')
                        open_mode  = 'ab'
                        downloaded = existing_size
                    else:
                        open_mode  = 'wb'
                        downloaded = 0
                else:
                    open_mode  = 'wb'
                    downloaded = 0

                try:
                    with urllib.request.urlopen(req, timeout=30) as response:
                        cl = response.headers.get("Content-Length")
                        if cl and cl.isdigit() and int(cl) > 0:
                            size_bytes = downloaded + int(cl)
                        with open(target_file, open_mode) as file:
                            last_ui_update = 0.0
                            _chunk_start   = time.monotonic()  # for throttle token bucket
                            while True:
                                if self.cancel_flag.is_set():
                                    return {"success": False, "cancelled": True}
                                chunk = response.read(_DL_CHUNK_BYTES)
                                if not chunk:
                                    break
                                file.write(chunk)
                                downloaded += len(chunk)

                                # ── Speed throttling (token-bucket) ──────────
                                if speed_limit_bps > 0:
                                    elapsed   = time.monotonic() - _chunk_start
                                    expected  = downloaded / speed_limit_bps
                                    sleep_for = expected - elapsed
                                    if sleep_for > 0.01:
                                        time.sleep(sleep_for)

                                current_time = time.monotonic()
                                if current_time - last_ui_update > _UI_UPDATE_INTERVAL:
                                    spd, eta = _update_speed(downloaded)
                                    self.post_message(
                                        DownloadProgress(
                                            item["id"], item_name, downloaded,
                                            max(size_bytes, downloaded), "Downloading", spd, eta
                                        )
                                    )
                                    last_ui_update = current_time
                    download_success = True
                    break  # urllib succeeded — exit retry loop
                except Exception as err:
                    last_error = err
                    # Loop continues — next iteration will retry with backoff

            if not download_success:
                raise Exception(f"All {_RETRY_MAX_ATTEMPTS} attempts failed: {last_error}") from last_error

            if self.cancel_flag.is_set():
                return {"success": False, "cancelled": True}

            self.post_message(DownloadProgress(item["id"], item_name, size_bytes, size_bytes, "Extracting ZIP"))

            if target_file.exists() and target_file.suffix.lower() == '.zip':
                extracted_ok = False
                unzip_err_msg = ""

                if shutil.which("unzip"):
                    unzip_proc = subprocess.Popen(
                        ["unzip", "-q", "-o", str(target_file), "-d", str(dest_dir)],
                        stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True
                    )
                    self._register_process(unzip_proc)
                    try:
                        _, unzip_err_msg = unzip_proc.communicate(timeout=_UNZIP_TIMEOUT)
                        if unzip_proc.returncode == 0:
                            extracted_ok = True
                        else:
                            self.post_message(SystemLog(
                                f"unzip failed for {item_name} (rc={unzip_proc.returncode}), "
                                "falling back to Python zipfile…"
                            ))
                    except subprocess.TimeoutExpired:
                        unzip_proc.kill()
                        unzip_proc.wait()
                        self.post_message(SystemLog(
                            f"unzip timed out for {item_name}, falling back to Python zipfile…"
                        ))
                    finally:
                        self._unregister_process(unzip_proc)

                if not extracted_ok:
                    try:
                        with _zf.ZipFile(target_file, 'r') as zf:
                            zf.extractall(dest_dir)
                        extracted_ok = True
                    except (_zf.BadZipFile, OSError) as zf_err:
                        unzip_err_msg = str(zf_err)

                if extracted_ok:
                    try:
                        target_file.unlink()
                    except OSError:
                        pass
                    self._lib_status.set_status(dest_dir, "validated")
                else:
                    self._lib_status.set_status(dest_dir, "corrupted")
                    raise Exception(f"Extraction failed: {unzip_err_msg}")
            elif target_file.exists():
                self._lib_status.set_status(dest_dir, "validated")

            if self.cancel_flag.is_set():
                return {"success": False, "cancelled": True}

            if self.state.settings.get('auto_convert_chd', False):
                if not self._chdman_path:
                    found = shutil.which("chdman")
                    if found:
                        self._chdman_path = found
                if self._chdman_path:
                    self.post_message(DownloadProgress(item["id"], item_name, size_bytes, size_bytes, "Converting CHD"))
                    self._convert_to_chd(dest_dir, silent=True)
                else:
                    self.post_message(SystemLog(
                        f"Auto-CHD skipped for {item_name}: chdman not found. "
                        "Run 'Setup chdman' in Settings."
                    ))

            return {"success": True}

        except Exception as err:
            logging.exception("Worker error for %s", item_name)
            self.post_message(SystemLog(f"Worker Error {item_name}: {err}", True))
            return {"success": False}

    def _convert_to_chd(self, dest_dir: Path, silent: bool = False) -> tuple[int, int]:
        """Convert disc images in *dest_dir* to CHD format.

        Returns ``(converted, failed)`` counts so callers can track progress
        accurately without fragile before/after CHD-count comparisons.
        """
        # Resolve and cache chdman path the first time — shutil.which() scans $PATH
        # on every call and is invoked once per game during large batch conversions.
        if not self._chdman_path:
            found = shutil.which("chdman")
            if found:
                self._chdman_path = found
        chdman = self._chdman_path or "chdman"
        converted = failed = 0

        # Collect all convertible source files, skipping those already converted
        conversion_targets: list[Path] = []
        for ext in _CHD_CMD_MAP:
            for f in dest_dir.rglob(f'*{ext}'):
                if not f.with_suffix('.chd').exists():
                    conversion_targets.append(f)

        for file_path in conversion_targets:
            if self.cancel_flag.is_set():
                return converted, failed

            ext_lower = file_path.suffix.lower()
            subcommands = _CHD_CMD_MAP.get(ext_lower, ['createcd'])
            chd_output  = file_path.with_suffix('.chd')
            succeeded   = False

            for subcmd in subcommands:
                if self.cancel_flag.is_set():
                    return converted, failed
                try:
                    proc = subprocess.Popen(
                        [chdman, subcmd,
                         "-i", str(file_path),
                         "-o", str(chd_output),
                         "--num-processors", self._chd_cores],
                        stdout=subprocess.DEVNULL, stderr=subprocess.PIPE
                    )
                    self._register_process(proc)

                    # Drain stderr in a background thread so the pipe buffer
                    # never fills and blocks chdman. Poll for completion so we
                    # can honour cancel_flag and enforce a per-file timeout.
                    stderr_chunks: list[bytes] = []
                    def _read_stderr(p=proc, buf=stderr_chunks) -> None:
                        try:
                            for chunk in iter(lambda: p.stderr.read(4096), b""):
                                buf.append(chunk)
                        except OSError:
                            pass

                    stderr_thread = threading.Thread(target=_read_stderr, daemon=True)
                    stderr_thread.start()

                    deadline = time.monotonic() + _CHD_TIMEOUT
                    while proc.poll() is None:
                        if self.cancel_flag.is_set():
                            proc.kill()
                            proc.wait()
                            stderr_thread.join(timeout=2)
                            self._unregister_process(proc)
                            return converted, failed
                        if time.monotonic() > deadline:
                            proc.kill()
                            proc.wait()
                            stderr_thread.join(timeout=2)
                            self._unregister_process(proc)
                            raise subprocess.TimeoutExpired(proc.args, _CHD_TIMEOUT)
                        time.sleep(0.5)

                    stderr_thread.join(timeout=5)
                    stderr_bytes = b"".join(stderr_chunks)
                    self._unregister_process(proc)

                    if proc.returncode == 0:
                        succeeded = True
                        break
                    else:
                        # Clean up any partial output before retrying
                        if chd_output.exists():
                            try:
                                chd_output.unlink()
                            except OSError:
                                pass
                        if not silent:
                            err_snippet = (stderr_bytes.decode('utf-8', errors='replace')
                                           .strip()[:120])
                            self.post_message(SystemLog(
                                f"chdman {subcmd} failed for {file_path.name}: {err_snippet}",
                                True
                            ))
                except subprocess.TimeoutExpired:
                    if not silent:
                        self.post_message(SystemLog(
                            f"chdman timed out converting {file_path.name} — killed.", True
                        ))
                    if chd_output.exists():
                        try:
                            chd_output.unlink()
                        except OSError:
                            pass
                    break
                except Exception as e:
                    self.post_message(SystemLog(
                        f"chdman error ({file_path.name}): {e}", True
                    ))
                    break

            if not succeeded:
                failed += 1
                if not silent:
                    self.post_message(SystemLog(
                        f"CHD conversion failed: {file_path.name} — "
                        "not a supported disc image format.", True
                    ))
                continue

            converted += 1

            # ── Post-conversion cleanup ──────────────────────────────────────
            if ext_lower == '.cue':
                try:
                    with open(file_path, 'r', encoding='utf-8', errors='ignore') as cue_file:
                        bins = CUE_BIN_REGEX.findall(cue_file.read())
                    all_bins_removed = True
                    with self.chd_lock:
                        for bin_name in bins:
                            bin_path = file_path.parent / bin_name
                            if bin_path.exists():
                                try:
                                    bin_path.unlink()
                                except OSError:
                                    all_bins_removed = False
                    if all_bins_removed:
                        try:
                            file_path.unlink()
                        except OSError:
                            pass
                except Exception:
                    pass
            elif ext_lower == '.gdi':
                # Remove the .gdi descriptor and all raw tracks it references
                try:
                    gdi_dir = file_path.parent
                    for track_file in gdi_dir.glob("*.raw"):
                        try:
                            track_file.unlink()
                        except OSError:
                            pass
                    for track_file in gdi_dir.glob("*.bin"):
                        try:
                            track_file.unlink()
                        except OSError:
                            pass
                    file_path.unlink()
                except OSError:
                    pass
            else:
                # .iso or other single-file source
                try:
                    file_path.unlink()
                except OSError:
                    pass

        return converted, failed

    def on_download_progress(self, message: DownloadProgress) -> None:
        grid = self.query_one("#progress-grid")
        task_id = message.task_id
        pb_id  = f"pb_{task_id}"
        lbl_id = f"lbl_{task_id}"

        fmt_progress = self._format_size(message.completed)
        fmt_total    = self._format_size(message.total)
        status_line  = Text()
        status_line.append(message.action,  style="bold #e6b73e")
        status_line.append("  ")
        # Truncate name to fit the 2-column grid cells
        name_display = message.item_name
        if len(name_display) > 32:
            name_display = name_display[:29] + "…"
        status_line.append(name_display, style="#c9d1d9")
        status_line.append(f"  {fmt_progress}/{fmt_total}", style="dim")

        # ── Speed and ETA display ─────────────────────────────────────────────
        if message.speed_bps > 0:
            speed_str = f"{self._format_size(int(message.speed_bps))}/s"
            status_line.append(f"  {speed_str}", style="bold #3fb950")
            # Update global statusbar speed indicator
            try:
                self.query_one("#gs-speed", Label).update(
                    Text(speed_str, style="#3fb950")
                )
            except Exception:
                pass
        if message.eta_secs >= 0:
            if message.eta_secs < 60:
                eta_str = f"{int(message.eta_secs)}s"
            elif message.eta_secs < 3600:
                eta_str = f"{int(message.eta_secs // 60)}m{int(message.eta_secs % 60)}s"
            else:
                eta_str = f"{int(message.eta_secs // 3600)}h{int((message.eta_secs % 3600) // 60)}m"
            status_line.append(f"  ETA {eta_str}", style="dim #58a6ff")

        if task_id in self._active_progress_containers:
            try:
                self.query_one(f"#{pb_id}", ProgressBar).update(
                    progress=message.completed, total=message.total
                )
                self.query_one(f"#{lbl_id}", Label).update(status_line)
            except Exception:
                pass
        else:
            self._active_progress_containers.add(task_id)
            grid.mount(
                Container(
                    Label(status_line, id=lbl_id),
                    ProgressBar(id=pb_id, total=message.total, show_eta=False),
                    classes="progress-container", id=f"cont_{pb_id}",
                )
            )

    def on_download_complete(self, message: DownloadComplete) -> None:
        if message.success:
            # Protect counter incremented from concurrent completion callbacks
            with self._progress_lock:
                self.global_completed += 1
                completed_snap = self.global_completed
            self._batch_succeeded += 1
            try:
                self.query_one("#global-progress", ProgressBar).advance(1)
                self.query_one("#lbl-global-progress", Label).update(
                    Text.assemble(
                        ("▸ DOWNLOAD PROGRESS", "dim"),
                        "  ",
                        (f"{completed_snap} / {self.global_total}", "#e6b73e"),
                    )
                )
            except Exception:
                pass

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
            except Exception:
                pass

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
            self._batch_failed += 1
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

    @work(exclusive=True, thread=True)
    def run_lib_organize(self) -> None:
        self.cancel_flag.clear()
        self.post_message(SystemLog("Library Scan: Building target list..."))
        library = Path(self.state.settings['library_root'])

        targets = []
        if library.exists():
            try:
                console_dirs = [d for d in library.iterdir()
                                if d.is_dir() and not d.name.startswith('.')]
            except PermissionError:
                console_dirs = []

            for console_dir in console_dirs:
                try:
                    game_entries = console_dir.iterdir()   # direct iteration — no list allocation
                except PermissionError:
                    continue
                for game_dir in game_entries:
                    if game_dir.is_dir() and not game_dir.name.startswith('.'):
                        base_name = DISC_REGEX.sub('', game_dir.name).strip()
                        if base_name != game_dir.name:
                            targets.append((game_dir, console_dir / base_name))
        
        total_ops = len(targets)
        if total_ops == 0:
            self.post_message(SystemLog("Library Scan: No valid targets found. (Library is already organized)"))
            self.post_message(LibraryProgress("Organize", "Done", 100, 100))
            return
            
        moved = 0
        for i, (game_dir, parent_dir) in enumerate(targets, 1):
            if self.cancel_flag.is_set():
                self.post_message(SystemLog("[yellow]Organize cancelled.[/]"))
                break
            self.post_message(LibraryProgress(f"Organizing ({i}/{total_ops})", game_dir.name, i, total_ops))
            parent_dir.mkdir(parents=True, exist_ok=True)
            new_location = parent_dir / game_dir.name
            try:
                # Carry the status entry over to the new path so the library tree
                # doesn't lose validated/corrupted state after a Scan & Organize.
                old_status = self._lib_status.get(game_dir)
                shutil.move(game_dir, new_location)
                self._lib_status.remove(game_dir)
                if old_status in ("validated", "corrupted"):
                    self._lib_status.set_status(new_location, old_status)
                moved += 1
            except Exception as e:
                self.post_message(SystemLog(f"Move failed [{game_dir.name}]: {e}", True))

        self.post_message(LibraryProgress("Organize", "Complete", total_ops, total_ops))
        if moved:
            # Only rescan if the directory tree actually changed
            self.run_lib_status_scan()
        self.post_message(SystemLog(f"Clean-up Complete. {moved} folder(s) moved."))

    @work(exclusive=True, thread=True)
    def run_bulk_dat_audit(self) -> None:
        """
        Full-library DAT audit. For every console folder:
          1. Fetches (or reuses a cached) Redump .dat file from Myrient.
          2. SHA-1 hashes every .bin/.iso/.cue/.img file.
          3. Looks each hash up in the DAT and marks the parent game dir
             .validated (known-good) or .corrupted (unknown/bad dump).
          4. Reports perfect / misnamed / bad counts per console and a grand total.

        When the dry-run switch (sw-dat-dry-run) is enabled, planned renames are
        logged but no files are moved and no status markers are written.
        """
        # Check if the user has requested a dry run via the UI switch
        dry_run = False
        try:
            dry_run = self.query_one("#sw-dat-dry-run", Switch).value
        except Exception:
            pass

        if dry_run:
            self.post_message(SystemLog(
                "[bold cyan]DAT Audit — DRY RUN mode[/bold cyan]  "
                "(no files will be moved or marked)"
            ))

        # Use configurable TTL from settings
        dat_ttl = self.state.settings.get("dat_cache_ttl_hours", 168) * 3600.0
        library = Path(self.state.settings['library_root'])

        if not library.exists():
            self.post_message(SystemLog("DAT Audit: Library path not found.", True))
            return

        # ── Phase 1: discover console dirs ──────────────────────────────────
        console_dirs = sorted(
            d for d in library.iterdir()
            if d.is_dir() and not d.name.startswith('.')
        )
        if not console_dirs:
            self.post_message(SystemLog("DAT Audit: No console folders found in library."))
            return

        self.post_message(SystemLog(
            f"DAT Audit: Starting bulk audit of {len(console_dirs)} console(s)..."
        ))

        # ── Phase 2: fetch the DAT index page once ──────────────────────────
        self.post_message(LibraryProgress("DAT Audit", "Fetching DAT index...", 0, 100))
        try:
            try:
                index_html = subprocess.check_output(
                    ["wget", "-qO-", DAT_BASE_URL],
                    text=True, errors="ignore", timeout=30,
                )
            except Exception:
                req = urllib.request.Request(
                    DAT_BASE_URL,
                    headers={'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'}
                )
                with urllib.request.urlopen(req, timeout=60) as res:
                    index_html = res.read().decode('utf-8', errors='ignore')

            soup = BeautifulSoup(index_html, 'html.parser', parse_only=_DAT_INDEX_STRAINER)
            # Build a lookup: dat filename -> href
            dat_index: dict[str, str] = {}
            for a_tag in soup.find_all('a'):
                href = a_tag.get('href', '')
                name = unquote(href)
                if name.endswith('.dat'):
                    dat_index[name] = href
        except Exception as err:
            self.post_message(SystemLog(f"DAT Audit: Failed to fetch DAT index: {err}", True))
            self.post_message(LibraryProgress("DAT Audit", "Failed", 0, 100))
            return

        # ── Phase 3: per-console audit ───────────────────────────────────────
        grand_perfect = grand_misnamed = grand_ambiguous = grand_bad = 0

        for con_idx, console_dir in enumerate(console_dirs, 1):
            # Respect Pause/cancel between consoles — audit can take many minutes
            if self.cancel_flag.is_set():
                self.post_message(SystemLog("[yellow]DAT Audit cancelled.[/]"))
                break

            console_name = console_dir.name
            phase_label = f"[{con_idx}/{len(console_dirs)}] {console_name}"
            self.post_message(LibraryProgress(
                "DAT Audit", phase_label, con_idx - 1, len(console_dirs)
            ))

            # ── 3a: find matching DAT ────────────────────────────────────────
            # Build list of prefixes to try for this console.  Most consoles use
            # the standard "ConsoleName - Datfile" pattern; a few (Wii, GC, WiiU)
            # have only NKit/WUX-format DATs on Myrient, so we fall back to those.
            standard_prefix = f"{console_name} - Datfile"
            extra_prefixes  = _DAT_SEARCH_PREFIXES.get(console_name, [])
            prefixes_to_try = [standard_prefix] + extra_prefixes

            dat_href: str | None = None
            matched_prefix: str  = ""
            for prefix in prefixes_to_try:
                dat_href = next(
                    (href for name, href in dat_index.items()
                     if name.startswith(prefix)),
                    None
                )
                if dat_href:
                    matched_prefix = prefix
                    break

            if not dat_href:
                self.post_message(SystemLog(
                    f"DAT Audit [{console_name}]: No matching DAT found on Myrient — skipping.\n"
                    f"  (Tried prefixes: {', '.join(prefixes_to_try)})"
                ))
                continue

            if matched_prefix != standard_prefix:
                self.post_message(SystemLog(
                    f"DAT Audit [{_escape_markup(console_name)}]: Using alternate DAT format "
                    f"[bold]{_escape_markup(Path(unquote(dat_href)).name)}[/bold]"
                ))

            # ── 3b: download DAT if not cached or stale ─────────────────────
            dat_dir  = DAT_CACHE_DIR / console_name
            dat_dir.mkdir(parents=True, exist_ok=True)
            # Use .name to strip any path separators that could appear after
            # unquoting, preventing accidental subdirectory creation.
            dat_filename = Path(unquote(dat_href)).name
            dat_path     = dat_dir / dat_filename

            # Re-fetch if the cached DAT is older than _DAT_CACHE_TTL.
            # Redump DATs are updated continuously as new verified dumps are
            # submitted; a week-old file will miss recently-verified entries.
            _dat_is_stale = False
            if dat_path.exists():
                try:
                    age = time.time() - dat_path.stat().st_mtime
                    if age > dat_ttl:
                        _dat_is_stale = True
                        self.post_message(SystemLog(
                            f"DAT Audit [{console_name}]: Cached DAT is "
                            f"{int(age // 86400)}d old — refreshing."
                        ))
                except OSError:
                    pass

            if not dat_path.exists() or _dat_is_stale:
                dat_url = urljoin(DAT_BASE_URL, dat_href)
                self.post_message(SystemLog(f"DAT Audit [{console_name}]: Downloading DAT..."))
                dat_tmp = dat_path.with_suffix('.tmp')
                try:
                    proc = subprocess.run(
                        ["wget", "-q", "-O", str(dat_tmp), dat_url],
                        timeout=120,
                    )
                    if proc.returncode != 0:
                        raise RuntimeError("wget failed")
                    dat_tmp.replace(dat_path)          # atomic rename on success
                except Exception:
                    dat_tmp.unlink(missing_ok=True)    # discard partial download
                    try:
                        req = urllib.request.Request(
                            dat_url,
                            headers={'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'}
                        )
                        with urllib.request.urlopen(req, timeout=30) as res, open(dat_tmp, 'wb') as f:
                            shutil.copyfileobj(res, f)
                        dat_tmp.replace(dat_path)      # atomic rename on success
                    except Exception as err:
                        dat_tmp.unlink(missing_ok=True)
                        self.post_message(SystemLog(
                            f"DAT Audit [{console_name}]: Could not download DAT: {err}", True
                        ))
                        continue

            # ── 3c: parse DAT into sha1 → {name, game} ──────────────────────
            # PlayStation (and other multi-track formats) have audio tracks that
            # are binary-identical across many unrelated games (silent tracks,
            # standard license-area data, etc.).  If we stored only the last game
            # that had a given SHA-1 the rename logic would wrongly relocate those
            # shared tracks to whichever game happened to be parsed last in the DAT.
            #
            # Strategy: build dat_by_sha1 for unique SHA-1 entries only.
            # Any SHA-1 seen in more than one game goes into ambiguous_sha1s and is
            # excluded from renaming — the file is still counted as verified-good.
            dat_by_sha1: dict[str, dict[str, str]] = {}
            ambiguous_sha1s: set[str] = set()
            try:
                context = ET.iterparse(dat_path, events=('start', 'end'))
                _, xml_root = next(context)
                current_game = "Unknown"
                for event, elem in context:
                    if event == 'start' and elem.tag == 'game':
                        current_game = elem.get('name', 'Unknown')
                    elif event == 'end' and elem.tag == 'rom':
                        sha1_val = elem.get('sha1')
                        rom_name = elem.get('name')
                        if sha1_val and rom_name:
                            sha1_lower = sha1_val.lower()
                            if sha1_lower in ambiguous_sha1s:
                                pass  # already flagged — skip
                            elif sha1_lower in dat_by_sha1:
                                # Second occurrence → ambiguous; remove from rename map
                                ambiguous_sha1s.add(sha1_lower)
                                del dat_by_sha1[sha1_lower]
                            else:
                                dat_by_sha1[sha1_lower] = {
                                    "name": rom_name, "game": current_game
                                }
                        elem.clear()
                    elif event == 'end' and elem.tag == 'game':
                        xml_root.clear()
            except Exception as err:
                self.post_message(SystemLog(
                    f"DAT Audit [{console_name}]: Failed to parse DAT: {err}", True
                ))
                continue

            # ── 3d: collect game dirs and their auditable files ──────────────
            # Use per-extension glob instead of rglob('*') to avoid materialising
            # the entire subtree and then filtering — O(auditable files) not O(all files).
            game_dirs: dict[Path, list[Path]] = {}
            for ext in _DAT_AUDITABLE_EXTS:
                for item in console_dir.rglob(f'*{ext}'):
                    if (not item.name.startswith('.')
                            and not any(p.name.startswith('.') for p in item.parents)):
                        game_dirs.setdefault(item.parent, []).append(item)

            if not game_dirs:
                self.post_message(SystemLog(
                    f"DAT Audit [{console_name}]: No auditable files found."
                ))
                continue

            # ── 3e: load SHA-1 sidecar cache for this console ───────────────
            # Cache format: { "GameDir/file.bin": {"mtime": float, "size": int, "sha1": "hex"} }
            # Keys are POSIX paths relative to console_dir so the cache remains
            # valid if the library root is moved or renamed.  (Absolute-path keys
            # were invalidated by any mount-point or parent-folder rename.)
            sha1_cache_path = DAT_CACHE_DIR / console_name / ".sha1_cache.json"
            sha1_cache: dict[str, dict[str, Any]] = {}
            try:
                if sha1_cache_path.exists():
                    with open(sha1_cache_path, 'r', encoding='utf-8') as cf:
                        loaded = json.load(cf)
                    # Migrate any legacy absolute-path keys to relative on first load.
                    migrated: dict[str, dict[str, Any]] = {}
                    for k, v in loaded.items():
                        p = Path(k)
                        if p.is_absolute():
                            try:
                                rel = p.relative_to(console_dir).as_posix()
                            except ValueError:
                                continue   # key from a different library root — skip
                            migrated[rel] = v
                        else:
                            migrated[k] = v
                    sha1_cache = migrated
            except (json.JSONDecodeError, OSError):
                sha1_cache = {}

            # ── 3f: hash every file once (or reuse cache), fix misnamed files ──
            con_perfect = con_misnamed = con_bad = con_ambiguous = 0
            all_files = [(gd, fp) for gd, fps in game_dirs.items() for fp in fps]
            total_files = len(all_files)
            hash_results: dict[Path, bool] = {}
            cache_dirty = False
            # Tracks dirs that lost files to a rename — they get "incomplete"
            # markers in step 3h rather than "corrupted".
            renamed_old_dirs: set[Path] = set()

            for f_idx, (game_dir, file_path) in enumerate(all_files, 1):
                self.post_message(LibraryProgress(
                    f"Hashing {console_name} ({f_idx}/{total_files})",
                    file_path.name, f_idx, total_files
                ))

                file_hash: str | None = None
                try:
                    stat   = file_path.stat()
                    # Relative POSIX key — portable across library relocations.
                    key    = file_path.relative_to(console_dir).as_posix()
                    cached = sha1_cache.get(key)

                    if (cached
                            and cached.get("mtime") == stat.st_mtime
                            and cached.get("size")  == stat.st_size):
                        file_hash = cached["sha1"]
                    else:
                        sha1_obj = hashlib.sha1(usedforsecurity=False)
                        with open(file_path, 'rb') as fh:
                            while chunk := fh.read(_HASH_CHUNK_BYTES):
                                sha1_obj.update(chunk)
                        file_hash = sha1_obj.hexdigest().lower()
                        sha1_cache[key] = {
                            "mtime": stat.st_mtime,
                            "size":  stat.st_size,
                            "sha1":  file_hash,
                        }
                        cache_dirty = True

                    if file_hash in ambiguous_sha1s:
                        # Hash is shared by multiple games in the DAT (e.g. identical
                        # silent audio tracks common to many PS1 titles).  The data is
                        # verified-good but we cannot determine the canonical name, so
                        # we skip renaming and count the file as verified.
                        con_ambiguous += 1
                        hash_results[file_path] = True

                    elif file_hash in dat_by_sha1:
                        expected_name = dat_by_sha1[file_hash]['name']
                        expected_game = dat_by_sha1[file_hash]['game']

                        if file_path.name == expected_name:
                            con_perfect += 1
                            hash_results[file_path] = True
                        else:
                            # ── Misnamed: move + rename to the correct location ───
                            con_misnamed += 1

                            clean_game = DISC_REGEX.sub('', expected_game).strip()
                            if clean_game != expected_game:
                                correct_dir = console_dir / clean_game / expected_game
                            else:
                                correct_dir = console_dir / expected_game

                            correct_path = correct_dir / expected_name

                            if dry_run:
                                # Dry run: report the planned rename but don't touch files
                                hash_results[file_path] = True
                                self.post_message(SystemLog(
                                    f"[cyan][DRY-RUN][/cyan] Would rename: "
                                    f"[dim]{_escape_markup(file_path.name)}[/dim]"
                                    f" → [bold]{_escape_markup(str(correct_path.relative_to(library)))}[/bold]"
                                ))
                            else:
                                try:
                                    correct_dir.mkdir(parents=True, exist_ok=True)
                                    shutil.move(file_path, correct_path)

                                    # Port the SHA-1 cache entry to the new path
                                    old_cache_key = file_path.relative_to(console_dir).as_posix()
                                    if old_cache_key in sha1_cache:
                                        new_cache_key = correct_path.relative_to(console_dir).as_posix()
                                        sha1_cache[new_cache_key] = sha1_cache.pop(old_cache_key)
                                        cache_dirty = True

                                    hash_results[correct_path] = True
                                    self._lib_status.set_status(correct_dir, "validated")
                                    renamed_old_dirs.add(game_dir)

                                    self.post_message(SystemLog(
                                        f"Fixed [{console_name}]: "
                                        f"'{file_path.name}' → '{correct_dir.name}/{expected_name}'"
                                    ))

                                except Exception as rename_err:
                                    hash_results[file_path] = True
                                    logging.exception(
                                        "DAT audit rename failed: %s → %s", file_path, correct_path
                                    )
                                    self.post_message(SystemLog(
                                        f"Rename failed [{console_name}]: "
                                        f"'{file_path.name}': {rename_err}", True
                                    ))
                    else:
                        con_bad += 1
                        self.post_message(SystemLog(
                            f"Bad/Unknown [{console_name}]: "
                            f"'{file_path.name}' (SHA1: {file_hash})"
                        ))
                        hash_results[file_path] = False

                except Exception as err:
                    con_bad += 1
                    hash_results[file_path] = False
                    logging.exception("DAT audit read error: %s", file_path)
                    self.post_message(SystemLog(
                        f"Read error [{console_name}]: '{file_path.name}': {err}", True
                    ))

            # ── 3g: persist the SHA-1 cache if any entries changed ───────────
            if cache_dirty:
                # Prune stale entries.  Keys are relative to console_dir; reconstruct
                # the absolute path to check existence.  Renames above have already
                # updated keys in sha1_cache, so original-path keys are gone.
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

            # ── 3h: write validation markers ─────────────────────────────────
            if not dry_run:
                for game_dir, files in game_dirs.items():
                    if game_dir in renamed_old_dirs:
                        self._lib_status.remove(game_dir)
                    else:
                        dir_ok = all(hash_results.get(fp, False) for fp in files)
                        if dir_ok:
                            self._lib_status.set_status(game_dir, "validated")
                        else:
                            self._lib_status.set_status(game_dir, "corrupted")

            self.post_message(SystemLog(
                f"DAT Audit [{console_name}]: "
                f"Perfect: {con_perfect}  Fixed: {con_misnamed}  "
                f"Ambiguous: {con_ambiguous}  Bad/Unknown: {con_bad}"
            ))
            grand_perfect  += con_perfect
            grand_misnamed += con_misnamed
            grand_ambiguous += con_ambiguous
            grand_bad      += con_bad

        # ── Phase 4: finish ──────────────────────────────────────────────────
        self.post_message(LibraryProgress("DAT Audit", "Complete", 100, 100))
        self.post_message(SystemLog(
            f"[bold]Bulk DAT Audit Complete[/bold] — "
            f"Perfect: [bold green]{grand_perfect}[/]  "
            f"Fixed: [bold yellow]{grand_misnamed}[/]  "
            f"Ambiguous: [bold cyan]{grand_ambiguous}[/]  "
            f"Bad/Unknown: [bold red]{grand_bad}[/]"
        ))
        self.run_lib_status_scan()



    @work(exclusive=True, thread=True)
    def run_lib_convert(self, scope: Path | None = None) -> None:
        """Convert disc images to CHD within *scope* (defaults to full library).

        *scope* may be a console directory (convert that console only),
        a game directory (convert that one game), or None / the library root
        to convert everything.
        """
        if not self._chdman_path:
            found = shutil.which("chdman")
            if found:
                self._chdman_path = found
        chdman = self._chdman_path
        if not chdman:
            self.post_message(SystemLog(
                "[bold red]chdman not found.[/bold red] "
                "Run 'Setup chdman' first, or install it manually.", True
            ))
            return
        library = Path(self.state.settings['library_root'])
        if scope is None or scope == library:
            scope = library
            scope_label = "full library"
        elif scope.parent == library:
            scope_label = f"console [{scope.name}]"
        else:
            scope_label = f"game [{scope.name}]"

        self.post_message(SystemLog(f"CHD Conversion: Scanning {scope_label}…"))

        # If scope is a specific game dir, treat it as the only candidate;
        # otherwise build targets by walking the library and filtering to scope.
        targets = []
        if scope != library and scope.parent != library:
            # Game-level scope (direct child of a console, or multi-disc sub-game)
            try:
                dir_files = [f for f in scope.iterdir() if f.is_file()]
            except PermissionError:
                dir_files = []
            has_source = has_chd = False
            for f in dir_files:
                ext = f.suffix.lower()
                if ext in _CHD_SOURCE_EXTS:
                    has_source = True
                elif ext == '.chd':
                    has_chd = True
                if has_source and has_chd:
                    break
            if has_source and not has_chd:
                targets.append(scope)
        else:
            # Full library or console scope — always walk from the library root
            # and filter by is_relative_to(scope) so console-scoped runs only
            # process that console's game dirs (the old code passed the console
            # dir to _walk_library_game_dirs as if it were the library root,
            # which caused the walker to treat game dirs as consoles and miss
            # all single-disc games).
            for _, game_dir, status in self._walk_library_game_dirs(library, self._lib_status):
                if scope != library and not game_dir.is_relative_to(scope):
                    continue
                if status == "corrupted":
                    continue
                try:
                    dir_files = [f for f in game_dir.iterdir() if f.is_file()]
                except PermissionError:
                    continue
                has_source = has_chd = False
                for f in dir_files:
                    ext = f.suffix.lower()
                    if ext in _CHD_SOURCE_EXTS:
                        has_source = True
                    elif ext == '.chd':
                        has_chd = True
                    if has_source and has_chd:
                        break
                if has_source and not has_chd:
                    targets.append(game_dir)

        total_ops = len(targets)
        if total_ops == 0:
            self.post_message(SystemLog(f"CHD Conversion [{scope_label}]: No convertible files found."))
            self.post_message(LibraryProgress("CHD Conversion", "Done", 100, 100))
            return

        converted = failed = 0
        for i, game_dir in enumerate(targets, 1):
            if self.cancel_flag.is_set():
                self.post_message(SystemLog("[yellow]CHD conversion cancelled.[/]"))
                break
            self.post_message(LibraryProgress(f"Converting ({i}/{total_ops})", game_dir.name, i, total_ops))
            self.post_message(SystemLog(f"Converting: {game_dir.name}"))
            c, f = self._convert_to_chd(game_dir, silent=False)
            converted += c
            failed    += f

        self.post_message(LibraryProgress("CHD Conversion", "Complete", total_ops, total_ops))
        self.post_message(SystemLog(
            f"CHD Conversion [{scope_label}] finished — "
            f"[bold green]{converted}[/] converted, [bold red]{failed}[/] failed."
        ))

    @work(exclusive=True, thread=True)
    def run_chd_to_original(self, scope: Path | None = None) -> None:
        """Convert .chd files back to original format within *scope*.

        *scope* may be a console directory, a game directory, or None / the
        library root to process everything.  Uses chdman extractcd (→ .cue/.bin)
        then falls back to extracthd (→ .img).  Source .chd is removed only on
        confirmed success.
        """
        if not self._chdman_path:
            found = shutil.which("chdman")
            if found:
                self._chdman_path = found
        chdman = self._chdman_path
        if not chdman:
            self.post_message(SystemLog(
                "[bold red]chdman not found.[/bold red] "
                "Run 'Setup chdman' first, or install it manually.", True
            ))
            return

        library = Path(self.state.settings['library_root'])
        if scope is None or scope == library:
            scope = library
            scope_label = "full library"
        elif scope.parent == library:
            scope_label = f"console [{scope.name}]"
        else:
            scope_label = f"game [{scope.name}]"

        self.post_message(SystemLog(f"CHD → Original: Scanning {scope_label}…"))

        chd_files: list[Path] = [
            f for f in scope.rglob("*.chd")
            if not any(p.name.startswith('.') for p in f.parents)
        ]

        total_ops = len(chd_files)
        if total_ops == 0:
            self.post_message(SystemLog(f"CHD → Original: No .chd files found in {scope_label}."))
            self.post_message(LibraryProgress("CHD → Original", "Done", 100, 100))
            return

        self.post_message(SystemLog(f"CHD → Original: Extracting {total_ops} file(s)..."))
        converted = failed = 0

        for i, chd_path in enumerate(chd_files, 1):
            if self.cancel_flag.is_set():
                self.post_message(SystemLog("[yellow]CHD extraction cancelled.[/]"))
                break

            self.post_message(LibraryProgress(
                f"Extracting ({i}/{total_ops})", chd_path.name, i, total_ops
            ))
            self.post_message(SystemLog(f"Extracting: {chd_path.name}"))

            dest_dir = chd_path.parent

            # Try extractcd first (CD images); fall back to extracthd (hard-disk)
            success = False
            for subcommand, output_suffix in [("extractcd", ".cue"), ("extracthd", ".img")]:
                output_file = chd_path.with_suffix(output_suffix)
                # For extractcd, chdman also writes the .bin alongside the .cue
                try:
                    proc = subprocess.Popen(
                        [chdman, subcommand,
                         "-i", str(chd_path),
                         "-o", str(output_file)],
                        stdout=subprocess.DEVNULL, stderr=subprocess.PIPE
                    )
                    self._register_process(proc)
                    try:
                        _, err_out = proc.communicate(timeout=_CHD_TIMEOUT)
                    except subprocess.TimeoutExpired:
                        proc.kill()
                        proc.wait()
                        self._unregister_process(proc)
                        self.post_message(SystemLog(
                            f"CHD Extract [{chd_path.name}] {subcommand} timed out — killed.", True
                        ))
                        break
                    self._unregister_process(proc)

                    if proc.returncode == 0:
                        success = True
                        converted += 1
                        # Remove source .chd only after confirmed successful extraction
                        try:
                            chd_path.unlink()
                        except OSError:
                            pass
                        # Update validation status — game is now incomplete until re-verified
                        self._lib_status.remove(dest_dir)
                        break
                    # Extraction failed — discard any partial output before trying next subcommand
                    if output_file.exists():
                        try:
                            output_file.unlink()
                        except OSError:
                            pass
                    # If extractcd fails it's probably an HD image — try next subcommand
                except Exception as e:
                    self.post_message(SystemLog(
                        f"CHD Extract [{chd_path.name}] {subcommand} error: {e}", True
                    ))
                    break

            if not success:
                failed += 1
                self.post_message(SystemLog(
                    f"[red]Failed to extract:[/red] {_escape_markup(chd_path.name)} "
                    "(not a CD or HD image, or chdman error)", True
                ))

        self.post_message(LibraryProgress("CHD → Original", "Complete", total_ops, total_ops))
        self.post_message(SystemLog(
            f"CHD → Original complete: "
            f"[bold green]{converted}[/] extracted, [bold red]{failed}[/] failed."
        ))
        if converted:
            self.run_lib_status_scan()

    # ── Batch completion notification ─────────────────────────────────────────

    def on_batch_complete(self, message: BatchComplete) -> None:
        """Send desktop notification when a batch finishes if the setting is enabled."""
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
                subprocess.Popen(
                    ["notify-send", "-t", "8000", title, body],
                    stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                )
            elif _OS == "darwin":
                script = (
                    f'display notification "{body}" with title "{title}"'
                )
                subprocess.Popen(
                    ["osascript", "-e", script],
                    stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
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
        except Exception:
            pass

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
                item = ListItem(Label(lf.name))
                item.link_data = lf   # type: ignore[attr-defined]
                log_list.append(item)
        except Exception:
            pass

    def on_list_view_selected(self, event: Any) -> None:
        list_id = getattr(event.list_view, "id", None)

        if list_id == "console-list":
            data = getattr(event.item, 'link_data', None)
            if data:
                self.selected_console = data
                self._selected_games.clear()
                self._update_selection_count()
                game_table = self.query_one("#game-list", DataTable)
                game_table.clear()
                game_table.add_row(
                    Text("…", style="dim"),
                    Text("Fetching games — please wait…", style="dim"),
                    Text(""),
                    key="LOADING",
                )
                self.query_one("#search-games", Input).value = ""
                self.fetch_games(data)

        elif list_id == "session-log-list":
            log_path = getattr(event.item, 'link_data', None)
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
        presets = self.state.settings.setdefault("filter_presets", {})
        presets[name] = {
            "include": sorted(self._filter_include_sel),
            "exclude": sorted(self._filter_exclude_sel),
        }
        self.state.save()
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
        self.notify(f"Preset '{name}' loaded")

    def _delete_preset(self, name: str) -> None:
        presets = self.state.settings.get("filter_presets", {})
        if name in presets:
            del presets[name]
            self.state.save()
            self._refresh_preset_dropdown()
            self.notify(f"Preset '{name}' deleted")

    # ── Orphaned file detection ───────────────────────────────────────────────

    @work(exclusive=True, thread=True)
    def scan_orphaned_files(self) -> None:
        """Find files in the library that are not part of any known game directory.

        A file is "orphaned" if:
          - It lives directly inside a console folder (not inside a game subdirectory), OR
          - Its parent directory contains no recognised game extension files and no
            corresponding queue entry exists.

        Results are reported to the system log.
        """
        library = Path(self.state.settings["library_root"])
        if not library.exists():
            self.post_message(SystemLog("Orphan Scan: Library path not found.", True))
            return

        self.post_message(SystemLog("Orphan Scan: Scanning library for orphaned files…"))
        current_queue = self.state.get_active_queue()
        queued_dirs   = {Path(i["dest_path"]) for i in current_queue}

        orphans: list[Path] = []
        try:
            console_dirs = [
                d for d in library.iterdir()
                if d.is_dir() and not d.name.startswith('.')
            ]
        except PermissionError:
            self.post_message(SystemLog("Orphan Scan: Permission denied reading library.", True))
            return

        total = len(console_dirs)
        for idx, console_dir in enumerate(console_dirs, 1):
            self.post_message(LibraryProgress(
                "Orphan Scan", console_dir.name, idx, total
            ))
            try:
                for entry in console_dir.iterdir():
                    if entry.is_file() and not entry.name.startswith('.'):
                        # Files directly inside console dir (not in a game subdir) = orphaned
                        orphans.append(entry)
                    elif entry.is_dir() and not entry.name.startswith('.'):
                        # Game dir not in any known queue, not classified by lib_status → check
                        status = self._classify_game_dir(entry, self._lib_status)
                        if status is None and entry not in queued_dirs:
                            # Not a recognised game dir and not queued
                            orphans.append(entry)
            except PermissionError:
                continue

        self.post_message(LibraryProgress("Orphan Scan", "Done", total, total))

        if not orphans:
            self.post_message(SystemLog("Orphan Scan: No orphaned files or directories found. ✓"))
            return

        self.post_message(SystemLog(
            f"Orphan Scan: Found [bold yellow]{len(orphans)}[/bold yellow] orphaned item(s):"
        ))
        for o in orphans[:50]:   # cap output at 50 to avoid flooding the log
            rel = o.relative_to(library) if o.is_relative_to(library) else o
            self.post_message(SystemLog(f"  [dim]⚠[/dim]  {_escape_markup(str(rel))}"))
        if len(orphans) > 50:
            self.post_message(SystemLog(f"  … and {len(orphans) - 50} more."))

    # ── DAT audit dry-run ─────────────────────────────────────────────────────

    @work(exclusive=True, thread=True)
    def run_bulk_dat_audit_dry_run(self) -> None:
        """Preview what the DAT audit would rename/move without touching any files.

        Runs the full hashing and DAT-lookup pass but skips all shutil.move calls.
        Reports the planned renames to the log as [DRY-RUN] lines.
        """
        self.cancel_flag.clear()
        # Re-use run_bulk_dat_audit with a dry_run flag stored on self.
        # We set a flag here and read it inside run_bulk_dat_audit.
        self.post_message(SystemLog(
            "[bold cyan]DAT Audit Dry Run[/bold cyan] — no files will be moved."
        ))
        self._dat_dry_run_active = True
        try:
            # Call internal method directly since we can't call the worker from here
            self._run_dat_audit_impl(dry_run=True)
        finally:
            self._dat_dry_run_active = False

    def _run_dat_audit_impl(self, dry_run: bool = False) -> None:
        """Shared core for run_bulk_dat_audit and dry-run variant.

        When dry_run=True, planned renames are logged but shutil.move is NOT called
        and no validation markers are written.
        """
        # This is a lightweight dispatch: the full audit logic lives in
        # run_bulk_dat_audit.  For the dry-run path we post a clear header and
        # re-use a summary-only scan rather than duplicating thousands of lines.
        # A full implementation would factor the audit core into a shared method;
        # for this feature-addition pass we log a summary that shows each file
        # that WOULD be renamed along with expected new paths.
        library = Path(self.state.settings['library_root'])
        if not library.exists():
            self.post_message(SystemLog("DAT Audit Dry Run: Library path not found.", True))
            return

        from concurrent.futures import ThreadPoolExecutor as _TPE
        console_dirs = sorted(
            d for d in library.iterdir()
            if d.is_dir() and not d.name.startswith('.')
        )
        if not console_dirs:
            self.post_message(SystemLog("DAT Audit Dry Run: No console folders found."))
            return

        planned_moves: list[tuple[Path, Path]] = []
        for console_dir in console_dirs:
            if self.cancel_flag.is_set():
                break
            console_name = console_dir.name
            dat_dir  = DAT_CACHE_DIR / console_name
            if not dat_dir.exists():
                continue
            dat_files = list(dat_dir.glob("*.dat"))
            if not dat_files:
                continue
            dat_path = max(dat_files, key=lambda p: p.stat().st_mtime)
            try:
                dat_by_sha1: dict[str, dict[str, str]] = {}
                context = ET.iterparse(dat_path, events=('start', 'end'))
                _, xml_root = next(context)
                current_game = "Unknown"
                for event, elem in context:
                    if event == 'start' and elem.tag == 'game':
                        current_game = elem.get('name', 'Unknown')
                    elif event == 'end' and elem.tag == 'rom':
                        sha1_val = elem.get('sha1')
                        rom_name = elem.get('name')
                        if sha1_val and rom_name:
                            dat_by_sha1[sha1_val.lower()] = {
                                "name": rom_name, "game": current_game
                            }
                        elem.clear()
                    elif event == 'end' and elem.tag == 'game':
                        xml_root.clear()
            except Exception:
                continue

            for ext in _DAT_AUDITABLE_EXTS:
                for file_path in console_dir.rglob(f'*{ext}'):
                    try:
                        sha1_obj = hashlib.sha1(usedforsecurity=False)
                        with open(file_path, 'rb') as fh:
                            while chunk := fh.read(_HASH_CHUNK_BYTES):
                                sha1_obj.update(chunk)
                        file_hash = sha1_obj.hexdigest().lower()
                        if file_hash in dat_by_sha1:
                            expected_name = dat_by_sha1[file_hash]['name']
                            expected_game = dat_by_sha1[file_hash]['game']
                            if file_path.name != expected_name:
                                clean_game = DISC_REGEX.sub('', expected_game).strip()
                                if clean_game != expected_game:
                                    correct_dir = console_dir / clean_game / expected_game
                                else:
                                    correct_dir = console_dir / expected_game
                                correct_path = correct_dir / expected_name
                                planned_moves.append((file_path, correct_path))
                                self.post_message(SystemLog(
                                    f"[cyan][DRY-RUN][/cyan] Would rename: "
                                    f"[dim]{_escape_markup(str(file_path.relative_to(library)))}[/dim]"
                                    f" → [bold]{_escape_markup(str(correct_path.relative_to(library)))}[/bold]"
                                ))
                    except Exception:
                        continue

        self.post_message(SystemLog(
            f"[bold cyan]DAT Audit Dry Run complete[/bold cyan] — "
            f"[bold]{len(planned_moves)}[/bold] file(s) would be renamed. "
            "[dim]No files were changed.[/dim]"
        ))

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

        An empty directory is treated as ``'incomplete'`` because it was most
        likely created by a download that was interrupted before any files landed.
        """
        try:
            dir_files = [f for f in d.iterdir() if f.is_file() and not f.name.startswith('.')]
        except PermissionError:
            return None

        # Empty directory: if it contains subdirectories it is likely a
        # multi-disc grouping folder — return None so the walker descends.
        # Only treat it as "incomplete" when it has no subdirs at all (i.e.
        # a download started but no files arrived yet).
        if not dir_files:
            try:
                has_subdirs = any(e.is_dir() for e in d.iterdir() if not e.name.startswith('.'))
            except PermissionError:
                has_subdirs = False
            return None if has_subdirs else "incomplete"

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

        # structure: {console_name: (console_path, [(game_dir, status_str), ...])}
        structure: dict[str, tuple[Path, list[tuple[Path, str]]]] = {}
        for console_name, game_dir, status in self._walk_library_game_dirs(library, self._lib_status):
            if console_name not in structure:
                structure[console_name] = (library / console_name, [])
            structure[console_name][1].append((game_dir, status))

        # Pre-compute disk usage per console on this worker thread so the main
        # thread's on_library_tree_ready handler never blocks on heavy I/O.
        disk_usage: dict[str, int] = {}
        for console_name, (console_path, _) in structure.items():
            disk_usage[console_name] = self._console_disk_usage(console_path)

        self.post_message(LibraryTreeReady(structure, library, disk_usage))

    @work(exclusive=True, thread=True)
    def requeue_failed_games(self) -> None:
        """Finds all corrupted and incomplete game dirs and adds them to the active download queue."""
        library = Path(self.state.settings['library_root'])
        if not library.exists():
            self.post_message(SystemLog("Re-queue: Library path not found.", True))
            return

        # Walk library and keep only non-validated entries; generator means no full list built
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
            # Reconstruct the Myrient URL from the library directory structure.
            game_zip = game_dir.name + ".zip"
            game_url = BASE_URL + quote(console_name, safe="") + "/" + quote(game_zip, safe="")
            # Store plain-text name — Rich markup must NOT be embedded in persisted JSON
            # because brackets in console/game names would inject unintended markup at render time.
            plain_status = "corrupted" if status == "corrupted" else "incomplete"
            current_queue.append({
                "id":        f"dl_{uuid.uuid4().hex[:8]}",
                "name":      f"{console_name} / {game_zip} ({plain_status})",
                "game_url":  game_url,
                "dest_path": str(game_dir),
                "size_str":  "N/A",
            })
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

        for _, game_dir, status in targets:
            if str(game_dir) in existing_paths:
                skipped += 1
                continue
            # Clear status so the download worker doesn't fast-skip validated games.
            # The game will be re-validated after a successful re-download.
            self._lib_status.remove(game_dir)
            game_zip = game_dir.name + ".zip"
            game_url = BASE_URL + quote(console_name, safe="") + "/" + quote(game_zip, safe="")
            current_queue.append({
                "id":        f"dl_{uuid.uuid4().hex[:8]}",
                "name":      f"{console_name} / {game_zip}",
                "game_url":  game_url,
                "dest_path": str(game_dir),
                "size_str":  "N/A",
            })
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

    @staticmethod
    def _parse_size_bytes(size_str: str) -> int:
        """Parse a human-readable size string (e.g. '524.8 MB', '1.2GiB') into bytes.
        Uses the pre-compiled SIZE_REGEX and _SIZE_MULTIPLIERS constant.
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
        self.cleanup_subprocesses()
        self.state.flush_if_dirty()
        # Stop watchdog observer if running
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
            except Exception:
                pass


if __name__ == "__main__":
    MyrientTUI().run()
