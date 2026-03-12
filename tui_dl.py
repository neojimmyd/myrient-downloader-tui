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
from collections import Counter, deque
from pathlib import Path
from typing import Any, Iterator
from urllib.parse import quote, unquote, urljoin

from bs4 import BeautifulSoup, SoupStrainer
from rich.text import Text
from textual import work
from textual.app import App, ComposeResult
from textual.containers import Container, Horizontal, Vertical, VerticalScroll
from textual.events import Key
from textual.message import Message
from textual.screen import ModalScreen
from textual.timer import Timer
from textual.widgets import (
    Button, DataTable, Footer, Header, Input,
    Label, ListItem, ListView, ProgressBar, RichLog, Select,
    Switch, TabbedContent, TabPane, Tree
)

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

# PS2 Master Disc Patcher — bundled inside the PSDB release from alex-free
_PSDB_RELEASE_URL = (
    "https://github.com/alex-free/playstation-disc-burner/releases/download/"
    "v1.0.4/playstation-disc-burner-v1.0.4-x86_64.zip"
)
_PS2MDP_BINARY_NAME = "ps2-master-disc-patcher"   # name inside the PSDB zip

# Consoles whose Redump DAT name does NOT follow the standard
# "{console_name} - Datfile (N) (date).dat" pattern.  Each entry maps a
# console folder name to a list of prefix strings to try (in order) when
# searching the Myrient DAT index.  The first matching prefix wins.
_DAT_SEARCH_PREFIXES: dict[str, list[str]] = {
    # Wii and GameCube are distributed as NKit RVZ on Myrient; no plain Datfile exists.
    "Nintendo - Wii":      ["Nintendo - Wii - NKit RVZ", "Nintendo - Wii -"],
    "Nintendo - GameCube": ["Nintendo - GameCube - NKit RVZ", "Nintendo - GameCube -"],
    # Wii U uses WUX format on Myrient
    "Nintendo - Wii U":    ["Nintendo - Wii U - WUX", "Nintendo - Wii U -"],
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

# Platform-appropriate chdman download URLs (standalone builds)
import platform as _platform
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

# Frozenset for O(1) membership test in on_library_progress
_PROGRESS_DONE_STATES: frozenset[str] = frozenset({"done", "complete", "failed"})

DEFAULT_SETTINGS: dict[str, Any] = {
    # Default library sits next to the script, not inside _DATA_DIR.
    "library_root": str(_SCRIPT_DIR / "Myrient_Library"),
    "filter_include": [],
    "filter_exclude": [],
    "max_concurrent": 4,
    "auto_convert_chd": False,
    "chdman_path": "",   # empty = search PATH / tools dir at runtime
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
        with self._lock:
            if name in self.data["queues"] and name != self.data["active_queue"]:
                del self.data["queues"][name]
                self._write_locked()
                return True
        return False


class LibraryStatus:
    """Thread-safe, file-backed store for game directory validation status.

    Replaces per-directory ``.validated`` / ``.corrupted`` marker files with a
    single ``library_root/.myrient_status.json`` dict:

        { "Console Name/Game Dir": "validated" | "corrupted" }

    Absence from the dict means ``"incomplete"``.  Keys are POSIX-style paths
    relative to the library root so the entire file is portable — the library
    can be moved to a different mount point without invalidating any entries.

    On first load, any existing ``.validated`` / ``.corrupted`` marker files are
    migrated into the JSON store and then deleted, so the transition is seamless
    for existing libraries.
    """

    STATUS_FILE = ".myrient_status.json"

    def __init__(self) -> None:
        self._lock    = threading.Lock()
        self._data:   dict[str, str] = {}
        self._library: Path | None   = None
        self._path:    Path | None   = None
        self._dirty   = False

    # ── Public API ────────────────────────────────────────────────────────────

    def load(self, library: Path) -> None:
        """(Re)load status from *library*.  Safe to call from any thread.

        All shared state (_library, _path, _data, _dirty) is updated inside a
        single lock acquisition so concurrent readers never see a torn view.
        """
        new_path = library / self.STATUS_FILE
        data: dict[str, str] = {}
        try:
            if new_path.exists():
                with open(new_path, 'r', encoding='utf-8') as f:
                    data = json.load(f)
        except (json.JSONDecodeError, OSError):
            data = {}
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
            return str(path)

    def _flush(self) -> None:
        """Atomically write the current dict to disk if dirty.

        ``_dirty`` is reset to ``False`` only after a successful write.
        If the write fails (disk full, permissions, etc.) the flag stays True
        so the next mutation attempt will retry the flush.
        """
        if self._path is None:
            return
        with self._lock:
            if not self._dirty:
                return
            snapshot = dict(self._data)
            path     = self._path
        # Write outside the lock — file I/O must not block readers.
        try:
            path.parent.mkdir(parents=True, exist_ok=True)
            tmp = path.with_suffix('.tmp')
            with open(tmp, 'w', encoding='utf-8') as f:
                json.dump(snapshot, f, indent=2, sort_keys=True)
            tmp.replace(path)
            # Only clear _dirty after confirming the write succeeded.
            with self._lock:
                self._dirty = False
        except OSError:
            pass

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
    """Search input that intercepts ↑↓ / Space / Enter before Input consumes them.

    Textual's Input widget handles keys internally in ``_on_key`` before they
    bubble to the App.  Up/down arrows, space, and enter are all swallowed that
    way, so App.on_key never sees them when this widget is focused.

    This subclass intercepts exactly those keys and posts lightweight messages
    so the app can move the game-list cursor, toggle selections, and queue games
    — all without the user ever leaving the search box.
    """

    class NavUp(Message):       pass
    class NavDown(Message):     pass
    class ToggleAtCursor(Message): pass
    class QueueSelected(Message):  pass

    def _on_key(self, event: Key) -> None:
        if event.key == "up":
            self.post_message(self.NavUp())
            event.prevent_default()
            event.stop()
        elif event.key == "down":
            self.post_message(self.NavDown())
            event.prevent_default()
            event.stop()
        elif event.key == "space":
            self.post_message(self.ToggleAtCursor())
            event.prevent_default()
            event.stop()
        elif event.key == "enter":
            self.post_message(self.QueueSelected())
            event.prevent_default()
            event.stop()
        else:
            super()._on_key(event)


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
    def __init__(self, task_id: str, item_name: str, completed: int, total: int, action: str = "Downloading"):
        self.task_id = task_id
        self.item_name = item_name
        self.completed = completed
        self.total = total
        self.action = action
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
    def __init__(self, structure: dict[str, tuple[Path, list[tuple[Path, str]]]], library_path: Path):
        self.structure = structure
        self.library_path = library_path
        super().__init__()


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


# --- Main Application ---
class MyrientTUI(App):
    TITLE = "MYRIENT"
    SUB_TITLE = "ROM Library Manager"

    CSS = """
    /* ════════════════════════════════════════════════════════════
       MYRIENT  —  Deep Space Terminal Theme
       Amber-on-obsidian · sharp edges · semantic color only
       ════════════════════════════════════════════════════════════ */

    /* ── Base ──────────────────────────────────────────────────── */
    Screen {
        background: #0d1117;
        color: #e6edf3;
    }

    /* ── Header ─────────────────────────────────────────────────── */
    Header {
        background: #0d1117;
        color: #e6edf3;
        border-bottom: solid #e6b73e;
    }

    /* ── Footer ─────────────────────────────────────────────────── */
    Footer {
        background: #0d1117;
        color: #606878;
        border-top: solid #2a2f3a;
    }

    /* ── Tab strip ──────────────────────────────────────────────── */
    TabbedContent > Tabs {
        background: #0d1117;
        border-bottom: solid #2a2f3a;
    }
    TabbedContent > Tabs > Tab {
        color: #606878;
        padding: 0 3;
        background: #0d1117;
    }
    TabbedContent > Tabs > Tab.-active {
        color: #e6b73e;
        text-style: bold;
        background: #0d1117;
        border-top: tall #e6b73e;
    }
    TabbedContent > Tabs > Tab:hover {
        color: #9aa0aa;
        background: #0d1117;
    }
    #tabs       { height: 1fr; }
    TabPane     { background: #0d1117; }

    /* ── Layout ─────────────────────────────────────────────────── */
    .h-layout   { layout: horizontal; height: 1fr; }
    .panel      {
        height: 1fr;
        border: solid #2a2f3a;
        padding: 1 2;
        background: #0d1117;
    }
    .panel-25   { width: 25%; }
    .panel-30   { width: 30%; }
    .panel-35   { width: 35%; }
    .panel-40   { width: 40%; }
    .panel-50   { width: 50%; }
    .panel-60   { width: 60%; }
    .panel-65   { width: 65%; }
    .panel-70   { width: 70%; }
    .panel-75   { width: 75%; }
    .panel-100  { width: 100%; }

    /* ── Section headers ────────────────────────────────────────── */
    .section-header {
        height: auto;
        color: #e6b73e;
        text-style: bold;
        border-left: thick #e6b73e;
        padding: 0 0 0 2;
        margin-bottom: 1;
    }

    /* ── Hint bar (keyboard hints, counts) ──────────────────────── */
    .hint-bar {
        height: auto;
        color: #606878;
        margin-top: 1;
        margin-bottom: 0;
        text-align: right;
    }

    /* ── Search / Input ─────────────────────────────────────────── */
    .search-bar     { margin-bottom: 1; }
    Input {
        background: #0d1117;
        border: solid #3a4050;
        color: #e6edf3;
    }
    Input:focus { border: solid #e6b73e; }

    /* ── ListView (console list) ────────────────────────────────── */
    #console-list {
        height: 1fr;
        border: solid #2a2f3a;
        background: #0d1117;
    }
    ListView > ListItem {
        background: transparent;
        padding: 0 1;
        color: #e0e6ee;
    }
    ListView > ListItem.--highlight {
        background: #1a1f2e;
        color: #e6edf3;
    }
    ListView:focus > ListItem.--highlight {
        background: #1a1f2e;
        border-left: thick #e6b73e;
    }

    /* ── Game browser DataTable ─────────────────────────────────── */
    #game-list {
        height: 1fr;
        border: solid #2a2f3a;
        background: #0d1117;
    }
    #game-list > .datatable--header  { display: none; }
    #game-list > .datatable--cursor  { background: #1a1f2e; }

    /* ── Selection counter ──────────────────────────────────────── */
    #game-selection-count {
        height: auto;
        color: #3fb950;
        text-style: bold;
        margin: 0 0 1 0;
        text-align: right;
    }

    /* ── Queue table ────────────────────────────────────────────── */
    #queue-table {
        height: 1fr;
        border: solid #2a2f3a;
        background: #0d1117;
    }

    /* ── Filter DataTables (Settings) ───────────────────────────── */
    .filter-table {
        height: 8;
        border: solid #2a2f3a;
        margin-bottom: 1;
        background: #0d1117;
    }
    .filter-table > .datatable--header { display: none; }
    .filter-table > .datatable--cursor { background: #1a1f2e; }

    /* ── Library tree ───────────────────────────────────────────── */
    Tree {
        height: 1fr;
        border: solid #2a2f3a;
        background: #0d1117;
        margin-bottom: 1;
    }
    Tree > .tree--guides { color: #3a4050; }
    Tree > .tree--cursor { background: #1a1f2e; }

    /* ── Buttons ────────────────────────────────────────────────── */
    Button {
        background: #0d1117;
        color: #9aa0aa;
        border: solid #3a4050;
        margin: 0 1;
        min-width: 14;
        text-style: none;
    }
    Button:hover {
        background: #2a2f3a;
        color: #e6edf3;
        border: solid #606878;
    }
    Button:focus {
        border: solid #e6b73e;
        color: #e6edf3;
    }
    Button.-success {
        background: #0d2318;
        color: #3fb950;
        border: solid #238636;
    }
    Button.-success:hover {
        background: #238636;
        color: #e6edf3;
        border: solid #2ea043;
    }
    Button.-error {
        background: #2a0e0e;
        color: #f85149;
        border: solid #da3633;
    }
    Button.-error:hover {
        background: #da3633;
        color: #e6edf3;
        border: solid #f85149;
    }
    Button.-warning {
        background: #271d06;
        color: #d29922;
        border: solid #9e6a03;
    }
    Button.-warning:hover {
        background: #9e6a03;
        color: #e6edf3;
        border: solid #d29922;
    }
    Button.-primary {
        background: #0d1926;
        color: #58a6ff;
        border: solid #1f6feb;
    }
    Button.-primary:hover {
        background: #1f6feb;
        color: #e6edf3;
        border: solid #58a6ff;
    }

    /* ── Button rows ────────────────────────────────────────────── */
    .btn-row {
        height: auto;
        align: center middle;
        margin-top: 1;
    }
    .ops-btn { width: 100%; margin: 0 0 1 0; }

    /* ── Queue toolbar ──────────────────────────────────────────── */
    .queue-toolbar {
        height: auto;
        border-bottom: solid #2a2f3a;
        margin-bottom: 1;
        padding: 0 0 1 0;
        layout: grid;
        grid-size: 2;
        grid-gutter: 1;
    }
    .queue-toolbar Select   { column-span: 2; }
    .queue-toolbar Input    { column-span: 2; }
    .toolbar-btn-row {
        column-span: 2;
        height: auto;
        align: center middle;
    }

    /* ── Progress ───────────────────────────────────────────────── */
    #progress-area       { padding: 1 2; background: #0d1117; }
    #lbl-global-progress { margin-bottom: 1; color: #9aa0aa; }
    #global-progress     { margin-bottom: 1; display: none; }
    .thread-divider      { margin-top: 1; color: #3a4050; }
    .progress-container  {
        height: auto;
        margin-bottom: 1;
        padding: 0 0 1 0;
        border-bottom: solid #2a2f3a;
    }
    #lib-progress-bar { display: none; }
    ProgressBar > .bar--bar      { color: #e6b73e; }
    ProgressBar > .bar--complete { color: #3fb950; }

    /* ── Library tab layout wrapper ─────────────────────────────── */
    #lib-tab-wrapper { height: 1fr; }

    /* ── Library status bar (full-width strip, bottom of Library tab) ── */
    #lib-status-bar {
        height: 4;
        padding: 0 2;
        border-top: solid #2a2f3a;
        background: #0d1117;
        layout: horizontal;
        align: left middle;
    }
    #lib-status-label {
        width: 1fr;
        height: auto;
        color: #9aa0aa;
        content-align: left middle;
    }
    #lib-status-bar ProgressBar {
        width: 35%;
        display: none;
    }

    /* ── Settings ───────────────────────────────────────────────── */
    .legend-label  { margin: 1 0; color: #606878; }
    .setting-label { margin-top: 1; color: #9aa0aa; }
    Switch { background: transparent; }

    /* ── Logs ───────────────────────────────────────────────────── */
    RichLog {
        height: 1fr;
        border: none;
        background: #0d1117;
        color: #9aa0aa;
    }

    /* ── Confirm dialog ─────────────────────────────────────────── */
    ConfirmDeleteScreen {
        align: center middle;
        background: rgba(0, 0, 0, 0.75);
    }
    #dialog {
        padding: 2 3;
        width: 72;
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
    #dialog-btn-row {
        height: auto;
        align: center middle;
        width: 1fr;
    }
    #dialog-btn-row Button {
        width: 1fr;
        margin: 0 1;
    }
    """

    BINDINGS = [
        ("ctrl+q", "quit",                  "Quit"),
        ("ctrl+d", "toggle_dark",           "Theme"),
        ("ctrl+r", "refresh_browser",       "Refresh"),
    ]

    def __init__(self):
        super().__init__()
        self.state = ConfigManager(CONFIG_FILE)
        self._lib_status = LibraryStatus()
        # TTL-aware cache: stores (data, timestamp) to prevent stale results across long sessions
        self._link_cache: dict[str, tuple[list[dict[str, str]], float]] = {}
        # Lock protects _link_cache from concurrent reads/writes across fetch_consoles
        # and fetch_games, which can run on separate exclusive workers simultaneously.
        self._link_cache_lock = threading.Lock()

        self._all_consoles_data: list[dict[str, str]] = []
        self._all_games_data:    list[dict[str, str]] = []
        self._games_lookup:      dict[str, dict[str, str]] = {}

        self.selected_console: dict[str, str] | None = None

        self.proc_lock      = threading.Lock()
        self.active_processes: set = set()
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
        """Locate ps2-master-disc-patcher binary. Returns full path or ''."""
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
        """Download the PS2 Master Disc Patcher binary from the PSDB GitHub release.

        Extracts only the patcher binary (and region.ini if present) into
        myrient_data/tools/.  The originals are left untouched.
        """
        self.post_message(SystemLog("PS2 Patcher Setup: Checking for existing installation..."))
        path = self._find_ps2mdp()
        if path:
            self._ps2mdp_path = path
            self.post_message(SystemLog(
                f"ps2-master-disc-patcher already available at: [bold]{path}[/bold]"
            ))
            return

        self.post_message(SystemLog(
            "PS2 Patcher Setup: Downloading PSDB release to extract patcher binary…\n"
            f"  Source: {_PSDB_RELEASE_URL}"
        ))

        import zipfile as _zf

        tmp_zip = _TOOLS_DIR / "_psdb_download.zip"
        try:
            try:
                subprocess.run(
                    ["wget", "-q", "--timeout=60", "--tries=3",
                     "-O", str(tmp_zip), _PSDB_RELEASE_URL],
                    check=True, timeout=180,
                )
            except Exception:
                req = urllib.request.Request(
                    _PSDB_RELEASE_URL,
                    headers={"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64)"},
                )
                with urllib.request.urlopen(req, timeout=90) as resp, \
                        open(tmp_zip, "wb") as fout:
                    shutil.copyfileobj(resp, fout)

            with _zf.ZipFile(tmp_zip, "r") as zf:
                extracted_any = False
                for member in zf.namelist():
                    base = Path(member).name
                    if base in (_PS2MDP_BINARY_NAME,
                                _PS2MDP_BINARY_NAME + ".exe",
                                "region.ini"):
                        dest = _TOOLS_DIR / base
                        with zf.open(member) as src, open(dest, "wb") as dst:
                            shutil.copyfileobj(src, dst)
                        if base != "region.ini":
                            dest.chmod(dest.stat().st_mode | 0o111)
                        extracted_any = True
                        self.post_message(SystemLog(
                            f"PS2 Patcher Setup: Extracted [bold]{base}[/bold] → {dest}"
                        ))

            if not extracted_any:
                self.post_message(SystemLog(
                    "[bold red]PS2 Patcher Setup: binary not found inside the downloaded zip.[/bold red]\n"
                    "The PSDB release layout may have changed. Manual install:\n"
                    f"  1. Download: {_PSDB_RELEASE_URL}\n"
                    f"  2. Extract '{_PS2MDP_BINARY_NAME}' to myrient_data/tools/\n"
                    "  3. chmod +x myrient_data/tools/ps2-master-disc-patcher",
                    True,
                ))
                return

            # Write a default region.ini (USA) if the zip didn't include one
            region_ini = _TOOLS_DIR / "region.ini"
            if not region_ini.exists():
                region_ini.write_text("U\n", encoding="ascii")
                self.post_message(SystemLog(
                    "PS2 Patcher Setup: Created default region.ini (USA). "
                    "Edit myrient_data/tools/region.ini to change region: "
                    "J=Japan, U=USA, E=Europe, W=World"
                ))

            path = self._find_ps2mdp()
            if path:
                self._ps2mdp_path = path
                self.post_message(SystemLog(
                    f"[bold green]PS2 Master Disc Patcher ready![/bold green] Path: [bold]{path}[/bold]"
                ))
            else:
                self.post_message(SystemLog(
                    "[bold red]Setup finished but binary still not found.[/bold red]", True
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

        The patcher produces a sibling _MD.iso / _MD copy of each image.
        Originals are never deleted.
        """
        ps2mdp = self._ps2mdp_path or self._find_ps2mdp()
        if not ps2mdp:
            self.post_message(SystemLog(
                "[bold red]ps2-master-disc-patcher not found.[/bold red] "
                "Run 'Setup PS2 Patcher' first.", True
            ))
            return

        library  = Path(self.state.settings["library_root"])
        scope_path: Path = getattr(self, "_ps2mdp_target", library)

        # ── Build the list of game dirs to process ───────────────────────────
        if scope_path == library:
            scope_label = "full library (PS2 only)"
            game_dirs: list[Path] = []
            for console_dir in sorted(library.iterdir()):
                if not console_dir.is_dir() or console_dir.name.startswith('.'):
                    continue
                # Only process folders that look like PS2 consoles
                if "PlayStation 2" not in console_dir.name:
                    continue
                for _, gd, _ in self._walk_library_game_dirs(library, self._lib_status):
                    if gd.is_relative_to(console_dir):
                        game_dirs.append(gd)
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

        # Patcher accepts .iso (DVD 2048 B/s) and .bin (CD 2352 B/s)
        _PATCH_EXTS = frozenset({".iso", ".ISO", ".bin", ".BIN"})
        patcher_dir = Path(ps2mdp).parent

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
                candidates = [
                    f for f in game_dir.iterdir()
                    if f.is_file()
                    and f.suffix in _PATCH_EXTS
                    and "_MD" not in f.stem
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

                expected_out = game_dir / (src_file.stem + "_MD" + src_file.suffix)
                if expected_out.exists():
                    self.post_message(SystemLog(
                        f"PS2 MD: Skipping [bold]{src_file.name}[/bold] — _MD copy already exists."
                    ))
                    skipped += 1
                    continue

                self.post_message(SystemLog(f"PS2 MD: Patching [bold]{src_file.name}[/bold]…"))
                try:
                    # Run patcher from its own directory so it can find region.ini
                    proc = subprocess.Popen(
                        [ps2mdp, str(src_file)],
                        cwd=str(patcher_dir),
                        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                    )
                    self._register_process(proc)
                    stdout_b, stderr_b = proc.communicate(timeout=300)
                    self._unregister_process(proc)

                    # Patcher writes output next to the INPUT, but sector backup files
                    # land in cwd (patcher_dir). Move them into the game dir.
                    for backup_name in ("CD_Sectors.bin", "DVD_Sectors.bin"):
                        bp = patcher_dir / backup_name
                        if bp.exists():
                            try:
                                bp.rename(game_dir / backup_name)
                            except OSError:
                                pass

                    if proc.returncode == 0 and expected_out.exists():
                        patched += 1
                        self.post_message(SystemLog(
                            f"[green]PS2 MD: ✓ Patched →[/green] {expected_out.name}"
                        ))
                    else:
                        failed += 1
                        err_msg = (stderr_b + stdout_b).decode("utf-8", errors="replace").strip()[:200]
                        self.post_message(SystemLog(
                            f"[red]PS2 MD: Patcher failed[/red] for {src_file.name}: {err_msg}",
                            True,
                        ))
                except subprocess.TimeoutExpired:
                    proc.kill()
                    failed += 1
                    self.post_message(SystemLog(
                        f"[red]PS2 MD: Timeout[/red] patching {src_file.name}", True
                    ))
                except Exception as e:
                    failed += 1
                    self.post_message(SystemLog(
                        f"[red]PS2 MD: Error[/red] patching {src_file.name}: {e}", True
                    ))

        self.post_message(LibraryProgress("PS2 MD Patch", "Complete", total, total))
        self.post_message(SystemLog(
            f"PS2 Master Disc Patch complete — "
            f"[bold green]{patched}[/] patched, "
            f"[bold yellow]{skipped}[/] skipped, "
            f"[bold red]{failed}[/] failed.\n"
            "Originals are preserved. Delete them manually once you've verified the _MD copies."
        ))

    @staticmethod
    def _format_size(size_bytes: int) -> str:
        if size_bytes == 0:
            return "0 B"
        size_float = float(size_bytes)
        for unit in _SIZE_UNITS:
            if size_float < 1024.0:
                return f"{size_float:.2f} {unit}"
            size_float /= 1024.0
        return f"{size_float:.2f} PB"

    def compose(self) -> ComposeResult:
        yield Header(show_clock=True)
        with TabbedContent(id="tabs"):

            # ── ◈ Browse ─────────────────────────────────────────────────────
            with TabPane("  ◈ Browse  ", id="tab-browser"):
                with Horizontal(classes="h-layout"):
                    with Vertical(classes="panel panel-35"):
                        yield Label("▸ CONSOLES", classes="section-header")
                        yield Input(
                            placeholder="  filter consoles…",
                            id="search-consoles",
                            classes="search-bar",
                        )
                        yield ListView(id="console-list")

                    with Vertical(classes="panel panel-65"):
                        yield Label("▸ GAMES", classes="section-header")
                        yield GameSearchInput(
                            placeholder="  search games…",
                            id="search-games",
                            classes="search-bar",
                        )
                        yield DataTable(id="game-list", cursor_type="row", zebra_stripes=False)
                        yield Label("", id="game-selection-count")
                        with Horizontal(classes="btn-row"):
                            yield Button("▸ Queue Selected", id="btn-add-queue", variant="success")
                            yield Button("↺ Refresh", id="btn-refresh-games")
                        yield Label(
                            "[dim]↑↓[/dim] navigate · [dim]Space[/dim] select · [dim]Enter[/dim] queue",
                            classes="hint-bar",
                        )

            # ── ▶ Downloads ──────────────────────────────────────────────────
            with TabPane("  ▶ Downloads  ", id="tab-queue-dl"):
                with Horizontal(classes="h-layout"):
                    with Vertical(classes="panel panel-40"):
                        yield Label("▸ QUEUE PROFILES", classes="section-header")
                        with Vertical(classes="queue-toolbar"):
                            yield Select([], id="queue-select", prompt="active profile…")
                            yield Input(placeholder="new profile name…", id="input-new-queue")
                            with Horizontal(classes="toolbar-btn-row"):
                                yield Button("Create", id="btn-create-queue", variant="success")
                                yield Button("Delete", id="btn-delete-queue", variant="error")
                        yield DataTable(id="queue-table")
                        with Horizontal(classes="btn-row"):
                            yield Button("Remove", id="btn-remove-items", variant="warning")
                            yield Button("▶ Start", id="btn-start-dl", variant="primary")
                            yield Button("■ Pause", id="btn-pause-dl", variant="error")

                    with VerticalScroll(classes="panel panel-60", id="progress-area"):
                        yield Label(
                            "▸ DOWNLOAD PROGRESS",
                            id="lbl-global-progress",
                            classes="section-header",
                        )
                        yield ProgressBar(id="global-progress", show_eta=True)
                        yield Label(
                            "[dim]active threads appear below[/dim]",
                            classes="thread-divider",
                        )

            # ── ⬡ Library ────────────────────────────────────────────────────
            with TabPane("  ⬡ Library  ", id="tab-library"):
                with Vertical(id="lib-tab-wrapper"):
                    with Horizontal(classes="h-layout"):
                        with Vertical(classes="panel panel-75"):
                            yield Label("▸ LOCAL LIBRARY", classes="section-header")
                            yield Tree("Scanning…", id="lib-tree")
                            with Horizontal(classes="btn-row"):
                                yield Button(
                                    "✕ Delete Selected",
                                    id="btn-lib-delete",
                                    variant="error",
                                )

                        with VerticalScroll(classes="panel panel-25"):
                            yield Label("▸ OPERATIONS", classes="section-header")
                            yield Button(
                                "Scan & Organize",
                                id="btn-lib-organize",
                                classes="ops-btn",
                            )
                            yield Button(
                                "Verify vs. Redump DAT",
                                id="btn-lib-dat-audit",
                                classes="ops-btn",
                            )
                            yield Button(
                                "Convert to CHD",
                                id="btn-lib-convert",
                                classes="ops-btn",
                            )
                            yield Button(
                                "CHD → Original",
                                id="btn-lib-chd-to-orig",
                                classes="ops-btn",
                            )
                            yield Button(
                                "⚙ Setup chdman",
                                id="btn-setup-chdman",
                                classes="ops-btn",
                            )
                            yield Button(
                                "PS2 Master Disc Patch",
                                id="btn-ps2-md-patch",
                                classes="ops-btn",
                            )
                            yield Button(
                                "⚙ Setup PS2 Patcher",
                                id="btn-setup-ps2mdp",
                                classes="ops-btn",
                            )
                            yield Button(
                                "↺ Refresh Status",
                                id="btn-lib-refresh-status",
                                classes="ops-btn",
                            )
                            yield Button(
                                "Re-queue Failures",
                                id="btn-requeue-failed",
                                classes="ops-btn",
                            )
                            yield Button(
                                "Re-queue Console",
                                id="btn-requeue-console",
                                classes="ops-btn",
                            )
                            yield Label(
                                "[bold green]✓[/] Validated  "
                                "[bold red]✗[/] Corrupted  "
                                "[yellow]~[/] Incomplete",
                                classes="legend-label",
                            )

                    # ── Full-width status bar spanning the bottom of the tab ──
                    with Container(id="lib-status-bar"):
                        yield Label("Idle", id="lib-status-label")
                        yield ProgressBar(id="lib-progress-bar", show_eta=True)

            # ── ◎ Settings ───────────────────────────────────────────────────
            with TabPane("  ◎ Settings  ", id="tab-settings"):
                with Horizontal(classes="h-layout"):
                    with VerticalScroll(classes="panel panel-50"):
                        yield Label("▸ PATHS & ENGINE", classes="section-header")
                        yield Label("Library root path", classes="setting-label")
                        yield Input(
                            value=self.state.settings["library_root"],
                            id="set-lib-path",
                        )
                        yield Label(
                            "Max concurrent downloads  [dim](1–10)[/dim]",
                            classes="setting-label",
                        )
                        yield Input(
                            value=str(self.state.settings["max_concurrent"]),
                            id="set-threads",
                        )
                        yield Label(
                            "Auto-convert to CHD after download",
                            classes="setting-label",
                        )
                        yield Switch(
                            value=self.state.settings.get("auto_convert_chd", False),
                            id="set-auto-chd",
                        )
                        yield Button(
                            "▸ Save Settings",
                            id="btn-save-settings",
                            variant="success",
                        )

                    with VerticalScroll(classes="panel panel-50"):
                        yield Label("▸ REGIONAL INCLUDE FILTER", classes="section-header")
                        yield Label(
                            "[dim]Only show games matching these regions  (empty = show all)[/dim]",
                            classes="setting-label",
                        )
                        yield DataTable(id="set-include", classes="filter-table")
                        yield Label("▸ TYPE EXCLUDE FILTER", classes="section-header")
                        yield Label(
                            "[dim]Hide games matching these tags[/dim]",
                            classes="setting-label",
                        )
                        yield DataTable(id="set-exclude", classes="filter-table")
                        yield Button(
                            "✕ Clear Filters",
                            id="btn-clear-filters",
                            variant="warning",
                            classes="ops-btn",
                        )

            # ── ≡ Logs ───────────────────────────────────────────────────────
            with TabPane("  ≡ Logs  ", id="tab-logs"):
                with Vertical(classes="panel panel-100"):
                    yield RichLog(id="sys-log", markup=True, wrap=True, max_lines=1000)

        yield Footer()

    def on_mount(self) -> None:
        # Queue table
        table = self.query_one("#queue-table", DataTable)
        table.add_columns("Game Name", "Size", "Target Path")
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
                "CHD conversion is disabled. Use [bold]'Setup chdman'[/bold] in Library → Operations to install.",
                is_error=False,
            )

        # Resolve PS2 Master Disc Patcher path once at startup
        self._ps2mdp_path = self._find_ps2mdp()
        if not self._ps2mdp_path:
            self._log(
                "[yellow]ps2-master-disc-patcher not found.[/yellow] "
                "PS2 Master Disc patching disabled. Use [bold]'Setup PS2 Patcher'[/bold] to install.",
                is_error=False,
            )

        # Open session log — one file per run, named by wall-clock start time.
        try:
            SESSION_LOG_DIR.mkdir(parents=True, exist_ok=True)
            ts = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
            log_path = SESSION_LOG_DIR / f"myrient_{ts}.log"
            self._session_log_file = open(log_path, 'w', encoding='utf-8', buffering=1)
            self._session_log_file.write(
                f"# Myrient session log — started {datetime.datetime.now().isoformat()}\n"
            )
        except OSError as e:
            self._session_log_file = None
            self._log(f"Could not open session log file: {e}", is_error=True)

    def _log(self, msg: str, is_error: bool = False) -> None:
        try:
            log_widget = self.query_one("#sys-log", RichLog)
            ts = datetime.datetime.now().strftime("%H:%M:%S")
            line = Text()
            line.append(ts, style="dim #606878")
            line.append("  ")
            if is_error:
                line.append("ERR", style="bold #f85149")
            else:
                line.append("INF", style="dim #e6b73e")
            line.append("  ")
            try:
                line.append_text(Text.from_markup(msg))
            except Exception:
                line.append(msg)
            log_widget.write(line)
        except Exception:
            pass

        # Mirror to session log — strip markup to plain text for readability.
        # _log is always invoked on the main thread (via on_system_log message
        # dispatch), so no lock is needed for file writes here.
        if self._session_log_file is not None:
            try:
                full_ts = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
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

    def on_library_tree_ready(self, message: LibraryTreeReady) -> None:
        """Runs on the main thread — safe to touch the widget tree.
        Uses rich.text.Text objects for all user-controlled labels so that
        brackets in game/console names (e.g. [USA], [SLES-00867]) are NEVER
        parsed as markup tags.
        """
        AMBER  = "#e6b73e"
        GREEN  = "bold green"
        RED    = "bold red"
        YELLOW = "yellow"
        DIM    = "dim"

        def _game_label(name: str, status: str) -> Text:
            t = Text(no_wrap=True, overflow="ellipsis")
            if status == "validated":
                t.append("✓  ", style=GREEN)
                t.append(name,   style=GREEN)
            elif status == "corrupted":
                t.append("✗  ", style=RED)
                t.append(name,   style=RED)
            else:
                t.append("~  ", style=YELLOW)
                t.append(name,   style=YELLOW)
            return t

        def _console_label(name: str, n_ok: int, n_bad: int, n_inc: int) -> Text:
            t = Text(no_wrap=True)
            t.append(name, style=f"bold {AMBER}")
            if n_ok:
                t.append(f"  {n_ok}✓", style=GREEN)
            if n_bad:
                t.append(f"  {n_bad}✗", style=RED)
            if n_inc:
                t.append(f"  {n_inc}~", style=YELLOW)
            return t

        try:
            tree = self.query_one("#lib-tree", Tree)
            tree.clear()
            library = message.library_path
            root_name = library.name if library.exists() else "Library"
            root_label = Text(root_name, style=f"bold {AMBER}", no_wrap=True)
            tree.root.label = root_label

            for console_name, (console_path, games) in message.structure.items():
                counts = Counter(s for _, s in games)
                n_ok  = counts["validated"]
                n_bad = counts["corrupted"]
                n_inc = counts["incomplete"]
                console_node = tree.root.add(
                    _console_label(console_name, n_ok, n_bad, n_inc),
                    data=console_path,
                )
                for game_dir, status in games:
                    console_node.add_leaf(_game_label(game_dir.name, status), data=game_dir)

            if not message.structure:
                no_games = Text("No consoles found — check library path in Settings", style=DIM)
                tree.root.add_leaf(no_games)

            tree.root.expand()
            self.query_one("#lib-status-label", Label).update("[dim]Scan complete[/dim]")
            self.query_one("#lib-progress-bar", ProgressBar).display = False
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
                pct = int(message.completed / message.total * 100) if message.total else 0
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
        if not spans:
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
        search-games keys (↑↓/Space/Enter) are handled by GameSearchInput._on_key
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
            table.add_row(item['name'], item['size_str'], item['dest_path'], key=item['id'])

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

    def on_list_view_selected(self, event) -> None:
        list_id = getattr(event.list_view, "id", None)

        if list_id == "console-list":
            data = getattr(event.item, 'link_data', None)
            if data:
                self.selected_console = data

                # Clear stale game selections so they don't silently carry over
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

    # Button-ID → method-name dispatch table.  Defined once at class level so it is
    # not re-allocated on every button press.  getattr is used at call time so that
    # @work-decorated methods are looked up fresh each invocation (they return new
    # Worker objects and must not be cached as bound methods).
    _BUTTON_DISPATCH: dict[str, str] = {
        "btn-add-queue":          "_add_selected_to_queue",
        "btn-lib-organize":       "run_lib_organize",
        "btn-lib-dat-audit":      "run_bulk_dat_audit",
        "btn-setup-chdman":      "setup_chdman_auto",
        "btn-setup-ps2mdp":      "setup_ps2mdp_auto",
        "btn-lib-refresh-status": "run_lib_status_scan",
        "btn-requeue-failed":     "requeue_failed_games",
    }

    def on_button_pressed(self, event: Button.Pressed) -> None:
        button_id = event.button.id

        if button_id in self._BUTTON_DISPATCH:
            getattr(self, self._BUTTON_DISPATCH[button_id])()
            return

        if button_id == "btn-refresh-games" and self.selected_console:
            self.fetch_games(self.selected_console)
            
        elif button_id == "btn-create-queue":
            input_box = self.query_one("#input-new-queue", Input)
            if input_box.value and self.state.create_queue(input_box.value):
                input_box.value = ""
                self._refresh_queue_dropdown()
                self._refresh_queue_table()
                self.notify("Queue Created")
                
        elif button_id == "btn-delete-queue":
            if self.state.delete_queue(self.state.active_queue_name): 
                self._refresh_queue_dropdown()
                self._refresh_queue_table()
                self.notify("Queue Deleted")
                
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

                threads_input = self.query_one("#set-threads", Input).value
                thread_count = int(threads_input) if threads_input.isdigit() else 4
                self.state.settings["max_concurrent"] = max(1, min(10, thread_count))

                self.state.settings["auto_convert_chd"] = self.query_one("#set-auto-chd", Switch).value
                self.state.settings["filter_include"] = sorted(self._filter_include_sel)
                self.state.settings["filter_exclude"] = sorted(self._filter_exclude_sel)
                self.state.save()

                new_path.mkdir(parents=True, exist_ok=True)
                # Reload status store from the new library root before scanning
                self._lib_status.load(new_path)
                self.run_lib_status_scan()
                self.notify("Settings saved")

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
                # Resolve: game leaf → its parent console dir; anything else → as-is
                if node_path.parent.parent == library:
                    # grandchild — game inside a grouping folder; use the console
                    scope = node_path.parent.parent
                elif node_path.parent == library:
                    scope = node_path          # console node
                elif node_path == library:
                    scope = library            # root → full scan
                else:
                    scope = node_path          # game node (direct child of console)
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
        self.query_one("#tabs", TabbedContent).active = "tab-queue-dl"

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
        with self._link_cache_lock:
            cached = self._link_cache.get(url)
            if cached and (now - cached[1]) < _LINK_CACHE_TTL:
                return cached[0]
            # Evict stale entries before inserting — prevents unbounded growth
            expired = [k for k, (_, ts) in self._link_cache.items()
                       if (now - ts) >= _LINK_CACHE_TTL]
            for k in expired:
                del self._link_cache[k]

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

        queue = self.state.get_active_queue()  # already returns a fresh list copy
        max_threads = self.state.settings.get("max_concurrent", 4)

        if not queue:
            with self._engine_lock:
                self.engine_running = False
            return

        self.cancel_flag.clear()
        self._active_progress_containers.clear()   # fresh slate for this batch
        
        self.global_total = len(queue)
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
            except Exception:
                pass
                
        self.call_from_thread(init_global_pb)
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
            except Exception:
                pass

        if self.cancel_flag.is_set():
            self.post_message(SystemLog("[bold yellow]Downloads Successfully Paused[/]"))
            self.call_from_thread(_finish_ui)
        else:
            self.post_message(SystemLog("[bold green]Batch Queue Finished[/]"))
            self.state.flush_if_dirty()  # ensure final queue state is persisted immediately
            self.call_from_thread(_finish_ui)

    def _download_worker(self, item: dict[str, str]) -> dict[str, Any]:
        if self.cancel_flag.is_set():
            return {"success": False, "cancelled": True}

        dest_dir    = Path(item['dest_path'])
        # urlparse correctly extracts the path component, discarding any query
        # string (?foo=bar) that .split('/')[-1] would bake into the filename.
        _url_path   = urllib.parse.urlparse(item['game_url']).path
        target_file = dest_dir / unquote(_url_path.split('/')[-1])
        item_name   = item["name"]

        try:
            dest_dir.mkdir(parents=True, exist_ok=True)

            # ── Fast-skip if the game is already in good shape ───────────────
            # CHD-converted games have no source files but are still valid.
            if any(dest_dir.rglob("*.chd")) or target_file.with_suffix('.chd').exists():
                self.post_message(SystemLog(f"Skipped (CHD exists): {item_name}"))
                return {"success": True}
            # Non-CHD games: skip if already validated and not corrupted.
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

            # Prevent ZeroDivisionErrors by ensuring byte math is >= 1
            size_bytes = max(self._parse_size_bytes(item["size_str"]), 1)

            cmd = [
                "wget", "--progress=dot:mega", "-c", "--timeout=20", "--tries=3",
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

                    # Grab the real Content-Length from wget's output so the
                    # progress bar shows accurate byte counts even when the queue
                    # item's size_str was "N/A" or imprecise.
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
                            self.post_message(
                                DownloadProgress(item["id"], item_name, current_bytes, size_bytes, "Downloading")
                            )
                            last_ui_update = current_time
            finally:
                proc.wait()
                self._unregister_process(proc)

            if self.cancel_flag.is_set():
                return {"success": False, "cancelled": True}

            if proc.returncode != 0:
                error_msg = " | ".join(stderr_log)
                self.post_message(
                    SystemLog(f"Wget failed for {item_name}. Fallback to Urllib... ({error_msg})", True)
                )

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
                        # Update size_bytes from Content-Length if available so the
                        # progress bar shows real byte counts instead of the queue estimate.
                        cl = response.headers.get("Content-Length")
                        if cl and cl.isdigit() and int(cl) > 0:
                            content_length = int(cl)
                            size_bytes = content_length + downloaded  # total including already-downloaded
                        with open(target_file, open_mode) as file:
                            last_ui_update = 0.0
                            while True:
                                if self.cancel_flag.is_set():
                                    return {"success": False, "cancelled": True}
                                chunk = response.read(_DL_CHUNK_BYTES)
                                if not chunk:
                                    break
                                file.write(chunk)
                                downloaded += len(chunk)
                                current_time = time.monotonic()
                                if current_time - last_ui_update > _UI_UPDATE_INTERVAL:
                                    self.post_message(
                                        DownloadProgress(
                                            item["id"], item_name, downloaded,
                                            max(size_bytes, downloaded), "Downloading"
                                        )
                                    )
                                    last_ui_update = current_time
                except Exception as err:
                    raise Exception(f"Urllib socket failed: {err}") from err

            if self.cancel_flag.is_set():
                return {"success": False, "cancelled": True}

            self.post_message(DownloadProgress(item["id"], item_name, size_bytes, size_bytes, "Extracting ZIP"))

            if target_file.exists() and target_file.suffix.lower() == '.zip':
                unzip_proc = subprocess.Popen(
                    ["unzip", "-q", "-o", str(target_file), "-d", str(dest_dir)],
                    stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True
                )
                self._register_process(unzip_proc)
                _, unzip_err = unzip_proc.communicate()
                self._unregister_process(unzip_proc)

                if unzip_proc.returncode == 0:
                    try:
                        target_file.unlink()
                    except OSError:
                        pass  # zip delete failed — extraction still succeeded
                    self._lib_status.set_status(dest_dir, "validated")
                else:
                    self._lib_status.set_status(dest_dir, "corrupted")
                    raise Exception(f"Unzip failed: {unzip_err}")
            elif target_file.exists():
                self._lib_status.set_status(dest_dir, "validated")

            if self.cancel_flag.is_set():
                return {"success": False, "cancelled": True}

            if self.state.settings.get('auto_convert_chd', False):
                if self._chdman_path or shutil.which("chdman"):
                    self.post_message(DownloadProgress(item["id"], item_name, size_bytes, size_bytes, "Converting CHD"))
                    self._convert_to_chd(dest_dir, silent=True)
                else:
                    self.post_message(SystemLog(
                        f"Auto-CHD skipped for {item_name}: chdman not found. "
                        "Run 'Setup chdman' in Library → Operations."
                    ))

            return {"success": True}

        except Exception as err:
            logging.exception("Worker error for %s", item_name)   # full traceback to disk
            self.post_message(SystemLog(f"Worker Error {item_name}: {err}", True))
            return {"success": False}

    def _convert_to_chd(self, dest_dir: Path, silent: bool = False) -> None:
        chdman = self._chdman_path or shutil.which("chdman") or "chdman"

        # Map each source extension to the chdman subcommands to try (in order).
        # CD images (.cue/.gdi) use createcd.
        # Raw ISOs are most likely DVD-based (Wii, PS2, GC, Xbox) → createdvd first,
        # then createcd as fallback for the rare CD-ROM ISO.
        _CMD_MAP: dict[str, list[str]] = {
            '.cue': ['createcd'],
            '.gdi': ['createcd'],
            '.iso': ['createdvd', 'createcd'],
        }

        # Collect all convertible source files, skipping those already converted
        conversion_targets: list[Path] = []
        for ext in _CMD_MAP:
            for f in dest_dir.rglob(f'*{ext}'):
                if not f.with_suffix('.chd').exists():
                    conversion_targets.append(f)

        for file_path in conversion_targets:
            if self.cancel_flag.is_set():
                return

            ext_lower = file_path.suffix.lower()
            subcommands = _CMD_MAP.get(ext_lower, ['createcd'])
            chd_output  = file_path.with_suffix('.chd')
            succeeded   = False

            for subcmd in subcommands:
                if self.cancel_flag.is_set():
                    return
                try:
                    proc = subprocess.Popen(
                        [chdman, subcmd,
                         "-numprocessors", self._chd_cores,
                         "-i", str(file_path),
                         "-o", str(chd_output)],
                        stdout=subprocess.DEVNULL, stderr=subprocess.PIPE
                    )
                    self._register_process(proc)
                    _, stderr_bytes = proc.communicate()
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
                except Exception as e:
                    self.post_message(SystemLog(
                        f"chdman error ({file_path.name}): {e}", True
                    ))
                    break

            if not succeeded:
                if not silent:
                    self.post_message(SystemLog(
                        f"CHD conversion failed: {file_path.name} — "
                        "not a supported disc image format.", True
                    ))
                continue

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

    def on_download_progress(self, message: DownloadProgress) -> None:
        area = self.query_one("#progress-area")
        task_id = message.task_id
        pb_id  = f"pb_{task_id}"
        lbl_id = f"lbl_{task_id}"

        fmt_progress = self._format_size(message.completed)
        fmt_total    = self._format_size(message.total)
        status_line  = Text()
        status_line.append(message.action,  style="bold #e6b73e")
        status_line.append("  ")
        status_line.append(message.item_name, style="#c9d1d9")
        status_line.append(f"  {fmt_progress} / {fmt_total}", style="dim")

        if task_id in self._active_progress_containers:
            # Fast path: container already exists — update in place, no exception needed
            try:
                self.query_one(f"#{pb_id}", ProgressBar).update(
                    progress=message.completed, total=message.total
                )
                self.query_one(f"#{lbl_id}", Label).update(status_line)
            except Exception:
                pass
        else:
            # First progress message for this task — mount the container
            self._active_progress_containers.add(task_id)
            area.mount(
                Container(
                    Label(status_line, id=lbl_id),
                    ProgressBar(id=pb_id, total=message.total, show_eta=True),
                    classes="progress-container", id=f"cont_{pb_id}",
                )
            )

    def on_download_complete(self, message: DownloadComplete) -> None:
        if message.success:
            # Protect counter incremented from concurrent completion callbacks
            with self._progress_lock:
                self.global_completed += 1
                completed_snap = self.global_completed
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

        else:
            # Download failed — mark label as failed, hide bar, then remove
            # the container after a short delay so the user can see the failure.
            # Without removal the progress area fills up with ✗ Failed rows.
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
            shutil.move(str(game_dir), str(new_location))
            # Carry the status entry over to the new path so the library tree
            # doesn't lose validated/corrupted state after a Scan & Organize.
            old_status = self._lib_status.get(game_dir)
            self._lib_status.remove(game_dir)
            if old_status in ("validated", "corrupted"):
                self._lib_status.set_status(new_location, old_status)
            moved += 1

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
        """
        library = Path(self.state.settings['library_root'])
        auditable_exts = {'.bin', '.iso', '.cue', '.img', '.gdi', '.wbfs', '.rvz', '.gcz', '.nrg', '.mdf', '.wux'}

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
                with urllib.request.urlopen(req, timeout=20) as res:
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
        dat_cache_root = DAT_CACHE_DIR

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
                    f"DAT Audit [{console_name}]: Using alternate DAT format "
                    f"[bold]{Path(unquote(dat_href)).name}[/bold]"
                ))

            # ── 3b: download DAT if not cached ──────────────────────────────
            dat_dir  = dat_cache_root / console_name
            dat_dir.mkdir(parents=True, exist_ok=True)
            # Use .name to strip any path separators that could appear after
            # unquoting, preventing accidental subdirectory creation.
            dat_filename = Path(unquote(dat_href)).name
            dat_path     = dat_dir / dat_filename

            if not dat_path.exists():
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
            for ext in auditable_exts:
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
            # Cache format: { "/abs/path/to/file": {"mtime": float, "size": int, "sha1": "hex"} }
            # A file is considered cached if its mtime AND size match exactly — this
            # is the same heuristic used by rsync and git and is reliable for ROM files.
            sha1_cache_path = dat_cache_root / console_name / ".sha1_cache.json"
            sha1_cache: dict[str, dict[str, Any]] = {}
            try:
                if sha1_cache_path.exists():
                    with open(sha1_cache_path, 'r', encoding='utf-8') as cf:
                        sha1_cache = json.load(cf)
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
                    key    = str(file_path)
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

                            # Respect the disc-grouping convention already used by
                            # the downloader: if the game name contains a Disc/Side
                            # suffix, nest it under the clean base name.
                            clean_game = DISC_REGEX.sub('', expected_game).strip()
                            if clean_game != expected_game:
                                correct_dir = console_dir / clean_game / expected_game
                            else:
                                correct_dir = console_dir / expected_game

                            correct_path = correct_dir / expected_name

                            try:
                                correct_dir.mkdir(parents=True, exist_ok=True)
                                shutil.move(str(file_path), str(correct_path))

                                # Port the SHA-1 cache entry to the new path so the
                                # next audit doesn't re-hash the file.
                                old_cache_key = str(file_path)
                                if old_cache_key in sha1_cache:
                                    sha1_cache[str(correct_path)] = sha1_cache.pop(old_cache_key)
                                    cache_dirty = True

                                hash_results[correct_path] = True

                                # The destination directory now contains a validated file.
                                self._lib_status.set_status(correct_dir, "validated")

                                # The source dir lost a file — mark incomplete in step 3h.
                                renamed_old_dirs.add(game_dir)

                                self.post_message(SystemLog(
                                    f"Fixed [{console_name}]: "
                                    f"'{file_path.name}' → '{correct_dir.name}/{expected_name}'"
                                ))

                            except Exception as rename_err:
                                # Rename failed — log it, but the hash is still valid
                                # so don't penalise the file as corrupted.
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
                # Prune stale entries.  We check existence rather than comparing against
                # the original `game_dirs` path set, because renames above have already
                # updated the sha1_cache keys to new paths — the original paths are gone.
                sha1_cache = {k: v for k, v in sha1_cache.items() if Path(k).exists()}
                try:
                    sha1_cache_path.parent.mkdir(parents=True, exist_ok=True)
                    tmp_cache = sha1_cache_path.with_suffix('.tmp')
                    with open(tmp_cache, 'w', encoding='utf-8') as cf:
                        json.dump(sha1_cache, cf)
                    tmp_cache.replace(sha1_cache_path)
                except OSError:
                    pass

            # ── 3h: write validation markers ─────────────────────────────────
            for game_dir, files in game_dirs.items():
                if game_dir in renamed_old_dirs:
                    # Files were moved out — mark incomplete (data was valid,
                    # dir just no longer has all its files).
                    self._lib_status.remove(game_dir)
                else:
                    # Normal case: every auditable file must have a known-good hash.
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
        chdman = self._chdman_path or shutil.which("chdman") or ""
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

        # Source extensions that chdman can convert to CHD
        _CHD_SOURCE_EXTS = frozenset({'.bin', '.iso', '.cue', '.gdi'})

        # If scope is a specific game dir, treat it as the only candidate
        if scope.parent != library and scope != library:
            game_scope_dirs = [scope]
        else:
            game_scope_dirs = None  # use walker

        targets = []
        if game_scope_dirs is not None:
            for gd in game_scope_dirs:
                try:
                    dir_files = [f for f in gd.iterdir() if f.is_file()]
                except PermissionError:
                    continue
                has_source = any(f.suffix.lower() in _CHD_SOURCE_EXTS for f in dir_files)
                has_chd    = any(f.suffix.lower() == '.chd'            for f in dir_files)
                if has_source and not has_chd:
                    targets.append(gd)
        else:
            for _, game_dir, status in self._walk_library_game_dirs(scope, self._lib_status):
                if status == "corrupted":
                    continue
                try:
                    dir_files = [f for f in game_dir.iterdir() if f.is_file()]
                except PermissionError:
                    continue
                has_source = any(f.suffix.lower() in _CHD_SOURCE_EXTS for f in dir_files)
                has_chd    = any(f.suffix.lower() == '.chd'            for f in dir_files)
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
            before = list(game_dir.rglob("*.chd"))
            self._convert_to_chd(game_dir, silent=False)
            after  = list(game_dir.rglob("*.chd"))
            if len(after) > len(before):
                converted += 1
            else:
                failed += 1

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
        chdman = self._chdman_path or shutil.which("chdman") or ""
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
                    _, err_out = proc.communicate()
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
                    # If extractcd fails it's probably an HD image — try next subcommand
                except Exception as e:
                    self.post_message(SystemLog(
                        f"CHD Extract [{chd_path.name}] {subcommand} error: {e}", True
                    ))
                    break

            if not success:
                failed += 1
                self.post_message(SystemLog(
                    f"[red]Failed to extract:[/red] {chd_path.name} "
                    "(not a CD or HD image, or chdman error)", True
                ))

        self.post_message(LibraryProgress("CHD → Original", "Complete", total_ops, total_ops))
        self.post_message(SystemLog(
            f"CHD → Original complete: "
            f"[bold green]{converted}[/] extracted, [bold red]{failed}[/] failed."
        ))
        if converted:
            self.run_lib_status_scan()

    # ── Shared library-traversal helpers ─────────────────────────────────────

    @staticmethod
    def _classify_game_dir(d: Path, lib_status: LibraryStatus) -> str | None:
        """Classify a candidate game directory.

        Returns ``'validated'``, ``'corrupted'``, ``'incomplete'``, or ``None``
        (not a recognised game dir — caller should skip it).
        Status is read from *lib_status* — no marker files are checked.
        """
        try:
            dir_files = [f for f in d.iterdir() if f.is_file() and not f.name.startswith('.')]
        except PermissionError:
            return None
        # Broad set covering every disc/cart/tape image format from Myrient Redump:
        #   CD:   .bin .cue .img .iso .nrg .mdf .mds
        #   DVD:  .iso (reused)
        #   Wii/GC: .wbfs .rvz .gcz (Dolphin formats)
        #   DC:   .gdi
        #   CHD:  .chd
        #   Misc: .rom .xiso .ecm
        _GAME_EXTS = frozenset({
            '.bin', '.iso', '.cue', '.chd', '.img',
            '.wbfs', '.rvz', '.gcz', '.gdi',
            '.nrg', '.mdf', '.mds',
            '.rom', '.xiso', '.ecm',
        })
        has_game = any(f.suffix.lower() in _GAME_EXTS for f in dir_files)
        has_zip  = any(f.suffix.lower() == '.zip'     for f in dir_files)
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

        self.post_message(LibraryTreeReady(structure, library))

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
            # Switch to the queue tab so the user can see what was added
            self.call_from_thread(
                lambda: setattr(self.query_one("#tabs", TabbedContent), "active", "tab-queue-dl")
            )

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
            self.call_from_thread(
                lambda: setattr(self.query_one("#tabs", TabbedContent), "active", "tab-queue-dl")
            )

        self.post_message(SystemLog(
            f"Re-queue Console [{console_name}]: "
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
        self.state.flush_if_dirty()   # persist any deferred queue mutations before exit
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
