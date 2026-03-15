#!/usr/bin/env python3
"""
Myrient TUI Downloader & Library Manager
A high-performance Textual application for managing Redump libraries.
"""
from __future__ import annotations  # enable PEP 604 / lowercase generics on 3.9+

import concurrent.futures
import datetime
import enum
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
import sys
import threading
import time
import urllib.parse
import urllib.request
import uuid
import xml.etree.ElementTree as ET
import zipfile as _zf
from collections import Counter, deque
from pathlib import Path
from typing import Any, Iterator, TypedDict
from urllib.parse import quote, unquote, urljoin

from bs4 import BeautifulSoup, SoupStrainer
from rich.markup import escape as _escape_markup
from rich.text import Text
from textual import events, work
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
# These run at import time, not inside a function, because MyrientTUI is a
# single-file application entry point (not a library).  If you ever need to
# import this module in a test without side effects, move these into an
# _initialize() helper called only from `if __name__ == "__main__"`.
#
# socket.setdefaulttimeout: caps all urllib connections made by this process.
# _DATA_DIR / _TOOLS_DIR: created once so every subsequent open/write can assume
#   the directories exist without repeating mkdir() at each call site.
# logging.basicConfig: configures the root logger for error-to-file mirroring.
socket.setdefaulttimeout(60)

# ── Strongly-typed data structures ───────────────────────────────────────────
# Using TypedDict over plain dict[str, str] gives IDE auto-complete, mypy
# type-checking, and catches key typos like item["gameurl"] at analysis time
# rather than at runtime inside a worker thread.

class ConsoleItem(TypedDict):
    """One row returned by the Myrient console index scrape."""
    name:     str   # decoded display name, e.g. "Sony - PlayStation 2/"
    url_part: str   # href as-scraped (still percent-encoded), e.g. "Sony%20-%20PlayStation%202/"
    size_str: str   # always "N/A" for directories

class GameItem(TypedDict):
    """One row returned by a Myrient console-page scrape."""
    name:     str   # decoded filename, e.g. "Ico (USA).zip"
    url_part: str   # percent-encoded href fragment
    size_str: str   # human-readable size, e.g. "2.3GB"

class QueueItem(TypedDict):
    """One entry persisted in myrient_config.json → queues → <name>."""
    id:        str   # unique token, e.g. "dl_a1b2c3d4"
    name:      str   # display label shown in the queue table
    game_url:  str   # full absolute Myrient download URL
    dest_path: str   # absolute path of the local game directory
    size_str:  str   # human-readable file size (may be "N/A")

class RomEntry(TypedDict):
    """One <rom> element parsed from a Redump DAT file."""
    name:  str   # filename stored in the DAT (e.g. "Ico (USA).bin")
    game:  str   # parent <game name="…"> attribute

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
_PS2MDP_BINARY_NAME    = "ps2_master"
_PS2MDP_RELEASE_VERSION = "v1.0.5"   # update this alongside the URL and SHA-256 below
_PS2MDP_RELEASE_URL  = (
    "https://github.com/alex-free/playstation-disc-burner/releases/download/"
    f"{_PS2MDP_RELEASE_VERSION}/playstation-disc-burner-{_PS2MDP_RELEASE_VERSION}-x86_64.zip"
)
# SHA-256 of the release zip, verified against the v1.0.5 x86_64 GitHub release.
# If this hash does not match after download, setup is aborted — guards against
# MITM attacks or a compromised/replaced GitHub release asset.
# ─── When upgrading to a new release: update _PS2MDP_RELEASE_VERSION above,
#     download the new zip, and run: sha256sum playstation-disc-burner-*.zip
_PS2MDP_RELEASE_SHA256 = (
    "fa862ff48f7979f9e20d30ace3af5bd1f11bfca04bfe1c354caf38a3ebaf2d5b"
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

# Regex to extract percentage from chdman stderr output.
# Compiled once at module level — was previously re-compiled per file inside
# convert_to_chd's inner loop.
_CHD_PCT_RE = re.compile(rb'(\d+(?:\.\d+)?)%')

# Maximum number of session log files kept in myrient_data/logs/.
# Oldest files beyond this count are pruned at startup.
_SESSION_LOG_MAX_FILES: int = 30

# Pre-built environment dict for wget — forces C locale for consistent progress
# output parsing.  Allocated once instead of copying os.environ per invocation.
_WGET_ENV: dict[str, str] = {**os.environ, "LC_ALL": "C"}

# Pre-built kwargs for subprocess.Popen that lower process priority so that
# CPU-heavy children (chdman) don't starve the rest of the system.
if _OS == "windows":
    _LOW_PRIO_POPEN: dict[str, Any] = {"creationflags": 0x00004000}  # BELOW_NORMAL
else:
    def _nice_preexec() -> None:
        try:
            os.nice(15)
        except OSError:
            pass
        # Best-effort idle I/O scheduling via ioprio_set(2) syscall.
        # Avoids os.system/subprocess from within preexec_fn, which can
        # deadlock in multi-threaded programs (only async-signal-safe
        # functions are safe between fork and exec).
        try:
            import ctypes
            _NR_IOPRIO_SET = 251  # x86_64; arm64 uses 30
            IOPRIO_WHO_PROCESS = 1
            IOPRIO_CLASS_IDLE = 3
            ioprio = (IOPRIO_CLASS_IDLE << 13) | 0
            ctypes.CDLL("libc.so.6", use_errno=True).syscall(
                _NR_IOPRIO_SET, IOPRIO_WHO_PROCESS, 0, ioprio
            )
        except Exception:
            pass
    _LOW_PRIO_POPEN: dict[str, Any] = {"preexec_fn": _nice_preexec}

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


# ── Global bandwidth limiter ─────────────────────────────────────────────────
class TokenBucket:
    """Thread-safe token bucket for shared bandwidth limiting across workers.

    Tokens represent bytes.  Call ``consume(n)`` before sending/receiving *n*
    bytes — it will sleep just long enough to stay within the configured rate.
    A rate of 0 means unlimited (consume returns immediately).
    """
    __slots__ = ("_rate", "_capacity", "_tokens", "_last", "_lock")

    def __init__(self, rate_bps: int) -> None:
        self._rate     = rate_bps          # bytes per second (0 = unlimited)
        self._capacity = max(rate_bps, 1)  # max burst = 1 second of data
        self._tokens   = float(self._capacity)
        self._last     = time.monotonic()
        self._lock     = threading.Lock()

    @property
    def rate(self) -> int:
        return self._rate

    def consume(self, n: int) -> None:
        if self._rate <= 0:
            return
        with self._lock:
            now = time.monotonic()
            elapsed = now - self._last
            self._last = now
            self._tokens = min(self._capacity, self._tokens + elapsed * self._rate)
            if self._tokens >= n:
                self._tokens -= n
                return
            deficit = n - self._tokens
            self._tokens = 0.0
        # Sleep outside the lock so other threads can consume concurrently
        time.sleep(deficit / self._rate)


# ── Download engine state machine ────────────────────────────────────────────
class EngineState(enum.Enum):
    IDLE     = "idle"
    RUNNING  = "running"
    PAUSING  = "pausing"
    PAUSED   = "paused"


def _sha256_file(path: Path) -> str:
    """Return the lowercase hex SHA-256 digest of *path*.
    Uses ``_HASH_CHUNK_BYTES`` for I/O buffer size consistency.
    """
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        while chunk := fh.read(_HASH_CHUNK_BYTES):
            h.update(chunk)
    return h.hexdigest().lower()


def _safe_extractall(zf: "_zf.ZipFile", dest: Path) -> None:
    """Extract *zf* into *dest* while blocking path-traversal attacks.

    Python < 3.12 does not sanitise member paths in ``ZipFile.extractall``,
    so a crafted ZIP containing entries like ``../../.bashrc`` can write files
    outside *dest*.  This helper resolves every member path and raises
    ``ValueError`` for any entry that would land outside *dest*.

    Python 3.12+ has built-in extraction filters (``filter='data'``); we use
    those when available so we benefit from any additional hardening they add.
    """
    if sys.version_info >= (3, 12):
        zf.extractall(dest, filter="data")   # type: ignore[call-arg]
        return
    dest_resolved = dest.resolve()
    for member in zf.infolist():
        # Resolve the target path and check it stays inside dest.
        # Path.is_relative_to() (Python 3.9+) handles platform path separators
        # and normalises away any .. components before the comparison.
        target = (dest / member.filename).resolve()
        if not (target == dest_resolved or target.is_relative_to(dest_resolved)):
            raise ValueError(
                f"ZIP path traversal blocked: {member.filename!r} "
                f"would land at {target}, outside {dest_resolved}"
            )
    zf.extractall(dest)


DEFAULT_SETTINGS: dict[str, Any] = {
    # Default library sits next to the script, not inside _DATA_DIR.
    "library_root": str(_SCRIPT_DIR / "Myrient_Library"),
    "filter_include": [],
    "filter_exclude": [],
    "max_concurrent": 4,
    "auto_convert_chd": False,

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
            "settings": json.loads(json.dumps(DEFAULT_SETTINGS)),
            "active_queue": "default",
            "queues": {"default": []},
            "download_history": [],
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
                base["settings"] = {**json.loads(json.dumps(DEFAULT_SETTINGS)), **disk_data.get("settings", {})}
                base["queues"] = disk_data.get("queues", {"default": []})
                base["download_history"] = disk_data.get("download_history", [])
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
        try:
            with open(temp_file, 'w', encoding="utf-8") as f:
                json.dump(self.data, f)
            os.replace(temp_file, self.config_path)
        except OSError:
            # Restore dirty flag so the next flush retries the write.
            # Without this, a failed write silently drops the data.
            self._dirty = True
            raise

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
    def queues(self) -> dict[str, list[QueueItem]]:
        return self.data["queues"]

    @property
    def active_queue_name(self) -> str:
        return self.data["active_queue"]

    def get_active_queue(self) -> list[QueueItem]:
        with self._lock:
            return list(self.data["queues"].get(self.active_queue_name, []))

    def active_queue_length(self) -> int:
        """Return the number of items in the active queue without copying it."""
        with self._lock:
            return len(self.data["queues"].get(self.active_queue_name, []))

    def update_active_queue(self, new_queue: list[QueueItem], immediate: bool = True) -> None:
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
        with self._lock:
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

    def set_setting(self, key: str, value: Any, *, immediate: bool = True) -> None:
        """Write a single top-level setting key and persist to disk.

        Prefer this over ``self.state.settings[key] = value`` in the UI layer
        because it holds the lock for the whole read-modify-write and calls
        ``_write_locked()`` so the change is durable.

        Pass ``immediate=False`` to defer the disk write to the next
        ``flush_if_dirty()`` cycle (for high-frequency updates like live
        sliders).
        """
        with self._lock:
            self.data["settings"][key] = value
            if immediate:
                self._write_locked()
            else:
                self._dirty = True

    def update_settings(self, updates: dict[str, Any]) -> None:
        """Apply multiple setting keys in a single lock window and flush once.

        Use this in the Settings-save handler instead of assigning to
        ``self.state.settings[key]`` individually, which bypasses the lock.
        """
        with self._lock:
            self.data["settings"].update(updates)
            self._write_locked()

    # ── B1: Download history ────────────────────────────────────────────────
    _HISTORY_MAX = 500  # cap to prevent unbounded config growth

    def record_download(self, name: str, console: str, size_str: str) -> None:
        """Append a completed download to the history log."""
        entry = {
            "name": name,
            "console": console,
            "size": size_str,
            "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
        }
        with self._lock:
            history = self.data.setdefault("download_history", [])
            history.append(entry)
            # Trim oldest entries if over cap
            if len(history) > self._HISTORY_MAX:
                self.data["download_history"] = history[-self._HISTORY_MAX:]
            self._dirty = True

    @property
    def download_history(self) -> list[dict[str, str]]:
        with self._lock:
            return list(self.data.get("download_history", []))

    def clear_history(self) -> None:
        with self._lock:
            self.data["download_history"] = []
            self._dirty = True

    def mutate_settings(self, fn: Any) -> None:
        """Call *fn(settings_dict)* while holding the lock and flush once.

        Use this when the mutation is more complex than a flat key update
        (e.g. nested dict insert/delete on filter_presets).
        """
        with self._lock:
            fn(self.data["settings"])
            self._write_locked()


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
        self._defer_flush = False

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
        if not self._defer_flush:
            self._flush()

    def remove(self, path: Path) -> None:
        """Remove *path* from the store (marks it incomplete) and flush."""
        key = self._key(path)
        if key is None:
            return
        with self._lock:
            self._data.pop(key, None)
            self._dirty = True
        if not self._defer_flush:
            self._flush()

    def defer_flushes(self, defer: bool = True) -> None:
        """When *defer* is True, ``set_status``/``remove`` mark dirty but skip
        disk I/O.  When set back to False, a single flush captures all pending
        changes.  Used by the bulk DAT audit to avoid N disk writes for N game
        dirs — reduces I/O from O(games) to O(consoles).
        """
        self._defer_flush = defer
        if not defer:
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
        with self._lock:
            lib = self._library
        if lib is None:
            return None
        try:
            return path.relative_to(lib).as_posix()
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
    def __init__(self, consoles: list[ConsoleItem]):
        self.consoles = consoles
        super().__init__()

class GamesLoaded(Message):
    def __init__(self, games: list[GameItem]):
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
    def __init__(self, item: QueueItem, success: bool, cancelled: bool = False):
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
    """Carries the fully-built library structure to the main thread for Tree rendering.

    Each game entry is ``(game_dir, status_str, has_chd)`` where *has_chd*
    indicates whether the directory contains at least one ``.chd`` file.
    """
    def __init__(self, structure: dict[str, tuple[Path, list[tuple[Path, str, bool]]]], library_path: Path,
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
                ("── Browse ──", ""),
                ("↑ ↓",       "Navigate lists and tables"),
                ("Space",     "Toggle game selection"),
                ("Tab",       "Toggle game selection (browser)"),
                ("Enter / q", "Queue selected games"),
                ("",          ""),
                ("── Queue ──", ""),
                ("Delete",    "Remove highlighted queue item"),
                ("Shift+↑",  "Move queue item up"),
                ("Shift+↓",  "Move queue item down"),
                ("",          ""),
                ("── Nav ──",  ""),
                ("1–5",       "Switch nav pane (browse/dl/lib/set/logs)"),
            ]
            for key, desc in rows:
                if not key:
                    yield Label("", classes="help-row")
                elif key.startswith("──"):
                    yield Label(Text(f"  {key}", style="bold #e6b73e"), classes="help-row")
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


# ─────────────────────────────────────────────────────────────────────────────
# Scraper — Myrient HTTP index wrapper
# Owns the TTL-aware link cache and all HTTP fetch logic so MyrientTUI only
# needs to call scraper.scrape_links() / scraper.clear_cache().
# ─────────────────────────────────────────────────────────────────────────────
class MyrientScraper:
    """Thread-safe Myrient HTTP index scraper with TTL-aware in-memory cache.

    Extracted from MyrientTUI to satisfy the Single Responsibility Principle.
    The UI class creates one instance in ``__init__`` and delegates all network
    fetch + cache logic here; it only calls scraper.scrape_links() / scraper.clear_cache().

    Parameters
    ----------
    post_message_fn:
        Callable that accepts a ``Message`` object and posts it to the Textual
        app's message queue.  Matches the signature of ``App.post_message``.
    """

    def __init__(self, post_message_fn: Any) -> None:
        self._post = post_message_fn
        # TTL-aware cache: (data, timestamp) | ("_PENDING", timestamp)
        self._cache: dict[str, tuple[Any, float]] = {}
        self._lock  = threading.Lock()

    # ── Public API ────────────────────────────────────────────────────────────

    def clear_cache(self) -> None:
        """Flush the entire link cache (e.g. on Ctrl+R refresh)."""
        with self._lock:
            self._cache.clear()

    def scrape_links(self, url: str) -> list[ConsoleItem | GameItem]:
        """Return the list of items at *url*, served from cache when fresh.

        Thread-safe: a ``_PENDING`` sentinel prevents concurrent threads from
        issuing duplicate HTTP requests for the same URL.

        Returns an empty list on network error (error is posted as ``SystemLog``).
        """
        now = time.monotonic()

        with self._lock:
            cached = self._cache.get(url)
            if cached is not None:
                value, ts = cached
                if value == "_PENDING":
                    # Another thread is already fetching — return empty list;
                    # the first thread's completion will post ConsolesLoaded/GamesLoaded.
                    return []
                elif (now - ts) < _LINK_CACHE_TTL:
                    return value  # type: ignore[return-value]
            snapshot_items = list(self._cache.items())
            self._cache[url] = ("_PENDING", now)

        # Evict stale entries outside the lock.
        # Exclude the current url — we just set it to _PENDING above; the snapshot
        # still holds the OLD (stale) value for this key, so without the exclusion
        # the pop() below would delete the fresh sentinel we just inserted.
        expired = [k for k, (_, ts) in snapshot_items if (now - ts) >= _LINK_CACHE_TTL and k != url]
        if expired:
            with self._lock:
                for k in expired:
                    self._cache.pop(k, None)

        try:
            req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
            with urllib.request.urlopen(req, timeout=15) as res:
                soup = BeautifulSoup(res.read(), "html.parser", parse_only=_SCRAPE_STRAINER)
                items: list[ConsoleItem | GameItem] = []

                for a_tag in soup.find_all("a"):
                    href = a_tag.get("href")
                    if not href or href.startswith("?") or href in ["../", "./", "/"]:
                        continue
                    if "Parent Directory" in a_tag.text:
                        continue

                    size_str   = "N/A"
                    parent_row = a_tag.find_parent("tr")
                    if parent_row:
                        matches = SIZE_REGEX.findall(parent_row.get_text(separator=" "))
                        if matches:
                            size_str = f"{matches[-1][0]}{matches[-1][1]}"

                    items.append({          # type: ignore[misc]
                        "name":     unquote(href),
                        "url_part": href,
                        "size_str": size_str,
                    })

                with self._lock:
                    self._cache[url] = (items, time.monotonic())
                return items

        except Exception as err:
            with self._lock:
                if self._cache.get(url, (None,))[0] == "_PENDING":
                    del self._cache[url]
            self._post(SystemLog(f"Scrape Error: {err}", True))
            return []


# ─────────────────────────────────────────────────────────────────────────────
# Toolchain — chdman + PS2 Master Disc Patcher setup / invocation
# Extracted from MyrientTUI so binary discovery, package-manager install, and
# external-process invocations live in one auditable place.
# ─────────────────────────────────────────────────────────────────────────────
class Toolchain:
    """Manages external tool discovery and invocation (chdman, ps2_master).

    Extracted from MyrientTUI to satisfy the Single Responsibility Principle.
    MyrientTUI creates one instance and calls its methods; it never directly
    invokes chdman or ps2_master itself.

    Parameters
    ----------
    post_message_fn:
        Callable matching ``App.post_message`` — used to emit ``SystemLog`` and
        ``DownloadProgress`` messages from worker threads.
    cancel_flag:
        The shared ``threading.Event`` that workers poll to detect pause/cancel.
    register_process / unregister_process:
        Callbacks that add/remove a ``subprocess.Popen`` from the app's tracked
        process set so ``cleanup_subprocesses`` can kill them on quit.
    chd_lock:
        Mutex that serialises concurrent .cue/.bin cleanup across CHD workers.
    """

    def __init__(
        self,
        post_message_fn: Any,
        cancel_flag: threading.Event,
        register_process: Any,
        unregister_process: Any,
        chd_lock: threading.Lock,
    ) -> None:
        self._post             = post_message_fn
        self.cancel_flag       = cancel_flag
        self._reg_proc         = register_process
        self._unreg_proc       = unregister_process
        self.chd_lock          = chd_lock
        self.chdman_path: str  = ""
        self.ps2mdp_path: str  = ""
        # Limit chdman cores aggressively — LZMA compression is extremely
        # memory-hungry per core (~600 MB each for DVD images).  Using too many
        # cores on a system with limited RAM causes OOM/freeze, especially in
        # WSL2 which shares memory with the Windows host.
        _cpu = os.cpu_count() or 2
        self.chd_cores: int    = max(1, min(2, _cpu // 4))
        # Serialise concurrent chdman invocations (e.g. auto-CHD during
        # parallel downloads) so only one runs at a time.
        self._chd_sem          = threading.Semaphore(1)

    # ── Binary discovery ──────────────────────────────────────────────────────

    @staticmethod
    def find_chdman() -> str:
        """Locate chdman. Returns full path string or '' if not found."""
        local_candidates = [
            _TOOLS_DIR / "chdman",
            _TOOLS_DIR / "chdman.exe",
            _SCRIPT_DIR / "chdman",
            _SCRIPT_DIR / "chdman.exe",
        ]
        for p in local_candidates:
            if p.is_file() and os.access(p, os.X_OK):
                return str(p)
        return shutil.which("chdman") or ""

    @staticmethod
    def find_ps2mdp() -> str:
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

    def refresh_chdman(self) -> None:
        """Re-resolve chdman path and cache it on self.chdman_path."""
        self.chdman_path = self.find_chdman()

    def refresh_ps2mdp(self) -> None:
        """Re-resolve ps2_master path and cache it on self.ps2mdp_path."""
        self.ps2mdp_path = self.find_ps2mdp()

    # ── chdman setup ──────────────────────────────────────────────────────────

    def setup_chdman_auto(self) -> None:
        """Try to install chdman via the system package manager."""
        self._post(SystemLog("chdman Setup: Checking for existing installation..."))
        path = self.find_chdman()
        if path:
            self.chdman_path = path
            self._post(SystemLog(f"chdman already available at: [bold]{path}[/bold]"))
            return

        self._post(SystemLog("chdman Setup: Attempting package-manager install..."))
        for label, cmd in _PKG_INSTALL_CMDS:
            mgr = shutil.which(cmd[0])
            if not mgr:
                continue
            self._post(SystemLog(f"chdman Setup: Trying [bold]{label}[/bold]…"))
            try:
                result = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
                if result.returncode == 0:
                    path = self.find_chdman()
                    if path:
                        self.chdman_path = path
                        self._post(SystemLog(
                            f"[bold green]chdman installed successfully![/bold green] "
                            f"Path: [bold]{path}[/bold]"
                        ))
                        return
                else:
                    self._post(SystemLog(
                        f"chdman Setup: {label} returned non-zero "
                        f"(may need sudo). Output: {result.stderr[:120]}", True
                    ))
            except (subprocess.TimeoutExpired, OSError) as e:
                self._post(SystemLog(f"chdman Setup: {label} failed — {e}", True))

        self._post(SystemLog(
            "[bold yellow]chdman auto-install failed.[/bold yellow] "
            "Manual options:\n"
            "  • Linux (Debian/Ubuntu):  sudo apt install mame-tools\n"
            "  • Linux (Arch):           sudo pacman -S mame-tools\n"
            "  • Linux (Fedora):         sudo dnf install mame-tools\n"
            "  • macOS (Homebrew):       brew install rom-tools\n"
            "  • Windows: download MAME tools from https://www.mamedev.org/release.html\n"
            "Place chdman(.exe) in the myrient_data/tools/ folder to use it without installing."
        ))

    # ── PS2 Master Disc Patcher setup ─────────────────────────────────────────

    def setup_ps2mdp_auto(self) -> None:
        """Download and verify ps2_master from the PSDB v1.0.5 x86_64 release zip."""
        self._post(SystemLog("PS2 Patcher Setup: Checking for existing installation..."))
        path = self.find_ps2mdp()
        if path:
            self.ps2mdp_path = path
            self._post(SystemLog(f"ps2_master already available at: [bold]{path}[/bold]"))
            return

        self._post(SystemLog(
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

            # ── SHA-256 integrity check ───────────────────────────────────────
            self._post(SystemLog("PS2 Patcher Setup: Verifying download integrity…"))
            actual_sha256 = _sha256_file(tmp_zip)
            if actual_sha256 != _PS2MDP_RELEASE_SHA256:
                self._post(SystemLog(
                    f"[bold red]PS2 Patcher Setup: SHA-256 mismatch — aborting.[/bold red]\n"
                    f"  Pinned version : {_PS2MDP_RELEASE_VERSION}\n"
                    f"  Expected SHA-256: {_PS2MDP_RELEASE_SHA256}\n"
                    f"  Got SHA-256:      {actual_sha256}\n"
                    "This usually means the release asset was updated upstream. "
                    "To upgrade: set _PS2MDP_RELEASE_VERSION to the new tag, update "
                    "_PS2MDP_RELEASE_URL and _PS2MDP_RELEASE_SHA256 at the top of the source "
                    "(run 'sha256sum' on the new zip to get the correct digest).",
                    True,
                ))
                return

            # ── Extract ps2_master binary from bin/ in the release zip ────────
            extracted_binary = False
            with _zf.ZipFile(tmp_zip, "r") as zf:
                all_members = zf.namelist()
                self._post(SystemLog(
                    f"PS2 Patcher Setup: Zip has {len(all_members)} entries. First 60:\n  " +
                    "\n  ".join(all_members[:60]) +
                    ("\n  …" if len(all_members) > 60 else "")
                ))
                for member in all_members:
                    if member.endswith("/"):
                        continue
                    base  = Path(member).name
                    in_bin = "/bin/" in member
                    if base == _PS2MDP_BINARY_NAME and in_bin and not extracted_binary:
                        dest = _TOOLS_DIR / _PS2MDP_BINARY_NAME
                        with zf.open(member) as src, open(dest, "wb") as dst:
                            shutil.copyfileobj(src, dst)
                        dest.chmod(dest.stat().st_mode | 0o111)
                        extracted_binary = True
                        self._post(SystemLog(
                            f"PS2 Patcher Setup: Extracted [bold]{base}[/bold] "
                            f"from [dim]{member}[/dim] → {dest}"
                        ))
                        break

            if not extracted_binary:
                self._post(SystemLog(
                    "[bold red]PS2 Patcher Setup: binary not found in release zip.[/bold red]\n"
                    "Check the zip contents log above. Manual install:\n"
                    f"  1. Download: {_PS2MDP_RELEASE_URL}\n"
                    f"  2. Extract 'bin/{_PS2MDP_BINARY_NAME}' to myrient_data/tools/\n"
                    f"  3. chmod +x myrient_data/tools/{_PS2MDP_BINARY_NAME}",
                    True,
                ))
                return

            path = self.find_ps2mdp()
            if path:
                self.ps2mdp_path = path
                self._post(SystemLog(
                    f"[bold green]PS2 Master Disc Patcher ready![/bold green] "
                    f"Path: [bold]{path}[/bold]"
                ))
            else:
                self._post(SystemLog(
                    "[bold red]Setup finished but binary not found — "
                    "extraction may have failed.[/bold red]", True
                ))

        except Exception as err:
            self._post(SystemLog(f"[bold red]PS2 Patcher Setup failed:[/bold red] {err}", True))
        finally:
            try:
                tmp_zip.unlink(missing_ok=True)
            except OSError:
                pass

    # ── CHD conversion ────────────────────────────────────────────────────────

    def convert_to_chd(self, dest_dir: Path, silent: bool = False,
                        cancel: threading.Event | None = None) -> tuple[int, int]:
        """Convert disc images in *dest_dir* to CHD format.

        *cancel* overrides ``self.cancel_flag`` when provided, allowing library
        operations and download auto-CHD to use separate cancellation signals.

        Returns ``(converted, failed)`` counts.
        Delegates to the same logic previously inlined in MyrientTUI._convert_to_chd.
        """
        _cancel = cancel or self.cancel_flag
        if not self.chdman_path:
            found = shutil.which("chdman")
            if found:
                self.chdman_path = found
        chdman   = self.chdman_path or "chdman"
        converted = failed = 0

        conversion_targets: list[Path] = []
        # Collect .cue files first — when a .cue exists, its referenced .bin
        # files must NOT be converted independently (chdman createcd reads the
        # .cue and processes all referenced tracks).  Build a set of .bin paths
        # claimed by .cue sheets so we can skip them.
        cue_claimed_bins: set[Path] = set()
        cue_files: list[Path] = []
        for f in dest_dir.rglob("*.cue"):
            if not f.with_suffix(".chd").exists():
                cue_files.append(f)
                try:
                    with open(f, "r", encoding="utf-8", errors="ignore") as cf:
                        for bin_name in CUE_BIN_REGEX.findall(cf.read()):
                            cue_claimed_bins.add(f.parent / bin_name)
                except OSError:
                    pass
        conversion_targets.extend(cue_files)
        # Now collect remaining source files, skipping .cue (already added)
        # and any .bin that is referenced by a .cue sheet.
        for ext in _CHD_CMD_MAP:
            if ext == ".cue":
                continue
            for f in dest_dir.rglob(f"*{ext}"):
                if f in cue_claimed_bins:
                    continue
                if not f.with_suffix(".chd").exists():
                    conversion_targets.append(f)

        for file_path in conversion_targets:
            if _cancel.is_set():
                return converted, failed

            ext_lower   = file_path.suffix.lower()
            subcommands = _CHD_CMD_MAP.get(ext_lower, ["createcd"])
            chd_output  = file_path.with_suffix(".chd")
            succeeded   = False

            for subcmd in subcommands:
                if _cancel.is_set():
                    return converted, failed
                self._chd_sem.acquire()
                try:
                    proc = subprocess.Popen(
                        [chdman, subcmd,
                         "-i", str(file_path),
                         "-o", str(chd_output),
                         "--numprocessors", str(self.chd_cores)],
                        stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
                        **_LOW_PRIO_POPEN,
                    )
                    self._reg_proc(proc)

                    stderr_chunks: list[bytes] = []
                    _chd_progress_pct: list[float] = [0.0]

                    def _read_stderr(p: subprocess.Popen = proc,
                                     buf: list[bytes] = stderr_chunks,
                                     pct: list[float] = _chd_progress_pct) -> None:
                        try:
                            for chunk in iter(lambda: p.stderr.read(4096), b""):
                                buf.append(chunk)
                                m = _CHD_PCT_RE.search(chunk)
                                if m:
                                    pct[0] = float(m.group(1))
                        except OSError:
                            pass

                    stderr_thread = threading.Thread(target=_read_stderr, daemon=True)
                    stderr_thread.start()

                    deadline = time.monotonic() + _CHD_TIMEOUT
                    while proc.poll() is None:
                        if _cancel.is_set():
                            proc.kill()
                            proc.wait()
                            stderr_thread.join(timeout=2)
                            self._unreg_proc(proc)
                            return converted, failed
                        if time.monotonic() > deadline:
                            proc.kill()
                            proc.wait()
                            stderr_thread.join(timeout=2)
                            self._unreg_proc(proc)
                            raise subprocess.TimeoutExpired(proc.args, _CHD_TIMEOUT)
                        # Report CHD conversion progress
                        if not silent and _chd_progress_pct[0] > 0:
                            self._post(LibraryProgress(
                                "CHD convert",
                                f"{file_path.name} ({_chd_progress_pct[0]:.0f}%)",
                                int(_chd_progress_pct[0]),
                                100,
                            ))
                        time.sleep(0.5)

                    stderr_thread.join(timeout=5)
                    stderr_bytes = b"".join(stderr_chunks)
                    self._unreg_proc(proc)

                    if proc.returncode == 0:
                        succeeded = True
                        break
                    else:
                        if chd_output.exists():
                            try:
                                chd_output.unlink()
                            except OSError:
                                pass
                        if not silent:
                            err_snippet = (stderr_bytes.decode("utf-8", errors="replace")
                                           .strip()[:200])
                            self._post(SystemLog(
                                f"chdman {subcmd} failed for {file_path.name}: {err_snippet}",
                                True
                            ))
                except subprocess.TimeoutExpired:
                    if not silent:
                        self._post(SystemLog(
                            f"chdman timed out converting {file_path.name} — killed.", True
                        ))
                    if chd_output.exists():
                        try:
                            chd_output.unlink()
                        except OSError:
                            pass
                    break
                except Exception as e:
                    self._post(SystemLog(f"chdman error ({file_path.name}): {e}", True))
                    break
                finally:
                    self._chd_sem.release()

            if not succeeded:
                failed += 1
                if not silent:
                    self._post(SystemLog(
                        f"CHD conversion failed: {file_path.name} — "
                        "not a supported disc image format.", True
                    ))
                continue

            converted += 1

            # ── Post-conversion cleanup ──────────────────────────────────────
            # Preserve the original .cue — it is tiny and its byte-exact content
            # (including CRLF line endings and track naming) is what the Redump DAT
            # expects.  chdman extractcd regenerates a .cue with different formatting,
            # so keeping the original is the only way to guarantee a SHA1 match on
            # round-trip.  Only the .bin track files are deleted.
            if ext_lower == ".cue":
                try:
                    with open(file_path, "r", encoding="utf-8", errors="ignore") as cf:
                        bins = CUE_BIN_REGEX.findall(cf.read())
                    with self.chd_lock:
                        for bin_name in bins:
                            bin_path = file_path.parent / bin_name
                            if bin_path.exists():
                                try:
                                    bin_path.unlink()
                                except OSError as ose:
                                    logging.error("CHD cleanup: could not delete %s: %s", bin_path, ose)
                                    self._post(SystemLog(
                                        f"CHD cleanup: could not delete {bin_path.name}: {ose}", True
                                    ))
                except Exception as e:
                    logging.debug("CHD cue sheet cleanup failed: %s", e)
            elif ext_lower == ".gdi":
                gdi_dir = file_path.parent
                for track_file in list(gdi_dir.glob("*.raw")) + list(gdi_dir.glob("*.bin")):
                    try:
                        track_file.unlink()
                    except OSError as ose:
                        logging.error("CHD cleanup: could not delete track %s: %s", track_file, ose)
                        self._post(SystemLog(
                            f"CHD cleanup: could not delete {track_file.name}: {ose}", True
                        ))
                try:
                    file_path.unlink()
                except OSError as ose:
                    logging.error("CHD cleanup: could not delete gdi %s: %s", file_path, ose)
                    self._post(SystemLog(
                        f"CHD cleanup: could not delete {file_path.name}: {ose}", True
                    ))
            else:
                try:
                    file_path.unlink()
                except OSError as ose:
                    logging.error("CHD cleanup: could not delete source %s: %s", file_path, ose)
                    self._post(SystemLog(
                        f"CHD cleanup: could not delete {file_path.name}: {ose}", True
                    ))

        return converted, failed


# ─────────────────────────────────────────────────────────────────────────────
# Pane widget classes — purely for compose() organisation.
# All event handling, state, and workers remain on MyrientTUI.
# Messages bubble up through the DOM normally; query_one() searches all
# descendants, so nothing changes for the handler layer.
# ─────────────────────────────────────────────────────────────────────────────

class BrowsePane(Vertical):
    """Console browser + game selection."""

    def compose(self) -> ComposeResult:
        with Horizontal(id="browse-layout"):
            with Vertical(id="browse-left"):
                with Horizontal(id="browse-console-header"):
                    yield Label("Consoles", classes="section-header")
                    yield Label("", id="console-count")
                yield Input(placeholder="  filter consoles…", id="search-consoles", classes="search-bar")
                yield ListView(id="console-list")
            with Vertical(id="browse-right"):
                yield Label("", id="breadcrumb")
                with Horizontal(id="browse-search-bar"):
                    yield GameSearchInput(placeholder="  search games…", id="search-games", classes="search-bar")
                    yield Button("Global", id="btn-toggle-global", classes="browse-global-btn")
                with Horizontal(id="browse-toolbar"):
                    yield Button("Queue Selected", id="btn-add-queue", variant="success")
                    yield Button("Select All", id="btn-select-all")
                    yield Button("Refresh", id="btn-refresh-games")
                    yield Label("", id="game-selection-count")
                yield DataTable(id="game-list", cursor_type="row", zebra_stripes=False)
                yield Label(
                    "Select a console to browse games",
                    id="browse-empty-state",
                )


class DownloadsPane(Vertical):
    """Queue management + active download progress."""

    def compose(self) -> ComposeResult:
        with Horizontal(id="downloads-layout"):
            with Vertical(id="queue-panel"):
                yield Label("Queue", classes="section-header")
                with Vertical(classes="queue-toolbar"):
                    yield Select([], id="queue-select", prompt="active profile…")
                    yield Input(placeholder="new profile name…", id="input-new-queue")
                    with Horizontal(classes="btn-row"):
                        yield Button("Create", id="btn-create-queue", variant="success")
                        yield Button("Delete", id="btn-delete-queue", variant="error")
                yield DataTable(id="queue-table")
                with Horizontal(classes="queue-controls"):
                    yield Button("▲", id="btn-queue-up", classes="reorder-btn")
                    yield Button("▼", id="btn-queue-down", classes="reorder-btn")
                    yield Button("Remove", id="btn-remove-items", variant="warning")
                    yield Button("▶ Start", id="btn-start-dl", variant="primary")
                    yield Button("■ Stop", id="btn-pause-dl", variant="error")
                with Horizontal(classes="btn-row"):
                    yield Label("[dim]Schedule:[/dim]", classes="setting-label")
                    yield Input(placeholder="HH:MM (empty=now)", id="input-schedule-time", classes="schedule-input")
                    yield Button("⏱ Schedule", id="btn-schedule-dl")
                with Horizontal(classes="btn-row"):
                    yield Button("Export", id="btn-export-queue", variant="default")
                    yield Button("Import", id="btn-import-queue", variant="default")
                with Collapsible(title="Queue Settings", collapsed=True, id="queue-settings-collapsible"):
                    yield Label("[dim]Per-queue speed limit (MB/s, 0=unlimited)[/dim]")
                    yield Input(placeholder="0", id="input-queue-speed-limit")
                    yield Label("[dim]Max concurrent downloads (blank=use global)[/dim]")
                    yield Input(placeholder="", id="input-queue-max-concurrent")
                    yield Button("Apply to Queue", id="btn-apply-queue-settings")
                yield Label(
                    "[dim]Ctrl+J[/dim] jump to console  [dim]?[/dim] help",
                    classes="hint-bar",
                )

            with Vertical(id="progress-panel"):
                yield Label("▸ DOWNLOAD PROGRESS", id="lbl-global-progress")
                yield ProgressBar(id="global-progress", show_eta=True)
                with VerticalScroll(id="progress-area"):
                    with Container(id="progress-grid"):
                        pass
                with Collapsible(title="Download History", collapsed=True, id="history-collapsible"):
                    yield DataTable(id="history-table")
                    yield Button("Clear History", id="btn-clear-history", variant="warning")


class LibraryPane(Vertical):
    """Library tree view + contextual detail panel."""

    def compose(self) -> ComposeResult:
        with Vertical(id="lib-tab-wrapper"):
            # ── Header: merged summary + compact tree controls ────────────
            with Horizontal(id="lib-header-bar"):
                yield Label("", id="lib-summary-bar")
                yield Label(" ▸ ", id="btn-lib-expand-all", classes="lib-hdr-btn")
                yield Label(" ▾ ", id="btn-lib-collapse-all", classes="lib-hdr-btn")
                yield Label(" ✕ ", id="btn-lib-delete", classes="lib-hdr-btn lib-hdr-del")
            # ── Contextual toolbar (horizontal, above tree) ──────────────
            with Horizontal(id="lib-toolbar"):
                yield Button("Verify DAT", id="btn-lib-dat-audit", classes="lib-tb-btn")
                yield Button("Convert CHD", id="btn-lib-convert", classes="lib-tb-btn")
                yield Button("CHD→Orig", id="btn-lib-chd-to-orig", classes="lib-tb-btn")
                yield Button("Organize", id="btn-lib-organize", classes="lib-tb-btn")
                yield Button("Refresh", id="btn-lib-refresh-status", classes="lib-tb-btn")
                yield Button("PS2 Patch", id="btn-ps2-md-patch", classes="lib-tb-btn")
                yield Button("Requeue ✗", id="btn-requeue-failed", classes="lib-tb-btn")
                yield Button("Requeue ~", id="btn-requeue-corrupted", classes="lib-tb-btn")
                yield Button("Requeue Console", id="btn-requeue-console", classes="lib-tb-btn")
                yield Label("Dry Run", id="lbl-dat-dry-run", classes="lib-tb-label --lib-hidden")
                yield Switch(value=False, id="sw-dat-dry-run", classes="--lib-hidden")
            # ── Tree (full width) ─────────────────────────────────────────
            yield Tree("Library", id="lib-tree")
            # ── Status bar ────────────────────────────────────────────────
            with Container(id="lib-status-bar"):
                yield Label("Idle", id="lib-status-label")
                yield ProgressBar(id="lib-progress-bar", show_eta=True)


class SettingsPane(Vertical):
    """Settings organised into tabbed sections."""

    def compose(self) -> ComposeResult:
        with TabbedContent(id="settings-tabs"):
            with TabPane("Engine", id="tab-engine"):
                with VerticalScroll():
                    yield Label("Library root path", classes="setting-label")
                    yield Input(id="set-lib-path")
                    yield Label("Max concurrent downloads  [dim](1–10)[/dim]", classes="setting-label")
                    yield Input(id="set-threads")
                    yield Label("Global speed limit per download  [dim](MB/s, 0=unlimited)[/dim]", classes="setting-label")
                    yield Input(id="set-speed-limit")
                    yield Label("DAT cache TTL  [dim](hours, 0=always refresh)[/dim]", classes="setting-label")
                    yield Input(id="set-dat-ttl")
                    yield Rule()
                    yield Label("Auto-convert to CHD after download", classes="setting-label")
                    yield Switch(id="set-auto-chd")
                    yield Label("Watch library for changes  [dim](requires watchdog)[/dim]", classes="setting-label")
                    yield Switch(id="set-watch-library")
                    yield Label("Desktop notification on batch complete", classes="setting-label")
                    yield Switch(id="set-notify-batch")
                    yield Rule()
                    yield Button("▸ Save Settings", id="btn-save-settings", variant="success")
            with TabPane("Filters", id="tab-filters"):
                with VerticalScroll():
                    yield Label("Include Filter", classes="section-header")
                    yield Label("[dim]Show only matching regions (empty = show all)[/dim]", classes="setting-label")
                    yield DataTable(id="set-include", classes="filter-table")
                    yield Label("[dim]Additional include regex[/dim]", classes="setting-label")
                    yield Input(placeholder="e.g. (USA|World).*Disc 1", id="set-custom-include")
                    yield Label("Exclude Filter", classes="section-header")
                    yield Label("[dim]Hide games matching these tags[/dim]", classes="setting-label")
                    yield DataTable(id="set-exclude", classes="filter-table")
                    yield Label("[dim]Additional exclude regex[/dim]", classes="setting-label")
                    yield Input(placeholder="e.g. Demo|Sample|Promo", id="set-custom-exclude")
                    yield Rule()
                    yield Button("✕ Clear Filters", id="btn-clear-filters", variant="warning", classes="ops-btn")
                    yield Rule()
                    yield Label("Filter Presets", classes="section-header")
                    yield Label("[dim]Save/load current filter combination as a named preset[/dim]", classes="setting-label")
                    yield Input(placeholder="preset name…", id="input-preset-name")
                    with Horizontal(classes="preset-row"):
                        yield Button("Save Preset", id="btn-save-preset", variant="success")
                        yield Button("Load Preset", id="btn-load-preset", variant="primary")
                        yield Button("Del Preset", id="btn-del-preset", variant="error")
                    yield Select([], id="preset-select", prompt="choose preset…")
            with TabPane("Tools", id="tab-tools"):
                with VerticalScroll():
                    yield Label("[dim]Install or locate conversion / patching tools[/dim]", classes="setting-label")
                    yield Button("Setup chdman", id="btn-setup-chdman", classes="ops-btn")
                    yield Button("Setup PS2 Patcher", id="btn-setup-ps2mdp", classes="ops-btn")
                    yield Rule()
                    yield Label("[dim]Pre-cache all console game lists for faster browsing[/dim]", classes="setting-label")
                    yield Button("Prefetch All Consoles", id="btn-prefetch-consoles", classes="ops-btn")
                    yield Rule()
                    yield Label("Batch Queue Import", classes="section-header")
                    yield Label("[dim]Import game URLs or names from a text file (one per line)[/dim]", classes="setting-label")
                    yield Input(placeholder="path to .txt file…", id="input-batch-import-path")
                    yield Button("Import from File", id="btn-batch-import", classes="ops-btn")


class LogsPane(Vertical):
    """System log + session file browser."""

    def compose(self) -> ComposeResult:
        with Vertical(id="logs-layout"):
            with Horizontal(id="log-toolbar"):
                yield Button("All", id="log-filter-all", classes="log-filter-btn")
                yield Button("Errors", id="log-filter-err", classes="log-filter-btn")
                yield Input(placeholder="  search logs…", id="log-search")
                yield Button("↺ Sessions", id="btn-refresh-session-logs")
            yield RichLog(id="sys-log", markup=True, wrap=True, max_lines=2000)
            yield Rule(id="sessions-divider")
            with Horizontal(id="sessions-layout"):
                yield ListView(id="session-log-list")
                yield RichLog(id="session-log-view", markup=False, wrap=True, max_lines=5000)


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
        width: 1fr;
        min-width: 28;
        max-width: 55;
        height: 1fr;
        background: #080c12;
        border-right: solid #1c2333;
        padding: 1 1 1 2;
        layout: vertical;
    }
    #browse-console-header {
        height: 1;
        layout: horizontal;
        margin-bottom: 1;
    }
    #browse-console-header .section-header { width: 1fr; margin-bottom: 0; border-bottom: none; }
    #console-count { width: auto; height: 1; color: #3d4451; content-align: right middle; }
    #browse-right {
        width: 2fr;
        height: 1fr;
        padding: 1 2;
        layout: vertical;
    }
    #breadcrumb { height: 1; color: #3d4451; margin-bottom: 0; }
    #browse-search-bar { height: auto; layout: horizontal; align: left middle; }
    #browse-search-bar .search-bar { width: 1fr; }
    .browse-global-btn { width: auto; min-width: 10; height: 3; margin: 0 0 1 1; }
    #browse-toolbar {
        height: auto;
        layout: horizontal;
        align: left middle;
        margin-bottom: 1;
    }
    #browse-toolbar Button { width: auto; min-width: 8; margin: 0 1 0 0; height: 3; }
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
        margin: 0 0 0 1;
        height: 3;
        content-align: left middle;
    }
    #browse-empty-state {
        height: 1fr;
        width: 1fr;
        content-align: center middle;
        color: #3d4451;
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
    #history-collapsible { height: auto; max-height: 16; margin-top: 1; }
    #history-table       { height: auto; max-height: 12; border: solid #1c2333; background: #0d1117; }
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
    #lib-header-bar {
        height: 1;
        layout: horizontal;
        padding: 0 1;
        background: #080c12;
    }
    #lib-summary-bar {
        width: 1fr;
        height: 1;
        color: #3d4451;
        content-align: left middle;
    }
    .lib-hdr-btn { width: 5; height: 1; color: #606878; content-align: center middle; background: #161b22; }
    .lib-hdr-btn:hover { color: #c9d1d9; background: #21262d; }
    .lib-hdr-del { color: #f85149; }
    .lib-hdr-del:hover { color: #ff7b72; background: #21262d; }
    #lib-toolbar {
        height: auto;
        min-height: 3;
        layout: horizontal;
        content-align: left middle;
        padding: 0 1;
        background: #080c12;
        overflow: hidden auto;
    }
    .lib-tb-btn { width: auto; min-width: 8; margin: 0 1 0 0; height: 3; }
    .lib-tb-label { height: 3; content-align: left middle; margin: 0 1 0 0; color: #9aa0aa; }
    .--lib-hidden { display: none; }
    #lib-tree {
        height: 1fr;
        border: solid #1c2333;
        background: #0d1117;
        margin: 0 1 0 1;
    }
    #lib-tree > .tree--guides { color: #1c2333; }
    #lib-tree > .tree--cursor { background: #0f1520; }
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

    /* ═══════════════════════════════════════════════════════════════════════
       LIGHT THEME OVERRIDES
       Activated when user toggles theme with Ctrl+D
       Screen.-light-mode is the Textual CSS class added in light mode.
       ═══════════════════════════════════════════════════════════════════════ */
    Screen.-light-mode { background: #ffffff; color: #1f2328; }
    Screen.-light-mode Header { background: #f6f8fa; color: #656d76; border-bottom: solid #d0d7de; }
    Screen.-light-mode Footer { background: #f6f8fa; color: #656d76; border-top: solid #d0d7de; }
    Screen.-light-mode #nav-sidebar { background: #f6f8fa; border-right: solid #d0d7de; }
    Screen.-light-mode #nav-logo { color: #9a6700; border-bottom: solid #d0d7de; }
    Screen.-light-mode .nav-btn { color: #656d76; }
    Screen.-light-mode .nav-btn:hover { background: #ffffff; color: #1f2328; }
    Screen.-light-mode .nav-btn:focus { background: #ffffff; color: #1f2328; border: solid #d0d7de; }
    Screen.-light-mode .nav-btn.--nav-active { background: #ffffff; color: #9a6700; border-left: thick #9a6700; }
    Screen.-light-mode #nav-status { border-top: solid #d0d7de; color: #656d76; }
    Screen.-light-mode #content-area { background: #ffffff; }
    Screen.-light-mode #global-statusbar { background: #f6f8fa; border-top: solid #d0d7de; }
    Screen.-light-mode #gs-engine { color: #656d76; }
    Screen.-light-mode #gs-speed { color: #1a7f37; }
    Screen.-light-mode #gs-queue { color: #656d76; }
    Screen.-light-mode .section-header { color: #656d76; border-bottom: solid #d0d7de; }
    Screen.-light-mode .search-bar { background: #f6f8fa; color: #1f2328; border: solid #d0d7de; }
    Screen.-light-mode .search-bar:focus { border: solid #0969da; }
    Screen.-light-mode #breadcrumb { color: #656d76; background: #f6f8fa; border-bottom: solid #d0d7de; }
    Screen.-light-mode DataTable { background: #ffffff; color: #1f2328; }
    Screen.-light-mode DataTable > .datatable--header { background: #f6f8fa; color: #656d76; }
    Screen.-light-mode DataTable > .datatable--cursor { background: #ddf4ff; color: #1f2328; }
    Screen.-light-mode .console-list-container { background: #f6f8fa; border-right: solid #d0d7de; }
    Screen.-light-mode ListView { background: #f6f8fa; }
    Screen.-light-mode ListView > ListItem { color: #656d76; }
    Screen.-light-mode ListView > ListItem.-highlight { background: #ddf4ff; }
    Screen.-light-mode Tree { background: #ffffff; color: #1f2328; }
    Screen.-light-mode Tree > .tree--cursor { background: #ddf4ff; color: #1f2328; }
    Screen.-light-mode #lib-header-bar { background: #f6f8fa; border-bottom: solid #d0d7de; }
    Screen.-light-mode #lib-toolbar { background: #f6f8fa; }
    Screen.-light-mode #lib-tree { background: #ffffff; }
    Screen.-light-mode #lib-tree > .tree--cursor { background: #ddf4ff; color: #1f2328; }
    Screen.-light-mode RichLog { background: #ffffff; color: #1f2328; }
    Screen.-light-mode Input { background: #f6f8fa; color: #1f2328; border: solid #d0d7de; }
    Screen.-light-mode Input:focus { border: solid #0969da; }
    Screen.-light-mode Button { background: #f6f8fa; color: #1f2328; border: solid #d0d7de; }
    Screen.-light-mode Button:hover { background: #eaeef2; }
    Screen.-light-mode ProgressBar Bar { background: #eaeef2; }
    Screen.-light-mode ProgressBar Bar > .bar--bar { color: #0969da; }
    Screen.-light-mode Collapsible { background: #ffffff; }
    Screen.-light-mode CollapsibleTitle { color: #656d76; }
    Screen.-light-mode Select { background: #f6f8fa; color: #1f2328; }
    Screen.-light-mode Switch { background: #eaeef2; }
    Screen.-light-mode TabbedContent ContentSwitcher { background: #ffffff; }
    Screen.-light-mode TabbedContent Tab { color: #656d76; }
    Screen.-light-mode TabbedContent Tab.-active { color: #0969da; }
    Screen.-light-mode Rule { color: #d0d7de; }
    Screen.-light-mode #queue-table { background: #ffffff; }
    Screen.-light-mode #help-modal-content { background: #ffffff; }
    Screen.-light-mode #help-title { color: #9a6700; }
    Screen.-light-mode .help-row { color: #1f2328; }
    Screen.-light-mode .help-key { color: #0969da; }
    """

    BINDINGS = [
        ("ctrl+q", "quit",           "Quit"),
        ("ctrl+d", "toggle_dark",    "Theme"),
        ("ctrl+r", "refresh_browser","Refresh"),
        ("ctrl+j", "jump_to_console","Jump→Browser"),
        ("question_mark", "show_help", "Help"),
        ("1", "nav_pane('pane-browse')",    "Browse"),
        ("2", "nav_pane('pane-downloads')", "Downloads"),
        ("3", "nav_pane('pane-library')",   "Library"),
        ("4", "nav_pane('pane-settings')",  "Settings"),
        ("5", "nav_pane('pane-logs')",      "Logs"),
    ]

    def __init__(self):
        super().__init__()
        self.state = ConfigManager(CONFIG_FILE)
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

    @property
    def engine_running(self) -> bool:
        """Backward-compatible check — True when the download engine is active."""
        return self._engine_state in (EngineState.RUNNING, EngineState.PAUSING)

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

        # Game browser table — virtual rendering, no header
        game_table = self.query_one("#game-list", DataTable)
        game_table.add_column("", key="sel", width=3)
        game_table.add_column("Game", key="name")
        game_table.add_column("Size", key="size", width=10)
        game_table.show_header = False
        # Start with empty state visible, game view hidden
        self._show_browse_game_view(False)
        self._browse_global_mode = False

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

        # Initial toolbar state — show root-level operations
        self._update_lib_toolbar(None)

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
        """Adjust progress grid columns based on terminal width."""
        try:
            grid = self.query_one("#progress-grid", Container)
            cols = 2 if self.size.width >= 120 else 1
            grid.styles.grid_size_columns = cols
        except Exception as e:
            logging.debug("Resize progress grid failed: %s", e)

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
            t.append("Redump", style="#3d4451")
            t.append("  ›  ", style="dim #1c2333")
            t.append(console_name, style="#9aa0aa")
            if game_count > 0:
                t.append(f"  ({game_count:,})", style="dim #3d4451")
            lbl.update(t)
        except Exception as e:
            logging.debug("Update breadcrumb failed: %s", e)

    def _show_browse_game_view(self, show: bool) -> None:
        """Toggle between the game table/toolbar and the empty-state placeholder."""
        try:
            self.query_one("#game-list", DataTable).display = show
            self.query_one("#browse-toolbar").display = show
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
        def _game_label(name: str, status: str, has_chd: bool = False) -> Text:
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
            if has_chd:
                t.append(" │ ", style="dim #00ffbb")
                t.append("CHD", style="dim #58a6ff")
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

        try:
            tree = self.query_one("#lib-tree", Tree)
            tree.clear()
            library = message.library_path
            root_name = library.name if library.exists() else "Library"
            root_label = Text(root_name, style=f"bold {_TREE_AMBER}", no_wrap=True)
            tree.root.label = root_label

            for console_name, (console_path, games) in message.structure.items():
                counts = Counter(s for _, s, _ in games)
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
                # C6+A2: Group multi-disc games into inline labels
                # Partition into disc entries (keyed by base name) and singles
                # disc_groups values: (game_dir, status, disc_label_str, has_chd)
                disc_groups: dict[str, list[tuple[Path, str, str, bool]]] = {}
                singles: dict[str, tuple[Path, str, bool]] = {}
                for game_dir, status, has_chd in games:
                    m = DISC_REGEX.search(game_dir.name)
                    if m:
                        base = DISC_REGEX.sub('', game_dir.name).strip()
                        disc_label = m.group(0).strip()  # e.g. "(Disc 1)"
                        disc_groups.setdefault(base, []).append((game_dir, status, disc_label, has_chd))
                    else:
                        singles[game_dir.name] = (game_dir, status, has_chd)

                # Build unified sorted list: (sort_key, label, data_path)
                tree_entries: list[tuple[str, Text, Path]] = []

                for name, (game_dir, status, has_chd) in singles.items():
                    if name in disc_groups:
                        continue  # rendered as disc group instead
                    tree_entries.append((name.lower(), _game_label(name, status, has_chd), game_dir))

                for base_name, discs in disc_groups.items():
                    discs.sort(key=lambda d: d[2])  # sort by disc label
                    t = Text(no_wrap=True, overflow="ellipsis")
                    # Aggregate status for leading icon + game name
                    statuses = {s for _, s, _, _ in discs}
                    if statuses == {"validated"}:
                        t.append("✓ ", style=_TREE_GREEN)
                        t.append(base_name, style=_TREE_GREEN)
                    elif "corrupted" in statuses:
                        t.append("✗ ", style=_TREE_RED)
                        t.append(base_name, style=_TREE_RED)
                    else:
                        t.append("~ ", style=_TREE_YELLOW)
                        t.append(base_name, style=_TREE_YELLOW)
                    # Dim pipe separator to visually divide name from disc labels
                    t.append(" │ ", style="dim #00ffbb")
                    # CHD indicator if any disc is in CHD format
                    any_chd = any(c for _, _, _, c in discs)
                    if any_chd:
                        t.append("CHD ", style="dim #58a6ff")
                    # Per-disc status: dim grey number + small colored icon
                    for i, (_, st, dlbl, _) in enumerate(discs):
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
                    tree_entries.append((base_name.lower(), t, group_path))

                # Render all entries in alphabetical order
                tree_entries.sort(key=lambda e: e[0])
                for _, label, data_path in tree_entries:
                    console_node.add_leaf(label, data=data_path)

            if not message.structure:
                no_games = Text("No consoles found — check library path in Settings", style=_TREE_DIM)
                tree.root.add_leaf(no_games)

            tree.root.expand()
            self.query_one("#lib-status-label", Label).update("[dim]Scan complete[/dim]")
            self.query_one("#lib-progress-bar", ProgressBar).display = False

            # Update merged summary bar
            try:
                all_statuses = [s for _, games in message.structure.values() for _, s, _ in games]
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

    # ── Library detail panel — contextual toolbar + file detail view ─────

    def on_tree_node_highlighted(self, event: Tree.NodeHighlighted) -> None:
        """Update toolbar and status bar when the library tree cursor moves."""
        if event.control.id != "lib-tree":
            return
        self._update_lib_toolbar(event.node)
        self._update_lib_selection_status(event.node)

    def on_click(self, event: events.Click) -> None:
        """Handle clicks on header label controls."""
        widget = event.widget
        if not isinstance(widget, Label):
            return
        wid = widget.id
        if wid == "btn-lib-expand-all":
            self._lib_expand_all()
        elif wid == "btn-lib-collapse-all":
            self._lib_collapse_all()
        elif wid == "btn-lib-delete":
            self._lib_delete_selected()

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
            "btn-lib-organize":       {"root"},
            "btn-lib-refresh-status": {"root"},
            "btn-ps2-md-patch":       {"console", "game"},
            "btn-requeue-failed":     {"root"},
            "btn-requeue-corrupted":  {"root"},
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
        # Dry-run switch visible only alongside DAT audit
        show_dry = level in _vis.get("btn-lib-dat-audit", set())
        for wid in ("sw-dat-dry-run", "lbl-dat-dry-run"):
            try:
                w = self.query_one(f"#{wid}")
                if show_dry:
                    w.remove_class("--lib-hidden")
                else:
                    w.add_class("--lib-hidden")
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
            status = self._lib_status.get(node_path)
            if status == "validated":
                t.append("✓ ", style="bold green")
            elif status == "corrupted":
                t.append("✗ ", style="bold red")
            else:
                t.append("~ ", style="yellow")
            t.append(node_path.name, style="#c9d1d9")
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

        elif fid == "queue-table":
            if event.key == "space":
                self._queue_toggle_selection()
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

    def on_switch_changed(self, event: Switch.Changed) -> None:
        """Persist switch state immediately so worker threads can read it safely."""
        if event.switch.id == "sw-dat-dry-run":
            self.state.set_setting("dat_dry_run", event.value, immediate=False)

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
                        1.0, lambda: self.run_global_search(val)
                    )
            else:
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
            self.query_one("#sw-dat-dry-run", Switch).value = \
                self.state.settings.get("dat_dry_run", False)
        except Exception as e:
            logging.debug("Load sw-dat-dry-run toggle failed: %s", e)

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
        "btn-lib-organize":         "run_lib_organize",
        "btn-setup-chdman":         "setup_chdman_auto",
        "btn-setup-ps2mdp":         "setup_ps2mdp_auto",
        "btn-lib-refresh-status":   "run_lib_status_scan",
        "btn-requeue-failed":       "requeue_failed_games",
        "btn-prefetch-consoles":    "prefetch_all_consoles",
        "btn-refresh-session-logs": "_refresh_session_log_list",
        "btn-schedule-dl":          "_schedule_download",
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
            self._browse_global_mode = not getattr(self, "_browse_global_mode", False)
            try:
                btn = self.query_one("#btn-toggle-global", Button)
                search_input = self.query_one("#search-games", Input)
                if self._browse_global_mode:
                    btn.variant = "primary"
                    btn.label = "Global"
                    search_input.placeholder = "  search all consoles… (min 3 chars)"
                    search_input.value = ""
                    search_input.focus()
                else:
                    btn.variant = "default"
                    btn.label = "Global"
                    search_input.placeholder = "  search games…"
                    search_input.value = ""
                    self._global_search_results = {}
                    if self.selected_console:
                        self._render_games("")
                        self._show_browse_game_view(True)
                    else:
                        self._show_browse_game_view(False)
            except Exception:
                pass
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
                    
        elif button_id == "btn-start-dl":
            if self.state.get_active_queue():
                self.start_download_engine()
                
        elif button_id == "btn-pause-dl":
            with self._engine_lock:
                if self._engine_state == EngineState.RUNNING:
                    self._engine_state = EngineState.PAUSING
                elif self._engine_state != EngineState.PAUSING:
                    # Also allow cancelling library operations
                    self._lib_cancel.set()
                    self.post_message(SystemLog("[bold yellow]Cancel signal sent to library operation.[/]"))
                    return
            self.post_message(SystemLog("[bold yellow]Pause signal sent. Suspending threads and preserving partial files...[/]"))
            self._update_global_statusbar()
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
            except Exception as e:
                logging.debug("Clear filter table visuals failed: %s", e)
            self.state.update_settings({"filter_include": [], "filter_exclude": []})
            self.notify("Filters cleared")

        elif button_id == "btn-save-settings":
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

                # Apply all changes in one lock window — prevents other threads
                # from reading a partially-updated settings dict.
                # Read custom regex filters
                try:
                    custom_inc = self.query_one("#set-custom-include", Input).value.strip()
                except Exception:
                    custom_inc = self.state.settings.get("custom_include_regex", "")
                try:
                    custom_exc = self.query_one("#set-custom-exclude", Input).value.strip()
                except Exception:
                    custom_exc = self.state.settings.get("custom_exclude_regex", "")

                self.state.update_settings({
                    "library_root":             str(new_path),
                    "max_concurrent":           max(1, min(10, thread_count)),
                    "speed_limit_mbps":         speed_limit,
                    "dat_cache_ttl_hours":      dat_ttl_hours,
                    "auto_convert_chd":         self.query_one("#set-auto-chd", Switch).value,
                    "watch_library":            self.query_one("#set-watch-library", Switch).value,
                    "notify_on_batch_complete": self.query_one("#set-notify-batch", Switch).value,
                    "filter_include":           sorted(self._filter_include_sel),
                    "filter_exclude":           sorted(self._filter_exclude_sel),
                    "custom_include_regex":     custom_inc,
                    "custom_exclude_regex":     custom_exc,
                })

                new_path.mkdir(parents=True, exist_ok=True)
                self._lib_status.load(new_path)
                self.run_lib_status_scan()
                self.notify("Settings saved")

                # Note: dat_cache_ttl_hours is read fresh from self.state.settings
                # inside _run_dat_audit_impl at the start of each audit run, so
                # no global mutation is needed here.

                # Restart or stop watchdog based on new setting
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
                
        elif button_id == "btn-export-queue":
            try:
                export_path = _DATA_DIR / f"queue_export_{self.state.active_queue_name}.json"
                queue = self.state.get_active_queue()
                with open(export_path, 'w', encoding='utf-8') as f:
                    json.dump(queue, f, indent=2)
                self.notify(f"Queue exported to {export_path.name}")
                self.post_message(SystemLog(f"Queue exported: {export_path}"))
            except Exception as e:
                self.notify(f"Export failed: {e}", severity="error")

        elif button_id == "btn-import-queue":
            try:
                import_path = _DATA_DIR / f"queue_export_{self.state.active_queue_name}.json"
                if not import_path.exists():
                    # Try generic name
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
                self.notify(f"Imported {added} item(s) from {import_path.name}")
            except Exception as e:
                self.notify(f"Import failed: {e}", severity="error")

        elif button_id == "btn-requeue-corrupted":
            self.requeue_failed_games(corrupted_only=True)

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
                           "btn-lib-dat-audit"):
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
                sub_folder = data['name'].replace('.zip', '').strip()
                clean_base = DISC_REGEX.sub('', sub_folder).strip()
                if clean_base != sub_folder:
                    dest_path = library_root / gs_console / clean_base / sub_folder
                else:
                    dest_path = library_root / gs_console / sub_folder
                if str(dest_path) in existing_paths:
                    continue
                game_url = BASE_URL + quote(gs_console, safe="") + "/" + quote(data["url_part"], safe="")
                current_queue.append({
                    "id": f"dl_{uuid.uuid4().hex[:8]}",
                    "name": f"{gs_console} / {data['name']}",
                    "game_url": game_url,
                    "dest_path": str(dest_path),
                    "size_str": data["size_str"],
                })
                existing_paths.add(str(dest_path))
                added_count += 1
            self._selected_games.clear()
            self._update_selection_count()
            self.state.update_active_queue(current_queue)
            self._refresh_queue_table()
            self.notify(f"Queued {added_count} item(s)")
            self._update_global_statusbar()
            return

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
        except Exception as e:
            logging.debug("Focus search-games input failed: %s", e)

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
        items = self.scraper.scrape_links(BASE_URL)
        _SKIP_NAMES = {"files", "donate", "upload", "faq", "contact", "login", "register"}
        consoles = [
            i for i in items
            if i["url_part"].endswith('/')
            and i["name"].strip('/').lower() not in _SKIP_NAMES
        ]
        self.post_message(ConsolesLoaded(consoles))  # type: ignore[arg-type]

    @work(exclusive=True, thread=True)
    def prefetch_all_consoles(self) -> None:
        """Concurrently scrape all console game pages and warm the link cache."""
        self._lib_cancel.clear()
        items = self.scraper.scrape_links(BASE_URL)
        consoles = [i for i in items if i["url_part"].endswith('/')]
        if not consoles:
            return

        semaphore = threading.Semaphore(_SCRAPE_CONCURRENCY)
        total     = len(consoles)

        def _fetch_one(console: ConsoleItem, idx: int) -> None:
            with semaphore:
                if self._lib_cancel.is_set():
                    return
                url = urljoin(BASE_URL, console["url_part"])
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
        url = urljoin(BASE_URL, console_data["url_part"])
        # C2: Show loading indicator in breadcrumb
        def _show_loading() -> None:
            try:
                lbl = self.query_one("#breadcrumb", Label)
                t = Text()
                t.append("Redump", style="#3d4451")
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
            if not game["url_part"].lower().endswith('.zip'):
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

        # B6: Pre-flight disk space check
        try:
            library_root = Path(self.state.settings["library_root"])
            library_root.mkdir(parents=True, exist_ok=True)
            needed = sum(self._parse_size_bytes(it["size_str"]) for it in queue)
            free = shutil.disk_usage(library_root).free
            if needed > 0 and needed > free:
                self.post_message(SystemLog(
                    f"[bold red]Insufficient disk space![/bold red] "
                    f"Need {self._format_size(needed)}, only {self._format_size(free)} free.", True
                ))
                with self._engine_lock:
                    self._engine_state = EngineState.IDLE
                self.call_from_thread(self._update_global_statusbar)
                return
        except OSError:
            pass  # best-effort; proceed if we can't stat the filesystem

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

    # ──────────────────────────────────────────────────────────────────────────
    # Download-worker sub-methods
    # Extracted from the old monolithic _download_worker to satisfy SRP and
    # make each phase independently testable.
    # ──────────────────────────────────────────────────────────────────────────

    @staticmethod
    def _compute_speed(
        cur_bytes: int,
        size_bytes: int,
        speed_samples: "deque[tuple[float, int]]",
    ) -> tuple[float, float]:
        """Return ``(speed_bps, eta_secs)`` from a rolling sample window.

        Appends the current snapshot to *speed_samples*, evicts entries older
        than ``_SPEED_WINDOW``, then computes an instantaneous speed and ETA.
        Returns ``(0.0, -1.0)`` when there are fewer than two samples.
        """
        now = time.monotonic()
        speed_samples.append((now, cur_bytes))
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

    def _run_wget(
        self,
        item: QueueItem,
        target_file: Path,
        item_name: str,
        size_bytes: int,
        speed_limit_bps: int,
        speed_samples: "deque[tuple[float, int]]",
    ) -> tuple[bool, int]:
        """Run wget for one download attempt.

        Returns ``(True, updated_size_bytes)`` on success (rc=0).
        Returns ``(False, size_bytes)`` on any failure so the caller can fall
        through to the urllib fallback on the same attempt.

        Side effects: posts ``DownloadProgress`` messages; terminates process
        and returns early on cancel.
        """
        cmd = [
            "wget", "--progress=dot:mega", "-c", "--timeout=20", "--tries=1",
            "--user-agent=Mozilla/5.0 (Windows NT 10.0; Win64; x64)",
            "-e", "robots=off", "-O", str(target_file), item["game_url"],
        ]
        # A8: Use shared bucket rate, divided across concurrent workers
        bucket = getattr(self, "_bandwidth_bucket", None)
        effective_rate = bucket.rate if bucket and bucket.rate > 0 else speed_limit_bps
        if effective_rate > 0:
            # Divide evenly across max threads so aggregate ≈ cap
            q_settings = self.state.get_queue_settings(self.state.active_queue_name)
            n_threads = q_settings.get("max_concurrent",
                                       self.state.settings.get("max_concurrent", 4))
            per_thread = max(1, effective_rate // n_threads)
            cmd.insert(1, f"--limit-rate={per_thread}")
        proc = subprocess.Popen(
            cmd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
            text=True, env=_WGET_ENV,
        )
        self._register_process(proc)

        stderr_log    = deque(maxlen=5)
        last_ui_update = 0.0

        try:
            for line in proc.stderr:
                if self.cancel_flag.is_set():
                    proc.terminate()
                    return False, size_bytes

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
                        spd, eta = self._compute_speed(current_bytes, size_bytes, speed_samples)
                        self.post_message(
                            DownloadProgress(item["id"], item_name, current_bytes,
                                             size_bytes, "Downloading", spd, eta)
                        )
                        last_ui_update = current_time
        finally:
            try:
                proc.wait(timeout=10)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait()
            self._unregister_process(proc)

        if self.cancel_flag.is_set():
            return False, size_bytes

        if proc.returncode == 0:
            return True, size_bytes

        error_msg = " | ".join(stderr_log)
        self.post_message(SystemLog(
            f"wget failed for {item_name}. "
            f"Falling back to urllib… ({error_msg})", True
        ))
        return False, size_bytes

    def _run_urllib_fallback(
        self,
        item: QueueItem,
        target_file: Path,
        item_name: str,
        size_bytes: int,
        speed_limit_bps: int,
        speed_samples: "deque[tuple[float, int]]",
    ) -> tuple[bool, int]:
        """Stream the download via urllib with optional token-bucket throttling.

        Supports HTTP range-resume if *target_file* already exists and is
        smaller than *size_bytes*.

        Returns ``(True, updated_size_bytes)`` on success.
        Returns ``(False, size_bytes)`` and lets the caller handle the exception
        (i.e. the retry-loop ``last_error`` is set by the caller's try/except).
        """
        req = urllib.request.Request(
            item["game_url"],
            headers={"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64)"},
        )

        if target_file.exists():
            existing_size = target_file.stat().st_size
            if existing_size < size_bytes:
                req.add_header("Range", f"bytes={existing_size}-")
                open_mode      = "ab"
                downloaded     = existing_size
                _resume_offset = existing_size   # used to verify 206 below
            else:
                open_mode      = "wb"
                downloaded     = 0
                _resume_offset = 0
        else:
            open_mode      = "wb"
            downloaded     = 0
            _resume_offset = 0

        with urllib.request.urlopen(req, timeout=30) as response:
            # If we sent a Range header but the server returned 200 (not 206),
            # it is sending the full file from byte 0.  Opening in "ab" would
            # prepend the already-downloaded bytes, corrupting the file.
            # Detect this and restart the write from scratch.
            actual_status = response.status
            if _resume_offset > 0 and actual_status != 206:
                open_mode  = "wb"
                downloaded = 0
            cl = response.headers.get("Content-Length")
            if cl and cl.isdigit() and int(cl) > 0:
                size_bytes = downloaded + int(cl)
            with open(target_file, open_mode) as file:
                last_ui_update = 0.0
                while True:
                    if self.cancel_flag.is_set():
                        return False, size_bytes
                    chunk = response.read(_DL_CHUNK_BYTES)
                    if not chunk:
                        break
                    file.write(chunk)
                    downloaded += len(chunk)

                    # ── Shared bandwidth throttle ─────────────────────────────
                    bucket = getattr(self, "_bandwidth_bucket", None)
                    if bucket is not None:
                        bucket.consume(len(chunk))

                    current_time = time.monotonic()
                    if current_time - last_ui_update > _UI_UPDATE_INTERVAL:
                        spd, eta = self._compute_speed(
                            downloaded, max(size_bytes, downloaded), speed_samples
                        )
                        self.post_message(
                            DownloadProgress(
                                item["id"], item_name, downloaded,
                                max(size_bytes, downloaded), "Downloading", spd, eta,
                            )
                        )
                        last_ui_update = current_time

        return True, size_bytes

    def _run_extraction(
        self,
        target_file: Path,
        dest_dir: Path,
        item_name: str,
    ) -> bool:
        """Extract *target_file* (ZIP) into *dest_dir*.

        Tries the ``unzip`` system binary first for speed; falls back to
        Python's ``zipfile`` module on timeout or non-zero exit.

        Updates ``_lib_status`` to ``"validated"`` on success or
        ``"corrupted"`` on failure.  Posts ``SystemLog`` on errors.

        Returns ``True`` on success, raises ``Exception`` on failure.
        """
        if not (target_file.exists() and target_file.suffix.lower() == ".zip"):
            # Non-zip payload (e.g. bare ISO/CHD): mark validated and return
            if target_file.exists():
                self._lib_status.set_status(dest_dir, "validated")
            return True

        extracted_ok  = False
        unzip_err_msg = ""

        if self._unzip_available:
            unzip_proc = subprocess.Popen(
                ["unzip", "-q", "-o", str(target_file), "-d", str(dest_dir)],
                stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True,
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
                with _zf.ZipFile(target_file, "r") as zf:
                    _safe_extractall(zf, dest_dir)
                extracted_ok = True
            except (_zf.BadZipFile, OSError, ValueError) as zf_err:
                unzip_err_msg = str(zf_err)

        if extracted_ok:
            try:
                target_file.unlink()
            except OSError as ose:
                self.post_message(SystemLog(
                    f"Extraction succeeded but could not delete zip "
                    f"{target_file.name}: {ose}", True
                ))
            self._lib_status.set_status(dest_dir, "validated")
            return True
        else:
            self._lib_status.set_status(dest_dir, "corrupted")
            raise Exception(f"Extraction failed: {unzip_err_msg}")

    def _run_chd_auto(
        self,
        item: QueueItem,
        item_name: str,
        dest_dir: Path,
        size_bytes: int,
    ) -> None:
        """Trigger auto-CHD conversion if enabled in settings.

        No-ops when ``auto_convert_chd`` is False or chdman is not available.
        Posts a ``DownloadProgress`` message with action "Converting CHD" so
        the progress bar shows the conversion phase while chdman runs.
        """
        if not self.state.settings.get("auto_convert_chd", False):
            return
        # Resolve locally rather than writing back to the shared Toolchain attribute —
        # multiple concurrent workers calling this method would race on that write.
        chdman = self.toolchain.chdman_path or Toolchain.find_chdman()
        if chdman:
            self.post_message(
                DownloadProgress(item["id"], item_name, size_bytes, size_bytes, "Converting CHD")
            )
            self._convert_to_chd(dest_dir, silent=True)
        else:
            self.post_message(SystemLog(
                f"Auto-CHD skipped for {item_name}: chdman not found. "
                "Run 'Setup chdman' in Settings."
            ))

    def _download_worker(self, item: QueueItem) -> dict[str, Any]:
        """Orchestrate a single download: skip-check → retry-loop → extract → CHD.

        Each network phase is delegated to a focused sub-method:
          * ``_run_wget``          — wget subprocess with progress parsing
          * ``_run_urllib_fallback`` — urllib streaming with token-bucket throttle
          * ``_run_extraction``    — ZIP extraction (unzip binary or zipfile fallback)
          * ``_run_chd_auto``      — optional post-download CHD conversion

        Returns ``{"success": True}`` on completion, ``{"success": False}`` on
        unrecoverable error, or ``{"success": False, "cancelled": True}`` when
        the cancel flag fires.
        """
        if self.cancel_flag.is_set():
            return {"success": False, "cancelled": True}

        dest_dir    = Path(item["dest_path"])
        _url_path   = urllib.parse.urlparse(item["game_url"]).path
        target_file = dest_dir / unquote(_url_path.split("/")[-1])
        item_name   = item["name"]

        try:
            dest_dir.mkdir(parents=True, exist_ok=True)

            # ── Fast-skip if the game is already in good shape ───────────────
            if any(dest_dir.rglob("*.chd")) or target_file.with_suffix(".chd").exists():
                self.post_message(SystemLog(f"Skipped (CHD exists): {item_name}"))
                return {"success": True}
            if self._lib_status.get(dest_dir) == "validated":
                # Verify game files still exist — a stale "validated" entry
                # persists after files are deleted or the directory is recreated
                # empty (common with multi-disc games where individual discs are
                # re-queued after partial deletion).
                try:
                    has_game_files = any(
                        f.suffix.lower() in _GAME_EXTS
                        for f in dest_dir.iterdir()
                        if f.is_file()
                    )
                except (PermissionError, OSError):
                    has_game_files = False
                if has_game_files:
                    self.post_message(SystemLog(f"Skipped (Already validated): {item_name}"))
                    return {"success": True}
                # Stale validated status — game files are missing; clear and re-download.
                self._lib_status.remove(dest_dir)
                self.post_message(SystemLog(
                    f"Cleared stale validation for {item_name} — re-downloading."
                ))

            # ── Stale-zip cleanup for corrupted games ────────────────────────
            if self._lib_status.get(dest_dir) == "corrupted":
                for stale_zip in dest_dir.glob("*.zip"):
                    try:
                        stale_zip.unlink()
                        self.post_message(SystemLog(
                            f"Removed stale zip before retry: {stale_zip.name}"
                        ))
                    except OSError as ose:
                        self.post_message(SystemLog(
                            f"Could not remove stale zip {stale_zip.name}: {ose} "
                            "(file may be locked — retry may fail)", True
                        ))

            size_bytes = max(self._parse_size_bytes(item["size_str"]), 1)

            # ── Resolve per-queue speed limit (convert MB/s → B/s) ───────────
            q_settings      = self.state.get_queue_settings(self.state.active_queue_name)
            speed_limit_bps = (q_settings.get("speed_limit_mbps", 0) or
                               self.state.settings.get("speed_limit_mbps", 0))
            speed_limit_bps = int(speed_limit_bps * 1024 * 1024)

            speed_samples: deque[tuple[float, int]] = deque()

            # ── Retry loop with exponential backoff + jitter ─────────────────
            attempt          = 0
            download_success = False
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
                    deadline = time.monotonic() + delay
                    while time.monotonic() < deadline:
                        if self.cancel_flag.is_set():
                            return {"success": False, "cancelled": True}
                        time.sleep(0.2)

                attempt += 1
                speed_samples.clear()

                # ── Phase 1: wget ────────────────────────────────────────────
                # Skip entirely when wget is not installed — avoids a failing
                # Popen call (FileNotFoundError) on every retry attempt.
                if self._wget_available:
                    ok, size_bytes = self._run_wget(
                        item, target_file, item_name, size_bytes,
                        speed_limit_bps, speed_samples,
                    )
                    if self.cancel_flag.is_set():
                        return {"success": False, "cancelled": True}
                    if ok:
                        download_success = True
                        break
                else:
                    ok = False

                # ── Phase 2: urllib fallback ─────────────────────────────────
                try:
                    ok, size_bytes = self._run_urllib_fallback(
                        item, target_file, item_name,
                        size_bytes, speed_limit_bps, speed_samples,
                    )
                    if self.cancel_flag.is_set():
                        return {"success": False, "cancelled": True}
                    if ok:
                        download_success = True
                        break
                except Exception as err:
                    last_error = err
                    # Loop continues — next iteration retries with backoff

            if not download_success:
                raise Exception(
                    f"All {_RETRY_MAX_ATTEMPTS} attempts failed: {last_error}"
                ) from last_error

            if self.cancel_flag.is_set():
                return {"success": False, "cancelled": True}

            # ── Phase 3: extraction ──────────────────────────────────────────
            self.post_message(
                DownloadProgress(item["id"], item_name, size_bytes, size_bytes, "Extracting ZIP")
            )
            self._run_extraction(target_file, dest_dir, item_name)

            if self.cancel_flag.is_set():
                return {"success": False, "cancelled": True}

            # ── Phase 4: optional auto-CHD conversion ────────────────────────
            self._run_chd_auto(item, item_name, dest_dir, size_bytes)

            # B1: Record in download history
            console_name = item["name"].split(" / ")[0].strip() if " / " in item["name"] else ""
            self.state.record_download(
                item_name,
                console_name,
                item["size_str"],
            )
            return {"success": True}

        except Exception as err:
            logging.exception("Worker error for %s", item_name)
            self.post_message(SystemLog(f"Worker Error {item_name}: {err}", True))
            return {"success": False}

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
            except Exception as e:
                logging.debug("Update speed indicator failed: %s", e)
        elif message.action in ("Extracting ZIP", "Converting CHD"):
            # C7: Phase label in statusbar when not downloading
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
            status_line.append(f"  ETA {eta_str}", style="dim #58a6ff")

        if task_id in self._active_progress_containers:
            try:
                self.query_one(f"#{pb_id}", ProgressBar).update(
                    progress=message.completed, total=message.total
                )
                self.query_one(f"#{lbl_id}", Label).update(status_line)
            except Exception as e:
                logging.debug("Update download progress widget failed: %s", e)
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

    @work(exclusive=True, thread=True)
    def run_lib_organize(self) -> None:
        self._lib_cancel.clear()
        self.post_message(SystemLog("Library Scan: Building target list..."))
        library = Path(self.state.settings['library_root'])

        targets = []
        # Collect empty orphaned directories for cleanup (e.g. multi-disc
        # parent folders left behind after all disc subfolders were deleted).
        empty_dirs: list[Path] = []

        if library.exists():
            try:
                console_dirs = [d for d in library.iterdir()
                                if d.is_dir() and not d.name.startswith('.')]
            except PermissionError:
                console_dirs = []

            for console_dir in console_dirs:
                try:
                    game_entries = list(console_dir.iterdir())
                except PermissionError:
                    continue
                for game_dir in game_entries:
                    if not game_dir.is_dir() or game_dir.name.startswith('.'):
                        continue
                    base_name = DISC_REGEX.sub('', game_dir.name).strip()
                    if base_name != game_dir.name:
                        targets.append((game_dir, console_dir / base_name))
                    else:
                        # Check if this is an empty orphaned folder
                        try:
                            if not any(game_dir.iterdir()):
                                empty_dirs.append(game_dir)
                        except PermissionError:
                            pass

        total_ops = len(targets) + len(empty_dirs)
        if total_ops == 0:
            self.post_message(SystemLog("Library Scan: No valid targets found. (Library is already organized)"))
            self.post_message(LibraryProgress("Organize", "Done", 100, 100))
            return

        changed = 0
        step = 0
        for game_dir, parent_dir in targets:
            step += 1
            if self._lib_cancel.is_set():
                self.post_message(SystemLog("[yellow]Organize cancelled.[/]"))
                break
            self.post_message(LibraryProgress(f"Organizing ({step}/{total_ops})", game_dir.name, step, total_ops))
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
                changed += 1
            except Exception as e:
                self.post_message(SystemLog(f"Move failed [{game_dir.name}]: {e}", True))

        # Remove empty orphaned directories
        for empty_dir in empty_dirs:
            step += 1
            if self._lib_cancel.is_set():
                break
            self.post_message(LibraryProgress(f"Cleanup ({step}/{total_ops})", empty_dir.name, step, total_ops))
            try:
                # Re-check emptiness in case something changed since the scan
                if empty_dir.exists() and not any(empty_dir.iterdir()):
                    self._lib_status.remove(empty_dir)
                    empty_dir.rmdir()
                    self.post_message(SystemLog(f"Removed empty folder: {empty_dir.name}"))
                    changed += 1
            except OSError:
                pass

        self.post_message(LibraryProgress("Organize", "Complete", total_ops, total_ops))
        if changed:
            # Only rescan if the directory tree actually changed
            self.run_lib_status_scan()
        self.post_message(SystemLog(f"Clean-up Complete. {changed} folder(s) organized/removed."))

    @work(exclusive=True, thread=True)
    def run_bulk_dat_audit(self, scope: Path | None = None) -> None:
        """
        DAT audit scoped to *scope* (library root, console dir, or game dir).
        For every console folder in scope:
          1. Fetches (or reuses a cached) Redump .dat file from Myrient.
          2. SHA-1 hashes every .bin/.iso/.cue/.img file.
          3. Looks each hash up in the DAT and marks the parent game dir
             .validated (known-good) or .corrupted (unknown/bad dump).
          4. Reports perfect / misnamed / bad counts per console and a grand total.

        When the dry-run switch (sw-dat-dry-run) is enabled, planned renames are
        logged but no files are moved and no status markers are written.
        """
        self._lib_cancel.clear()
        dry_run = self.state.settings.get("dat_dry_run", False)

        if dry_run:
            self.post_message(SystemLog(
                "[bold cyan]DAT Audit — DRY RUN mode[/bold cyan]  "
                "(no files will be moved or marked)"
            ))

        dat_ttl = self.state.settings.get("dat_cache_ttl_hours", 168) * 3600.0
        library = Path(self.state.settings['library_root'])

        if not library.exists():
            self.post_message(SystemLog("DAT Audit: Library path not found.", True))
            return

        if scope is None:
            scope = library

        # ── Phase 1: discover console dirs (scoped) ─────────────────────────
        if scope == library:
            console_dirs = sorted(
                d for d in library.iterdir()
                if d.is_dir() and not d.name.startswith('.')
            )
            scope_label = "full library"
        elif scope.parent == library:
            # Single console
            console_dirs = [scope] if scope.is_dir() else []
            scope_label = f"console [{scope.name}]"
        else:
            # Game dir — resolve to its console parent
            console_parent = scope.parent
            while console_parent.parent != library and console_parent != library:
                console_parent = console_parent.parent
            console_dirs = [console_parent] if console_parent.is_dir() else []
            scope_label = f"game [{scope.name}]"

        if not console_dirs:
            self.post_message(SystemLog("DAT Audit: No console folders found in library."))
            return

        self.post_message(SystemLog(
            f"DAT Audit [{scope_label}]: Starting audit of {len(console_dirs)} console(s)..."
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
            # Respect cancel between consoles — audit can take many minutes
            if self._lib_cancel.is_set():
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

            # Re-fetch if the cached DAT is older than dat_ttl (read from settings above).
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
            # Defer LibraryStatus disk flushes for the entire per-console pass.
            # set_status/remove are called once per game dir in step 3h (and per
            # rename in 3f); deferring reduces I/O from O(games) to O(1) per console.
            self._lib_status.defer_flushes(True)
            con_perfect = con_misnamed = con_bad = con_ambiguous = 0
            all_files = [(gd, fp) for gd, fps in game_dirs.items() for fp in fps]
            total_files = len(all_files)
            hash_results: dict[Path, bool] = {}
            cache_dirty = False
            # Tracks dirs that lost files to a rename — they get "incomplete"
            # markers in step 3h rather than "corrupted".
            renamed_old_dirs: set[Path] = set()

            for f_idx, (game_dir, file_path) in enumerate(all_files, 1):
                if self._lib_cancel.is_set():
                    break
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
            try:
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
            finally:
                # Single flush for all status changes in this console.
                self._lib_status.defer_flushes(False)

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
        self._lib_cancel.clear()
        # Resolve locally — worker threads must not write back to toolchain.chdman_path
        # since concurrent @work threads could race on that shared attribute.
        chdman = self.toolchain.chdman_path or Toolchain.find_chdman()
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
            # Check this dir directly for source files
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
                # Multi-disc grouping folder — scan subdirectories
                try:
                    subdirs = sorted(d for d in scope.iterdir() if d.is_dir() and not d.name.startswith('.'))
                except PermissionError:
                    subdirs = []
                for sub in subdirs:
                    try:
                        sub_files = [f for f in sub.iterdir() if f.is_file()]
                    except PermissionError:
                        continue
                    s_src = s_chd = False
                    for f in sub_files:
                        ext = f.suffix.lower()
                        if ext in _CHD_SOURCE_EXTS:
                            s_src = True
                        elif ext == '.chd':
                            s_chd = True
                        if s_src and s_chd:
                            break
                    if s_src and not s_chd:
                        targets.append(sub)
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
            if self._lib_cancel.is_set():
                self.post_message(SystemLog("[yellow]CHD conversion cancelled.[/]"))
                break
            self.post_message(LibraryProgress(f"Converting ({i}/{total_ops})", game_dir.name, i, total_ops))
            self.post_message(SystemLog(f"Converting: {game_dir.name}"))
            c, f = self._convert_to_chd(game_dir, silent=False, cancel=self._lib_cancel)
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
        self._lib_cancel.clear()
        # Resolve locally — same race-safety rationale as run_lib_convert.
        chdman = self.toolchain.chdman_path or Toolchain.find_chdman()
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
            if self._lib_cancel.is_set():
                self.post_message(SystemLog("[yellow]CHD extraction cancelled.[/]"))
                break

            self.post_message(LibraryProgress(
                f"Extracting ({i}/{total_ops})", chd_path.name, i, total_ops
            ))
            self.post_message(SystemLog(f"Extracting: {chd_path.name}"))

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
                        self.post_message(SystemLog(
                            f"CHD Extract [{chd_path.name}] {subcommand} timed out — killed.", True
                        ))
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
                        self._lib_status.remove(dest_dir)
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

    # ── Library tree expand/collapse helpers ────────────────────────────────

    def _lib_expand_all(self) -> None:
        try:
            tree = self.query_one("#lib-tree", Tree)
            tree.root.expand_all()
        except Exception:
            pass

    def _lib_collapse_all(self) -> None:
        try:
            tree = self.query_one("#lib-tree", Tree)
            tree.root.collapse_all()
            tree.root.expand()  # keep root visible
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

    # ── Disk space dashboard ─────────────────────────────────────────────────

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
        except Exception:
            pass

    def _refresh_queue_row_visual(self, table: DataTable, item_id: str) -> None:
        """Update a queue row's visual to reflect multi-select state."""
        try:
            current_queue = self.state.get_active_queue()
            item = next((i for i in current_queue if i["id"] == item_id), None)
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
        the library tree.  ``run_lib_organize`` cleans these up on request.
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

        # structure: {console_name: (console_path, [(game_dir, status_str, has_chd), ...])}
        structure: dict[str, tuple[Path, list[tuple[Path, str, bool]]]] = {}
        for console_name, game_dir, status in self._walk_library_game_dirs(library, self._lib_status):
            # Detect .chd files — lightweight suffix check on already-listed dir
            try:
                has_chd = any(f.suffix.lower() == '.chd' for f in game_dir.iterdir() if f.is_file())
            except PermissionError:
                has_chd = False
            if console_name not in structure:
                structure[console_name] = (library / console_name, [])
            structure[console_name][1].append((game_dir, status, has_chd))

        # Pre-compute disk usage per console on this worker thread so the main
        # thread's on_library_tree_ready handler never blocks on heavy I/O.
        disk_usage: dict[str, int] = {}
        for console_name, (console_path, _) in structure.items():
            disk_usage[console_name] = self._console_disk_usage(console_path)

        self.post_message(LibraryTreeReady(structure, library, disk_usage))

    def _lookup_game_size(self, console_name: str, game_zip: str) -> str:
        """Look up a game's size from the scrape cache. Returns 'N/A' on miss."""
        try:
            url = BASE_URL + quote(console_name, safe="") + "/"
            games = self.scraper.scrape_links(url)
            for g in games:
                if g["name"] == game_zip:
                    return g.get("size_str", "N/A")
        except Exception:
            pass
        return "N/A"

    def _find_disc_variants(self, console_name: str, base_name: str) -> list[GameItem]:
        """Scrape the console page on Myrient and return disc-specific entries
        whose base name (with the disc suffix stripped) matches *base_name*.

        Used by the requeue methods to expand multi-disc parent folders into
        individual per-disc queue items.
        """
        console_url = BASE_URL + quote(console_name, safe="") + "/"
        all_games = self.scraper.scrape_links(console_url)
        variants: list[GameItem] = []
        for g in all_games:
            name: str = g["name"]  # e.g. "Resident Evil 2 (USA) (Disc 1).zip"
            if not name.lower().endswith(".zip"):
                continue
            folder_name = name[:-4]  # strip .zip
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
        console_url = BASE_URL + quote(console_name, safe="") + "/"
        for g in variants:
            disc_folder = g["name"][:-4]  # strip .zip
            disc_dest = library / console_name / game_dir.name / disc_folder
            if str(disc_dest) in existing_paths:
                continue
            self._lib_status.remove(disc_dest)
            disc_url = urljoin(console_url, g["url_part"])
            label = f"{console_name} / {g['name']}"
            if include_status_label:
                plain = "corrupted" if status == "corrupted" else "incomplete"
                label += f" ({plain})"
            current_queue.append({
                "id":        f"dl_{uuid.uuid4().hex[:8]}",
                "name":      label,
                "game_url":  disc_url,
                "dest_path": str(disc_dest),
                "size_str":  g.get("size_str", "N/A"),
            })
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
    def requeue_failed_games(self, corrupted_only: bool = False) -> None:
        """Finds corrupted (and optionally incomplete) game dirs and adds them to the queue.

        Multi-disc parent folders (e.g. ``Resident Evil 2 (USA)/`` with no disc
        subfolders) are detected automatically: the console page is scraped to
        find matching disc entries and each disc is queued individually.
        """
        library = Path(self.state.settings['library_root'])
        if not library.exists():
            self.post_message(SystemLog("Re-queue: Library path not found.", True))
            return

        # Walk library and keep only non-validated entries; generator means no full list built
        if corrupted_only:
            targets = [
                (cn, gd, s)
                for cn, gd, s in self._walk_library_game_dirs(library, self._lib_status)
                if s == "corrupted"
            ]
        else:
            targets = [
                (cn, gd, s)
                for cn, gd, s in self._walk_library_game_dirs(library, self._lib_status)
                if s != "validated"
            ]

        if not targets:
            label = "corrupted" if corrupted_only else "incomplete or corrupted"
            self.post_message(SystemLog(f"Re-queue: No {label} games found. Library looks clean!"))
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

            # ── Multi-disc parent detection ────────────────────────────────
            # If the dir name has no disc suffix, it may be a grouping folder
            # whose disc subfolders were deleted.  Scrape the console page to
            # find individual disc zips and queue each one.
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

            # Reconstruct the Myrient URL from the library directory structure.
            game_zip = game_dir.name + ".zip"
            game_url = BASE_URL + quote(console_name, safe="") + "/" + quote(game_zip, safe="")
            size_str = self._lookup_game_size(console_name, game_zip)
            # Store plain-text name — Rich markup must NOT be embedded in persisted JSON
            # because brackets in console/game names would inject unintended markup at render time.
            plain_status = "corrupted" if status == "corrupted" else "incomplete"
            current_queue.append({
                "id":        f"dl_{uuid.uuid4().hex[:8]}",
                "name":      f"{console_name} / {game_zip} ({plain_status})",
                "game_url":  game_url,
                "dest_path": str(game_dir),
                "size_str":  size_str,
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

            game_zip = game_dir.name + ".zip"
            game_url = BASE_URL + quote(console_name, safe="") + "/" + quote(game_zip, safe="")
            size_str = self._lookup_game_size(console_name, game_zip)
            current_queue.append({
                "id":        f"dl_{uuid.uuid4().hex[:8]}",
                "name":      f"{console_name} / {game_zip}",
                "game_url":  game_url,
                "dest_path": str(game_dir),
                "size_str":  size_str,
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

    # ── Global cross-console search (2A) ──────────────────────────────────────

    @work(exclusive=True, thread=True)
    def run_global_search(self, query: str) -> None:
        """Search all consoles for games matching *query*. Uses prefetch cache."""
        if not query or len(query) < 2:
            return
        self._lib_cancel.clear()
        self.post_message(SystemLog(f"Global search: \"{_escape_markup(query)}\"…"))

        items = self.scraper.scrape_links(BASE_URL)
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
                url = urljoin(BASE_URL, console["url_part"])
                self.post_message(LibraryProgress(
                    "Searching", console["name"].strip('/'), idx, len(consoles)
                ))
                games = self.scraper.scrape_links(url)
                for g in games:
                    if not g["url_part"].lower().endswith('.zip'):
                        continue
                    if self._fuzzy_spans(query, g["name"]) is not None:
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
                    gt.add_row(Text(" "), name_text, game["size_str"], key=key)
                if not results:
                    gt.add_row("", Text("No matches found.", style="dim"), "", key="EMPTY")
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
            if line.startswith(("http://", "https://")) and "myrient" in line.lower():
                try:
                    parsed = urllib.parse.urlparse(line)
                    parts = [unquote(p) for p in parsed.path.strip('/').split('/') if p]
                    if len(parts) >= 3:
                        console_name = parts[-2]
                        game_zip = parts[-1]
                        game_name = game_zip.replace('.zip', '').strip()
                        clean_base = DISC_REGEX.sub('', game_name).strip()
                        if clean_base != game_name:
                            dest_path = library_root / console_name / clean_base / game_name
                        else:
                            dest_path = library_root / console_name / game_name
                        if str(dest_path) not in existing_paths:
                            current_queue.append({
                                "id": f"dl_{uuid.uuid4().hex[:8]}",
                                "name": f"{console_name} / {game_zip}",
                                "game_url": line,
                                "dest_path": str(dest_path),
                                "size_str": "N/A",
                            })
                            existing_paths.add(str(dest_path))
                            added += 1
                except Exception:
                    continue
            elif " / " in line:
                parts = line.split(" / ", 1)
                console_name = parts[0].strip()
                game_zip = parts[1].strip()
                if not game_zip.endswith('.zip'):
                    game_zip += '.zip'
                game_name = game_zip.replace('.zip', '').strip()
                clean_base = DISC_REGEX.sub('', game_name).strip()
                if clean_base != game_name:
                    dest_path = library_root / console_name / clean_base / game_name
                else:
                    dest_path = library_root / console_name / game_name
                game_url = BASE_URL + quote(console_name, safe="") + "/" + quote(game_zip, safe="")
                if str(dest_path) not in existing_paths:
                    current_queue.append({
                        "id": f"dl_{uuid.uuid4().hex[:8]}",
                        "name": f"{console_name} / {game_zip}",
                        "game_url": game_url,
                        "dest_path": str(dest_path),
                        "size_str": "N/A",
                    })
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


if __name__ == "__main__":
    MyrientTUI().run()
