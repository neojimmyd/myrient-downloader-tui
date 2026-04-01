"""Module-level constants, regex patterns, and tunable parameters."""
from __future__ import annotations

import logging
import os
import platform as _platform
import re
import socket
from pathlib import Path
from typing import Any

from bs4 import SoupStrainer

# ── Module-level side effects ────────────────────────────────────────────────
socket.setdefaulttimeout(60)

# ── All program data lives in a single subfolder next to tui_dl.py ───────────
_SCRIPT_DIR = Path(__file__).parent.parent.resolve()
_DATA_DIR   = _SCRIPT_DIR / "myrient_data"
_DATA_DIR.mkdir(parents=True, exist_ok=True)
_TOOLS_DIR  = _DATA_DIR / "tools"
_TOOLS_DIR.mkdir(parents=True, exist_ok=True)

# PS2 Master Disc Patcher
_PS2MDP_BINARY_NAME     = "ps2_master"
_PS2MDP_RELEASE_VERSION = "v1.0.5"
_PS2MDP_RELEASE_URL  = (
    "https://github.com/alex-free/playstation-disc-burner/releases/download/"
    f"{_PS2MDP_RELEASE_VERSION}/playstation-disc-burner-{_PS2MDP_RELEASE_VERSION}-x86_64.zip"
)
_PS2MDP_RELEASE_SHA256 = (
    "fa862ff48f7979f9e20d30ace3af5bd1f11bfca04bfe1c354caf38a3ebaf2d5b"
)

# DAT search prefix overrides
_DAT_SEARCH_PREFIXES: dict[str, list[str]] = {
    "Nintendo - Wii":                              ["Nintendo - Wii - NKit RVZ", "Nintendo - Wii -"],
    "Nintendo - Wii - NKit RVZ":                   ["Nintendo - Wii - NKit RVZ"],
    "Nintendo - Wii - NKit RVZ [zstd-19-128k]":    ["Nintendo - Wii - NKit RVZ"],
    "Nintendo - GameCube":                          ["Nintendo - GameCube - NKit RVZ", "Nintendo - GameCube -"],
    "Nintendo - GameCube - NKit RVZ":               ["Nintendo - GameCube - NKit RVZ"],
    "Nintendo - GameCube - NKit RVZ [zstd-19-128k]":["Nintendo - GameCube - NKit RVZ"],
    "Nintendo - Wii U":                             ["Nintendo - Wii U - WUX", "Nintendo - Wii U -"],
    "Nintendo - Wii U - WUX":                       ["Nintendo - Wii U - WUX"],
}

SESSION_LOG_DIR = _DATA_DIR / "logs"
DAT_CACHE_DIR   = _DATA_DIR / "dats"

# ── Logging ──────────────────────────────────────────────────────────────────
logging.basicConfig(
    filename=str(_DATA_DIR / 'myrient_errors.log'),
    level=logging.ERROR,
    format='%(asctime)s - [%(levelname)s] - %(message)s'
)

# ── Pre-compiled regex ───────────────────────────────────────────────────────
SIZE_REGEX      = re.compile(r'(?<!\d)(\d+(?:\.\d+)?)\s*([KMGT]i?B?)', re.IGNORECASE)
DISC_REGEX      = re.compile(r'\s*\((?:Disc|Disk|Tape|Side)\s+[^)]+\)', re.IGNORECASE)
CUE_BIN_REGEX   = re.compile(r'FILE\s+"([^"]+)"')
WGET_PROG_REGEX   = re.compile(r'(\d+)%')
WGET_LENGTH_REGEX = re.compile(r'Length:\s+(\d+)')

# ── Extension sets ───────────────────────────────────────────────────────────
_GAME_EXTS: frozenset[str] = frozenset({
    '.bin', '.iso', '.cue', '.chd', '.img',
    '.wbfs', '.rvz', '.gcz', '.gdi',
    '.nrg', '.mdf', '.mds',
    '.rom', '.xiso', '.ecm',
})

_CHD_SOURCE_EXTS: frozenset[str] = frozenset({'.bin', '.iso', '.cue', '.gdi'})

_CHD_CMD_MAP: dict[str, list[str]] = {
    '.bin': ['createcd'],
    '.cue': ['createcd'],
    '.gdi': ['createcd'],
    '.iso': ['createdvd', 'createcd'],
}

_DAT_AUDITABLE_EXTS: frozenset[str] = frozenset({
    '.bin', '.iso', '.cue', '.img', '.gdi',
    '.wbfs', '.rvz', '.gcz', '.nrg', '.mdf', '.wux',
})

_PS2_PATCH_EXTS: frozenset[str] = frozenset({'.iso', '.bin'})

# B6/F4: Accepted download extensions — archives + raw game files served by Myrient.
_DOWNLOAD_EXTS: frozenset[str] = frozenset({
    '.zip', '.7z', '.rvz', '.chd', '.iso', '.wux',
    '.wbfs', '.gcz', '.xiso',
})

_OS = _platform.system().lower()

_PKG_INSTALL_CMDS: list[tuple[str, list[str]]] = [
    ("apt-get",  ["apt-get", "install", "-y", "mame-tools"]),
    ("dnf",      ["dnf",     "install", "-y", "mame-tools"]),
    ("pacman",   ["pacman",  "-S",  "--noconfirm", "mame-tools"]),
    ("brew",     ["brew",    "install", "rom-tools"]),
]

# ── BeautifulSoup strainers ──────────────────────────────────────────────────
_SCRAPE_STRAINER = SoupStrainer(["a", "tr"])
_DAT_INDEX_STRAINER = SoupStrainer("a")

# ── Tunable numbers ─────────────────────────────────────────────────────────
_UI_UPDATE_INTERVAL: float = 0.25
_DL_CHUNK_BYTES:     int   = 1 * 1024 * 1024
_HASH_CHUNK_BYTES:   int   = 8 * 1024 * 1024
_LINK_CACHE_TTL:     float = 300.0
_SEARCH_DEBOUNCE:    float = 0.15
_FLUSH_INTERVAL:     float = 3.0

# ── Download retry / speed constants ─────────────────────────────────────────
_RETRY_MAX_ATTEMPTS: int   = 5
_RETRY_BASE_DELAY:   float = 2.0
_RETRY_MAX_DELAY:    float = 60.0
_SPEED_WINDOW:       float = 5.0

_SCRAPE_CONCURRENCY: int = 8
_WATCH_DEBOUNCE:     float = 2.0

_SIZE_UNITS: tuple[str, ...] = ('B', 'KB', 'MB', 'GB', 'TB')
_SIZE_MULTIPLIERS: dict[str, int] = {
    "K": 1024,
    "M": 1024 ** 2,
    "G": 1024 ** 3,
    "T": 1024 ** 4,
}

_CHD_TIMEOUT: int = 7200
_UNZIP_TIMEOUT: int = 600
_CHD_PCT_RE = re.compile(rb'(\d+(?:\.\d+)?)%')
_SESSION_LOG_MAX_FILES: int = 30

# ── wget env ─────────────────────────────────────────────────────────────────
_WGET_ENV: dict[str, str] = {**os.environ, "LC_ALL": "C"}

# ── Subprocess priority ──────────────────────────────────────────────────────
if _OS == "windows":
    _LOW_PRIO_POPEN: dict[str, Any] = {"creationflags": 0x00004000}
else:
    _LIBC_HANDLE = None
    try:
        import ctypes as _ctypes
        _LIBC_HANDLE = _ctypes.CDLL("libc.so.6", use_errno=True)
    except Exception:
        pass

    _ARCH = _platform.machine()
    if _ARCH in ("x86_64", "i686", "i386"):
        _NR_IOPRIO_SET = 251
    elif _ARCH in ("aarch64", "arm64"):
        _NR_IOPRIO_SET = 30
    elif _ARCH.startswith("arm"):
        _NR_IOPRIO_SET = 314
    else:
        _NR_IOPRIO_SET = None

    def _nice_preexec() -> None:
        try:
            os.nice(15)
        except OSError:
            pass
        if _LIBC_HANDLE is not None and _NR_IOPRIO_SET is not None:
            try:
                IOPRIO_WHO_PROCESS = 1
                IOPRIO_CLASS_IDLE = 3
                ioprio = (IOPRIO_CLASS_IDLE << 13) | 0
                _LIBC_HANDLE.syscall(
                    _NR_IOPRIO_SET, IOPRIO_WHO_PROCESS, 0, ioprio
                )
            except Exception:
                pass
    _LOW_PRIO_POPEN: dict[str, Any] = {"preexec_fn": _nice_preexec}

_PROGRESS_DONE_STATES: frozenset[str] = frozenset({"done", "complete", "failed"})

# ── Library tree label styles ────────────────────────────────────────────────
_TREE_AMBER:  str = "#e6b73e"
_TREE_GREEN:  str = "bold green"
_TREE_RED:    str = "bold red"
_TREE_YELLOW: str = "yellow"
_TREE_DIM:    str = "dim"
