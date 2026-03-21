"""Myrient TUI Downloader & Library Manager — package root.

Re-exports the main App class and commonly-used symbols so the entry point
can simply ``from myrient_tui import MyrientTUI``.
"""
from .constants import _COLLECTIONS, _DATA_DIR, _SCRIPT_DIR, _TOOLS_DIR, CONFIG_FILE
from .types import ConsoleItem, DataListItem, GameItem, GameMetadata, QueueItem, RomEntry
from .messages import (
    BatchComplete, ConsolesLoaded, DownloadComplete, DownloadProgress,
    GamesLoaded, LibraryProgress, LibraryTreeReady, LibraryWatchEvent,
    RatingsLoaded, SystemLog,
)
from .storage import SQLiteStorage
from .config import ConfigManager, DEFAULT_SETTINGS
from .library_status import LibraryStatus
from .scraper import MyrientScraper
from .toolchain import Toolchain, _sha256_file, _safe_extractall
from .download import DownloadWorker, EngineState, TokenBucket
from .library_ops import LibraryOperation
from .commands import LibraryCommand, OrganizeCommand, RefreshCommand, ConvertCommand, DatAuditCommand
from .modals import ConfirmDeleteScreen, ConfirmDownloadScreen, ConfirmVerifyScreen, HelpModal
from .utils import normalize_game_title, normalize_game_title_keep_disc, strip_extension

__all__ = [
    # App (lazy — import from .app directly to avoid circular deps)
    "MyrientTUI",
    # Types
    "ConsoleItem", "GameItem", "GameMetadata", "QueueItem", "RomEntry",
    # Messages
    "BatchComplete", "ConsolesLoaded", "DownloadComplete", "DownloadProgress",
    "GamesLoaded", "LibraryProgress", "LibraryTreeReady", "LibraryWatchEvent",
    "RatingsLoaded", "SystemLog",
    # Storage & Config
    "SQLiteStorage", "ConfigManager", "DEFAULT_SETTINGS",
    # Core
    "LibraryStatus", "MyrientScraper", "Toolchain",
    "DownloadWorker", "EngineState", "TokenBucket",
    "LibraryOperation",
    "LibraryCommand", "OrganizeCommand", "RefreshCommand", "ConvertCommand", "DatAuditCommand",
    # Modals
    "ConfirmDeleteScreen", "ConfirmDownloadScreen", "ConfirmVerifyScreen", "HelpModal",
    # Constants
    "_COLLECTIONS", "_DATA_DIR", "_SCRIPT_DIR", "_TOOLS_DIR", "CONFIG_FILE",
    # Helpers
    "_sha256_file", "_safe_extractall",
    "normalize_game_title", "normalize_game_title_keep_disc", "strip_extension",
]


def _get_app_class():
    """Lazy import to avoid circular dependency."""
    from .app import MyrientTUI
    return MyrientTUI
