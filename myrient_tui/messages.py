"""Custom Textual Message subclasses for inter-component communication."""
from __future__ import annotations

from pathlib import Path

from textual.message import Message

from .types import ConsoleItem, GameItem, GameMetadata, QueueItem


# C3: __slots__ on hot-path Message subclasses saves ~40 bytes per instance
# and speeds up attribute access during download batches.

class SystemLog(Message):
    __slots__ = ("message", "is_error")

    def __init__(self, message: str, is_error: bool = False):
        self.message = message
        self.is_error = is_error
        super().__init__()


class ConsolesLoaded(Message):
    __slots__ = ("consoles",)

    def __init__(self, consoles: list[ConsoleItem]):
        self.consoles = consoles
        super().__init__()


class GamesLoaded(Message):
    __slots__ = ("games",)

    def __init__(self, games: list[GameItem]):
        self.games = games
        super().__init__()


class DownloadProgress(Message):
    __slots__ = ("task_id", "item_name", "completed", "total",
                 "action", "speed_bps", "eta_secs")

    def __init__(self, task_id: str, item_name: str, completed: int, total: int,
                 action: str = "Downloading",
                 speed_bps: float = 0.0, eta_secs: float = -1.0):
        self.task_id   = task_id
        self.item_name = item_name
        self.completed = completed
        self.total     = total
        self.action    = action
        self.speed_bps = speed_bps
        self.eta_secs  = eta_secs
        super().__init__()


class DownloadComplete(Message):
    __slots__ = ("item", "success", "cancelled")

    def __init__(self, item: QueueItem, success: bool, cancelled: bool = False):
        self.item = item
        self.success = success
        self.cancelled = cancelled
        super().__init__()


class LibraryProgress(Message):
    __slots__ = ("task_name", "current_item", "completed", "total")

    def __init__(self, task_name: str, current_item: str, completed: int, total: int):
        self.task_name = task_name
        self.current_item = current_item
        self.completed = completed
        self.total = total
        super().__init__()


class LibraryTreeReady(Message):
    """Carries the fully-built library structure to the main thread for Tree rendering."""
    __slots__ = ("structure", "library_path", "disk_usage")

    def __init__(self, structure: dict[str, tuple[Path, list[tuple[Path, str, bool, bool]]]], library_path: Path,
                 disk_usage: dict[str, int] | None = None):
        self.structure = structure
        self.library_path = library_path
        self.disk_usage: dict[str, int] = disk_usage or {}
        super().__init__()


class BatchComplete(Message):
    """Posted when an entire download queue finishes."""
    __slots__ = ("total", "succeeded", "failed")

    def __init__(self, total: int, succeeded: int, failed: int):
        self.total     = total
        self.succeeded = succeeded
        self.failed    = failed
        super().__init__()


class RatingsLoaded(Message):
    """Posted when IGDB metadata arrives for the current console."""
    __slots__ = ("metadata",)

    def __init__(self, metadata: dict[str, GameMetadata]):
        self.metadata = metadata
        super().__init__()


class LibraryWatchEvent(Message):
    """Posted by the watchdog observer thread when a filesystem change is detected."""
    __slots__ = ()
