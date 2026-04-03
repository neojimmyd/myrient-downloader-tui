"""Configuration defaults and thread-safe state manager.

Backed by SQLite (via SQLiteStorage) for incremental persistence.
The in-memory ``data`` dict is still the primary read cache — SQLite is
the durable store that replaces the old monolithic JSON file.
"""
from __future__ import annotations

import copy
import threading
import time
from pathlib import Path
from typing import Any, Callable

from myrient_tui.constants import _SCRIPT_DIR
from myrient_tui.storage import SQLiteStorage
from myrient_tui.types import QueueItem


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
    "notify_on_batch_complete": True,  # desktop notification when batch finishes
    "favorite_consoles": [],        # pinned console names shown at top of browse list
    # Runtime-editable download sources (replaces hard-coded _COLLECTIONS)
    "sources": [
        {"name": "Redump",   "browse_url": "https://myrient.erista.me/files/Redump/",   "dat_url": "http://redump.org/downloads/"},
        {"name": "No-Intro", "browse_url": "https://myrient.erista.me/files/No-Intro/", "dat_url": "https://myrient.erista.me/dats/No-Intro/"},
    ],
    "active_source": "Redump",
    # F3: User-configurable quick-filter tags
    "include_tags": ["USA", "Europe", "Japan", "World"],
    "exclude_tags": ["Demo", "Beta", "Proto"],
    # F2: Verify extracted files against DAT after download
    "verify_after_download": False,
    # IGDB integration (Twitch Developer credentials)
    "igdb_client_id": "",
    "igdb_client_secret": "",
}


# --- State Management (Thread-Safe) ---
class ConfigManager:
    """Handles loading and atomic, thread-safe saving of state.

    All mutations to ``self.data`` are performed while holding ``_lock`` so that
    worker threads calling ``get_active_queue()`` concurrently never see a
    partially-mutated dict.

    Persistence is handled by ``SQLiteStorage`` — individual settings and queue
    items are written as row-level operations instead of serializing the entire
    state on every change.
    """

    def __init__(self, db_path: Path | None = None):
        self._lock = threading.RLock()
        self._dirty = False
        self._db = SQLiteStorage(db_path)
        self.data: dict[str, Any] = self._load()

    def _load(self) -> dict[str, Any]:
        """Load state from SQLite into the in-memory cache.

        SQLiteStorage handles the one-time JSON migration internally,
        so by the time we read here the DB is already populated.
        """
        # Merge defaults with whatever is in the DB
        db_settings = self._db.get_all_settings()
        settings = copy.deepcopy(DEFAULT_SETTINGS)
        settings.update(db_settings)

        # Migrate old "collection" key → "active_source" + "sources"
        if "collection" in settings and "active_source" not in settings:
            settings["active_source"] = settings.pop("collection")
            self._db.update_settings({
                "active_source": settings["active_source"],
                "sources": settings["sources"],
            })
            self._db._conn().execute("DELETE FROM settings WHERE key='collection'")
            self._db._conn().commit()

        active_queue = self._db.get_active_queue_name()
        queues = self._db.get_all_queues()
        if not queues:
            queues = {"default": []}
            self._db.create_queue("default")
        if active_queue not in queues:
            queues[active_queue] = []

        history = self._db.get_download_history()

        return {
            "settings": settings,
            "active_queue": active_queue,
            "queues": queues,
            "download_history": history,
        }

    # ── Internal write helper — must be called with _lock already held ───────
    def _write_locked(self) -> None:
        """Flush current in-memory state to SQLite. Caller MUST hold _lock."""
        self._dirty = False
        try:
            # Settings
            self._db.update_settings(self.data["settings"])
            # Queues — full replace for each queue
            for qname, items in self.data["queues"].items():
                # Ensure queue exists
                self._db.create_queue(qname)
                self._db.replace_queue(qname, items)
            # Active queue
            self._db.set_active_queue(self.data["active_queue"])
        except Exception:
            self._dirty = True
            raise

    def flush_if_dirty(self) -> None:
        """Write to disk only if state has been dirtied since the last save."""
        with self._lock:
            if not self._dirty:
                return
            self._write_locked()

    @property
    def settings(self) -> dict[str, Any]:
        with self._lock:
            return dict(self.data["settings"])

    def get_setting(self, key: str, default: Any = None) -> Any:
        """B3: Thread-safe single-key read — holds lock for the read."""
        with self._lock:
            return self.data["settings"].get(key, default)

    def get_active_source(self) -> dict:
        """Return the active source dict, falling back to the first source."""
        with self._lock:
            sources = self.data["settings"].get("sources", [])
            name = self.data["settings"].get("active_source", "")
            for s in sources:
                if s["name"] == name:
                    return dict(s)
            return dict(sources[0]) if sources else {
                "name": "", "browse_url": "", "dat_url": ""
            }

    @property
    def queues(self) -> dict[str, list[QueueItem]]:
        with self._lock:
            return dict(self.data["queues"])

    @property
    def active_queue_name(self) -> str:
        with self._lock:
            return self.data["active_queue"]

    def get_active_queue(self) -> list[QueueItem]:
        with self._lock:
            return list(self.data["queues"].get(self.active_queue_name, []))

    def get_queue_item(self, item_id: str) -> QueueItem | None:
        """P2: O(1)-ish lookup of a single queue item by id — avoids full list copy."""
        with self._lock:
            queue = self.data["queues"].get(self.active_queue_name, [])
            return next((i for i in queue if i["id"] == item_id), None)

    def active_queue_length(self) -> int:
        """Return the number of items in the active queue without copying it."""
        with self._lock:
            return len(self.data["queues"].get(self.active_queue_name, []))

    def update_active_queue(self, new_queue: list[QueueItem], immediate: bool = True) -> None:
        """Replace the active queue in memory and optionally persist.

        Pass ``immediate=False`` during active download batch runs to defer the
        disk write — the periodic flush timer handles persistence.
        """
        with self._lock:
            qname = self.active_queue_name
            self.data["queues"][qname] = new_queue
            if immediate:
                self._db.replace_queue(qname, new_queue)
            else:
                self._dirty = True

    def set_active_queue(self, name: str) -> None:
        with self._lock:
            if name in self.data["queues"]:
                self.data["active_queue"] = name
                self._db.set_active_queue(name)

    def create_queue(self, name: str) -> bool:
        with self._lock:
            if name not in self.data["queues"]:
                self.data["queues"][name] = []
                self.data["active_queue"] = name
                self._db.create_queue(name)
                self._db.set_active_queue(name)
                return True
        return False

    def delete_queue(self, name: str) -> bool:
        """Delete a queue by name.

        Allows deleting the active queue as long as at least one other queue
        exists — automatically switches to ``'default'`` (or the first
        remaining queue) before deleting.
        """
        with self._lock:
            if name not in self.data["queues"]:
                return False
            if len(self.data["queues"]) <= 1:
                return False
            del self.data["queues"][name]
            if self.data["active_queue"] == name:
                fallback = "default" if "default" in self.data["queues"] else next(iter(self.data["queues"]))
                self.data["active_queue"] = fallback
            self._db.delete_queue(name)
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
            self._db.set_setting("queue_settings", self.data["settings"]["queue_settings"])

    def set_setting(self, key: str, value: Any, *, immediate: bool = True) -> None:
        """Write a single top-level setting key and persist.

        Pass ``immediate=False`` to defer the disk write to the next
        ``flush_if_dirty()`` cycle.
        """
        with self._lock:
            self.data["settings"][key] = value
            if immediate:
                self._db.set_setting(key, value)
            else:
                self._dirty = True

    def update_settings(self, updates: dict[str, Any]) -> None:
        """Apply multiple setting keys in a single lock window and flush once."""
        with self._lock:
            self.data["settings"].update(updates)
            self._db.update_settings(updates)

    # ── Download history ────────────────────────────────────────────────
    _HISTORY_MAX = 500

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
            if len(history) > self._HISTORY_MAX:
                self.data["download_history"] = history[-self._HISTORY_MAX:]
            self._db.record_download(name, console, size_str)

    @property
    def download_history(self) -> list[dict[str, str]]:
        with self._lock:
            return list(self.data.get("download_history", []))

    def clear_history(self) -> None:
        with self._lock:
            self.data["download_history"] = []
            self._db.clear_history()

    def mutate_settings(self, fn: Callable[[dict[str, Any]], None]) -> None:
        """Call *fn(settings_dict)* while holding the lock and flush once.

        Use this when the mutation is more complex than a flat key update
        (e.g. nested dict insert/delete on filter_presets).
        """
        with self._lock:
            fn(self.data["settings"])
            self._db.update_settings(self.data["settings"])
