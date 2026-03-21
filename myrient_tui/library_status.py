"""Thread-safe library validation status store, backed by SQLite.

Tracks per-game-directory validation status ('validated' or 'corrupted').
Absence from the store means 'incomplete'.  Keys are POSIX-style paths
relative to the library root so the store is portable across mount points.

On first load, migrates any existing JSON status file and legacy marker
files (.validated/.corrupted) into the SQLite store.
"""
from __future__ import annotations

import json
import logging
import threading
from pathlib import Path

from myrient_tui.constants import _DATA_DIR
from myrient_tui.storage import SQLiteStorage


class LibraryStatus:
    """Thread-safe store for game directory validation status.

    Uses SQLiteStorage for durable persistence while keeping an in-memory
    cache for fast reads (the library tree reads status on every render).
    Batch operations use ``defer_flushes`` to amortize writes.
    """

    _LEGACY_STATUS_FILE = _DATA_DIR / ".myrient_status.json"

    def __init__(self) -> None:
        self._lock = threading.Lock()
        self._data: dict[str, str] = {}
        self._library: Path | None = None
        self._defer_flush = False
        self._pending: dict[str, str | None] = {}  # batched writes when deferred
        self._db: SQLiteStorage | None = None

    # ── Public API ────────────────────────────────────────────────────────────

    def load(self, library: Path, db: SQLiteStorage | None = None) -> None:
        """(Re)load status for *library*.  Safe to call from any thread.

        If *db* is provided, uses that SQLiteStorage instance; otherwise
        creates one internally.
        """
        if db is not None:
            self._db = db
        elif self._db is None:
            self._db = SQLiteStorage()

        # Load from SQLite
        data = self._db.get_all_library_status()

        # One-time migration from legacy JSON file
        if self._LEGACY_STATUS_FILE.exists():
            try:
                with open(self._LEGACY_STATUS_FILE, 'r', encoding='utf-8') as f:
                    json_data: dict[str, str] = json.load(f)
                # Only import keys not already in SQLite
                new_entries = {k: v for k, v in json_data.items() if k not in data}
                if new_entries:
                    self._db.migrate_library_status_json(new_entries)
                    data.update(new_entries)
                self._LEGACY_STATUS_FILE.unlink()
                logging.info("Migrated library status JSON → SQLite (%d entries)", len(json_data))
            except (json.JSONDecodeError, OSError):
                pass

        # One-time migration from library-root JSON file
        old_lib_path = library / ".myrient_status.json"
        if old_lib_path.exists():
            try:
                with open(old_lib_path, 'r', encoding='utf-8') as f:
                    old_data: dict[str, str] = json.load(f)
                new_entries = {k: v for k, v in old_data.items() if k not in data}
                if new_entries:
                    self._db.migrate_library_status_json(new_entries)
                    data.update(new_entries)
                old_lib_path.unlink()
            except (json.JSONDecodeError, OSError):
                pass

        with self._lock:
            self._library = library
            self._data = data

        self._migrate_marker_files(library)

    def get(self, path: Path) -> str | None:
        """Return ``'validated'``, ``'corrupted'``, or ``None`` (incomplete/unknown)."""
        with self._lock:
            lib = self._library
            key = self._key(path, lib)
            if key is None:
                return None
            return self._data.get(key)

    def set_status(self, path: Path, status: str) -> None:
        """Set *path* to ``'validated'`` or ``'corrupted'``."""
        if status not in ("validated", "corrupted"):
            raise ValueError(f"Invalid status {status!r}; expected 'validated' or 'corrupted'")
        with self._lock:
            lib = self._library
            key = self._key(path, lib)
            if key is None:
                return
            self._data[key] = status
            if self._defer_flush:
                self._pending[key] = status
                return
        # Write immediately if not deferring
        if self._db is not None:
            self._db.set_library_status(key, status)

    def remove(self, path: Path) -> None:
        """Remove *path* from the store (marks it incomplete)."""
        with self._lock:
            lib = self._library
            key = self._key(path, lib)
            if key is None:
                return
            self._data.pop(key, None)
            if self._defer_flush:
                self._pending[key] = None  # None = delete
                return
        if self._db is not None:
            self._db.remove_library_status(key)

    def defer_flushes(self, defer: bool = True) -> None:
        """When *defer* is True, mutations are batched in memory.

        When set back to False, all pending changes are flushed to SQLite
        in a single transaction.
        """
        self._defer_flush = defer
        if not defer:
            self._flush_pending()

    def prune(self, library: Path) -> None:
        """Drop entries whose directories no longer exist."""
        with self._lock:
            stale = [k for k in self._data if not (library / k).exists()]
            for k in stale:
                del self._data[k]
        if stale and self._db is not None:
            self._db.set_library_status_batch({k: None for k in stale})

    # ── Internal helpers ──────────────────────────────────────────────────────

    @staticmethod
    def _key(path: Path, library: Path | None) -> str | None:
        """Compute a POSIX-relative key for *path* against *library*."""
        if library is None:
            return None
        try:
            return path.relative_to(library).as_posix()
        except ValueError:
            return None

    def _flush_pending(self) -> None:
        """Write all pending batched changes to SQLite."""
        with self._lock:
            pending = dict(self._pending)
            self._pending.clear()
        if pending and self._db is not None:
            self._db.set_library_status_batch(pending)

    def _migrate_marker_files(self, library: Path) -> None:
        """One-time migration: scan for legacy ``.validated`` / ``.corrupted``
        files, import them into the store, then delete them."""
        if not library.exists():
            return
        migrated = 0
        batch: dict[str, str] = {}
        try:
            for marker_name, status in ((".validated", "validated"), (".corrupted", "corrupted")):
                for marker_file in library.rglob(marker_name):
                    game_dir = marker_file.parent
                    key = self._key(game_dir, library)
                    if key is None:
                        continue
                    with self._lock:
                        if key not in self._data:
                            self._data[key] = status
                            batch[key] = status
                    try:
                        marker_file.unlink()
                        migrated += 1
                    except OSError:
                        pass
        except (PermissionError, OSError):
            pass
        if batch and self._db is not None:
            self._db.migrate_library_status_json(batch)
        if migrated:
            logging.info("Migrated %d marker files → SQLite", migrated)
