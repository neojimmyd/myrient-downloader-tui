"""SQLite-backed storage for config, queues, history, and library status.

Replaces the monolithic JSON file with per-row CRUD — no more serializing
the entire state on every queue mutation.  Uses WAL mode for concurrent
reads from worker threads while the main thread writes.

Auto-migrates from the legacy JSON config on first run.
"""
from __future__ import annotations

import json
import logging
import sqlite3
import threading
import time
from pathlib import Path
from typing import Any

from myrient_tui.constants import _DATA_DIR, CONFIG_FILE

_DB_PATH = _DATA_DIR / "myrient.db"

# Schema version — bump when tables change.
_SCHEMA_VERSION = 1

_SCHEMA_SQL = """\
CREATE TABLE IF NOT EXISTS meta (
    key   TEXT PRIMARY KEY,
    value TEXT NOT NULL
);

-- Flat key/value for settings (value is JSON-encoded).
CREATE TABLE IF NOT EXISTS settings (
    key   TEXT PRIMARY KEY,
    value TEXT NOT NULL
);

-- Named download queues.
CREATE TABLE IF NOT EXISTS queues (
    name TEXT PRIMARY KEY
);

-- Items within a queue.  position determines display order.
CREATE TABLE IF NOT EXISTS queue_items (
    id       TEXT PRIMARY KEY,
    queue    TEXT NOT NULL REFERENCES queues(name) ON DELETE CASCADE,
    name     TEXT NOT NULL,
    game_url TEXT NOT NULL,
    dest_path TEXT NOT NULL,
    size_str TEXT NOT NULL DEFAULT 'N/A',
    status   TEXT NOT NULL DEFAULT 'pending',
    position INTEGER NOT NULL DEFAULT 0,
    extra    TEXT NOT NULL DEFAULT '{}'
);
CREATE INDEX IF NOT EXISTS idx_qi_queue ON queue_items(queue);

-- Download history log.
CREATE TABLE IF NOT EXISTS download_history (
    id        INTEGER PRIMARY KEY AUTOINCREMENT,
    name      TEXT NOT NULL,
    console   TEXT NOT NULL,
    size      TEXT NOT NULL,
    timestamp TEXT NOT NULL
);

-- Library validation status (replaces .myrient_status.json).
CREATE TABLE IF NOT EXISTS library_status (
    path   TEXT PRIMARY KEY,
    status TEXT NOT NULL CHECK(status IN ('validated', 'corrupted'))
);

-- IGDB metadata cache.
CREATE TABLE IF NOT EXISTS igdb_cache (
    platform_id   INTEGER NOT NULL,
    clean_name    TEXT NOT NULL,
    igdb_id       INTEGER,
    rating        REAL DEFAULT -1,
    popularity    INTEGER DEFAULT 0,
    genres        TEXT DEFAULT '[]',
    themes        TEXT DEFAULT '[]',
    game_modes    TEXT DEFAULT '[]',
    fetched_at    REAL NOT NULL,
    PRIMARY KEY (platform_id, clean_name)
);
"""

log = logging.getLogger(__name__)


class SQLiteStorage:
    """Thread-safe SQLite storage with WAL mode.

    Every public method acquires its own connection from the thread-local
    pool, so it is safe to call from any thread.
    """

    HISTORY_MAX = 500

    def __init__(self, db_path: Path | None = None) -> None:
        self.db_path = db_path or _DB_PATH
        self.db_path.parent.mkdir(parents=True, exist_ok=True)
        self._local = threading.local()
        self._init_schema()
        self._maybe_migrate_json()

    # ── Connection management ────────────────────────────────────────────

    def _conn(self) -> sqlite3.Connection:
        """Return a thread-local connection (created on first access)."""
        conn = getattr(self._local, 'conn', None)
        if conn is None:
            conn = sqlite3.connect(str(self.db_path), timeout=10)
            conn.execute("PRAGMA journal_mode=WAL")
            conn.execute("PRAGMA foreign_keys=ON")
            conn.execute("PRAGMA synchronous=NORMAL")
            conn.row_factory = sqlite3.Row
            self._local.conn = conn
        return conn

    def close(self) -> None:
        """Close the thread-local connection if open."""
        conn = getattr(self._local, 'conn', None)
        if conn is not None:
            conn.close()
            self._local.conn = None

    # ── Schema ───────────────────────────────────────────────────────────

    def _init_schema(self) -> None:
        conn = self._conn()
        conn.executescript(_SCHEMA_SQL)
        # Store schema version
        conn.execute(
            "INSERT OR IGNORE INTO meta(key, value) VALUES ('schema_version', ?)",
            (str(_SCHEMA_VERSION),),
        )
        conn.commit()

    # ── JSON migration ───────────────────────────────────────────────────

    def _maybe_migrate_json(self) -> None:
        """One-time migration from the legacy JSON config file."""
        conn = self._conn()
        row = conn.execute(
            "SELECT value FROM meta WHERE key='migrated_json'"
        ).fetchone()
        if row is not None:
            return  # already migrated

        json_path = CONFIG_FILE
        if not json_path.exists():
            # No legacy file — mark as migrated and seed defaults
            conn.execute(
                "INSERT INTO meta(key, value) VALUES ('migrated_json', '1')"
            )
            conn.execute(
                "INSERT OR IGNORE INTO queues(name) VALUES ('default')"
            )
            conn.execute(
                "INSERT OR IGNORE INTO meta(key, value) VALUES ('active_queue', 'default')"
            )
            conn.commit()
            return

        log.info("Migrating JSON config → SQLite: %s", json_path)
        try:
            with open(json_path, 'r', encoding='utf-8') as f:
                data = json.load(f)
        except (json.JSONDecodeError, OSError) as exc:
            log.error("JSON migration failed: %s", exc)
            conn.execute(
                "INSERT INTO meta(key, value) VALUES ('migrated_json', '1')"
            )
            conn.commit()
            return

        # Settings
        for k, v in data.get("settings", {}).items():
            conn.execute(
                "INSERT OR REPLACE INTO settings(key, value) VALUES (?, ?)",
                (k, json.dumps(v)),
            )

        # Queues and queue items
        queues = data.get("queues", {"default": []})
        active = data.get("active_queue", "default")
        for qname, items in queues.items():
            conn.execute("INSERT OR IGNORE INTO queues(name) VALUES (?)", (qname,))
            for pos, item in enumerate(items):
                # Extract known fields, put the rest in extra
                item_id = item.get("id", f"migrated_{pos}")
                known = {"id", "name", "game_url", "dest_path", "size_str", "status"}
                extra = {k: v for k, v in item.items() if k not in known}
                conn.execute(
                    "INSERT OR IGNORE INTO queue_items"
                    "(id, queue, name, game_url, dest_path, size_str, status, position, extra)"
                    " VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
                    (
                        item_id,
                        qname,
                        item.get("name", ""),
                        item.get("game_url", ""),
                        item.get("dest_path", ""),
                        item.get("size_str", "N/A"),
                        item.get("status", "pending"),
                        pos,
                        json.dumps(extra),
                    ),
                )
        conn.execute(
            "INSERT OR REPLACE INTO meta(key, value) VALUES ('active_queue', ?)",
            (active,),
        )

        # Download history
        for entry in data.get("download_history", []):
            conn.execute(
                "INSERT INTO download_history(name, console, size, timestamp)"
                " VALUES (?, ?, ?, ?)",
                (
                    entry.get("name", ""),
                    entry.get("console", ""),
                    entry.get("size", ""),
                    entry.get("timestamp", ""),
                ),
            )

        conn.execute(
            "INSERT INTO meta(key, value) VALUES ('migrated_json', '1')"
        )
        conn.commit()
        log.info("JSON → SQLite migration complete.")

    # ── Settings ─────────────────────────────────────────────────────────

    def get_setting(self, key: str, default: Any = None) -> Any:
        row = self._conn().execute(
            "SELECT value FROM settings WHERE key=?", (key,)
        ).fetchone()
        if row is None:
            return default
        return json.loads(row["value"])

    def get_all_settings(self) -> dict[str, Any]:
        rows = self._conn().execute("SELECT key, value FROM settings").fetchall()
        return {r["key"]: json.loads(r["value"]) for r in rows}

    def set_setting(self, key: str, value: Any) -> None:
        self._conn().execute(
            "INSERT OR REPLACE INTO settings(key, value) VALUES (?, ?)",
            (key, json.dumps(value)),
        )
        self._conn().commit()

    def update_settings(self, updates: dict[str, Any]) -> None:
        conn = self._conn()
        for k, v in updates.items():
            conn.execute(
                "INSERT OR REPLACE INTO settings(key, value) VALUES (?, ?)",
                (k, json.dumps(v)),
            )
        conn.commit()

    # ── Queue management ─────────────────────────────────────────────────

    def get_active_queue_name(self) -> str:
        row = self._conn().execute(
            "SELECT value FROM meta WHERE key='active_queue'"
        ).fetchone()
        return row["value"] if row else "default"

    def set_active_queue(self, name: str) -> None:
        conn = self._conn()
        exists = conn.execute(
            "SELECT 1 FROM queues WHERE name=?", (name,)
        ).fetchone()
        if exists:
            conn.execute(
                "INSERT OR REPLACE INTO meta(key, value) VALUES ('active_queue', ?)",
                (name,),
            )
            conn.commit()

    def list_queues(self) -> list[str]:
        rows = self._conn().execute("SELECT name FROM queues ORDER BY name").fetchall()
        return [r["name"] for r in rows]

    def create_queue(self, name: str) -> bool:
        conn = self._conn()
        try:
            conn.execute("INSERT INTO queues(name) VALUES (?)", (name,))
            conn.execute(
                "INSERT OR REPLACE INTO meta(key, value) VALUES ('active_queue', ?)",
                (name,),
            )
            conn.commit()
            return True
        except sqlite3.IntegrityError:
            return False

    def delete_queue(self, name: str) -> bool:
        conn = self._conn()
        count = conn.execute("SELECT COUNT(*) AS c FROM queues").fetchone()["c"]
        if count <= 1:
            return False
        exists = conn.execute(
            "SELECT 1 FROM queues WHERE name=?", (name,)
        ).fetchone()
        if not exists:
            return False
        conn.execute("DELETE FROM queues WHERE name=?", (name,))
        # If we deleted the active queue, switch to another
        active = self.get_active_queue_name()
        if active == name:
            fallback = conn.execute("SELECT name FROM queues LIMIT 1").fetchone()
            if fallback:
                conn.execute(
                    "INSERT OR REPLACE INTO meta(key, value) VALUES ('active_queue', ?)",
                    (fallback["name"],),
                )
        conn.commit()
        return True

    # ── Queue items ──────────────────────────────────────────────────────

    def get_queue_items(self, queue_name: str | None = None) -> list[dict[str, Any]]:
        """Return all items in a queue as dicts (compatible with QueueItem)."""
        qname = queue_name or self.get_active_queue_name()
        rows = self._conn().execute(
            "SELECT * FROM queue_items WHERE queue=? ORDER BY position",
            (qname,),
        ).fetchall()
        result = []
        for r in rows:
            item: dict[str, Any] = {
                "id": r["id"],
                "name": r["name"],
                "game_url": r["game_url"],
                "dest_path": r["dest_path"],
                "size_str": r["size_str"],
            }
            # Merge extra fields (status, progress, etc.)
            extra = json.loads(r["extra"]) if r["extra"] else {}
            if r["status"] != "pending":
                item["status"] = r["status"]
            item.update(extra)
            result.append(item)
        return result

    def get_queue_item(self, item_id: str) -> dict[str, Any] | None:
        row = self._conn().execute(
            "SELECT * FROM queue_items WHERE id=?", (item_id,)
        ).fetchone()
        if row is None:
            return None
        item: dict[str, Any] = {
            "id": row["id"],
            "name": row["name"],
            "game_url": row["game_url"],
            "dest_path": row["dest_path"],
            "size_str": row["size_str"],
        }
        extra = json.loads(row["extra"]) if row["extra"] else {}
        if row["status"] != "pending":
            item["status"] = row["status"]
        item.update(extra)
        return item

    def queue_length(self, queue_name: str | None = None) -> int:
        qname = queue_name or self.get_active_queue_name()
        row = self._conn().execute(
            "SELECT COUNT(*) AS c FROM queue_items WHERE queue=?", (qname,)
        ).fetchone()
        return row["c"]

    def add_queue_item(self, queue_name: str, item: dict[str, Any]) -> None:
        """Insert a single item at the end of the named queue."""
        conn = self._conn()
        # Get next position
        row = conn.execute(
            "SELECT COALESCE(MAX(position), -1) + 1 AS pos FROM queue_items WHERE queue=?",
            (queue_name,),
        ).fetchone()
        pos = row["pos"]
        known = {"id", "name", "game_url", "dest_path", "size_str", "status"}
        extra = {k: v for k, v in item.items() if k not in known}
        conn.execute(
            "INSERT OR REPLACE INTO queue_items"
            "(id, queue, name, game_url, dest_path, size_str, status, position, extra)"
            " VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
            (
                item["id"],
                queue_name,
                item.get("name", ""),
                item.get("game_url", ""),
                item.get("dest_path", ""),
                item.get("size_str", "N/A"),
                item.get("status", "pending"),
                pos,
                json.dumps(extra),
            ),
        )
        conn.commit()

    def update_queue_item(self, item_id: str, updates: dict[str, Any]) -> None:
        """Update specific fields on a queue item."""
        conn = self._conn()
        # First fetch current extra
        row = conn.execute(
            "SELECT extra FROM queue_items WHERE id=?", (item_id,)
        ).fetchone()
        if row is None:
            return

        known_cols = {"name", "game_url", "dest_path", "size_str", "status"}
        col_updates = {k: v for k, v in updates.items() if k in known_cols}
        extra_updates = {k: v for k, v in updates.items() if k not in known_cols and k != "id"}

        if extra_updates:
            current_extra = json.loads(row["extra"]) if row["extra"] else {}
            current_extra.update(extra_updates)
            col_updates["extra"] = json.dumps(current_extra)

        if col_updates:
            set_clause = ", ".join(f"{k}=?" for k in col_updates)
            values = list(col_updates.values()) + [item_id]
            conn.execute(
                f"UPDATE queue_items SET {set_clause} WHERE id=?",
                values,
            )
            conn.commit()

    def remove_queue_item(self, item_id: str) -> None:
        conn = self._conn()
        conn.execute("DELETE FROM queue_items WHERE id=?", (item_id,))
        conn.commit()

    def replace_queue(self, queue_name: str, items: list[dict[str, Any]]) -> None:
        """Replace all items in a queue (bulk update — used for reordering etc.)."""
        conn = self._conn()
        conn.execute("DELETE FROM queue_items WHERE queue=?", (queue_name,))
        known = {"id", "name", "game_url", "dest_path", "size_str", "status"}
        for pos, item in enumerate(items):
            extra = {k: v for k, v in item.items() if k not in known}
            conn.execute(
                "INSERT INTO queue_items"
                "(id, queue, name, game_url, dest_path, size_str, status, position, extra)"
                " VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
                (
                    item["id"],
                    queue_name,
                    item.get("name", ""),
                    item.get("game_url", ""),
                    item.get("dest_path", ""),
                    item.get("size_str", "N/A"),
                    item.get("status", "pending"),
                    pos,
                    json.dumps(extra),
                ),
            )
        conn.commit()

    def get_all_queues(self) -> dict[str, list[dict[str, Any]]]:
        """Return all queues with their items (for backward compat)."""
        result: dict[str, list[dict[str, Any]]] = {}
        for qname in self.list_queues():
            result[qname] = self.get_queue_items(qname)
        return result

    # ── Download history ─────────────────────────────────────────────────

    def record_download(self, name: str, console: str, size_str: str) -> None:
        conn = self._conn()
        conn.execute(
            "INSERT INTO download_history(name, console, size, timestamp)"
            " VALUES (?, ?, ?, ?)",
            (name, console, size_str, time.strftime("%Y-%m-%d %H:%M:%S")),
        )
        # Trim oldest entries
        conn.execute(
            "DELETE FROM download_history WHERE id NOT IN "
            "(SELECT id FROM download_history ORDER BY id DESC LIMIT ?)",
            (self.HISTORY_MAX,),
        )
        conn.commit()

    def get_download_history(self) -> list[dict[str, str]]:
        rows = self._conn().execute(
            "SELECT name, console, size, timestamp FROM download_history ORDER BY id"
        ).fetchall()
        return [dict(r) for r in rows]

    def clear_history(self) -> None:
        conn = self._conn()
        conn.execute("DELETE FROM download_history")
        conn.commit()

    # ── Library status ───────────────────────────────────────────────────

    def get_library_status(self, path_key: str) -> str | None:
        row = self._conn().execute(
            "SELECT status FROM library_status WHERE path=?", (path_key,)
        ).fetchone()
        return row["status"] if row else None

    def set_library_status(self, path_key: str, status: str) -> None:
        if status not in ("validated", "corrupted"):
            raise ValueError(f"Invalid status {status!r}")
        self._conn().execute(
            "INSERT OR REPLACE INTO library_status(path, status) VALUES (?, ?)",
            (path_key, status),
        )
        self._conn().commit()

    def remove_library_status(self, path_key: str) -> None:
        self._conn().execute(
            "DELETE FROM library_status WHERE path=?", (path_key,)
        )
        self._conn().commit()

    def get_all_library_status(self) -> dict[str, str]:
        rows = self._conn().execute(
            "SELECT path, status FROM library_status"
        ).fetchall()
        return {r["path"]: r["status"] for r in rows}

    def set_library_status_batch(self, updates: dict[str, str | None]) -> None:
        """Bulk update library status. None values remove the entry."""
        conn = self._conn()
        for path_key, status in updates.items():
            if status is None:
                conn.execute(
                    "DELETE FROM library_status WHERE path=?", (path_key,)
                )
            else:
                conn.execute(
                    "INSERT OR REPLACE INTO library_status(path, status) VALUES (?, ?)",
                    (path_key, status),
                )
        conn.commit()

    def prune_library_status(self, library: Path) -> int:
        """Remove entries whose directories no longer exist. Returns count removed."""
        all_entries = self.get_all_library_status()
        stale = [k for k in all_entries if not (library / k).exists()]
        if stale:
            conn = self._conn()
            for k in stale:
                conn.execute("DELETE FROM library_status WHERE path=?", (k,))
            conn.commit()
        return len(stale)

    def migrate_library_status_json(self, json_data: dict[str, str]) -> None:
        """Import library status entries from the legacy JSON file."""
        conn = self._conn()
        for path_key, status in json_data.items():
            if status in ("validated", "corrupted"):
                conn.execute(
                    "INSERT OR IGNORE INTO library_status(path, status) VALUES (?, ?)",
                    (path_key, status),
                )
        conn.commit()

    # ── IGDB cache ────────────────────────────────────────────────────────

    def get_igdb_cache(
        self, platform_id: int, clean_names: list[str], ttl: float = 2592000.0,
    ) -> tuple[dict[str, dict], list[str]]:
        """Return (hits, misses) for given clean_names within TTL.

        *hits* maps clean_name → row dict with rating, popularity, genres, etc.
        *misses* is the list of clean_names not found or expired.
        """
        if not clean_names:
            return {}, []
        now = time.time()
        cutoff = now - ttl
        conn = self._conn()
        hits: dict[str, dict] = {}
        misses: list[str] = []
        # Query in batches to avoid SQLite variable limit
        batch_size = 900
        for i in range(0, len(clean_names), batch_size):
            batch = clean_names[i:i + batch_size]
            placeholders = ",".join("?" * len(batch))
            rows = conn.execute(
                f"SELECT * FROM igdb_cache "
                f"WHERE platform_id=? AND clean_name IN ({placeholders}) "
                f"AND fetched_at > ?",
                [platform_id] + batch + [cutoff],
            ).fetchall()
            found = set()
            for r in rows:
                name = r["clean_name"]
                found.add(name)
                hits[name] = {
                    "igdb_id":    r["igdb_id"],
                    "rating":     r["rating"],
                    "popularity": r["popularity"],
                    "genres":     json.loads(r["genres"]),
                    "themes":     json.loads(r["themes"]),
                    "game_modes": json.loads(r["game_modes"]),
                }
            misses.extend(n for n in batch if n not in found)
        return hits, misses

    def set_igdb_cache(self, platform_id: int, entries: dict[str, dict]) -> None:
        """Upsert IGDB metadata for multiple games."""
        if not entries:
            return
        conn = self._conn()
        now = time.time()
        for clean_name, meta in entries.items():
            conn.execute(
                "INSERT OR REPLACE INTO igdb_cache "
                "(platform_id, clean_name, igdb_id, rating, popularity, "
                " genres, themes, game_modes, fetched_at) "
                "VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
                (
                    platform_id,
                    clean_name,
                    meta.get("igdb_id", 0),
                    meta.get("rating", -1),
                    meta.get("popularity", 0),
                    json.dumps(meta.get("genres", [])),
                    json.dumps(meta.get("themes", [])),
                    json.dumps(meta.get("game_modes", [])),
                    now,
                ),
            )
        conn.commit()

    def clear_igdb_cache(self) -> None:
        """Drop all cached IGDB data."""
        conn = self._conn()
        conn.execute("DELETE FROM igdb_cache")
        conn.commit()

    def clear_igdb_misses(self) -> int:
        """Delete only cached IGDB miss entries (igdb_id=0).

        Returns the number of rows deleted so callers can report it.
        """
        conn = self._conn()
        cur = conn.execute("DELETE FROM igdb_cache WHERE igdb_id = 0")
        conn.commit()
        return cur.rowcount
