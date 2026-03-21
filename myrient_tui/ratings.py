"""IGDB ratings provider — fetches and caches game metadata.

Uses the Twitch OAuth client-credentials flow to authenticate with the
IGDB API, then queries for game ratings, genres, themes, and game modes.
Results are cached in SQLite with a configurable TTL.
"""
from __future__ import annotations

import json
import logging
import re
import threading
import time
import urllib.request
import urllib.error
import urllib.parse
from typing import Callable

from .storage import SQLiteStorage
from .types import GameMetadata

log = logging.getLogger(__name__)

# IGDB API endpoint
_IGDB_URL = "https://api.igdb.com/v4/games"
_TWITCH_TOKEN_URL = "https://id.twitch.tv/oauth2/token"

# Minimum interval between IGDB requests (4 req/s limit).
_MIN_REQUEST_INTERVAL = 0.26

# Default cache TTL: 30 days.
DEFAULT_CACHE_TTL = 30 * 24 * 3600.0

# Characters stripped when comparing IGDB results to ROM names.
_NORM_RE = re.compile(r"[^a-z0-9 ]")

# ── Myrient console name → IGDB platform ID mapping ──────────────────────
# Covers the most common Redump + No-Intro consoles.
# Full list: https://api-docs.igdb.com/#platform
CONSOLE_PLATFORM_MAP: dict[str, int] = {
    # Sony
    "Sony - PlayStation":                    7,
    "Sony - PlayStation 2":                  8,
    "Sony - PlayStation 3":                  9,
    "Sony - PlayStation Portable":          38,
    # Nintendo
    "Nintendo - GameCube":                  21,
    "Nintendo - Wii":                        5,
    "Nintendo - Wii U":                     41,
    "Nintendo - Game Boy Advance":          24,
    "Nintendo - Game Boy":                  33,
    "Nintendo - Game Boy Color":            22,
    "Nintendo - Nintendo DS":               20,
    "Nintendo - Nintendo 3DS":              37,
    "Nintendo - Nintendo 64":                4,
    "Nintendo - Nintendo 64DD":              4,
    "Nintendo - Super Nintendo Entertainment System": 19,
    "Nintendo - Nintendo Entertainment System": 18,
    "Nintendo - Switch":                   130,
    # Sega
    "Sega - Dreamcast":                     23,
    "Sega - Saturn":                        32,
    "Sega - Mega Drive - Genesis":          29,
    "Sega - Mega-CD - Sega CD":            78,
    "Sega - Master System - Mark III":      64,
    "Sega - Game Gear":                     35,
    "Sega - 32X":                           30,
    # Microsoft
    "Microsoft - Xbox":                     11,
    "Microsoft - Xbox 360":                 12,
    # NEC
    "NEC - PC Engine - TurboGrafx 16":      86,
    "NEC - PC Engine CD - TurboGrafx-CD":   86,
    # SNK
    "SNK - Neo Geo CD":                    136,
    # Atari
    "Atari - Jaguar":                       62,
    "Atari - Lynx":                         61,
    "Atari - 2600":                         59,
    "Atari - 7800":                         60,
    # Panasonic
    "Panasonic - 3DO Interactive Multiplayer": 50,
    # Bandai
    "Bandai - WonderSwan":                  57,
    "Bandai - WonderSwan Color":            57,
    # Commodore
    "Commodore - Amiga CD":                 16,
    # Philips
    "Philips - CD-i":                      117,
}


class RatingsProvider:
    """Fetches and caches IGDB game metadata.

    Usage::

        provider = RatingsProvider(db, client_id="...", client_secret="...")
        metadata = provider.fetch_console("Sony - PlayStation 2", clean_names)
    """

    def __init__(
        self,
        db: SQLiteStorage,
        client_id: str = "",
        client_secret: str = "",
        cache_ttl: float = DEFAULT_CACHE_TTL,
    ) -> None:
        self.db = db
        self.client_id = client_id
        self.client_secret = client_secret
        self.cache_ttl = cache_ttl
        self._token: str = ""
        self._token_expires: float = 0.0
        self._last_request: float = 0.0

    @property
    def configured(self) -> bool:
        """True if IGDB credentials are present."""
        return bool(self.client_id and self.client_secret)

    # ── Authentication ────────────────────────────────────────────────────

    def _authenticate(self) -> str:
        """Obtain or reuse a Twitch OAuth bearer token."""
        now = time.time()
        if self._token and now < self._token_expires:
            return self._token

        params = urllib.parse.urlencode({
            "client_id": self.client_id,
            "client_secret": self.client_secret,
            "grant_type": "client_credentials",
        })
        req = urllib.request.Request(
            _TWITCH_TOKEN_URL,
            data=params.encode(),
            method="POST",
        )
        try:
            with urllib.request.urlopen(req, timeout=15) as resp:
                body = json.loads(resp.read())
            self._token = body["access_token"]
            # Expire a bit early to avoid edge-case failures.
            self._token_expires = now + body.get("expires_in", 3600) - 60
            log.info("IGDB: authenticated (token valid for %ds)", body.get("expires_in", 0))
            return self._token
        except Exception as exc:
            log.error("IGDB auth failed: %s", exc)
            raise

    # ── IGDB query ────────────────────────────────────────────────────────

    def _rate_limit(self) -> None:
        """Sleep if needed to respect the 4-req/s limit."""
        now = time.time()
        elapsed = now - self._last_request
        if elapsed < _MIN_REQUEST_INTERVAL:
            time.sleep(_MIN_REQUEST_INTERVAL - elapsed)
        self._last_request = time.time()

    def _query(self, body: str) -> list[dict]:
        """Send an Apicalypse query to IGDB and return parsed JSON."""
        token = self._authenticate()
        self._rate_limit()
        req = urllib.request.Request(
            _IGDB_URL,
            data=body.encode("utf-8"),
            headers={
                "Client-ID": self.client_id,
                "Authorization": f"Bearer {token}",
                "Content-Type": "text/plain",
            },
            method="POST",
        )
        try:
            with urllib.request.urlopen(req, timeout=30) as resp:
                return json.loads(resp.read())
        except urllib.error.HTTPError as exc:
            if exc.code == 401:
                # Token expired — clear and retry once.
                self._token = ""
                self._token_expires = 0.0
                token = self._authenticate()
                req.add_header("Authorization", f"Bearer {token}")
                self._rate_limit()
                with urllib.request.urlopen(req, timeout=30) as resp:
                    return json.loads(resp.read())
            log.error("IGDB query failed (HTTP %d): %s", exc.code, exc.reason)
            raise

    # ── Name matching ─────────────────────────────────────────────────────

    @staticmethod
    def _normalize_for_match(name: str) -> str:
        """Lowercase, strip punctuation for fuzzy comparison."""
        return _NORM_RE.sub("", name.lower()).strip()

    def _best_match(
        self, results: list[dict], clean_name: str,
    ) -> dict | None:
        """Pick the IGDB result whose name most closely matches *clean_name*."""
        target = self._normalize_for_match(clean_name)
        if not target:
            return None
        # Exact match first
        for r in results:
            if self._normalize_for_match(r.get("name", "")) == target:
                return r
        # Prefix match (IGDB name starts with our name, or vice versa)
        for r in results:
            igdb_norm = self._normalize_for_match(r.get("name", ""))
            if igdb_norm.startswith(target) or target.startswith(igdb_norm):
                return r
        return None

    # ── Public API ────────────────────────────────────────────────────────

    def fetch_console(
        self,
        console_name: str,
        clean_names: list[str],
        cancel: threading.Event | None = None,
        on_progress: Callable[[int, int], None] | None = None,
    ) -> dict[str, GameMetadata]:
        """Fetch IGDB metadata for a list of games on a given console.

        Returns a dict mapping clean_name → GameMetadata for every game
        that was found (either cached or freshly fetched).  Games not
        matched in IGDB are omitted from the result.

        *cancel*: if set, the batch loop stops early.
        *on_progress*: called with (fetched_so_far, total_misses) after
        each batch.
        """
        platform_id = CONSOLE_PLATFORM_MAP.get(console_name)
        if platform_id is None:
            log.debug("IGDB: no platform mapping for %r", console_name)
            return {}

        if not self.configured:
            return {}

        # Check cache first
        cached, misses = self.db.get_igdb_cache(
            platform_id, clean_names, self.cache_ttl,
        )

        if not misses:
            return cached  # type: ignore[return-value]

        # Batch-query IGDB for misses.  IGDB handles multi-KB Apicalypse
        # bodies fine; 50 names ≈ 2.5 KB which is well within limits.
        batch_size = 50
        fresh: dict[str, dict] = {}
        total_misses = len(misses)
        consecutive_failures = 0
        max_consecutive_failures = 3
        for i in range(0, total_misses, batch_size):
            if cancel and cancel.is_set():
                log.info("IGDB: fetch cancelled after %d/%d", i, total_misses)
                break
            batch = misses[i:i + batch_size]
            batch_results: dict[str, dict] = {}
            try:
                self._fetch_batch(platform_id, batch, batch_results)
            except Exception as exc:
                consecutive_failures += 1
                log.warning("IGDB batch %d failed: %s", i // batch_size + 1, exc)
                if consecutive_failures >= max_consecutive_failures:
                    raise RuntimeError(
                        f"IGDB: {consecutive_failures} consecutive failures — "
                        f"last error: {exc}"
                    ) from exc
                continue
            consecutive_failures = 0
            # Persist each batch immediately so progress survives interruption
            if batch_results:
                self.db.set_igdb_cache(platform_id, batch_results)
                fresh.update(batch_results)
            done = min(i + batch_size, total_misses)
            if on_progress:
                on_progress(done, total_misses)

        cached.update(fresh)
        return cached  # type: ignore[return-value]

    def _fetch_batch(
        self,
        platform_id: int,
        clean_names: list[str],
        out: dict[str, dict],
    ) -> None:
        """Query IGDB for a small batch of game names and populate *out*.

        Raises on query failure so the caller can track consecutive errors.
        """
        # Build OR-clauses for each name
        name_clauses = []
        for name in clean_names:
            escaped = name.replace('"', '\\"')
            name_clauses.append(f'name ~ *"{escaped}"*')

        where = " | ".join(f"({c})" for c in name_clauses)
        body = (
            "fields name, total_rating, total_rating_count, follows, "
            "genres.name, themes.name, game_modes.name; "
            f"where platforms = [{platform_id}] & ({where}); "
            "limit 500;"
        )

        results = self._query(body)

        # Match each result back to a clean_name
        for clean_name in clean_names:
            match = self._best_match(results, clean_name)
            if match is None:
                # Cache a miss so we don't re-query next time
                out[clean_name] = {
                    "igdb_id": 0,
                    "rating": -1,
                    "popularity": 0,
                    "genres": [],
                    "themes": [],
                    "game_modes": [],
                }
                continue
            out[clean_name] = {
                "igdb_id":    match.get("id", 0),
                "rating":     match.get("total_rating", -1) or -1,
                "popularity": match.get("total_rating_count", 0) or 0,
                "genres":     [g["name"] for g in match.get("genres", []) if "name" in g],
                "themes":     [t["name"] for t in match.get("themes", []) if "name" in t],
                "game_modes": [m["name"] for m in match.get("game_modes", []) if "name" in m],
            }
