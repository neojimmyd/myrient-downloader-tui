"""IGDB ratings provider — fetches and caches game metadata.

Uses the Twitch OAuth client-credentials flow to authenticate with the
IGDB API, then queries for game ratings, genres, themes, and game modes.
Results are cached in SQLite with a configurable TTL.
"""
from __future__ import annotations

import heapq
import json
import logging
import re
import threading
import time
import unicodedata
import urllib.request
import urllib.error
import urllib.parse
from collections.abc import Callable
from difflib import SequenceMatcher

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

# Detects title/subtitle separators (' - ' or ': ') for search-key extraction.
_SEP_RE = re.compile(r'\s+-\s+|:\s+')

# Known publisher/creator name prefixes (normalized form) that IGDB may
# prepend but Myrient omits.  Used by _best_match() Pass 1b.
_PUBLISHER_PREFIXES = (
    "sid meiers ",
    "tom clancys ",
    "disneys ",
    "walt disneys ",
    "clive barkers ",
    "peter jacksons ",
)

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
    "Nintendo - GameCube - NKit RVZ":       21,
    "Nintendo - GameCube - NKit RVZ [zstd-19-128k]": 21,
    "Nintendo - Wii":                        5,
    "Nintendo - Wii - NKit RVZ":             5,
    "Nintendo - Wii - NKit RVZ [zstd-19-128k]": 5,
    "Nintendo - Wii U":                     41,
    "Nintendo - Wii U - WUX":              41,
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
        self._rate_lock = threading.Lock()
        self._auth_lock = threading.Lock()

    @property
    def configured(self) -> bool:
        """True if IGDB credentials are present."""
        return bool(self.client_id and self.client_secret)

    # ── Authentication ────────────────────────────────────────────────────

    def _authenticate(self) -> str:
        """Obtain or reuse a Twitch OAuth bearer token.

        Serialized with ``_auth_lock`` so concurrent threads don't issue
        duplicate OAuth requests when the token expires.
        """
        with self._auth_lock:
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
        with self._rate_lock:
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
                with self._auth_lock:
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
        """Lowercase, transliterate accents, normalise articles, strip punctuation."""
        n = name.lower().replace('-', ' ')
        # Handle Redump's "Title, The" → "the title" article ordering
        for suffix in (', the', ', a', ', an'):
            if n.endswith(suffix):
                n = suffix[2:] + ' ' + n[:-len(suffix)]
                break
        # Decompose accented characters (é→e, ü→u, ñ→n, etc.)
        n = unicodedata.normalize('NFKD', n)
        n = _NORM_RE.sub("", n)
        return ' '.join(n.split())

    @staticmethod
    def _search_key(name: str) -> str:
        """Extract a search-friendly key from a clean game name.

        Redump uses ``' - '`` as a title/subtitle separator while IGDB uses
        ``': '``.  Searching with only the primary title avoids this literal
        mismatch in the wildcard query; :meth:`_best_match` then disambiguates
        among the broader result set.
        """
        m = _SEP_RE.search(name)
        if m and m.start() >= 4:
            return name[:m.start()].strip()
        return name

    @staticmethod
    def _strip_publisher(normalized: str) -> str:
        """Strip known publisher/creator name prefixes from a normalized name."""
        for p in _PUBLISHER_PREFIXES:
            if normalized.startswith(p):
                return normalized[len(p):]
        return normalized

    def _best_match(
        self, results: list[dict], clean_name: str,
    ) -> dict | None:
        """Pick the IGDB result whose name most closely matches *clean_name*."""
        target = self._normalize_for_match(clean_name)
        if not target:
            return None

        # Pass 1: exact normalized match
        for r in results:
            if self._normalize_for_match(r.get("name", "")) == target:
                return r

        # Pass 1b: exact match after stripping publisher/creator prefixes
        # Catches e.g. "Civilization II" → "Sid Meier's Civilization II"
        target_stripped = self._strip_publisher(target)
        for r in results:
            igdb_norm = self._normalize_for_match(r.get("name", ""))
            igdb_stripped = self._strip_publisher(igdb_norm)
            if (igdb_stripped != igdb_norm or target_stripped != target) \
                    and igdb_stripped == target_stripped:
                log.debug("IGDB publisher-prefix match %r → %r", clean_name, r.get("name", "?"))
                return r

        # Pass 2: prefix match — prefer the closest-length name
        best_prefix: dict | None = None
        best_diff = float('inf')
        for r in results:
            igdb_norm = self._normalize_for_match(r.get("name", ""))
            if igdb_norm.startswith(target) or target.startswith(igdb_norm):
                diff = abs(len(igdb_norm) - len(target))
                if diff < best_diff:
                    best_diff = diff
                    best_prefix = r
        if best_prefix is not None:
            return best_prefix

        # Pass 3: fuzzy matching via SequenceMatcher (threshold 0.68)
        best_fuzzy: dict | None = None
        best_ratio = 0.0
        for r in results:
            igdb_norm = self._normalize_for_match(r.get("name", ""))
            ratio = SequenceMatcher(None, target, igdb_norm).ratio()
            if ratio > best_ratio:
                best_ratio = ratio
                best_fuzzy = r
        if best_ratio >= 0.68:
            log.debug(
                "IGDB fuzzy match %r → %r (ratio=%.2f)",
                clean_name,
                best_fuzzy.get("name") if best_fuzzy else "?",
                best_ratio,
            )
            return best_fuzzy

        if best_ratio >= 0.55:
            log.debug(
                "IGDB near-miss %r → best candidate %r (ratio=%.2f, below 0.68)",
                clean_name,
                best_fuzzy.get("name") if best_fuzzy else "?",
                best_ratio,
            )

        return None

    # ── Public API ────────────────────────────────────────────────────────

    def fetch_console(
        self,
        console_name: str,
        clean_names: list[str],
        cancel: threading.Event | None = None,
        on_progress: Callable[[int, int], None] | None = None,
        on_log: Callable[[str], None] | None = None,
    ) -> dict[str, GameMetadata]:
        """Fetch IGDB metadata for a list of games on a given console.

        Returns a dict mapping clean_name → GameMetadata for every game
        that was found (either cached or freshly fetched).  Games not
        matched in IGDB are omitted from the result.

        *cancel*: if set, the batch loop stops early.
        *on_progress*: called with (fetched_so_far, total_misses) after
        each batch.
        *on_log*: called with a status string for TUI-visible messages.
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

        # For large miss counts, fetch all IGDB games for the platform and
        # match locally — avoids the 500-result cap and is more accurate.
        # For small miss counts, use targeted batch wildcard queries.
        if len(misses) >= 100:
            fresh = self._fetch_and_match_all(
                platform_id, misses, cancel, on_progress, on_log,
            )
        else:
            fresh = self._fetch_batched(
                platform_id, misses, cancel, on_progress,
            )

        cached.update(fresh)
        return cached  # type: ignore[return-value]

    @staticmethod
    def _meta_from_match(match: dict) -> dict:
        """Build a metadata dict from a matched IGDB result."""
        return {
            "igdb_id":    match.get("id", 0),
            "rating":     match.get("total_rating", -1) or -1,
            "popularity": match.get("total_rating_count", 0) or 0,
            "genres":     [g["name"] for g in match.get("genres", []) if "name" in g],
            "themes":     [t["name"] for t in match.get("themes", []) if "name" in t],
            "game_modes": [m["name"] for m in match.get("game_modes", []) if "name" in m],
        }

    @staticmethod
    def _miss_entry() -> dict:
        """Return a fresh miss-cache dict (avoids shared mutable lists)."""
        return {
            "igdb_id": 0, "rating": -1, "popularity": 0,
            "genres": [], "themes": [], "game_modes": [],
        }

    def _fetch_batch(
        self,
        platform_id: int,
        clean_names: list[str],
        out: dict[str, dict],
    ) -> None:
        """Query IGDB for a small batch of game names and populate *out*.

        Raises on query failure so the caller can track consecutive errors.
        """
        # Build OR-clauses using search keys for broader matching.
        # Redump separators (' - ') differ from IGDB (': '), so we query
        # with the primary title and let _best_match disambiguate.
        seen_clauses: set[str] = set()
        name_clauses: list[str] = []
        for name in clean_names:
            key = self._search_key(name)
            escaped = key.replace('"', '\\"')
            clause = f'name ~ *"{escaped}"*'
            if clause not in seen_clauses:
                seen_clauses.add(clause)
                name_clauses.append(clause)

        where = " | ".join(f"({c})" for c in name_clauses)
        body = (
            "fields name, total_rating, total_rating_count, follows, "
            "genres.name, themes.name, game_modes.name; "
            f"where platforms = [{platform_id}] & ({where}); "
            "limit 500;"
        )

        results = self._query(body)
        cap_hit = len(results) >= 500

        if cap_hit:
            log.info(
                "IGDB: 500-result cap hit for batch of %d names — "
                "will retry unmatched via search",
                len(clean_names),
            )

        # Match each result back to a clean_name
        unmatched: list[str] = []
        for clean_name in clean_names:
            match = self._best_match(results, clean_name)
            if match is None:
                unmatched.append(clean_name)
                continue
            out[clean_name] = self._meta_from_match(match)

        # When the 500-result cap was hit, some games may have been crowded
        # out of the response.  Retry unmatched names via individual search.
        if cap_hit and unmatched:
            log.info("IGDB: searching individually for %d unmatched games", len(unmatched))
            still_unmatched: list[str] = []
            for clean_name in unmatched:
                match = self._search_single(platform_id, clean_name)
                if match is not None:
                    out[clean_name] = self._meta_from_match(match)
                else:
                    still_unmatched.append(clean_name)
            unmatched = still_unmatched

        # Cache remaining unmatched as misses
        for clean_name in unmatched:
            out[clean_name] = self._miss_entry()

    def _search_single(
        self, platform_id: int, clean_name: str,
    ) -> dict | None:
        """Search IGDB for a single game using full-text search.

        Falls back to this when the batch wildcard query hit the 500-result
        cap and the game wasn't in the truncated result set.
        """
        escaped = clean_name.replace('"', '\\"')
        body = (
            f'search "{escaped}"; '
            "fields name, total_rating, total_rating_count, follows, "
            "genres.name, themes.name, game_modes.name; "
            f"where platforms = [{platform_id}]; "
            "limit 10;"
        )
        try:
            results = self._query(body)
        except Exception as exc:
            log.debug("IGDB search fallback failed for %r: %s", clean_name, exc)
            return None
        if not results:
            return None
        return self._best_match(results, clean_name)

    def _fetch_batched(
        self,
        platform_id: int,
        misses: list[str],
        cancel: threading.Event | None,
        on_progress: Callable[[int, int], None] | None,
    ) -> dict[str, dict]:
        """Fetch IGDB metadata using batched wildcard queries.

        Used for small miss counts (< 100) where per-name queries are
        more efficient than fetching the entire platform catalog.
        """
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
            if batch_results:
                self.db.set_igdb_cache(platform_id, batch_results)
                fresh.update(batch_results)
            done = min(i + batch_size, total_misses)
            if on_progress:
                on_progress(done, total_misses)
        return fresh

    def _fetch_and_match_all(
        self,
        platform_id: int,
        misses: list[str],
        cancel: threading.Event | None,
        on_progress: Callable[[int, int], None] | None,
        on_log: Callable[[str], None] | None = None,
    ) -> dict[str, dict]:
        """Fetch ALL IGDB games for a platform, then match locally.

        More accurate than batched wildcard queries for large game lists
        because it avoids the 500-result cap and wildcard substring
        issues.  Also uses alternative_names for broader matching.
        """
        _log = on_log or (lambda _: None)
        _log("IGDB: downloading full platform catalog from IGDB…")

        # Phase 1: paginated fetch of all IGDB games for this platform
        all_games: list[dict] = []
        offset = 0
        while True:
            if cancel and cancel.is_set():
                return {}
            body = (
                "fields name, alternative_names.name, "
                "total_rating, total_rating_count, follows, "
                "genres.name, themes.name, game_modes.name; "
                f"where platforms = [{platform_id}]; "
                "sort id asc; "
                f"limit 500; offset {offset};"
            )
            try:
                page = self._query(body)
            except Exception as exc:
                log.error("IGDB platform fetch failed at offset %d: %s", offset, exc)
                raise
            if not page:
                break
            all_games.extend(page)
            offset += len(page)
            _log(f"IGDB: downloaded {len(all_games)} games from IGDB so far…")
            if len(page) < 500:
                break

        log.info("IGDB: fetched %d games for platform %d", len(all_games), platform_id)
        _log(f"IGDB: {len(all_games)} games in IGDB for this platform — matching against {len(misses)} titles…")
        if not all_games:
            return {n: self._miss_entry() for n in misses}

        # Phase 2: build lookup structures from IGDB data
        igdb_entries: list[tuple[str, dict]] = []  # (primary_norm, game)
        exact_map: dict[str, dict] = {}
        stripped_map: dict[str, dict] = {}
        word_index: dict[str, list[int]] = {}

        for g in all_games:
            idx = len(igdb_entries)
            primary_norm = self._normalize_for_match(g.get("name", ""))
            igdb_entries.append((primary_norm, g))

            # Index primary name + all alternative names
            names = [g.get("name", "")]
            for alt in g.get("alternative_names", []):
                if isinstance(alt, dict) and alt.get("name"):
                    names.append(alt["name"])

            for name in names:
                norm = self._normalize_for_match(name)
                if not norm:
                    continue
                stripped = self._strip_publisher(norm)
                exact_map.setdefault(norm, g)
                if stripped != norm:
                    stripped_map.setdefault(stripped, g)
                for word in norm.split():
                    if len(word) >= 2:
                        word_index.setdefault(word, []).append(idx)

        # Phase 3: match each miss against the full IGDB list
        out: dict[str, dict] = {}
        chunk: dict[str, dict] = {}
        total = len(misses)

        for pos, clean_name in enumerate(misses):
            if cancel and cancel.is_set():
                break

            target = self._normalize_for_match(clean_name)
            target_stripped = self._strip_publisher(target)
            match: dict | None = None

            # Pass 1: O(1) exact match (includes alternative names)
            if target in exact_map:
                match = exact_map[target]

            # Pass 1b: publisher-prefix match
            if match is None:
                if target_stripped != target and target_stripped in exact_map:
                    match = exact_map[target_stripped]
                elif target in stripped_map:
                    match = stripped_map[target]
                elif target_stripped in stripped_map:
                    match = stripped_map[target_stripped]

            # Pass 2: prefix match (linear scan of primary names)
            if match is None:
                best_diff = float('inf')
                for norm, g in igdb_entries:
                    if norm.startswith(target) or target.startswith(norm):
                        diff = abs(len(norm) - len(target))
                        if diff < best_diff:
                            best_diff = diff
                            match = g

            # Pass 3: fuzzy match via inverted word index
            if match is None:
                target_words = [w for w in target.split() if len(w) >= 2]
                if target_words:
                    scores: dict[int, int] = {}
                    for word in target_words:
                        for i in word_index.get(word, ()):
                            scores[i] = scores.get(i, 0) + 1
                    top = heapq.nlargest(20, scores, key=scores.get)
                    best_ratio = 0.0
                    best_g: dict | None = None
                    for i in top:
                        norm = igdb_entries[i][0]
                        ratio = SequenceMatcher(None, target, norm).ratio()
                        if ratio > best_ratio:
                            best_ratio = ratio
                            best_g = igdb_entries[i][1]
                    if best_ratio >= 0.68:
                        match = best_g

            entry = self._meta_from_match(match) if match else self._miss_entry()
            out[clean_name] = entry
            chunk[clean_name] = entry

            # Persist in chunks for progress survival
            if len(chunk) >= 500:
                self.db.set_igdb_cache(platform_id, chunk)
                chunk.clear()
                if on_progress:
                    on_progress(pos + 1, total)

        if chunk:
            self.db.set_igdb_cache(platform_id, chunk)

        if on_progress:
            on_progress(total, total)

        matched = sum(1 for e in out.values() if e.get("igdb_id", 0) != 0)
        log.info("IGDB: matched %d/%d games for platform %d", matched, total, platform_id)
        _log(f"IGDB: matched {matched}/{total} games ({len(all_games)} in IGDB database)")
        # Log sample unmatched games for diagnostics
        unmatched_names = [n for n, e in out.items() if e.get("igdb_id", 0) == 0]
        if unmatched_names:
            sample = unmatched_names[:10]
            log.info(
                "IGDB: %d unmatched — sample: %s",
                len(unmatched_names), ", ".join(sample),
            )
            _log(f"IGDB: {len(unmatched_names)} unmatched — e.g. {', '.join(sample[:5])}")
        return out
