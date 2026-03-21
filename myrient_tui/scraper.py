from __future__ import annotations

import threading
import time
import urllib.request
from typing import Any, Callable
from urllib.parse import unquote

from bs4 import BeautifulSoup
from textual.message import Message

from myrient_tui.constants import _LINK_CACHE_TTL, _SCRAPE_STRAINER, SIZE_REGEX
from myrient_tui.messages import SystemLog
from myrient_tui.types import ConsoleItem, GameItem


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

    def __init__(self, post_message_fn: Callable[[Message], None]) -> None:
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
