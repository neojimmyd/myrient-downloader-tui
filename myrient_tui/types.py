"""Strongly-typed data structures used throughout Myrient TUI."""
from __future__ import annotations

from typing import Any, TypedDict

from textual.widgets import ListItem


class ConsoleItem(TypedDict):
    """One row returned by the Myrient console index scrape."""
    name:     str   # decoded display name, e.g. "Sony - PlayStation 2/"
    url_part: str   # href as-scraped (still percent-encoded)
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


class GameMetadata(TypedDict):
    """IGDB-sourced metadata cached locally for a single game."""
    igdb_id:    int          # IGDB game ID
    rating:     float        # total_rating 0-100, or -1 if unrated
    popularity: int          # total_rating_count from IGDB
    genres:     list[str]    # e.g. ["Puzzle", "Adventure"]
    themes:     list[str]    # e.g. ["Horror", "Survival"]
    game_modes: list[str]    # e.g. ["Single player", "Co-operative"]


class RomEntry(TypedDict):
    """One <rom> element parsed from a Redump DAT file."""
    name:  str   # filename stored in the DAT
    game:  str   # parent <game name="…"> attribute


class DataListItem(ListItem):
    """C2: ListItem subclass with a typed data field — replaces monkey-patching."""

    def __init__(self, *args: Any, data: Any = None, **kwargs: Any) -> None:
        super().__init__(*args, **kwargs)
        self.data = data
