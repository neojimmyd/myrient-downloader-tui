from __future__ import annotations

from textual.app import ComposeResult
from textual.containers import Horizontal, Vertical, VerticalScroll
from textual.events import Key
from textual.message import Message
from textual.widgets import Button, DataTable, Input, Label, ListView


class GameSearchInput(Input):
    """Search input that intercepts arrow/Tab/Enter before Input consumes them."""

    class NavUp(Message):           pass
    class NavDown(Message):         pass
    class ToggleAtCursor(Message):  pass
    class QueueSelected(Message):   pass

    def _on_key(self, event: Key) -> None:
        match event.key:
            case "up":    self.post_message(self.NavUp())
            case "down":  self.post_message(self.NavDown())
            case "tab":   self.post_message(self.ToggleAtCursor())
            case "enter": self.post_message(self.QueueSelected())
            case _:
                super()._on_key(event)
                return
        event.prevent_default()
        event.stop()


class BrowsePane(Vertical):
    """Console browser + game selection."""

    def compose(self) -> ComposeResult:
        with Horizontal(id="browse-layout"):
            with Vertical(id="browse-left"):
                with Horizontal(id="browse-console-header"):
                    yield Label("Consoles", classes="section-header")
                    yield Label("", id="console-count")
                yield Input(placeholder="  filter consoles…", id="search-consoles", classes="search-bar")
                yield ListView(id="console-list")
                with Horizontal(id="browse-tags-header"):
                    yield Label("Tags & Filters", classes="section-header")
                yield VerticalScroll(id="browse-tags-panel")
            with Vertical(id="browse-right"):
                # Row 1: breadcrumb + toolbar merged into one compact line
                with Horizontal(id="browse-header"):
                    yield Label("", id="breadcrumb")
                    yield Label("", id="game-selection-count")
                    yield Button("Queue Selected", id="btn-add-queue", variant="success")
                    yield Button("Select All", id="btn-select-all")
                    yield Button("Refresh", id="btn-refresh-games")
                # Row 2: search + global toggle
                with Horizontal(id="browse-search-bar"):
                    yield GameSearchInput(placeholder="  search games…", id="search-games", classes="search-bar")
                    yield Button("Global", id="btn-toggle-global", classes="browse-global-btn")
                # Row 3: DataTable with visible clickable column headers for sorting
                yield DataTable(id="game-list", cursor_type="row", zebra_stripes=False)
                yield Label(
                    "Select a console to browse games",
                    id="browse-empty-state",
                )
