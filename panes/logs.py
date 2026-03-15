from __future__ import annotations

from textual.app import ComposeResult
from textual.containers import Horizontal, Vertical
from textual.widgets import Button, Input, ListView, RichLog, Rule


class LogsPane(Vertical):
    """System log + session file browser."""

    def compose(self) -> ComposeResult:
        with Vertical(id="logs-layout"):
            with Horizontal(id="log-toolbar"):
                yield Button("All", id="log-filter-all", classes="log-filter-btn")
                yield Button("Errors", id="log-filter-err", classes="log-filter-btn")
                yield Input(placeholder="  search logs…", id="log-search")
                yield Button("↺ Sessions", id="btn-refresh-session-logs")
            yield RichLog(id="sys-log", markup=True, wrap=True, max_lines=2000)
            yield Rule(id="sessions-divider")
            with Horizontal(id="sessions-layout"):
                yield ListView(id="session-log-list")
                yield RichLog(id="session-log-view", markup=False, wrap=True, max_lines=5000)
