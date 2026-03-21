from __future__ import annotations

from textual.app import ComposeResult
from textual.containers import Container, Horizontal, Vertical, VerticalScroll
from textual.widgets import (
    Button, Collapsible, DataTable, Input, Label, ProgressBar, Select,
)


class DownloadsPane(Vertical):
    """Queue management + active download progress."""

    def compose(self) -> ComposeResult:
        with Horizontal(id="downloads-layout"):
            with Vertical(id="queue-panel"):
                yield Label("Queue", classes="section-header")
                yield DataTable(id="queue-table")
                yield Label("", id="queue-total-size")
                with Horizontal(classes="queue-controls"):
                    yield Button("Remove", id="btn-remove-items", variant="warning")
                    yield Button("▶ Start", id="btn-start-dl", variant="primary")
                    yield Button("■ Stop", id="btn-pause-dl", variant="error")
                with Collapsible(title="Queue Management", collapsed=True, id="queue-mgmt-collapsible"):
                    yield Select([], id="queue-select", prompt="active profile…")
                    yield Input(placeholder="new profile name…", id="input-new-queue")
                    with Horizontal(classes="btn-row"):
                        yield Button("Create", id="btn-create-queue", variant="success")
                        yield Button("Delete", id="btn-delete-queue", variant="error")
                    with Horizontal(classes="btn-row"):
                        yield Button("▲", id="btn-queue-up", classes="reorder-btn")
                        yield Button("▼", id="btn-queue-down", classes="reorder-btn")
                        yield Button("Clear All", id="btn-clear-queue", variant="error")
                    with Horizontal(classes="btn-row"):
                        yield Label("[dim]Schedule:[/dim]", classes="setting-label")
                        yield Input(placeholder="HH:MM (empty=now)", id="input-schedule-time", classes="schedule-input")
                        yield Button("⏱ Schedule", id="btn-schedule-dl")
                    with Horizontal(classes="btn-row"):
                        yield Button("Export", id="btn-export-queue", variant="default")
                        yield Button("Import", id="btn-import-queue", variant="default")
                    yield Input(placeholder="import/export path (blank=auto)", id="input-queue-io-path")
                with Collapsible(title="Queue Settings", collapsed=True, id="queue-settings-collapsible"):
                    yield Label("[dim]Per-queue speed limit (MB/s, 0=unlimited)[/dim]")
                    yield Input(placeholder="0", id="input-queue-speed-limit")
                    yield Label("[dim]Max concurrent downloads (blank=use global)[/dim]")
                    yield Input(placeholder="", id="input-queue-max-concurrent")
                    yield Button("Apply to Queue", id="btn-apply-queue-settings")
                with Collapsible(title="Download History", collapsed=True, id="history-collapsible"):
                    yield DataTable(id="history-table")
                    yield Button("Clear History", id="btn-clear-history", variant="warning")

            with Vertical(id="progress-panel"):
                yield Label("▸ DOWNLOAD PROGRESS", id="lbl-global-progress")
                yield ProgressBar(id="global-progress", show_eta=True)
                with VerticalScroll(id="progress-area"):
                    with Container(id="progress-grid"):
                        pass
