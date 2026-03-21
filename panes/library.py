from __future__ import annotations

from textual.app import ComposeResult
from textual.containers import Container, Horizontal, Vertical
from textual.widgets import (
    Button, Input, Label, ProgressBar, Tree,
)


class LibraryPane(Vertical):
    """Library tree view + contextual detail panel."""

    def compose(self) -> ComposeResult:
        with Vertical(id="lib-tab-wrapper"):
            # ── Header: merged summary + compact tree controls ────────────
            with Horizontal(id="lib-header-bar"):
                yield Label("", id="lib-summary-bar")
                yield Label(" ✕ ", id="btn-lib-delete", classes="lib-hdr-btn lib-hdr-del")
            # ── Contextual toolbar (horizontal, above tree) ──────────────
            with Horizontal(id="lib-toolbar"):
                yield Button("Verify", id="btn-lib-dat-audit", classes="lib-tb-btn")
                yield Button("Convert CHD", id="btn-lib-convert", classes="lib-tb-btn")
                yield Button("CHD→Orig", id="btn-lib-chd-to-orig", classes="lib-tb-btn")
                yield Button("Refresh", id="btn-lib-refresh", classes="lib-tb-btn")
                yield Button("PS2 Patch", id="btn-ps2-md-patch", classes="lib-tb-btn")
                yield Button("Requeue ✗", id="btn-requeue-failed", classes="lib-tb-btn")
                yield Button("Requeue Console", id="btn-requeue-console", classes="lib-tb-btn")
            # ── Library search ────────────────────────────────────────────
            yield Input(placeholder="  search library…", id="lib-search", classes="search-bar")
            # ── Tree (full width) ─────────────────────────────────────────
            yield Tree("Library", id="lib-tree")
            # ── Status bar ────────────────────────────────────────────────
            with Container(id="lib-status-bar"):
                yield Label("Idle", id="lib-status-label")
                yield ProgressBar(id="lib-progress-bar", show_eta=True)
