from __future__ import annotations

from textual.app import ComposeResult
from textual.containers import Horizontal, VerticalScroll
from textual.widgets import (
    Button, DataTable, Input, Label, Rule, Select, Switch,
    TabbedContent, TabPane,
)
from textual.containers import Vertical



class SettingsPane(Vertical):
    """Settings organised into tabbed sections."""

    def compose(self) -> ComposeResult:
        from myrient_tui.constants import _COLLECTIONS

        with TabbedContent(id="settings-tabs"):
            with TabPane("Engine", id="tab-engine"):
                with VerticalScroll():
                    yield Label("Collection source", classes="setting-label")
                    yield Select(
                        [(k, k) for k in _COLLECTIONS],
                        id="set-collection", prompt="collection…",
                    )
                    yield Label("Library root path", classes="setting-label")
                    yield Input(id="set-lib-path")
                    yield Label("Max concurrent downloads  [dim](1–10)[/dim]", classes="setting-label")
                    yield Input(id="set-threads")
                    yield Label("Global speed limit per download  [dim](MB/s, 0=unlimited)[/dim]", classes="setting-label")
                    yield Input(id="set-speed-limit")
                    yield Label("DAT cache TTL  [dim](hours, 0=always refresh)[/dim]", classes="setting-label")
                    yield Input(id="set-dat-ttl")
                    yield Rule()
                    yield Label("Auto-convert to CHD after download", classes="setting-label")
                    yield Switch(id="set-auto-chd")
                    yield Label("Watch library for changes  [dim](requires watchdog)[/dim]", classes="setting-label")
                    yield Switch(id="set-watch-library")
                    yield Label("Desktop notification on batch complete", classes="setting-label")
                    yield Switch(id="set-notify-batch")
                    yield Label("Verify downloads against DAT  [dim](hash check after extraction)[/dim]", classes="setting-label")
                    yield Switch(id="set-verify-dl")
                    yield Rule()
                    yield Label("IGDB Game Ratings  [dim](Twitch Developer credentials)[/dim]", classes="section-header")
                    yield Label("[dim]Create a free app at dev.twitch.tv for game ratings & genre tags[/dim]", classes="setting-label")
                    yield Label("Client ID", classes="setting-label")
                    yield Input(placeholder="Twitch Client ID", id="set-igdb-client-id")
                    yield Label("Client Secret", classes="setting-label")
                    yield Input(placeholder="Twitch Client Secret", id="set-igdb-client-secret", password=True)
                    yield Rule()
                    yield Button("▸ Save Settings", id="btn-save-settings", variant="success")
            with TabPane("Filters", id="tab-filters"):
                with VerticalScroll():
                    yield Label("Include Filter", classes="section-header")
                    yield Label("[dim]Show only matching regions (empty = show all)[/dim]", classes="setting-label")
                    yield DataTable(id="set-include", classes="filter-table")
                    yield Label("[dim]Additional include regex[/dim]", classes="setting-label")
                    yield Input(placeholder="e.g. (USA|World).*Disc 1", id="set-custom-include")
                    yield Label("Exclude Filter", classes="section-header")
                    yield Label("[dim]Hide games matching these tags[/dim]", classes="setting-label")
                    yield DataTable(id="set-exclude", classes="filter-table")
                    yield Label("[dim]Additional exclude regex[/dim]", classes="setting-label")
                    yield Input(placeholder="e.g. Demo|Sample|Promo", id="set-custom-exclude")
                    yield Rule()
                    yield Button("✕ Clear Filters", id="btn-clear-filters", variant="warning", classes="ops-btn")
                    yield Rule()
                    yield Label("Filter Presets", classes="section-header")
                    yield Label("[dim]Save/load current filter combination as a named preset[/dim]", classes="setting-label")
                    yield Input(placeholder="preset name…", id="input-preset-name")
                    with Horizontal(classes="preset-row"):
                        yield Button("Save Preset", id="btn-save-preset", variant="success")
                        yield Button("Load Preset", id="btn-load-preset", variant="primary")
                        yield Button("Del Preset", id="btn-del-preset", variant="error")
                    yield Select([], id="preset-select", prompt="choose preset…")
            with TabPane("Tools", id="tab-tools"):
                with VerticalScroll():
                    yield Label("[dim]Install or locate conversion / patching tools[/dim]", classes="setting-label")
                    yield Button("Setup chdman", id="btn-setup-chdman", classes="ops-btn")
                    yield Button("Setup PS2 Patcher", id="btn-setup-ps2mdp", classes="ops-btn")
                    yield Rule()
                    yield Label("[dim]Pre-cache all console game lists for faster browsing[/dim]", classes="setting-label")
                    yield Button("Prefetch All Consoles", id="btn-prefetch-consoles", classes="ops-btn")
                    yield Rule()
                    yield Label("[dim]Clear cached IGDB game ratings and metadata[/dim]", classes="setting-label")
                    yield Button("Clear IGDB Cache", id="btn-clear-igdb-cache", classes="ops-btn")
                    yield Rule()
                    yield Label("Batch Queue Import", classes="section-header")
                    yield Label("[dim]Import game URLs or names from a text file (one per line)[/dim]", classes="setting-label")
                    yield Input(placeholder="path to .txt file…", id="input-batch-import-path")
                    yield Button("Import from File", id="btn-batch-import", classes="ops-btn")
