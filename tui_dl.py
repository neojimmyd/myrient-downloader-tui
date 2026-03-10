#!/usr/bin/env python3
"""
Myrient TUI Downloader & Library Manager
A high-performance Textual application for managing Redump libraries.
"""

import concurrent.futures
import hashlib
import json
import logging
import os
import re
import shutil
import subprocess
import threading
import time
import urllib.request
import uuid
import xml.etree.ElementTree as ET
from collections import deque
from functools import lru_cache
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple
from urllib.parse import quote, unquote, urljoin

from bs4 import BeautifulSoup
from textual import work
from textual.app import App, ComposeResult
from textual.containers import Container, Horizontal, Vertical, VerticalScroll
from textual.message import Message
from textual.screen import ModalScreen
from textual.timer import Timer
from textual.widgets import (
    Button, DataTable, Footer, Header, Input,
    Label, ListItem, ListView, ProgressBar, RichLog, Select,
    SelectionList, TabbedContent, TabPane, Tree
)
from textual.widgets.selection_list import Selection

# --- Global Configurations & Pre-Compiled Regex ---
logging.basicConfig(
    filename='myrient_errors.log', 
    level=logging.ERROR,
    format='%(asctime)s - [%(levelname)s] - %(message)s'
)

BASE_URL = "https://myrient.erista.me/files/Redump/"
CONFIG_FILE = Path("myrient_data.json")

# Pre-compiled globally to minimize CPU cycles during tight loops
SIZE_REGEX = re.compile(r'(?<!\d)(\d+(?:\.\d+)?)\s*([KMGT]i?B?)', re.IGNORECASE)
DISC_REGEX = re.compile(r'\s*\((?:Disc|Disk|Tape|Side)\s+[^)]+\)', re.IGNORECASE)
CUE_BIN_REGEX = re.compile(r'FILE\s+"([^"]+)"')
WGET_PROG_REGEX = re.compile(r'(\d+)%')

DEFAULT_SETTINGS = {
    "library_root": str(Path("./Myrient_Library").resolve()),
    "filter_include": [],
    "filter_exclude": [],
    "max_concurrent": 4,
    "auto_convert_chd": False
}


# --- State Management (Thread-Safe) ---
class ConfigManager:
    """Handles loading and atomic, thread-safe saving of state."""
    
    def __init__(self, config_path: Path):
        self.config_path = config_path
        self._lock = threading.Lock()
        self.data: Dict[str, Any] = self._load()

    def _load(self) -> Dict[str, Any]:
        base = {
            "settings": DEFAULT_SETTINGS.copy(), 
            "active_queue": "default", 
            "queues": {"default": []}
        }
        if self.config_path.exists():
            try:
                with open(self.config_path, 'r', encoding="utf-8") as file:
                    disk_data = json.load(file)
                base["settings"] = {**DEFAULT_SETTINGS, **disk_data.get("settings", {})}
                base["queues"] = disk_data.get("queues", {"default": []})
                base["active_queue"] = disk_data.get("active_queue", "default")
                
                if base["active_queue"] not in base["queues"]:
                    base["queues"][base["active_queue"]] = []
            except (json.JSONDecodeError, OSError):
                pass
        return base

    def save(self) -> None:
        """Writes current memory state to disk safely via atomic rename."""
        with self._lock:
            temp_file = self.config_path.with_suffix('.tmp')
            with open(temp_file, 'w', encoding="utf-8") as file:
                json.dump(self.data, file)
            os.replace(temp_file, self.config_path)

    @property
    def settings(self) -> Dict[str, Any]: 
        return self.data["settings"]
        
    @property
    def queues(self) -> Dict[str, List[Dict[str, str]]]: 
        return self.data["queues"]
        
    @property
    def active_queue_name(self) -> str: 
        return self.data["active_queue"]
    
    def get_active_queue(self) -> List[Dict[str, str]]:
        return self.data["queues"].get(self.active_queue_name, [])

    def update_active_queue(self, new_queue: List[Dict[str, str]]) -> None:
        self.data["queues"][self.active_queue_name] = new_queue
        self.save()

    def set_active_queue(self, name: str) -> None:
        if name in self.data["queues"]:
            self.data["active_queue"] = name
            self.save()

    def create_queue(self, name: str) -> bool:
        if name not in self.data["queues"]:
            self.data["queues"][name] = []
            self.data["active_queue"] = name
            self.save()
            return True
        return False

    def delete_queue(self, name: str) -> bool:
        if name in self.data["queues"] and name != self.data["active_queue"]:
            del self.data["queues"][name]
            self.save()
            return True
        return False


# --- Custom UI Components & Messages ---
class SystemLog(Message):
    def __init__(self, message: str, is_error: bool = False):
        self.message = message
        self.is_error = is_error
        super().__init__()

class ConsolesLoaded(Message):
    def __init__(self, consoles: List[Dict[str, str]]):
        self.consoles = consoles
        super().__init__()

class GamesLoaded(Message):
    def __init__(self, games: List[Dict[str, str]]):
        self.games = games
        super().__init__()

class DownloadProgress(Message):
    def __init__(self, task_id: str, item_name: str, completed: int, total: int, action: str = "Downloading"):
        self.task_id = task_id
        self.item_name = item_name
        self.completed = completed
        self.total = total
        self.action = action
        super().__init__()

class DownloadComplete(Message):
    def __init__(self, item: Dict[str, str], success: bool, cancelled: bool = False):
        self.item = item
        self.success = success
        self.cancelled = cancelled
        super().__init__()

class LibraryProgress(Message):
    def __init__(self, task_name: str, current_item: str, completed: int, total: int):
        self.task_name = task_name
        self.current_item = current_item
        self.completed = completed
        self.total = total
        super().__init__()

class ConfirmDeleteScreen(ModalScreen[bool]):
    def __init__(self, target_name: str):
        super().__init__()
        self.target_name = target_name

    def compose(self) -> ComposeResult:
        with Container(id="dialog"):
            yield Label(f"Permanently delete [bold red]{self.target_name}[/bold red]?", id="question")
            yield Button("Cancel", variant="primary", id="btn-cancel")
            yield Button("Delete", variant="error", id="btn-delete")

    def on_button_pressed(self, event) -> None:
        self.dismiss(event.button.id == "btn-delete")


# --- Main Application ---
class MyrientTUI(App):
    TITLE = "Myrient Library Manager"
    SUB_TITLE = "Redump · No-Intro · TOSEC"

    CSS = """
    /* ── Base ─────────────────────────────────────────────────────────────── */
    Screen          { background: $surface; }
    #tabs           { height: 1fr; }
    Header          { background: $primary-darken-2; }

    /* ── Layout skeletons ─────────────────────────────────────────────────── */
    .h-layout       { layout: horizontal; height: 1fr; width: 1fr; }
    .pane           { height: 1fr; border: round $primary-darken-1; padding: 1 2; }
    .pane-35        { width: 35%; }
    .pane-40        { width: 40%; }
    .pane-60        { width: 60%; }
    .pane-65        { width: 65%; }
    .pane-75        { width: 75%; }
    .pane-25        { width: 25%; }
    .pane-50        { width: 50%; }
    .pane-100       { width: 100%; }

    /* ── Section headers ──────────────────────────────────────────────────── */
    .section-header {
        height: auto;
        color: $text-muted;
        text-style: bold;
        margin-bottom: 1;
        border-bottom: solid $primary-darken-1;
        padding-bottom: 1;
    }

    /* ── Search bars ──────────────────────────────────────────────────────── */
    .search-bar     { margin-bottom: 1; }

    /* ── Lists ────────────────────────────────────────────────────────────── */
    #console-list   { height: 1fr; border: solid $surface-lighten-2; }
    DataTable       { height: 1fr; border: solid $surface-lighten-2; }
    Tree            { height: 1fr; border: solid $surface-lighten-2; margin-bottom: 1; }

    /* ── Game list: hide checkbox, fade unselected, full-row highlight ───────
       SelectionList renders each option as a ToggleButton. The glyph lives
       inside .toggle--button — zeroing its width hides it without display:none
       which would also break keyboard navigation.                            */
    #game-list {
        height: 1fr;
        border: solid $surface-lighten-2;
        background: $surface-darken-1;
        color: $surface-darken-1;
    }
    /* Hide the [X] / [ ] glyph entirely */
    #game-list .toggle--button {
        width: 0;
        min-width: 0;
        padding: 0;
        margin: 0;
    }
    /* Cursor row — make it readable while navigating */
    #game-list .selection-list--option-highlighted {
        background: $surface-lighten-1;
        color: $text;
    }
    /* Selected row — full green background, whole line pops */
    #game-list .selection-list--option-selected {
        background: $success-darken-2;
        color: $success;
        text-style: bold;
    }
    /* Selected + cursor — slightly brighter so position is still visible */
    #game-list .selection-list--option-selected.selection-list--option-highlighted {
        background: $success-darken-1;
        color: $success;
        text-style: bold;
    }
    .filter-list    {
        height: 8;
        border: solid $surface-lighten-2;
        margin-bottom: 1;
    }
    .filter-list > .selection--selected {
        background: $primary-darken-2;
        color: $primary-lighten-2;
        text-style: bold;
    }
    .filter-list > .selection--highlighted {
        background: $surface-lighten-1;
        color: $text;
    }
    .filter-list > .selection--selected.selection--highlighted {
        background: $primary-darken-1;
        color: $primary-lighten-2;
        text-style: bold;
    }
    .btn-row        { height: auto; align: center middle; margin-top: 1; }
    Button          { margin: 0 1; min-width: 16; }

    /* ── Queue toolbar ────────────────────────────────────────────────────── */
    .queue-toolbar  {
        height: auto;
        border-bottom: solid $surface-lighten-2;
        margin-bottom: 1;
        padding: 0 0 1 0;
        layout: grid;
        grid-size: 2;
        grid-gutter: 1;
    }
    .queue-toolbar Select   { column-span: 2; }
    .queue-toolbar Input    { column-span: 2; }
    .toolbar-btn-row        { column-span: 2; height: auto; align: center middle; }

    /* ── Download progress area ───────────────────────────────────────────── */
    #progress-area       { padding: 1 2; }
    #lbl-global-progress { margin-bottom: 1; }
    #global-progress     { margin-bottom: 1; display: none; }
    .thread-divider      { margin-top: 1; color: $text-muted; }
    .progress-container  { height: auto; margin-bottom: 1; padding: 0 0 1 0; border-bottom: solid $surface-darken-1; }

    /* ── Library ops panel ────────────────────────────────────────────────── */
    .ops-btn          { width: 100%; margin: 0 0 1 0; }
    .legend-label     { margin: 1 0; color: $text-muted; }
    #lib-status-label { margin-top: 1; color: $text-muted; }
    #lib-progress-bar { display: none; }

    /* ── Settings ─────────────────────────────────────────────────────────── */
    .setting-label  { margin-top: 1; color: $text-muted; }

    /* ── Logs ─────────────────────────────────────────────────────────────── */
    RichLog         { height: 1fr; border: none; }

    /* ── Confirm dialog ───────────────────────────────────────────────────── */
    #dialog {
        grid-size: 2;
        padding: 1 2;
        width: 60;
        height: 10;
        border: thick $error;
        background: $surface;
        align: center middle;
    }
    #question { column-span: 2; content-align: center middle; height: 1fr; }
    """

    BINDINGS = [
        ("q",     "quit",        "Quit"),
        ("d",     "toggle_dark", "Theme"),
        ("ctrl+r","app.refresh_browser", "Refresh"),
    ]

    def __init__(self):
        super().__init__()
        self.state = ConfigManager(CONFIG_FILE)
        # TTL-aware cache: stores (data, timestamp) to prevent stale results across long sessions
        self._link_cache: Dict[str, Tuple[List[Dict[str, str]], float]] = {}
        self._link_cache_ttl: float = 300.0  # 5-minute TTL
        
        self._all_consoles_data: List[Dict[str, str]] = []
        self._all_games_data: List[Dict[str, str]] = []
        self._games_lookup: Dict[str, Dict[str, str]] = {}
        
        self.selected_console: Optional[Dict[str, str]] = None
        
        self.proc_lock = threading.Lock()
        self.active_processes = set()
        self.chd_lock = threading.Lock()
        
        self.global_total = 0
        self.global_completed = 0
        
        # Engine Control State
        # Use a lock to eliminate the TOCTOU race between checking and setting engine_running
        self.engine_running = False
        self._engine_lock = threading.Lock()
        self.cancel_flag = threading.Event()
        # global_completed is incremented from multiple threads; needs its own lock
        self._progress_lock = threading.Lock()
        
        # UI Debounce Timers
        self._search_timer: Optional[Timer] = None

    def _register_process(self, proc: subprocess.Popen) -> None:
        with self.proc_lock:
            self.active_processes.add(proc)

    def _unregister_process(self, proc: subprocess.Popen) -> None:
        with self.proc_lock:
            self.active_processes.discard(proc)

    def cleanup_subprocesses(self) -> None:
        """Safely tears down background tasks, enforcing a hard kill to prevent OS memory leaks."""
        # Snapshot under lock, then release immediately — blocking wait/kill must not hold the lock
        with self.proc_lock:
            procs = list(self.active_processes)
        for proc in procs:
            try:
                proc.terminate()
                proc.wait(timeout=1)
            except subprocess.TimeoutExpired:
                proc.kill()
            except Exception:
                pass

    @staticmethod
    def _format_size(size_bytes: int) -> str:
        if size_bytes == 0:
            return "0 B"
        size_float = float(size_bytes)
        for unit in ['B', 'KB', 'MB', 'GB', 'TB']:
            if size_float < 1024.0:
                return f"{size_float:.2f} {unit}"
            size_float /= 1024.0
        return f"{size_float:.2f} PB"

    def compose(self) -> ComposeResult:
        yield Header(show_clock=True)
        with TabbedContent(id="tabs"):

            # ── Browser ──────────────────────────────────────────────────────
            with TabPane("  Browser  ", id="tab-browser"):
                with Horizontal(classes="h-layout"):
                    with Vertical(classes="pane pane-35"):
                        yield Label("Consoles", classes="section-header")
                        yield Input(
                            placeholder="Filter consoles…",
                            id="search-consoles",
                            classes="search-bar",
                        )
                        yield ListView(id="console-list")

                    with Vertical(classes="pane pane-65"):
                        yield Label(
                            "Games  [dim](Space = select  ·  Enter = queue)[/dim]",
                            classes="section-header",
                        )
                        yield Input(
                            placeholder="Filter games…",
                            id="search-games",
                            classes="search-bar",
                        )
                        yield SelectionList(id="game-list")
                        with Horizontal(classes="btn-row"):
                            yield Button("Queue Selected", id="btn-add-queue", variant="success")
                            yield Button("↺  Refresh List", id="btn-refresh-games", variant="default")

            # ── Queue & Downloads ─────────────────────────────────────────────
            with TabPane("  Queue & Downloads  ", id="tab-queue-dl"):
                with Horizontal(classes="h-layout"):
                    with Vertical(classes="pane pane-40"):
                        yield Label("Queue Profiles", classes="section-header")
                        with Vertical(classes="queue-toolbar"):
                            yield Select([], id="queue-select", prompt="Active profile…")
                            yield Input(placeholder="New profile name…", id="input-new-queue")
                            with Horizontal(classes="toolbar-btn-row"):
                                yield Button("Create", id="btn-create-queue", variant="success")
                                yield Button("Delete", id="btn-delete-queue", variant="error")
                        yield DataTable(id="queue-table")
                        with Horizontal(classes="btn-row"):
                            yield Button("Remove", id="btn-remove-items", variant="warning")
                            yield Button("▶  Start", id="btn-start-dl", variant="primary")
                            yield Button("⏸  Pause", id="btn-pause-dl", variant="error")

                    with VerticalScroll(classes="pane pane-60", id="progress-area"):
                        yield Label(
                            "Queue Progress: 0 / 0",
                            id="lbl-global-progress",
                            classes="section-header",
                        )
                        yield ProgressBar(id="global-progress", show_eta=True)
                        yield Label(
                            "[dim]Active downloads appear below[/dim]",
                            classes="thread-divider",
                        )

            # ── Library Manager ───────────────────────────────────────────────
            with TabPane("  Library  ", id="tab-library"):
                with Horizontal(classes="h-layout"):
                    with Vertical(classes="pane pane-75"):
                        yield Label("Local Library", classes="section-header")
                        yield Tree("Scanning…", id="lib-tree")
                        with Horizontal(classes="btn-row"):
                            yield Button(
                                "🗑  Delete Selected",
                                id="btn-lib-delete",
                                variant="error",
                            )

                    with VerticalScroll(classes="pane pane-25"):
                        yield Label("Operations", classes="section-header")
                        yield Button(
                            "Scan & Organize",
                            id="btn-lib-organize",
                            classes="ops-btn",
                        )
                        yield Button(
                            "Verify vs. Redump DAT",
                            id="btn-lib-dat-audit",
                            classes="ops-btn",
                        )
                        yield Button(
                            "Convert to CHD",
                            id="btn-lib-convert",
                            classes="ops-btn",
                        )
                        yield Button(
                            "↺  Refresh Status",
                            id="btn-lib-refresh-status",
                            classes="ops-btn",
                        )
                        yield Label(
                            "[bold green]✓[/] Validated  "
                            "[bold red]✗[/] Corrupted  "
                            "[yellow]~[/] Incomplete",
                            classes="legend-label",
                        )
                        yield Button(
                            "Re-queue Failures",
                            id="btn-requeue-failed",
                            classes="ops-btn",
                        )
                        yield Label("Status", classes="section-header")
                        yield Label("Idle", id="lib-status-label")
                        yield ProgressBar(id="lib-progress-bar", show_eta=True)

            # ── Settings ──────────────────────────────────────────────────────
            with TabPane("  Settings  ", id="tab-settings"):
                with Horizontal(classes="h-layout"):
                    with VerticalScroll(classes="pane pane-50"):
                        yield Label("Paths & Engine", classes="section-header")
                        yield Label("Library root path", classes="setting-label")
                        yield Input(
                            value=self.state.settings["library_root"],
                            id="set-lib-path",
                        )
                        yield Label("Max concurrent downloads  [dim](1–10)[/dim]", classes="setting-label")
                        yield Input(
                            value=str(self.state.settings["max_concurrent"]),
                            id="set-threads",
                        )
                        yield Label("Post-download CHD conversion", classes="setting-label")
                        from textual.widgets import Switch
                        yield Switch(
                            value=self.state.settings.get("auto_convert_chd", False),
                            id="set-auto-chd",
                        )
                        yield Button("Save Settings", id="btn-save-settings", variant="success")

                    with VerticalScroll(classes="pane pane-50"):
                        yield Label("Regional Include Filter", classes="section-header")
                        yield Label(
                            "[dim]Only show games matching these tags (empty = show all)[/dim]",
                            classes="setting-label",
                        )
                        yield SelectionList(
                            Selection("USA",    "USA"),
                            Selection("Europe", "Europe"),
                            Selection("Japan",  "Japan"),
                            Selection("World",  "World"),
                            id="set-include",
                            classes="filter-list",
                        )
                        yield Label("Type Exclude Filter", classes="section-header")
                        yield Label(
                            "[dim]Hide games matching these tags[/dim]",
                            classes="setting-label",
                        )
                        yield SelectionList(
                            Selection("Demo",  "Demo"),
                            Selection("Beta",  "Beta"),
                            Selection("Proto", "Proto"),
                            id="set-exclude",
                            classes="filter-list",
                        )

            # ── Logs ──────────────────────────────────────────────────────────
            with TabPane("  Logs  ", id="tab-logs"):
                with Vertical(classes="pane pane-100"):
                    yield RichLog(id="sys-log", markup=True, wrap=True, max_lines=1000)

        yield Footer()

    def on_mount(self) -> None:
        table = self.query_one("#queue-table", DataTable)
        table.add_columns("Game Name", "Size", "Target Path")
        table.cursor_type = "row"
        
        self._refresh_queue_dropdown()
        self._refresh_queue_table()
        self._load_settings_toggles()
        self.fetch_consoles()
        self.run_lib_status_scan()

    def _log(self, msg: str, is_error: bool = False) -> None:
        try:
            log_widget = self.query_one("#sys-log", RichLog)
            prefix = "[bold red]ERROR:[/]" if is_error else "[dim cyan]INFO:[/]"
            log_widget.write(f"{prefix} {msg}")
        except Exception:
            pass

    def on_system_log(self, message: SystemLog) -> None: 
        self._log(message.message, message.is_error)

    def on_library_progress(self, message: LibraryProgress) -> None:
        try:
            progress_bar = self.query_one("#lib-progress-bar", ProgressBar)
            status_label = self.query_one("#lib-status-label", Label)

            # Show bar when work is in progress, hide when signalled complete/done
            is_done = message.current_item.lower() in ("done", "complete", "failed")
            progress_bar.display = not is_done
            if not is_done:
                progress_bar.update(total=message.total, progress=message.completed)

            item_display = message.current_item
            if len(item_display) > 50:
                item_display = item_display[:47] + "…"

            if is_done:
                status_label.update(f"[dim]{message.task_name}: {message.current_item}[/dim]")
            else:
                status_label.update(
                    f"[bold]{message.task_name}[/]\n[dim]{item_display}[/dim]"
                )
        except Exception:
            pass

    # --- Fuzzy Search Engine & Highlighter ---
    @staticmethod
    @lru_cache(maxsize=256)
    def _compile_fuzzy_pattern(query: str) -> re.Pattern:
        """Cache compiled fuzzy patterns — avoids re-compiling the same query on every keystroke frame."""
        return re.compile('.*'.join(re.escape(c) for c in query.lower()), re.IGNORECASE)

    @staticmethod
    @lru_cache(maxsize=256)
    def _compile_highlight_pattern(query: str) -> re.Pattern:
        """Cache compiled highlight patterns — character-by-character alternating capture groups."""
        pattern_str = "^(.*?)" + "".join(f"({re.escape(c)})(.*?)" for c in query) + "$"
        return re.compile(pattern_str, re.IGNORECASE)

    def fuzzy_match(self, query: str, text: str) -> bool:
        if not query:
            return True
        return self._compile_fuzzy_pattern(query).search(text.lower()) is not None

    def fuzzy_highlight_fast(self, text: str, hl_compiled: Optional[re.Pattern]) -> str:
        """Injects explicit [white] tags so text stays visible against dark backgrounds."""
        safe_text = text.replace("[", "\\[")
        
        if not hl_compiled:
            return f"[white]{safe_text}[/white]"
        
        # IMPORTANT: search on safe_text so group positions align with the escaped output
        match = hl_compiled.search(safe_text)
        if not match:
            return f"[white]{safe_text}[/white]"
            
        groups = match.groups()
        result_array = []
        
        for i, group_text in enumerate(groups):
            if not group_text:
                continue
            if i % 2 == 1:
                result_array.append(f"[bold #ff0044]{group_text}[/]")
            else:
                result_array.append(f"[white]{group_text}[/white]")
                
        return "".join(result_array)

    def on_input_changed(self, event) -> None:
        """Debounces search input to prevent UI stutter during rapid typing."""
        if self._search_timer is not None:
            self._search_timer.stop()
            
        if event.input.id == "search-consoles":
            self._search_timer = self.set_timer(0.15, lambda: self._render_consoles(event.value))
        elif event.input.id == "search-games":
            self._search_timer = self.set_timer(0.15, lambda: self._render_games(event.value))

    def _render_consoles(self, query: str = "") -> None:
        list_view = self.query_one("#console-list", ListView)
        list_view.clear()
        
        hl_compiled = self._compile_highlight_pattern(query) if query else None
            
        filtered_consoles = [c for c in self._all_consoles_data if self.fuzzy_match(query, c["name"])]
        new_items = []
        
        for console in filtered_consoles:
            highlighted_name = self.fuzzy_highlight_fast(console["name"].strip('/'), hl_compiled)
            item = ListItem(Label(highlighted_name))
            item.link_data = console
            new_items.append(item)
            
        if hasattr(list_view, "extend"):
            list_view.extend(new_items)
        else:
            list_view.mount(*new_items)

    def _render_games(self, query: str = "") -> None:
        game_list = self.query_one("#game-list", SelectionList)
        game_list.clear_options()

        fuzzy_pat   = self._compile_fuzzy_pattern(query) if query else None
        hl_compiled = self._compile_highlight_pattern(query) if query else None

        selections = []
        for game in self._all_games_data:
            if fuzzy_pat is None or fuzzy_pat.search(game["name"]):
                markup = self.fuzzy_highlight_fast(game["name"], hl_compiled)
                selections.append(Selection(markup, game["url_part"]))

        if not selections and self._all_games_data:
            selections = [Selection("[dim]No matches found.[/dim]", "EMPTY")]

        if selections:
            game_list.add_options(selections)

    # --- Queue & Settings Managers ---
    def _refresh_queue_dropdown(self) -> None:
        selector = self.query_one("#queue-select", Select)
        selector.set_options([(k, k) for k in self.state.queues.keys()])
        
        if self.state.active_queue_name in self.state.queues:
            selector.value = self.state.active_queue_name

    def _refresh_queue_table(self) -> None:
        table = self.query_one("#queue-table", DataTable)
        table.clear()
        
        for i, item in enumerate(self.state.get_active_queue()):
            table.add_row(item['name'], item['size_str'], item['dest_path'], key=str(i))

    def _load_settings_toggles(self) -> None:
        from textual.widgets import Switch
        try:
            self.query_one("#set-auto-chd", Switch).value = \
                self.state.settings.get("auto_convert_chd", False)
        except Exception:
            pass

        include_list = self.query_one("#set-include", SelectionList)
        exclude_list = self.query_one("#set-exclude", SelectionList)

        for tag in self.state.settings.get("filter_include", []):
            try:
                include_list.select(tag)
            except Exception:
                pass

        for tag in self.state.settings.get("filter_exclude", []):
            try:
                exclude_list.select(tag)
            except Exception:
                pass

    def on_select_changed(self, event) -> None:
        if event.control.id == "queue-select" and event.value != Select.BLANK:
            self.state.set_active_queue(str(event.value))
            self._refresh_queue_table()
            self.notify(f"Switched to: {event.value}")

    async def on_list_view_selected(self, event) -> None:
        list_id = getattr(event.list_view, "id", None)

        if list_id == "console-list":
            data = getattr(event.item, 'link_data', None)
            if data:
                self.selected_console = data

                game_list = self.query_one("#game-list", SelectionList)
                game_list.clear_options()
                game_list.add_options([Selection("[dim]Fetching games… please wait…[/dim]", "LOADING")])

                self.query_one("#search-games", Input).value = ""
                self.fetch_games(data)

    def on_button_pressed(self, event) -> None:
        button_id = event.button.id
        
        # Dispatch table replaces O(n) if/elif chain with O(1) dict lookup
        simple_dispatch = {
            "btn-add-queue":          self._add_selected_to_queue,
            "btn-lib-organize":       self.run_lib_organize,
            "btn-lib-dat-audit":      self.run_bulk_dat_audit,
            "btn-lib-convert":        self.run_lib_convert,
            "btn-lib-refresh-status": self.run_lib_status_scan,
            "btn-requeue-failed":     self.requeue_failed_games,
        }
        if button_id in simple_dispatch:
            simple_dispatch[button_id]()
            return

        if button_id == "btn-refresh-games" and self.selected_console:
            self.fetch_games(self.selected_console)
            
        elif button_id == "btn-create-queue":
            input_box = self.query_one("#input-new-queue", Input)
            if input_box.value and self.state.create_queue(input_box.value):
                input_box.value = ""
                self._refresh_queue_dropdown()
                self._refresh_queue_table()
                self.notify("Queue Created")
                
        elif button_id == "btn-delete-queue":
            if self.state.delete_queue(self.state.active_queue_name): 
                self._refresh_queue_dropdown()
                self._refresh_queue_table()
                self.notify("Queue Deleted")
                
        elif button_id == "btn-remove-items":
            table = self.query_one("#queue-table", DataTable)
            if table.cursor_row is not None:
                current_queue = self.state.get_active_queue()
                if 0 <= table.cursor_row < len(current_queue):
                    del current_queue[table.cursor_row]
                    self.state.update_active_queue(current_queue)
                    self._refresh_queue_table()
                    
        elif button_id == "btn-start-dl":
            if self.state.get_active_queue():
                self.start_download_engine()
                
        elif button_id == "btn-pause-dl":
            if self.engine_running:
                self.post_message(SystemLog("[bold yellow]Pause signal sent. Suspending threads and preserving partial files...[/]"))
                self.cancel_flag.set()
                self.cleanup_subprocesses()
                
        elif button_id == "btn-save-settings":
            try:
                from textual.widgets import Switch
                new_path = Path(self.query_one("#set-lib-path", Input).value).expanduser().resolve()
                self.state.settings["library_root"] = str(new_path)

                threads_input = self.query_one("#set-threads", Input).value
                thread_count = int(threads_input) if threads_input.isdigit() else 4
                self.state.settings["max_concurrent"] = max(1, min(10, thread_count))

                self.state.settings["auto_convert_chd"] = self.query_one("#set-auto-chd", Switch).value
                self.state.settings["filter_include"] = self.query_one("#set-include", SelectionList).selected
                self.state.settings["filter_exclude"] = self.query_one("#set-exclude", SelectionList).selected
                self.state.save()

                new_path.mkdir(parents=True, exist_ok=True)
                self.run_lib_status_scan()
                self.notify("Settings saved")

                if self.selected_console:
                    self.fetch_games(self.selected_console)

            except Exception as err:
                self.notify(f"Error saving settings: {err}", severity="error")
                
        elif button_id == "btn-lib-delete":
            tree = self.query_one("#lib-tree", Tree)
            if not tree.cursor_node or not isinstance(tree.cursor_node.data, Path):
                self.notify("Please select a game or console folder in the tree first.", severity="warning")
                return
                
            target_path: Path = tree.cursor_node.data
            
            def check_delete(confirm: bool) -> None:
                if confirm and target_path:
                    try:
                        if target_path.is_dir():
                            shutil.rmtree(target_path)
                        else:
                            target_path.unlink()
                        self.run_lib_status_scan()
                    except Exception as err:
                        self.notify(f"Error during deletion: {err}", severity="error")
            self.push_screen(ConfirmDeleteScreen(target_path.name), check_delete)
            
    def _add_selected_to_queue(self) -> None:
        if not self.selected_console:
            return

        game_list = self.query_one("#game-list", SelectionList)
        selected_urls = game_list.selected
        if not selected_urls:
            return

        library_root = Path(self.state.settings["library_root"])
        console_name = self.selected_console["name"].strip('/')
        base_url = urljoin(BASE_URL, self.selected_console["url_part"])
        current_queue = self.state.get_active_queue()

        added_count = 0
        for url_part in selected_urls:
            if url_part in ["LOADING", "EMPTY"]:
                continue

            data = self._games_lookup.get(url_part)
            if not data:
                continue

            sub_folder = data['name'].replace('.zip', '').strip()
            clean_base = DISC_REGEX.sub('', sub_folder).strip()

            if DISC_REGEX.search(sub_folder):
                dest_path = library_root / console_name / clean_base / sub_folder
            else:
                dest_path = library_root / console_name / sub_folder

            current_queue.append({
                "id": f"dl_{uuid.uuid4().hex[:8]}",
                "name": f"[{console_name}] {data['name']}",
                "game_url": urljoin(base_url, data["url_part"]),
                "dest_path": str(dest_path),
                "size_str": data["size_str"]
            })
            added_count += 1

        game_list.deselect_all()
        self.state.update_active_queue(current_queue)
        self._refresh_queue_table()
        self.notify(f"Queued {added_count} item(s)")
        self.query_one("#tabs", TabbedContent).active = "tab-queue-dl"

    # --- UI Message Receivers ---
    async def on_consoles_loaded(self, message: ConsolesLoaded) -> None:
        self._all_consoles_data = message.consoles
        self._render_consoles(self.query_one("#search-consoles", Input).value)

    async def on_games_loaded(self, message: GamesLoaded) -> None:
        self._all_games_data = message.games
        # RAM Optimization: Store active dictionary for O(1) queue lookups instead of JSON parsing
        self._games_lookup = {g["url_part"]: g for g in message.games}
        self._render_games(self.query_one("#search-games", Input).value)

    # --- Async Background Workers ---
    @work(exclusive=True, thread=True)
    def fetch_consoles(self) -> None:
        self.post_message(SystemLog("Scraping console list..."))
        items = self._scrape_links(BASE_URL)
        
        consoles = []
        for item in items:
            if item["url_part"].endswith('/'):
                consoles.append(item)
                
        self.post_message(ConsolesLoaded(consoles))

    @work(exclusive=True, thread=True)
    def fetch_games(self, console_data: Dict[str, str]) -> None:
        url = urljoin(BASE_URL, console_data["url_part"])
        self.post_message(SystemLog(f"Listing games for {console_data['name']}..."))
        items = self._scrape_links(url)
        
        inc_filters = self.state.settings["filter_include"]
        exc_filters = self.state.settings["filter_exclude"]
        
        filtered_games = []
        for game in items:
            if not game["url_part"].lower().endswith('.zip'):
                continue
                
            if inc_filters and not any(tag in game["name"] for tag in inc_filters):
                continue
                
            if exc_filters and any(tag in game["name"] for tag in exc_filters):
                continue
                
            filtered_games.append(game)
            
        self.post_message(GamesLoaded(filtered_games))

    def _scrape_links(self, url: str) -> List[Dict[str, str]]:
        # Return cached result only if it's still within the TTL window
        now = time.monotonic()
        cached = self._link_cache.get(url)
        if cached and (now - cached[1]) < self._link_cache_ttl:
            return cached[0]
            
        try:
            req = urllib.request.Request(url, headers={'User-Agent': 'Mozilla/5.0'})
            with urllib.request.urlopen(req, timeout=15) as res:
                soup = BeautifulSoup(res.read(), 'html.parser')
                items = []
                
                for a_tag in soup.find_all('a'):
                    href = a_tag.get('href')
                    
                    if not href or href.startswith('?') or href in ['../', './', '/']:
                        continue
                    if 'Parent Directory' in a_tag.text:
                        continue
                        
                    size_str = "N/A"
                    parent_row = a_tag.find_parent('tr')
                    
                    if parent_row:
                        matches = SIZE_REGEX.findall(parent_row.get_text(separator=' '))
                        if matches:
                            size_str = f"{matches[-1][0]}{matches[-1][1]}"
                            
                    items.append({
                        "name": unquote(href), 
                        "url_part": href, 
                        "size_str": size_str
                    })
                    
                self._link_cache[url] = (items, time.monotonic())
                return items
                
        except Exception as err:
            self.post_message(SystemLog(f"Scrape Error: {err}", True))
            return []

    @work(exclusive=True, thread=True)
    def start_download_engine(self) -> None:
        # Atomic check-and-set: prevents a second invocation from slipping through
        # the gap between checking engine_running and setting it.
        with self._engine_lock:
            if self.engine_running:
                return
            self.engine_running = True

        queue = self.state.get_active_queue().copy()
        max_threads = self.state.settings.get("max_concurrent", 4)

        if not queue:
            with self._engine_lock:
                self.engine_running = False
            return

        self.cancel_flag.clear()
        
        self.global_total = len(queue)
        self.global_completed = 0
        
        def init_global_pb() -> None:
            try:
                pb = self.query_one("#global-progress", ProgressBar)
                pb.display = True
                pb.update(total=self.global_total, progress=0)
                self.query_one("#lbl-global-progress", Label).update(
                    f"Queue Progress: 0 / {self.global_total}"
                )
            except Exception:
                pass
                
        self.call_from_thread(init_global_pb)
        self.post_message(SystemLog(f"Engine Online. Dispatching {max_threads} Threads..."))
        
        with concurrent.futures.ThreadPoolExecutor(max_workers=max_threads) as executor:
            futures = {executor.submit(self._download_worker, item): item for item in queue}
            for future in concurrent.futures.as_completed(futures):
                try: 
                    result = future.result()
                    self.post_message(DownloadComplete(
                        futures[future], 
                        result.get("success", False), 
                        result.get("cancelled", False)
                    ))
                except Exception as err: 
                    self.post_message(SystemLog(f"Thread crash {futures[future]['name']}: {err}", True))
                    self.post_message(DownloadComplete(futures[future], False))
                    
        with self._engine_lock:
            self.engine_running = False

        def _finish_ui(paused: bool) -> None:
            try:
                self.query_one("#global-progress", ProgressBar).display = False
                self.query_one("#lbl-global-progress", Label).update("Queue Progress: 0 / 0")
            except Exception:
                pass

        if self.cancel_flag.is_set():
            self.post_message(SystemLog("[bold yellow]Downloads Successfully Paused[/]"))
            self.call_from_thread(lambda: _finish_ui(True))
        else:
            self.post_message(SystemLog("[bold green]Batch Queue Finished[/]"))
            self.call_from_thread(lambda: _finish_ui(False))

    def _download_worker(self, item: Dict[str, str]) -> Dict[str, Any]:
        if self.cancel_flag.is_set():
            return {"success": False, "cancelled": True}
            
        dest_dir = Path(item['dest_path'])
        target_file = dest_dir / unquote(item['game_url'].split('/')[-1])
        item_name = item["name"]
        
        try:
            dest_dir.mkdir(parents=True, exist_ok=True)
            if any(dest_dir.rglob("*.chd")) or target_file.with_suffix('.chd').exists(): 
                self.post_message(SystemLog(f"Skipped (Already Exists): {item_name}"))
                return {"success": True}
                
            # Prevent ZeroDivisionErrors by ensuring byte math is >= 1
            size_bytes = max(self._parse_size_bytes(item["size_str"]), 1)
            
            cmd = [
                "wget", "--progress=dot:mega", "-c", "--timeout=20", "--tries=3", 
                "--user-agent=Mozilla/5.0 (Windows NT 10.0; Win64; x64)", 
                "-e", "robots=off", "-O", str(target_file), item['game_url']
            ]
            
            proc = subprocess.Popen(
                cmd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, 
                text=True, env={**os.environ, "LC_ALL": "C"}
            )
            self._register_process(proc)
            
            stderr_log = deque(maxlen=5)
            last_ui_update = 0.0
            
            try:
                for line in proc.stderr:
                    if self.cancel_flag.is_set():
                        proc.terminate()
                        return {"success": False, "cancelled": True}
                        
                    stderr_log.append(line.strip())
                    match = WGET_PROG_REGEX.search(line)
                    if match:
                        current_time = time.monotonic()
                        if current_time - last_ui_update > 0.25:
                            current_bytes = int((float(match.group(1)) / 100.0) * size_bytes)
                            self.post_message(
                                DownloadProgress(item["id"], item_name, current_bytes, size_bytes, "Downloading")
                            )
                            last_ui_update = current_time
            finally: 
                proc.wait()
                self._unregister_process(proc)
                
            if self.cancel_flag.is_set():
                return {"success": False, "cancelled": True}

            if proc.returncode != 0: 
                error_msg = " | ".join(stderr_log)
                self.post_message(
                    SystemLog(f"Wget failed for {item_name}. Fallback to Urllib... ({error_msg})", True)
                )
                
                req = urllib.request.Request(
                    item['game_url'], 
                    headers={'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64)'}
                )
                
                if target_file.exists():
                    existing_size = target_file.stat().st_size
                    if existing_size < size_bytes:
                        req.add_header('Range', f'bytes={existing_size}-')
                        open_mode = 'ab'
                        downloaded = existing_size
                    else:
                        open_mode = 'wb'
                        downloaded = 0
                else:
                    open_mode = 'wb'
                    downloaded = 0
                
                try:
                    with urllib.request.urlopen(req, timeout=30) as response:
                        with open(target_file, open_mode) as file:
                            last_ui_update = 0.0
                            while True:
                                if self.cancel_flag.is_set():
                                    return {"success": False, "cancelled": True}
                                    
                                chunk = response.read(1024 * 1024)
                                if not chunk:
                                    break
                                    
                                file.write(chunk)
                                downloaded += len(chunk)
                                current_time = time.monotonic()
                                if current_time - last_ui_update > 0.25:
                                    self.post_message(
                                        DownloadProgress(
                                            item["id"], item_name, downloaded, 
                                            max(size_bytes, downloaded), "Downloading"
                                        )
                                    )
                                    last_ui_update = current_time
                except Exception as err:
                    raise Exception(f"Urllib socket failed: {str(err)}")

            if self.cancel_flag.is_set():
                return {"success": False, "cancelled": True}

            self.post_message(DownloadProgress(item["id"], item_name, size_bytes, size_bytes, "Extracting ZIP"))

            if target_file.exists() and target_file.suffix.lower() == '.zip':
                unzip_proc = subprocess.Popen(
                    ["unzip", "-q", "-o", str(target_file), "-d", str(dest_dir)], 
                    stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True
                )
                self._register_process(unzip_proc)
                _, unzip_err = unzip_proc.communicate()
                self._unregister_process(unzip_proc)
                
                if unzip_proc.returncode == 0:
                    target_file.unlink()
                    (dest_dir / ".corrupted").unlink(missing_ok=True)
                    (dest_dir / ".validated").touch()
                else:
                    raise Exception(f"Unzip failed: {unzip_err}")
            elif target_file.exists():
                # Non-ZIP download (direct .bin/.iso/etc.) — still mark validated so re-runs skip it
                (dest_dir / ".corrupted").unlink(missing_ok=True)
                (dest_dir / ".validated").touch()
            
            if self.cancel_flag.is_set():
                return {"success": False, "cancelled": True}
            
            if self.state.settings.get('auto_convert_chd', False):
                self.post_message(DownloadProgress(item["id"], item_name, size_bytes, size_bytes, "Converting CHD"))
                self._convert_to_chd(dest_dir, silent=True)
                
            return {"success": True}
            
        except Exception as err: 
            self.post_message(SystemLog(f"Worker Error {item_name}: {str(err)}", True))
            return {"success": False}

    def _convert_to_chd(self, dest_dir: Path, silent: bool = False) -> None:
        cpu_count = os.cpu_count()
        cores = str(max(1, cpu_count - 1)) if cpu_count else "1"
        
        conversion_targets = [f for f in dest_dir.rglob('*') if f.suffix.lower() in ('.cue', '.iso')]
        
        for file_path in conversion_targets:
            if self.cancel_flag.is_set():
                return
                
            try:
                proc = subprocess.Popen(
                    ["chdman", "createcd", "-numprocessors", cores, "-i", str(file_path), "-o", str(file_path.with_suffix('.chd'))], 
                    stdout=subprocess.DEVNULL, stderr=subprocess.PIPE
                )
                self._register_process(proc)
                # NOTE: chd_lock previously wrapped proc.communicate(), fully serializing all CHD work
                # across threads. The lock is no longer needed here — chdman manages its own file I/O
                # and -numprocessors already limits CPU contention. We only guard post-conversion
                # file cleanup to prevent concurrent unlinking of the same .bin files.
                proc.communicate()
                self._unregister_process(proc)
                
                if proc.returncode == 0:
                    if file_path.suffix.lower() == '.cue':
                        try:
                            with open(file_path, 'r', encoding='utf-8', errors='ignore') as cue_file:
                                bins = CUE_BIN_REGEX.findall(cue_file.read())
                            with self.chd_lock:  # narrow lock: only around concurrent file removal
                                for bin_name in bins:
                                    bin_path = file_path.parent / bin_name
                                    if bin_path.exists():
                                        bin_path.unlink()
                        except Exception:
                            pass
                    file_path.unlink()
            except Exception:
                pass

    def on_download_progress(self, message: DownloadProgress) -> None:
        area = self.query_one("#progress-area")
        pb_id = f"pb_{message.task_id}"
        lbl_id = f"lbl_{message.task_id}"
        
        fmt_progress = self._format_size(message.completed)
        fmt_total = self._format_size(message.total)
        status_text = f"[bold cyan]{message.action}[/] | [white]{message.item_name}[/] [dim]({fmt_progress} / {fmt_total})[/dim]"
        
        try: 
            self.query_one(f"#{pb_id}", ProgressBar).update(progress=message.completed, total=message.total)
            self.query_one(f"#{lbl_id}", Label).update(status_text)
        except Exception: 
            area.mount(
                Container(
                    Label(status_text, id=lbl_id), 
                    ProgressBar(id=pb_id, total=message.total, show_eta=True), 
                    classes="progress-container", id=f"cont_{pb_id}"
                )
            )

    def on_download_complete(self, message: DownloadComplete) -> None:
        if message.success:
            # Protect counter incremented from concurrent completion callbacks
            with self._progress_lock:
                self.global_completed += 1
                completed_snap = self.global_completed
            try:
                self.query_one("#global-progress", ProgressBar).advance(1)
                self.query_one("#lbl-global-progress", Label).update(
                    f"Queue Progress: {completed_snap} / {self.global_total}"
                )
            except Exception:
                pass

            current_queue = self.state.get_active_queue()
            self.state.update_active_queue([i for i in current_queue if i["id"] != message.item["id"]])
            self._refresh_queue_table()
            
            try:
                self.query_one(f"#cont_pb_{message.item['id']}").remove()
            except Exception:
                pass
                
        elif message.cancelled:
            try:
                lbl_id = f"lbl_{message.item['id']}"
                self.query_one(f"#{lbl_id}", Label).update(
                    f"[yellow]Paused[/]  {message.item['name']}"
                )
            except Exception:
                pass

    @work(exclusive=True, thread=True)
    def run_lib_organize(self) -> None:
        self.post_message(SystemLog("Library Scan: Building target list..."))
        library = Path(self.state.settings['library_root'])
        
        targets = []
        if library.exists():
            for console_dir in library.iterdir():
                if console_dir.is_dir() and not console_dir.name.startswith('.'):
                    for game_dir in console_dir.iterdir():
                        if game_dir.is_dir() and not game_dir.name.startswith('.'):
                            base_name = DISC_REGEX.sub('', game_dir.name).strip()
                            if base_name != game_dir.name:
                                targets.append((game_dir, console_dir / base_name))
        
        total_ops = len(targets)
        if total_ops == 0:
            self.post_message(SystemLog("Library Scan: No valid targets found. (Library is already organized)"))
            self.post_message(LibraryProgress("Organize", "Done", 100, 100))
            return
            
        for i, (game_dir, parent_dir) in enumerate(targets, 1):
            self.post_message(LibraryProgress(f"Organizing ({i}/{total_ops})", game_dir.name, i, total_ops))
            parent_dir.mkdir(parents=True, exist_ok=True)
            
            if game_dir.parent != parent_dir:
                shutil.move(str(game_dir), str(parent_dir / game_dir.name))
                    
        self.post_message(LibraryProgress("Organize", "Complete", total_ops, total_ops))
        self.run_lib_status_scan()
        self.post_message(SystemLog("Clean-up Complete."))

    @work(exclusive=True, thread=True)
    def run_bulk_dat_audit(self) -> None:
        """
        Full-library DAT audit. For every console folder:
          1. Fetches (or reuses a cached) Redump .dat file from Myrient.
          2. SHA-1 hashes every .bin/.iso/.cue/.img file.
          3. Looks each hash up in the DAT and marks the parent game dir
             .validated (known-good) or .corrupted (unknown/bad dump).
          4. Reports perfect / misnamed / bad counts per console and a grand total.
        """
        library = Path(self.state.settings['library_root'])
        dat_base_url = "https://myrient.erista.me/dats/Redump/"
        auditable_exts = {'.bin', '.iso', '.cue', '.img'}

        if not library.exists():
            self.post_message(SystemLog("DAT Audit: Library path not found.", True))
            return

        # ── Phase 1: discover console dirs ──────────────────────────────────
        console_dirs = sorted(
            d for d in library.iterdir()
            if d.is_dir() and not d.name.startswith('.')
        )
        if not console_dirs:
            self.post_message(SystemLog("DAT Audit: No console folders found in library."))
            return

        self.post_message(SystemLog(
            f"DAT Audit: Starting bulk audit of {len(console_dirs)} console(s)..."
        ))

        # ── Phase 2: fetch the DAT index page once ──────────────────────────
        self.post_message(LibraryProgress("DAT Audit", "Fetching DAT index...", 0, 100))
        try:
            try:
                index_html = subprocess.check_output(
                    ["wget", "-qO-", dat_base_url], text=True, errors="ignore"
                )
            except Exception:
                req = urllib.request.Request(
                    dat_base_url,
                    headers={'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'}
                )
                with urllib.request.urlopen(req, timeout=20) as res:
                    index_html = res.read().decode('utf-8', errors='ignore')

            soup = BeautifulSoup(index_html, 'html.parser')
            # Build a lookup: console_name_prefix -> href
            dat_index: Dict[str, str] = {}
            for a_tag in soup.find_all('a'):
                href = a_tag.get('href', '')
                name = unquote(href)
                if name.endswith('.dat'):
                    dat_index[name] = href
        except Exception as err:
            self.post_message(SystemLog(f"DAT Audit: Failed to fetch DAT index: {err}", True))
            self.post_message(LibraryProgress("DAT Audit", "Failed", 0, 100))
            return

        # ── Phase 3: per-console audit ───────────────────────────────────────
        grand_perfect = grand_misnamed = grand_bad = 0
        dat_cache_root = library / ".dats"

        for con_idx, console_dir in enumerate(console_dirs, 1):
            console_name = console_dir.name
            phase_label = f"[{con_idx}/{len(console_dirs)}] {console_name}"
            self.post_message(LibraryProgress(
                "DAT Audit", phase_label, con_idx - 1, len(console_dirs)
            ))

            # ── 3a: find matching DAT ────────────────────────────────────────
            target_prefix = f"{console_name} - Datfile"
            dat_href = next(
                (href for name, href in dat_index.items()
                 if name.startswith(target_prefix)),
                None
            )
            if not dat_href:
                self.post_message(SystemLog(
                    f"DAT Audit [{console_name}]: No matching DAT found — skipping."
                ))
                continue

            # ── 3b: download DAT if not cached ──────────────────────────────
            dat_dir = dat_cache_root / console_name
            dat_dir.mkdir(parents=True, exist_ok=True)
            dat_path = dat_dir / unquote(dat_href)

            if not dat_path.exists():
                dat_url = urljoin(dat_base_url, dat_href)
                self.post_message(SystemLog(f"DAT Audit [{console_name}]: Downloading DAT..."))
                try:
                    proc = subprocess.run(["wget", "-q", "-O", str(dat_path), dat_url])
                    if proc.returncode != 0:
                        raise RuntimeError("wget failed")
                except Exception:
                    try:
                        req = urllib.request.Request(
                            dat_url,
                            headers={'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'}
                        )
                        with urllib.request.urlopen(req, timeout=30) as res, open(dat_path, 'wb') as f:
                            shutil.copyfileobj(res, f)
                    except Exception as err:
                        self.post_message(SystemLog(
                            f"DAT Audit [{console_name}]: Could not download DAT: {err}", True
                        ))
                        continue

            # ── 3c: parse DAT into sha1 → {name, game} ──────────────────────
            dat_by_sha1: Dict[str, Dict[str, str]] = {}
            try:
                context = ET.iterparse(dat_path, events=('start', 'end'))
                _, xml_root = next(context)
                current_game = "Unknown"
                for event, elem in context:
                    if event == 'start' and elem.tag == 'game':
                        current_game = elem.get('name', 'Unknown')
                    elif event == 'end' and elem.tag == 'rom':
                        sha1_val = elem.get('sha1')
                        rom_name = elem.get('name')
                        if sha1_val and rom_name:
                            dat_by_sha1[sha1_val.lower()] = {
                                "name": rom_name, "game": current_game
                            }
                        elem.clear()
                    elif event == 'end' and elem.tag == 'game':
                        xml_root.clear()
            except Exception as err:
                self.post_message(SystemLog(
                    f"DAT Audit [{console_name}]: Failed to parse DAT: {err}", True
                ))
                continue

            # ── 3d: collect game dirs and their auditable files ──────────────
            # A "game dir" is any non-hidden leaf directory containing auditable files.
            # We group files by their immediate parent so the .validated/.corrupted
            # marker lands on the game folder, not the console folder.
            game_dirs: Dict[Path, List[Path]] = {}
            for item in console_dir.rglob('*'):
                if (item.is_file()
                        and not item.name.startswith('.')
                        and not any(p.name.startswith('.') for p in item.parents)
                        and item.suffix.lower() in auditable_exts):
                    game_dirs.setdefault(item.parent, []).append(item)

            if not game_dirs:
                self.post_message(SystemLog(
                    f"DAT Audit [{console_name}]: No auditable files found."
                ))
                continue

            # ── 3e: hash every file once, log results, cache for marker step ──
            # hash_results: file_path -> True (known-good) | False (bad/error)
            con_perfect = con_misnamed = con_bad = 0
            all_files = [(gd, fp) for gd, fps in game_dirs.items() for fp in fps]
            total_files = len(all_files)
            hash_results: Dict[Path, bool] = {}

            for f_idx, (game_dir, file_path) in enumerate(all_files, 1):
                self.post_message(LibraryProgress(
                    f"Hashing {console_name} ({f_idx}/{total_files})",
                    file_path.name, f_idx, total_files
                ))
                sha1 = hashlib.sha1(usedforsecurity=False)
                try:
                    with open(file_path, 'rb') as fh:
                        while chunk := fh.read(8 * 1024 * 1024):
                            sha1.update(chunk)
                    file_hash = sha1.hexdigest().lower()

                    if file_hash in dat_by_sha1:
                        expected_name = dat_by_sha1[file_hash]['name']
                        if file_path.name == expected_name:
                            con_perfect += 1
                        else:
                            con_misnamed += 1
                            self.post_message(SystemLog(
                                f"Misnamed [{console_name}]: '{file_path.name}' → '{expected_name}'"
                            ))
                        hash_results[file_path] = True
                    else:
                        con_bad += 1
                        self.post_message(SystemLog(
                            f"Bad/Unknown [{console_name}]: '{file_path.name}' (SHA1: {file_hash})"
                        ))
                        hash_results[file_path] = False
                except Exception as err:
                    con_bad += 1
                    hash_results[file_path] = False
                    self.post_message(SystemLog(
                        f"Read error [{console_name}]: '{file_path.name}': {err}", True
                    ))

            # ── 3f: write markers using cached results — no re-reading files ──
            # A dir is validated only if every auditable file in it was a known-good hash.
            for game_dir, files in game_dirs.items():
                dir_ok = all(hash_results.get(fp, False) for fp in files)
                if dir_ok:
                    (game_dir / ".corrupted").unlink(missing_ok=True)
                    (game_dir / ".validated").touch()
                else:
                    (game_dir / ".validated").unlink(missing_ok=True)
                    (game_dir / ".corrupted").touch()

            self.post_message(SystemLog(
                f"DAT Audit [{console_name}]: "
                f"Perfect: {con_perfect}  Misnamed: {con_misnamed}  Bad/Unknown: {con_bad}"
            ))
            grand_perfect  += con_perfect
            grand_misnamed += con_misnamed
            grand_bad      += con_bad

        # ── Phase 4: finish ──────────────────────────────────────────────────
        self.post_message(LibraryProgress("DAT Audit", "Complete", 100, 100))
        self.post_message(SystemLog(
            f"[bold]Bulk DAT Audit Complete[/bold] — "
            f"Perfect: [bold green]{grand_perfect}[/]  "
            f"Misnamed: [bold yellow]{grand_misnamed}[/]  "
            f"Bad/Unknown: [bold red]{grand_bad}[/]"
        ))
        self.run_lib_status_scan()



    @work(exclusive=True, thread=True)
    def run_lib_convert(self) -> None:
        self.post_message(SystemLog("Scanning library for CHD conversion targets..."))
        library = Path(self.state.settings['library_root'])
        
        targets = []
        if library.exists():
            for game_dir in library.rglob('*'):
                if game_dir.is_dir() and not game_dir.name.startswith('.') and not any(p.name.startswith('.') for p in game_dir.parents):
                    # Cache iterdir() — previously called 3x per directory
                    dir_files = [f for f in game_dir.iterdir() if f.is_file()]
                    if any(f.suffix.lower() in ['.bin', '.iso', '.cue'] for f in dir_files):
                        if not any(f.name.lower().endswith('.zip') for f in dir_files):
                            if not (game_dir / ".corrupted").exists():
                                targets.append(game_dir)
                    
        total_ops = len(targets)
        if total_ops == 0:
            self.post_message(SystemLog("Library Scan: No valid files for CHD conversion found."))
            self.post_message(LibraryProgress("CHD Conversion", "Done", 100, 100))
            return
            
        for i, game_dir in enumerate(targets, 1):
            self.post_message(LibraryProgress(f"Converting ({i}/{total_ops})", game_dir.name, i, total_ops))
            self.post_message(SystemLog(f"Converting: {game_dir.name}"))
            self._convert_to_chd(game_dir, silent=True)
                
        self.post_message(LibraryProgress("CHD Conversion", "Complete", total_ops, total_ops))
        self.post_message(SystemLog("Bulk CHD Conversion Finished."))

    @work(exclusive=True, thread=True)
    def run_lib_status_scan(self) -> None:
        """Scans the library and rebuilds the Tree with color-coded game status nodes."""
        library = Path(self.state.settings['library_root'])

        # structure: {console_name: (console_path, [(game_dir, status_str), ...])}
        structure: Dict[str, tuple] = {}

        def _classify_dir(d: Path) -> Optional[str]:
            """Return 'validated'/'corrupted'/'incomplete'/None (skip) for a candidate game dir."""
            try:
                dir_files = [f for f in d.iterdir() if f.is_file() and not f.name.startswith('.')]
            except PermissionError:
                return None
            has_game = any(f.suffix.lower() in ('.bin', '.iso', '.cue', '.chd', '.img') for f in dir_files)
            has_zip  = any(f.suffix.lower() == '.zip' for f in dir_files)
            is_empty = len(dir_files) == 0
            if not (has_game or has_zip or is_empty):
                return None
            if (d / ".validated").exists():
                return "validated"
            if (d / ".corrupted").exists():
                return "corrupted"
            return "incomplete"

        if library.exists():
            try:
                console_entries = sorted(
                    (e for e in library.iterdir() if e.is_dir() and not e.name.startswith('.')),
                    key=lambda e: e.name
                )
            except PermissionError:
                console_entries = []

            for console_dir in console_entries:
                games = []
                try:
                    # Depth-1: direct child dirs (simple games)
                    # Depth-2: children of those dirs (grouped multi-disc games)
                    depth1 = sorted(
                        (e for e in console_dir.iterdir() if e.is_dir() and not e.name.startswith('.')),
                        key=lambda e: e.name
                    )
                except PermissionError:
                    continue

                for child in depth1:
                    status = _classify_dir(child)
                    if status is not None:
                        games.append((child, status))
                    else:
                        # May be a grouping folder (multi-disc base) — check its children
                        try:
                            for grandchild in sorted(
                                (e for e in child.iterdir() if e.is_dir() and not e.name.startswith('.')),
                                key=lambda e: e.name
                            ):
                                gs = _classify_dir(grandchild)
                                if gs is not None:
                                    games.append((grandchild, gs))
                        except PermissionError:
                            pass

                if games:
                    structure[console_dir.name] = (console_dir, games)

        def _build_tree() -> None:
            try:
                tree = self.query_one("#lib-tree", Tree)
                tree.clear()
                tree.root.label = f"[bold]{library.name if library.exists() else 'Library'}[/bold]"

                for console_name, (console_path, games) in structure.items():
                    n_ok   = sum(1 for _, s in games if s == "validated")
                    n_bad  = sum(1 for _, s in games if s == "corrupted")
                    n_inc  = sum(1 for _, s in games if s == "incomplete")
                    badges = " ".join(filter(None, [
                        f"[bold green]{n_ok}✓[/]"   if n_ok  else "",
                        f"[bold red]{n_bad}✗[/]"     if n_bad else "",
                        f"[yellow]{n_inc}~[/yellow]" if n_inc else "",
                    ]))
                    console_node = tree.root.add(
                        f"[bold cyan]{console_name}[/]  {badges}",
                        data=console_path
                    )
                    for game_dir, status in games:
                        if status == "validated":
                            label = f"[bold green]✓  {game_dir.name}[/]"
                        elif status == "corrupted":
                            label = f"[bold red]✗  {game_dir.name}[/]"
                        else:
                            label = f"[yellow]~  {game_dir.name}[/yellow]"
                        console_node.add_leaf(label, data=game_dir)

                tree.root.expand()
            except Exception:
                pass

        self.call_from_thread(_build_tree)

    @work(exclusive=True, thread=True)
    def requeue_failed_games(self) -> None:
        """Finds all corrupted and incomplete game dirs and adds them to the active download queue."""
        library = Path(self.state.settings['library_root'])
        if not library.exists():
            self.post_message(SystemLog("Re-queue: Library path not found.", True))
            return

        def _dir_status(d: Path) -> Optional[str]:
            """None = skip, else 'validated'/'corrupted'/'incomplete'."""
            try:
                dir_files = [f for f in d.iterdir() if f.is_file() and not f.name.startswith('.')]
            except PermissionError:
                return None
            has_game = any(f.suffix.lower() in ('.bin', '.iso', '.cue', '.chd', '.img') for f in dir_files)
            has_zip  = any(f.suffix.lower() == '.zip' for f in dir_files)
            if not (has_game or has_zip or len(dir_files) == 0):
                return None
            if (d / ".validated").exists():
                return "validated"
            return "corrupted" if (d / ".corrupted").exists() else "incomplete"

        targets: List[tuple] = []  # (console_name, game_dir, status)
        try:
            console_dirs = sorted(
                (e for e in library.iterdir() if e.is_dir() and not e.name.startswith('.')),
                key=lambda e: e.name
            )
        except PermissionError:
            console_dirs = []

        for console_dir in console_dirs:
            console_name = console_dir.name
            try:
                depth1 = sorted(
                    (e for e in console_dir.iterdir() if e.is_dir() and not e.name.startswith('.')),
                    key=lambda e: e.name
                )
            except PermissionError:
                continue

            for child in depth1:
                status = _dir_status(child)
                if status is not None:
                    if status != "validated":
                        targets.append((console_name, child, status))
                else:
                    try:
                        for grandchild in sorted(
                            (e for e in child.iterdir() if e.is_dir() and not e.name.startswith('.')),
                            key=lambda e: e.name
                        ):
                            gs = _dir_status(grandchild)
                            if gs is not None and gs != "validated":
                                targets.append((console_name, grandchild, gs))
                    except PermissionError:
                        pass

        if not targets:
            self.post_message(SystemLog("Re-queue: No incomplete or corrupted games found. Library looks clean!"))
            return

        current_queue  = self.state.get_active_queue()
        existing_paths = {i["dest_path"] for i in current_queue}
        added = 0

        for console_name, game_dir, status in targets:
            if str(game_dir) in existing_paths:
                continue
            # Reconstruct the Myrient download URL from the library directory structure.
            # The zip filename is always: game_dir.name + ".zip"
            game_zip  = game_dir.name + ".zip"
            game_url  = BASE_URL + quote(console_name + "/", safe="") + quote(game_zip, safe="")
            flag      = "[bold red]corrupted[/]" if status == "corrupted" else "[yellow]incomplete[/]"
            current_queue.append({
                "id":        f"dl_{uuid.uuid4().hex[:8]}",
                "name":      f"[{console_name}] {game_zip}  {flag}",
                "game_url":  game_url,
                "dest_path": str(game_dir),
                "size_str":  "N/A",
            })
            existing_paths.add(str(game_dir))
            added += 1

        if added:
            self.state.update_active_queue(current_queue)
            self.call_from_thread(self._refresh_queue_table)
            # Switch to the queue tab so the user can see what was added
            self.call_from_thread(
                lambda: setattr(self.query_one("#tabs", TabbedContent), "active", "tab-queue-dl")
            )

        self.post_message(SystemLog(
            f"Re-queued [bold]{added}[/bold] game(s): "
            f"{sum(1 for _,_,s in targets if s=='corrupted')} corrupted, "
            f"{sum(1 for _,_,s in targets if s=='incomplete')} incomplete."
        ))

    def _parse_size_bytes(self, size_str: str) -> int:
        if not size_str or size_str == "N/A":
            return 0
            
        clean = size_str.upper().replace(" ", "").replace("I", "").replace("B", "")
        units = {"K": 1024, "M": 1024**2, "G": 1024**3, "T": 1024**4}
        
        try: 
            if not clean:
                return 0
            return int(float(clean[:-1]) * units[clean[-1]]) if clean[-1] in units else int(float(clean))
        except (ValueError, IndexError, TypeError): 
            return 0

    async def on_unmount(self) -> None:
        self.cleanup_subprocesses()


if __name__ == "__main__":
    MyrientTUI().run()
