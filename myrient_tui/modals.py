"""Modal screen widgets — ConfirmDeleteScreen, ConfirmActionScreen, HelpModal."""
from __future__ import annotations

from pathlib import Path

from rich.text import Text
from textual.app import ComposeResult
from textual.containers import Horizontal, Vertical, VerticalScroll
from textual.screen import ModalScreen
from textual.widgets import Button, Label


class ConfirmDeleteScreen(ModalScreen[bool]):
    def __init__(self, target_name: str):
        super().__init__()
        self.target_name = target_name

    def compose(self) -> ComposeResult:
        with Vertical(id="dialog"):
            msg = Text.assemble(
                "Permanently delete ",
                (self.target_name, "bold red"),
                "?",
            )
            yield Label(msg, id="question")
            with Horizontal(id="dialog-btn-row"):
                yield Button("Cancel", variant="primary", id="btn-cancel")
                yield Button("Delete", variant="error",   id="btn-delete")

    def on_button_pressed(self, event: Button.Pressed) -> None:
        self.dismiss(event.button.id == "btn-delete")


class ConfirmDownloadScreen(ModalScreen[bool]):
    """U3: Confirmation dialog before starting large downloads."""

    def __init__(self, count: int, size_str: str):
        super().__init__()
        self.count = count
        self.size_str = size_str

    def compose(self) -> ComposeResult:
        with Vertical(id="dialog"):
            msg = Text.assemble(
                "Start downloading ",
                (f"{self.count} items", "bold #e6b73e"),
                " (~",
                (self.size_str, "bold #58a6ff"),
                ")?",
            )
            yield Label(msg, id="question")
            with Horizontal(id="dialog-btn-row"):
                yield Button("Cancel", variant="default", id="btn-cancel")
                yield Button("Start", variant="success",  id="btn-start")

    def on_button_pressed(self, event: Button.Pressed) -> None:
        self.dismiss(event.button.id == "btn-start")


class ConfirmVerifyScreen(ModalScreen[bool]):
    """Prompt user to apply DAT audit renames after a dry-run scan."""

    def __init__(self, misnamed: int, bad: int):
        super().__init__()
        self.misnamed = misnamed
        self.bad = bad

    def compose(self) -> ComposeResult:
        with Vertical(id="dialog"):
            msg = Text.assemble(
                "Verify found ",
                (f"{self.misnamed} fixable", "bold #e6b73e"),
                " and ",
                (f"{self.bad} bad/unknown", "bold red"),
                " file(s).\n\nApply renames and update status markers?",
            )
            yield Label(msg, id="question")
            with Horizontal(id="dialog-btn-row"):
                yield Button("Cancel", variant="default", id="btn-cancel")
                yield Button("Apply", variant="success", id="btn-apply")

    def on_button_pressed(self, event: Button.Pressed) -> None:
        self.dismiss(event.button.id == "btn-apply")


class ConfirmActionScreen(ModalScreen[bool]):
    """Reusable confirmation screen for library actions."""

    def __init__(self, action_name: str, game_paths: list[Path],
                 warning_text: str | None = None):
        super().__init__()
        self.action_name = action_name
        self.game_paths = game_paths
        self.warning_text = warning_text

    def compose(self) -> ComposeResult:
        is_destructive = self.warning_text is not None
        dialog_classes = "--destructive" if is_destructive else ""
        with Vertical(id="action-dialog", classes=dialog_classes):
            title = Text.assemble(
                "Confirm: ",
                (self.action_name, "bold"),
            )
            yield Label(title, id="action-title")
            if self.warning_text:
                yield Label(
                    Text(self.warning_text, style="bold red"),
                    id="action-warning",
                )
            count_label = Text.assemble(
                "On ",
                (f"{len(self.game_paths)}", "bold #58a6ff"),
                " game(s):",
            )
            yield Label(count_label)
            with VerticalScroll(id="action-game-list"):
                for p in self.game_paths[:100]:
                    yield Label(Text.assemble(("  • ", "dim"), (p.name, "#9aa0aa")))
                if len(self.game_paths) > 100:
                    yield Label(Text(f"  … and {len(self.game_paths) - 100} more", style="dim"))
            with Horizontal(id="action-btn-row"):
                yield Button("Cancel", variant="primary", id="btn-action-cancel")
                variant = "error" if is_destructive else "success"
                yield Button("Continue", variant=variant, id="btn-action-continue")

    def on_button_pressed(self, event: Button.Pressed) -> None:
        self.dismiss(event.button.id == "btn-action-continue")


class HelpModal(ModalScreen):
    """Keyboard shortcut reference, shown with ?."""

    BINDINGS = [("escape", "dismiss_modal", "Close"), ("question_mark", "dismiss_modal", "Close")]

    def compose(self) -> ComposeResult:
        # U5: Wrap in VerticalScroll so the modal scrolls on small terminals
        with Vertical(id="help-dialog"):
            yield Label("  Keyboard Shortcuts", id="help-title")
            with VerticalScroll(id="help-scroll"):
                rows = [
                    ("Ctrl+Q",    "Quit"),
                    ("Ctrl+D",    "Toggle dark/light theme"),
                    ("Ctrl+R",    "Refresh console list"),
                    ("Ctrl+J",    "Jump queue item → Browser"),
                    ("Ctrl+Enter","Start downloads"),         # U6
                    ("Ctrl+P",   "Pause downloads"),          # U6
                    ("Escape",    "Blur focused input"),
                    ("?",         "Show this help"),
                    ("",          ""),
                    ("── Browse ──", ""),
                    ("↑ ↓",       "Navigate lists and tables"),
                    ("Space",     "Toggle game selection"),
                    ("Tab",       "Toggle game selection (search box)"),
                    ("Enter / q", "Queue selected games"),
                    ("Global",    "Toggle cross-console search"),
                    ("",          ""),
                    ("── Queue ──", ""),
                    ("Space",     "Multi-select queue items"),
                    ("Shift+Spc", "Range-select queue items"),
                    ("Delete",    "Remove selected queue item(s)"),
                    ("Shift+↑",  "Move queue item up"),
                    ("Shift+↓",  "Move queue item down"),
                    ("",          ""),
                    ("── Library ──", ""),
                    ("Tab",        "Toggle game/console selection"),
                    ("Ctrl+A",    "Select all games"),
                    ("Escape",     "Clear selection"),
                    ("",          ""),
                    ("── Nav ──",  ""),
                    ("1–5",       "Switch pane (when not in input)"),
                ]
                for key, desc in rows:
                    if not key:
                        yield Label("", classes="help-row")
                    elif key.startswith("──"):
                        yield Label(Text(f"  {key}", style="bold #e6b73e"), classes="help-row")
                    else:
                        yield Label(
                            Text.assemble(
                                (f"  {key:<14}", "#58a6ff"),
                                (desc, "#9aa0aa"),
                            ),
                            classes="help-row",
                        )
            yield Button("Close", id="help-close", variant="primary")

    def action_dismiss_modal(self) -> None:
        self.dismiss()

    def on_button_pressed(self, _: Button.Pressed) -> None:
        self.dismiss()
