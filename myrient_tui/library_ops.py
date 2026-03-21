"""Library operation base class — shared helpers for cancel-flag management,
scope resolution, progress/log posting, and library-status access."""
from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING

from .messages import LibraryProgress, SystemLog

if TYPE_CHECKING:
    from .app import MyrientTUI


class LibraryOperation:
    """Base class for library worker operations with shared helpers.

    Encapsulates the common patterns: cancel-flag management, scope resolution,
    progress/log posting, and library-status access.
    """

    def __init__(self, app: MyrientTUI, scope: Path | None = None) -> None:
        self.app = app
        self.scope = scope
        self.cancel = app._lib_cancel
        self.cancel.clear()
        self.library = Path(app.state.settings['library_root'])
        self.lib_status = app._lib_status

    @property
    def cancelled(self) -> bool:
        return self.cancel.is_set()

    def log(self, msg: str, error: bool = False) -> None:
        self.app.post_message(SystemLog(msg, error))

    def progress(self, label: str, detail: str, current: int, total: int) -> None:
        self.app.post_message(LibraryProgress(label, detail, current, total))

    def resolve_scope(self) -> list[tuple[Path, list[Path]]]:
        """Resolve scope to list of (console_dir, [game_dirs]) pairs.

        Handles three levels:
        - scope=None or scope=library root -> all consoles
        - scope=console dir -> single console
        - scope=game dir -> single game (parent is console)
        """
        if not self.library.exists():
            self.log("Library path not found.", True)
            return []

        scope = self.scope

        if scope is None or scope == self.library:
            try:
                console_dirs = sorted(
                    d for d in self.library.iterdir()
                    if d.is_dir() and not d.name.startswith('.')
                )
            except PermissionError:
                return []
            result = []
            for cd in console_dirs:
                try:
                    games = sorted(
                        g for g in cd.iterdir()
                        if g.is_dir() and not g.name.startswith('.')
                    )
                except PermissionError:
                    continue
                if games:
                    result.append((cd, games))
            return result

        if scope.parent == self.library:
            try:
                games = sorted(
                    g for g in scope.iterdir()
                    if g.is_dir() and not g.name.startswith('.')
                )
            except PermissionError:
                return []
            return [(scope, games)] if games else []

        # Game-level scope
        console_dir = scope.parent
        return [(console_dir, [scope])]

    def scope_label(self) -> str:
        """Return a human-readable label for the current scope."""
        scope = self.scope
        if scope is None or scope == self.library:
            return "full library"
        if scope.parent == self.library:
            return f"console [{scope.name}]"
        return f"game [{scope.name}]"
