"""Library operation commands — self-contained units of work.

Each command encapsulates a library operation (organize, convert, audit)
with its own execute() method.  The app dispatches them via a single
``run_library_command()`` method, which handles the @work decorator,
cancel-flag management, and progress reporting.

This replaces the pattern of 100-500 line methods directly on MyrientTUI,
making each operation independently testable and composable.
"""
from __future__ import annotations

import hashlib
import itertools
import json
import logging
import shutil
import threading
import concurrent.futures
from pathlib import Path
from typing import Any, TYPE_CHECKING

from .constants import (
    _CHD_SOURCE_EXTS, _DAT_AUDITABLE_EXTS, _HASH_CHUNK_BYTES,
    DAT_CACHE_DIR, DISC_REGEX,
)
from .library_ops import LibraryOperation

if TYPE_CHECKING:
    from .app import MyrientTUI
    from .toolchain import Toolchain


class LibraryCommand:
    """Base class for library operation commands.

    Subclasses implement ``execute(op)`` which receives a fully-initialized
    ``LibraryOperation`` with cancel-flag, progress, and logging ready.

    Attributes:
        name:  Human-readable operation name (used in progress bars and logs).
        scope: Optional path to narrow the operation to a console or game dir.
    """

    name: str = "Operation"

    def __init__(self, scope: Path | None = None) -> None:
        self.scope = scope

    def execute(self, op: LibraryOperation, app: MyrientTUI) -> None:
        """Run the operation.  Called on a worker thread."""
        raise NotImplementedError


class OrganizeCommand(LibraryCommand):
    """Organize multi-disc games into parent folders and clean up empties."""

    name = "Organize"

    def execute(self, op: LibraryOperation, app: MyrientTUI) -> None:
        op.log("Library Scan: Building target list...")

        targets = []
        empty_dirs: list[Path] = []

        if op.library.exists():
            try:
                console_dirs = [d for d in op.library.iterdir()
                                if d.is_dir() and not d.name.startswith('.')]
            except PermissionError:
                console_dirs = []

            for console_dir in console_dirs:
                try:
                    game_entries = list(console_dir.iterdir())
                except PermissionError:
                    continue
                for game_dir in game_entries:
                    if not game_dir.is_dir() or game_dir.name.startswith('.'):
                        continue
                    base_name = DISC_REGEX.sub('', game_dir.name).strip()
                    if base_name != game_dir.name:
                        targets.append((game_dir, console_dir / base_name))
                    else:
                        try:
                            if not any(game_dir.iterdir()):
                                empty_dirs.append(game_dir)
                        except PermissionError:
                            pass

        total_ops = len(targets) + len(empty_dirs)
        if total_ops == 0:
            op.log("Library Scan: No valid targets found. (Library is already organized)")
            op.progress("Organize", "Done", 100, 100)
            return

        changed = 0
        step = 0
        for game_dir, parent_dir in targets:
            step += 1
            if op.cancelled:
                op.log("[yellow]Organize cancelled.[/]")
                break
            op.progress(f"Organizing ({step}/{total_ops})", game_dir.name, step, total_ops)
            parent_dir.mkdir(parents=True, exist_ok=True)
            new_location = parent_dir / game_dir.name
            try:
                old_status = op.lib_status.get(game_dir)
                shutil.move(game_dir, new_location)
                op.lib_status.remove(game_dir)
                if old_status in ("validated", "corrupted"):
                    op.lib_status.set_status(new_location, old_status)
                changed += 1
            except Exception as e:
                op.log(f"Move failed [{game_dir.name}]: {e}", True)

        for empty_dir in empty_dirs:
            step += 1
            if op.cancelled:
                break
            op.progress(f"Cleanup ({step}/{total_ops})", empty_dir.name, step, total_ops)
            try:
                if empty_dir.exists() and not any(empty_dir.iterdir()):
                    op.lib_status.remove(empty_dir)
                    empty_dir.rmdir()
                    op.log(f"Removed empty folder: {empty_dir.name}")
                    changed += 1
            except OSError:
                pass

        op.progress("Organize", "Complete", total_ops, total_ops)
        if changed:
            app.run_lib_status_scan()
        op.log(f"Clean-up Complete. {changed} folder(s) organized/removed.")


class RefreshCommand(LibraryCommand):
    """Organize multi-disc folders then refresh the library tree."""

    name = "Refresh"

    def execute(self, op: LibraryOperation, app: MyrientTUI) -> None:
        # Run organize first (moves disc variants into parent folders, cleans empties)
        OrganizeCommand().execute(op, app)
        # Always rescan — OrganizeCommand only rescans when it changes something,
        # but Refresh should always give a fresh view.
        app.run_lib_status_scan()


class ConvertCommand(LibraryCommand):
    """Convert disc images to CHD format."""

    name = "CHD Conversion"

    def __init__(self, scope: Path | None = None, toolchain: Toolchain | None = None) -> None:
        super().__init__(scope)
        self.toolchain = toolchain

    def execute(self, op: LibraryOperation, app: MyrientTUI) -> None:
        from .toolchain import Toolchain

        library = op.library
        scope_label = op.scope_label()
        chdman = (self.toolchain or app.toolchain).chdman_path or Toolchain.find_chdman()
        if not chdman:
            op.log(
                "[bold red]chdman not found.[/bold red] "
                "Run 'Setup chdman' first, or install it manually.", True,
            )
            return

        scope = self.scope
        if scope is None or scope == library:
            scope = library

        op.log(f"CHD Conversion: Scanning {scope_label}\u2026")

        targets = []
        if scope != library and scope.parent != library:
            # Game-level scope
            try:
                dir_files = [f for f in scope.iterdir() if f.is_file()]
            except PermissionError:
                dir_files = []
            has_source = has_chd = False
            for f in dir_files:
                ext = f.suffix.lower()
                if ext in _CHD_SOURCE_EXTS:
                    has_source = True
                elif ext == '.chd':
                    has_chd = True
                if has_source and has_chd:
                    break
            if has_source and not has_chd:
                targets.append(scope)
            else:
                try:
                    subdirs = sorted(d for d in scope.iterdir()
                                     if d.is_dir() and not d.name.startswith('.'))
                except PermissionError:
                    subdirs = []
                for sub in subdirs:
                    try:
                        sub_files = [f for f in sub.iterdir() if f.is_file()]
                    except PermissionError:
                        continue
                    s_src = s_chd = False
                    for f in sub_files:
                        ext = f.suffix.lower()
                        if ext in _CHD_SOURCE_EXTS:
                            s_src = True
                        elif ext == '.chd':
                            s_chd = True
                        if s_src and s_chd:
                            break
                    if s_src and not s_chd:
                        targets.append(sub)
        else:
            for _, game_dir, status in app._walk_library_game_dirs(library, op.lib_status):
                if scope != library and not game_dir.is_relative_to(scope):
                    continue
                if status == "corrupted":
                    continue
                try:
                    dir_files = [f for f in game_dir.iterdir() if f.is_file()]
                except PermissionError:
                    continue
                has_source = has_chd = False
                for f in dir_files:
                    ext = f.suffix.lower()
                    if ext in _CHD_SOURCE_EXTS:
                        has_source = True
                    elif ext == '.chd':
                        has_chd = True
                    if has_source and has_chd:
                        break
                if has_source and not has_chd:
                    targets.append(game_dir)

        total_ops = len(targets)
        if total_ops == 0:
            op.log(f"CHD Conversion [{scope_label}]: No convertible files found.")
            op.progress("CHD Conversion", "Done", 100, 100)
            return

        converted = failed = 0
        for i, game_dir in enumerate(targets, 1):
            if op.cancelled:
                op.log("[yellow]CHD conversion cancelled.[/]")
                break
            op.progress(f"Converting ({i}/{total_ops})", game_dir.name, i, total_ops)
            op.log(f"Converting: {game_dir.name}")
            c, f = app._convert_to_chd(game_dir, silent=False, cancel=op.cancel)
            converted += c
            failed += f

        op.progress("CHD Conversion", "Complete", total_ops, total_ops)
        op.log(
            f"CHD Conversion [{scope_label}] finished — "
            f"[bold green]{converted}[/] converted, [bold red]{failed}[/] failed."
        )


class DatAuditCommand(LibraryCommand):
    """Run DAT audit against Redump/No-Intro DAT files.

    Always runs in dry-run mode first so the user can review proposed
    changes.  If fixable files are found, a confirmation dialog is shown.
    On acceptance, a second pass applies the renames and writes markers.
    """

    name = "Verify"

    def execute(self, op: LibraryOperation, app: MyrientTUI) -> None:
        import threading
        from .modals import ConfirmVerifyScreen

        library = op.library
        dat_ttl = app.state.settings.get("dat_cache_ttl_hours", 168) * 3600.0

        if not library.exists():
            op.log("Verify: Library path not found.", True)
            return

        scope = self.scope
        if scope is None:
            scope = library

        # Phase 1: discover console dirs
        if scope == library:
            console_dirs = sorted(
                d for d in library.iterdir()
                if d.is_dir() and not d.name.startswith('.')
            )
        elif scope.parent == library:
            console_dirs = [scope] if scope.is_dir() else []
        else:
            console_parent = scope.parent
            while console_parent.parent != library and console_parent != library:
                console_parent = console_parent.parent
            console_dirs = [console_parent] if console_parent.is_dir() else []
        scope_label = op.scope_label()

        if not console_dirs:
            op.log("Verify: No console folders found in library.")
            return

        op.log(
            f"Verify [{scope_label}]: Scanning {len(console_dirs)} console(s)..."
        )

        # Phase 2: fetch DAT index
        dat_index = app._dat_fetch_index(op)
        if dat_index is None:
            return

        # Phase 3: dry-run scan — always preview first
        grand_perfect = grand_misnamed = grand_ambiguous = grand_bad = 0
        # Store per-console parsed data for the apply pass
        console_audit_data: list[tuple[Path, dict, set, dict]] = []

        for con_idx, console_dir in enumerate(console_dirs, 1):
            if op.cancelled:
                op.log("[yellow]Verify cancelled.[/]")
                break

            console_name = console_dir.name
            phase_label = f"[{con_idx}/{len(console_dirs)}] {console_name}"
            op.progress("Verify", phase_label, con_idx - 1, len(console_dirs))

            dat_path = app._dat_resolve_dat_file(console_name, dat_index, dat_ttl, op)
            if dat_path is None:
                continue

            parsed = app._dat_parse_xml(dat_path)
            if parsed is None:
                op.log(f"Verify [{console_name}]: Failed to parse DAT.", True)
                continue
            dat_by_sha1, ambiguous_sha1s, dat_all_games = parsed

            dat_disc_groups: dict[str, set[str]] = {}
            for gname in dat_all_games:
                base = DISC_REGEX.sub('', gname).strip()
                if base != gname:
                    dat_disc_groups.setdefault(base, set()).add(gname)

            # Always dry-run first
            perfect, misnamed, ambiguous, bad = app._dat_audit_one_console(
                console_dir, library, dat_by_sha1, ambiguous_sha1s,
                dat_disc_groups, True, op,
            )

            op.log(
                f"Verify [{console_name}]: "
                f"Perfect: {perfect}  Fixable: {misnamed}  "
                f"Ambiguous: {ambiguous}  Bad/Unknown: {bad}"
            )
            grand_perfect += perfect
            grand_misnamed += misnamed
            grand_ambiguous += ambiguous
            grand_bad += bad

            # Save data for the apply pass (always include — multi-disc check
            # needs to run even when no renames are needed)
            console_audit_data.append(
                (console_dir, dat_by_sha1, ambiguous_sha1s, dat_disc_groups)
            )

        op.progress("Verify", "Scan complete", 100, 100)
        op.log(
            f"[bold]Verify Scan Complete[/bold] — "
            f"Perfect: [bold green]{grand_perfect}[/]  "
            f"Fixable: [bold yellow]{grand_misnamed}[/]  "
            f"Ambiguous: [bold cyan]{grand_ambiguous}[/]  "
            f"Bad/Unknown: [bold red]{grand_bad}[/]"
        )

        # Phase 4: if there are fixable files, prompt user to apply
        if grand_misnamed > 0:
            # Prompt on the main thread, block this worker until the user decides
            result_event = threading.Event()
            user_accepted = [False]

            def _on_confirm(accepted: bool) -> None:
                user_accepted[0] = accepted
                result_event.set()

            def _show_dialog() -> None:
                app.push_screen(
                    ConfirmVerifyScreen(grand_misnamed, grand_bad),
                    callback=_on_confirm,
                )

            app.call_from_thread(_show_dialog)
            result_event.wait()

            if not user_accepted[0]:
                op.log("[dim]Verify: User declined — no changes applied.[/dim]")
                return
        else:
            op.log("No renames needed — library is clean.")

        # Phase 5: apply pass — validate markers + multi-disc completeness
        if grand_misnamed > 0:
            op.log("[bold]Applying renames...[/bold]")
        applied_fixed = 0
        for idx, (console_dir, dat_by_sha1, ambiguous_sha1s, dat_disc_groups) in enumerate(console_audit_data, 1):
            if op.cancelled:
                op.log("[yellow]Apply cancelled.[/]")
                break
            op.progress("Applying", console_dir.name, idx, len(console_audit_data))
            perfect, misnamed, ambiguous, bad = app._dat_audit_one_console(
                console_dir, library, dat_by_sha1, ambiguous_sha1s,
                dat_disc_groups, False, op,
            )
            applied_fixed += misnamed

        op.progress("Verify", "Complete", 100, 100)
        if applied_fixed > 0:
            op.log(f"[bold green]Applied {applied_fixed} rename(s).[/bold green]")
        app.run_lib_status_scan()
