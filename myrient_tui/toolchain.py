"""Toolchain -- chdman + PS2 Master Disc Patcher setup / invocation.

Extracted from the MyrientTUI monolith so binary discovery, package-manager
install, and external-process invocations live in one auditable place.
"""
from __future__ import annotations

import hashlib
import logging
import os
import shutil
import subprocess
import sys
import threading
import time
import urllib.request
import zipfile as _zf
from collections.abc import Callable
from pathlib import Path
from typing import Any

from myrient_tui.constants import (
    _CHD_CMD_MAP,
    _CHD_PCT_RE,
    _CHD_TIMEOUT,
    _DATA_DIR,
    _HASH_CHUNK_BYTES,
    _LOW_PRIO_POPEN,
    _PKG_INSTALL_CMDS,
    _PS2MDP_BINARY_NAME,
    _PS2MDP_RELEASE_SHA256,
    _PS2MDP_RELEASE_URL,
    _PS2MDP_RELEASE_VERSION,
    _SCRIPT_DIR,
    _TOOLS_DIR,
    CUE_BIN_REGEX,
)
from myrient_tui.messages import LibraryProgress, SystemLog


# ── Utility helpers ──────────────────────────────────────────────────────────

def _sha256_file(path: Path) -> str:
    """Return the lowercase hex SHA-256 digest of *path*.
    Uses ``_HASH_CHUNK_BYTES`` for I/O buffer size consistency.
    """
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        while chunk := fh.read(_HASH_CHUNK_BYTES):
            h.update(chunk)
    return h.hexdigest().lower()


def _safe_extractall(zf: _zf.ZipFile, dest: Path) -> None:
    """Extract *zf* into *dest* while blocking path-traversal attacks.

    Python < 3.12 does not sanitise member paths in ``ZipFile.extractall``,
    so a crafted ZIP containing entries like ``../../.bashrc`` can write files
    outside *dest*.  This helper resolves every member path and raises
    ``ValueError`` for any entry that would land outside *dest*.

    Python 3.12+ has built-in extraction filters (``filter='data'``); we use
    those when available so we benefit from any additional hardening they add.
    """
    if sys.version_info >= (3, 12):
        zf.extractall(dest, filter="data")   # type: ignore[call-arg]
        return
    dest_resolved = dest.resolve()
    for member in zf.infolist():
        # Resolve the target path and check it stays inside dest.
        # Path.is_relative_to() (Python 3.9+) handles platform path separators
        # and normalises away any .. components before the comparison.
        target = (dest / member.filename).resolve()
        if not (target == dest_resolved or target.is_relative_to(dest_resolved)):
            raise ValueError(
                f"ZIP path traversal blocked: {member.filename!r} "
                f"would land at {target}, outside {dest_resolved}"
            )
    zf.extractall(dest)


# ─────────────────────────────────────────────────────────────────────────────
# Toolchain — chdman + PS2 Master Disc Patcher setup / invocation
# Extracted from MyrientTUI so binary discovery, package-manager install, and
# external-process invocations live in one auditable place.
# ─────────────────────────────────────────────────────────────────────────────
class Toolchain:
    """Manages external tool discovery and invocation (chdman, ps2_master).

    Extracted from MyrientTUI to satisfy the Single Responsibility Principle.
    MyrientTUI creates one instance and calls its methods; it never directly
    invokes chdman or ps2_master itself.

    Parameters
    ----------
    post_message_fn:
        Callable matching ``App.post_message`` — used to emit ``SystemLog`` and
        ``DownloadProgress`` messages from worker threads.
    cancel_flag:
        The shared ``threading.Event`` that workers poll to detect pause/cancel.
    register_process / unregister_process:
        Callbacks that add/remove a ``subprocess.Popen`` from the app's tracked
        process set so ``cleanup_subprocesses`` can kill them on quit.
    chd_lock:
        Mutex that serialises concurrent .cue/.bin cleanup across CHD workers.
    """

    def __init__(
        self,
        post_message_fn: Callable[..., Any],
        cancel_flag: threading.Event,
        register_process: Callable[[subprocess.Popen[Any]], Any],
        unregister_process: Callable[[subprocess.Popen[Any]], Any],
        chd_lock: threading.Lock,
    ) -> None:
        self._post             = post_message_fn
        self.cancel_flag       = cancel_flag
        self._reg_proc         = register_process
        self._unreg_proc       = unregister_process
        self.chd_lock          = chd_lock
        self.chdman_path: str  = ""
        self.ps2mdp_path: str  = ""
        # Limit chdman cores aggressively — LZMA compression is extremely
        # memory-hungry per core (~600 MB each for DVD images).  Using too many
        # cores on a system with limited RAM causes OOM/freeze, especially in
        # WSL2 which shares memory with the Windows host.
        _cpu = os.cpu_count() or 2
        self.chd_cores: int    = max(1, min(2, _cpu // 4))
        # Serialise concurrent chdman invocations (e.g. auto-CHD during
        # parallel downloads) so only one runs at a time.
        self._chd_sem          = threading.Semaphore(1)

    # ── Binary discovery ──────────────────────────────────────────────────────

    @staticmethod
    def find_chdman() -> str:
        """Locate chdman. Returns full path string or '' if not found."""
        local_candidates = [
            _TOOLS_DIR / "chdman",
            _TOOLS_DIR / "chdman.exe",
            _SCRIPT_DIR / "chdman",
            _SCRIPT_DIR / "chdman.exe",
        ]
        for p in local_candidates:
            if p.is_file() and os.access(p, os.X_OK):
                return str(p)
        return shutil.which("chdman") or ""

    @staticmethod
    def find_ps2mdp() -> str:
        """Locate ps2_master binary. Returns full path or ''."""
        candidates = [
            _TOOLS_DIR / _PS2MDP_BINARY_NAME,
            _TOOLS_DIR / (_PS2MDP_BINARY_NAME + ".exe"),
            _SCRIPT_DIR / _PS2MDP_BINARY_NAME,
            _SCRIPT_DIR / (_PS2MDP_BINARY_NAME + ".exe"),
        ]
        for p in candidates:
            if p.is_file() and os.access(p, os.X_OK):
                return str(p)
        return shutil.which(_PS2MDP_BINARY_NAME) or ""

    def refresh_chdman(self) -> None:
        """Re-resolve chdman path and cache it on self.chdman_path."""
        self.chdman_path = self.find_chdman()

    def refresh_ps2mdp(self) -> None:
        """Re-resolve ps2_master path and cache it on self.ps2mdp_path."""
        self.ps2mdp_path = self.find_ps2mdp()

    # ── chdman setup ──────────────────────────────────────────────────────────

    def setup_chdman_auto(self) -> None:
        """Try to install chdman via the system package manager."""
        self._post(SystemLog("chdman Setup: Checking for existing installation..."))
        path = self.find_chdman()
        if path:
            self.chdman_path = path
            self._post(SystemLog(f"chdman already available at: [bold]{path}[/bold]"))
            return

        self._post(SystemLog("chdman Setup: Attempting package-manager install..."))
        for label, cmd in _PKG_INSTALL_CMDS:
            mgr = shutil.which(cmd[0])
            if not mgr:
                continue
            self._post(SystemLog(f"chdman Setup: Trying [bold]{label}[/bold]…"))
            try:
                result = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
                if result.returncode == 0:
                    path = self.find_chdman()
                    if path:
                        self.chdman_path = path
                        self._post(SystemLog(
                            f"[bold green]chdman installed successfully![/bold green] "
                            f"Path: [bold]{path}[/bold]"
                        ))
                        return
                else:
                    self._post(SystemLog(
                        f"chdman Setup: {label} returned non-zero "
                        f"(may need sudo). Output: {result.stderr[:120]}", True
                    ))
            except (subprocess.TimeoutExpired, OSError) as e:
                self._post(SystemLog(f"chdman Setup: {label} failed — {e}", True))

        self._post(SystemLog(
            "[bold yellow]chdman auto-install failed.[/bold yellow] "
            "Manual options:\n"
            "  • Linux (Debian/Ubuntu):  sudo apt install mame-tools\n"
            "  • Linux (Arch):           sudo pacman -S mame-tools\n"
            "  • Linux (Fedora):         sudo dnf install mame-tools\n"
            "  • macOS (Homebrew):       brew install rom-tools\n"
            "  • Windows: download MAME tools from https://www.mamedev.org/release.html\n"
            "Place chdman(.exe) in the myrient_data/tools/ folder to use it without installing."
        ))

    # ── PS2 Master Disc Patcher setup ─────────────────────────────────────────

    def setup_ps2mdp_auto(self) -> None:
        """Download and verify ps2_master from the PSDB v1.0.5 x86_64 release zip."""
        self._post(SystemLog("PS2 Patcher Setup: Checking for existing installation..."))
        path = self.find_ps2mdp()
        if path:
            self.ps2mdp_path = path
            self._post(SystemLog(f"ps2_master already available at: [bold]{path}[/bold]"))
            return

        self._post(SystemLog(
            "PS2 Patcher Setup: Downloading PSDB v1.0.5 x86_64 release zip…\n"
            f"  {_PS2MDP_RELEASE_URL}"
        ))

        tmp_zip = _TOOLS_DIR / "_ps2mdp_download.zip"
        try:
            # ── Download ─────────────────────────────────────────────────────
            try:
                subprocess.run(
                    ["wget", "-q", "--timeout=60", "--tries=3",
                     "-O", str(tmp_zip), _PS2MDP_RELEASE_URL],
                    check=True, timeout=300,
                )
            except Exception:
                req = urllib.request.Request(
                    _PS2MDP_RELEASE_URL,
                    headers={"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64)"},
                )
                with urllib.request.urlopen(req, timeout=120) as resp, \
                        open(tmp_zip, "wb") as fout:
                    shutil.copyfileobj(resp, fout)

            # ── SHA-256 integrity check ───────────────────────────────────────
            self._post(SystemLog("PS2 Patcher Setup: Verifying download integrity…"))
            actual_sha256 = _sha256_file(tmp_zip)
            if actual_sha256 != _PS2MDP_RELEASE_SHA256:
                self._post(SystemLog(
                    f"[bold red]PS2 Patcher Setup: SHA-256 mismatch — aborting.[/bold red]\n"
                    f"  Pinned version : {_PS2MDP_RELEASE_VERSION}\n"
                    f"  Expected SHA-256: {_PS2MDP_RELEASE_SHA256}\n"
                    f"  Got SHA-256:      {actual_sha256}\n"
                    "This usually means the release asset was updated upstream. "
                    "To upgrade: set _PS2MDP_RELEASE_VERSION to the new tag, update "
                    "_PS2MDP_RELEASE_URL and _PS2MDP_RELEASE_SHA256 at the top of the source "
                    "(run 'sha256sum' on the new zip to get the correct digest).",
                    True,
                ))
                return

            # ── Extract ps2_master binary from bin/ in the release zip ────────
            extracted_binary = False
            with _zf.ZipFile(tmp_zip, "r") as zf:
                all_members = zf.namelist()
                self._post(SystemLog(
                    f"PS2 Patcher Setup: Zip has {len(all_members)} entries. First 60:\n  " +
                    "\n  ".join(all_members[:60]) +
                    ("\n  …" if len(all_members) > 60 else "")
                ))
                for member in all_members:
                    if member.endswith("/"):
                        continue
                    base  = Path(member).name
                    in_bin = "/bin/" in member
                    if base == _PS2MDP_BINARY_NAME and in_bin and not extracted_binary:
                        dest = _TOOLS_DIR / _PS2MDP_BINARY_NAME
                        with zf.open(member) as src, open(dest, "wb") as dst:
                            shutil.copyfileobj(src, dst)
                        dest.chmod(dest.stat().st_mode | 0o111)
                        extracted_binary = True
                        self._post(SystemLog(
                            f"PS2 Patcher Setup: Extracted [bold]{base}[/bold] "
                            f"from [dim]{member}[/dim] → {dest}"
                        ))
                        break

            if not extracted_binary:
                self._post(SystemLog(
                    "[bold red]PS2 Patcher Setup: binary not found in release zip.[/bold red]\n"
                    "Check the zip contents log above. Manual install:\n"
                    f"  1. Download: {_PS2MDP_RELEASE_URL}\n"
                    f"  2. Extract 'bin/{_PS2MDP_BINARY_NAME}' to myrient_data/tools/\n"
                    f"  3. chmod +x myrient_data/tools/{_PS2MDP_BINARY_NAME}",
                    True,
                ))
                return

            path = self.find_ps2mdp()
            if path:
                self.ps2mdp_path = path
                self._post(SystemLog(
                    f"[bold green]PS2 Master Disc Patcher ready![/bold green] "
                    f"Path: [bold]{path}[/bold]"
                ))
            else:
                self._post(SystemLog(
                    "[bold red]Setup finished but binary not found — "
                    "extraction may have failed.[/bold red]", True
                ))

        except Exception as err:
            self._post(SystemLog(f"[bold red]PS2 Patcher Setup failed:[/bold red] {err}", True))
        finally:
            try:
                tmp_zip.unlink(missing_ok=True)
            except OSError:
                pass

    # ── CHD conversion ────────────────────────────────────────────────────────

    def convert_to_chd(self, dest_dir: Path, silent: bool = False,
                        cancel: threading.Event | None = None) -> tuple[int, int]:
        """Convert disc images in *dest_dir* to CHD format.

        *cancel* overrides ``self.cancel_flag`` when provided, allowing library
        operations and download auto-CHD to use separate cancellation signals.

        Returns ``(converted, failed)`` counts.
        Delegates to the same logic previously inlined in MyrientTUI._convert_to_chd.
        """
        _cancel = cancel or self.cancel_flag
        if not self.chdman_path:
            found = shutil.which("chdman")
            if found:
                self.chdman_path = found
        chdman   = self.chdman_path or "chdman"
        converted = failed = 0

        conversion_targets: list[Path] = []
        # Collect .cue files first — when a .cue exists, its referenced .bin
        # files must NOT be converted independently (chdman createcd reads the
        # .cue and processes all referenced tracks).  Build a set of .bin paths
        # claimed by .cue sheets so we can skip them.
        cue_claimed_bins: set[Path] = set()
        cue_files: list[Path] = []
        for f in dest_dir.rglob("*.cue"):
            if not f.with_suffix(".chd").exists():
                cue_files.append(f)
                try:
                    with open(f, "r", encoding="utf-8", errors="ignore") as cf:
                        for bin_name in CUE_BIN_REGEX.findall(cf.read()):
                            cue_claimed_bins.add(f.parent / bin_name)
                except OSError:
                    pass
        conversion_targets.extend(cue_files)
        # Now collect remaining source files, skipping .cue (already added)
        # and any .bin that is referenced by a .cue sheet.
        for ext in _CHD_CMD_MAP:
            if ext == ".cue":
                continue
            for f in dest_dir.rglob(f"*{ext}"):
                if f in cue_claimed_bins:
                    continue
                if not f.with_suffix(".chd").exists():
                    conversion_targets.append(f)

        for file_path in conversion_targets:
            if _cancel.is_set():
                return converted, failed

            ext_lower   = file_path.suffix.lower()
            subcommands = _CHD_CMD_MAP.get(ext_lower, ["createcd"])
            chd_output  = file_path.with_suffix(".chd")
            succeeded   = False

            for subcmd in subcommands:
                if _cancel.is_set():
                    return converted, failed
                self._chd_sem.acquire()
                try:
                    proc = subprocess.Popen(
                        [chdman, subcmd,
                         "-i", str(file_path),
                         "-o", str(chd_output),
                         "--numprocessors", str(self.chd_cores)],
                        stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
                        **_LOW_PRIO_POPEN,
                    )
                    self._reg_proc(proc)

                    stderr_chunks: list[bytes] = []
                    _chd_progress_pct: list[float] = [0.0]

                    def _read_stderr(p: subprocess.Popen = proc,
                                     buf: list[bytes] = stderr_chunks,
                                     pct: list[float] = _chd_progress_pct) -> None:
                        try:
                            for chunk in iter(lambda: p.stderr.read(4096), b""):
                                buf.append(chunk)
                                m = _CHD_PCT_RE.search(chunk)
                                if m:
                                    pct[0] = float(m.group(1))
                        except OSError:
                            pass

                    stderr_thread = threading.Thread(target=_read_stderr, daemon=True)
                    stderr_thread.start()

                    deadline = time.monotonic() + _CHD_TIMEOUT
                    while proc.poll() is None:
                        if _cancel.is_set():
                            proc.kill()
                            proc.wait()
                            stderr_thread.join(timeout=2)
                            self._unreg_proc(proc)
                            return converted, failed
                        if time.monotonic() > deadline:
                            proc.kill()
                            proc.wait()
                            stderr_thread.join(timeout=2)
                            self._unreg_proc(proc)
                            raise subprocess.TimeoutExpired(proc.args, _CHD_TIMEOUT)
                        # Report CHD conversion progress
                        if not silent and _chd_progress_pct[0] > 0:
                            self._post(LibraryProgress(
                                "CHD convert",
                                f"{file_path.name} ({_chd_progress_pct[0]:.0f}%)",
                                int(_chd_progress_pct[0]),
                                100,
                            ))
                        time.sleep(0.5)

                    stderr_thread.join(timeout=5)
                    stderr_bytes = b"".join(stderr_chunks)
                    self._unreg_proc(proc)

                    if proc.returncode == 0:
                        succeeded = True
                        break
                    else:
                        if chd_output.exists():
                            try:
                                chd_output.unlink()
                            except OSError:
                                pass
                        if not silent:
                            err_snippet = (stderr_bytes.decode("utf-8", errors="replace")
                                           .strip()[:200])
                            self._post(SystemLog(
                                f"chdman {subcmd} failed for {file_path.name}: {err_snippet}",
                                True
                            ))
                except subprocess.TimeoutExpired:
                    if not silent:
                        self._post(SystemLog(
                            f"chdman timed out converting {file_path.name} — killed.", True
                        ))
                    if chd_output.exists():
                        try:
                            chd_output.unlink()
                        except OSError:
                            pass
                    break
                except Exception as e:
                    self._post(SystemLog(f"chdman error ({file_path.name}): {e}", True))
                    break
                finally:
                    self._chd_sem.release()

            if not succeeded:
                failed += 1
                if not silent:
                    self._post(SystemLog(
                        f"CHD conversion failed: {file_path.name} — "
                        "not a supported disc image format.", True
                    ))
                continue

            converted += 1

            # ── Post-conversion cleanup ──────────────────────────────────────
            # Preserve the original .cue — it is tiny and its byte-exact content
            # (including CRLF line endings and track naming) is what the Redump DAT
            # expects.  chdman extractcd regenerates a .cue with different formatting,
            # so keeping the original is the only way to guarantee a SHA1 match on
            # round-trip.  Only the .bin track files are deleted.
            if ext_lower == ".cue":
                try:
                    with open(file_path, "r", encoding="utf-8", errors="ignore") as cf:
                        bins = CUE_BIN_REGEX.findall(cf.read())
                    with self.chd_lock:
                        for bin_name in bins:
                            bin_path = file_path.parent / bin_name
                            if bin_path.exists():
                                try:
                                    bin_path.unlink()
                                except OSError as ose:
                                    logging.error("CHD cleanup: could not delete %s: %s", bin_path, ose)
                                    self._post(SystemLog(
                                        f"CHD cleanup: could not delete {bin_path.name}: {ose}", True
                                    ))
                except Exception as e:
                    logging.debug("CHD cue sheet cleanup failed: %s", e)
            elif ext_lower == ".gdi":
                gdi_dir = file_path.parent
                for track_file in list(gdi_dir.glob("*.raw")) + list(gdi_dir.glob("*.bin")):
                    try:
                        track_file.unlink()
                    except OSError as ose:
                        logging.error("CHD cleanup: could not delete track %s: %s", track_file, ose)
                        self._post(SystemLog(
                            f"CHD cleanup: could not delete {track_file.name}: {ose}", True
                        ))
                try:
                    file_path.unlink()
                except OSError as ose:
                    logging.error("CHD cleanup: could not delete gdi %s: %s", file_path, ose)
                    self._post(SystemLog(
                        f"CHD cleanup: could not delete {file_path.name}: {ose}", True
                    ))
            else:
                try:
                    file_path.unlink()
                except OSError as ose:
                    logging.error("CHD cleanup: could not delete source %s: %s", file_path, ose)
                    self._post(SystemLog(
                        f"CHD cleanup: could not delete {file_path.name}: {ose}", True
                    ))

        return converted, failed
