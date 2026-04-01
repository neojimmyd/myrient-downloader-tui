"""Download engine: TokenBucket, EngineState, and DownloadWorker.

Extracted from the monolith ``tui_dl.py`` so each concern lives in its own
module.  The public surface is re-exported by ``myrient_tui.__init__``.
"""
from __future__ import annotations

import enum
import hashlib
import logging
import os
import random
import subprocess
import threading
import time
import urllib.parse
import urllib.request
import zipfile as _zf
from collections import deque
from pathlib import Path
from typing import TYPE_CHECKING, Any
from urllib.parse import unquote

from myrient_tui.constants import (
    _DL_CHUNK_BYTES,
    _GAME_EXTS,
    _RETRY_BASE_DELAY,
    _RETRY_MAX_ATTEMPTS,
    _RETRY_MAX_DELAY,
    _SPEED_WINDOW,
    _UI_UPDATE_INTERVAL,
    _UNZIP_TIMEOUT,
    _WGET_ENV,
    WGET_LENGTH_REGEX,
    WGET_PROG_REGEX,
)
from myrient_tui.messages import DownloadProgress, SystemLog
from myrient_tui.types import QueueItem
from myrient_tui.toolchain import Toolchain, _safe_extractall
from myrient_tui.utils import normalize_game_title

if TYPE_CHECKING:
    from .app import MyrientTUI


# ── Global bandwidth limiter ─────────────────────────────────────────────────
class TokenBucket:
    """Thread-safe token bucket for shared bandwidth limiting across workers.

    Tokens represent bytes.  Call ``consume(n)`` before sending/receiving *n*
    bytes — it will sleep just long enough to stay within the configured rate.
    A rate of 0 means unlimited (consume returns immediately).
    """
    __slots__ = ("_rate", "_capacity", "_tokens", "_last", "_lock")

    def __init__(self, rate_bps: int) -> None:
        self._rate     = rate_bps          # bytes per second (0 = unlimited)
        self._capacity = max(rate_bps, 1)  # max burst = 1 second of data
        self._tokens   = float(self._capacity)
        self._last     = time.monotonic()
        self._lock     = threading.Lock()

    @property
    def rate(self) -> int:
        return self._rate

    def consume(self, n: int) -> None:
        if self._rate <= 0:
            return
        with self._lock:
            now = time.monotonic()
            elapsed = now - self._last
            self._last = now
            self._tokens = min(self._capacity, self._tokens + elapsed * self._rate)
            if self._tokens >= n:
                self._tokens -= n
                return
            deficit = n - self._tokens
            self._tokens = 0.0
        # Sleep outside the lock so other threads can consume concurrently
        time.sleep(deficit / self._rate)


# ── Download engine state machine ────────────────────────────────────────────
class EngineState(enum.Enum):
    IDLE     = "idle"
    RUNNING  = "running"
    PAUSING  = "pausing"
    PAUSED   = "paused"


# ─────────────────────────────────────────────────────────────────────────────
# Download worker (A3) — encapsulates per-download state so MyrientTUI only
# needs a thin one-liner to kick off a download.
# ─────────────────────────────────────────────────────────────────────────────

class DownloadWorker:
    """Encapsulates all state and logic for a single download task.

    Created by ``MyrientTUI._download_worker`` with the owning app instance
    and the ``QueueItem`` to process.  Call :meth:`run` to execute the full
    download pipeline: skip-check -> retry-loop -> extract -> CHD.
    """

    def __init__(self, app: "MyrientTUI", item: QueueItem) -> None:
        self.app = app
        self.item = item
        self.dest_dir = Path(item["dest_path"])
        _url_path = urllib.parse.urlparse(item["game_url"]).path
        self.target_file = self.dest_dir / unquote(_url_path.split("/")[-1])
        self.item_name = item["name"]

    # ── Speed computation ────────────────────────────────────────────────

    @staticmethod
    def _compute_speed(
        cur_bytes: int,
        size_bytes: int,
        speed_samples: "deque[tuple[float, int]]",
    ) -> tuple[float, float]:
        """Return ``(speed_bps, eta_secs)`` from a rolling sample window.

        Appends the current snapshot to *speed_samples*, evicts entries older
        than ``_SPEED_WINDOW``, then computes an instantaneous speed and ETA.
        Returns ``(0.0, -1.0)`` when there are fewer than two samples.
        """
        now = time.monotonic()
        speed_samples.append((now, cur_bytes))
        cutoff = now - _SPEED_WINDOW
        while speed_samples and speed_samples[0][0] < cutoff:
            speed_samples.popleft()
        if len(speed_samples) < 2:
            return 0.0, -1.0
        dt = speed_samples[-1][0] - speed_samples[0][0]
        db = speed_samples[-1][1] - speed_samples[0][1]
        if dt <= 0:
            return 0.0, -1.0
        spd = db / dt
        remaining = size_bytes - cur_bytes
        eta = (remaining / spd) if spd > 0 and remaining > 0 else -1.0
        return spd, eta

    # ── Phase 1a: wget download ──────────────────────────────────────────

    def _run_wget(
        self,
        item: QueueItem,
        target_file: Path,
        item_name: str,
        size_bytes: int,
        speed_limit_bps: int,
        speed_samples: "deque[tuple[float, int]]",
    ) -> tuple[bool, int]:
        """Run wget for one download attempt.

        Returns ``(True, updated_size_bytes)`` on success (rc=0).
        Returns ``(False, size_bytes)`` on any failure so the caller can fall
        through to the urllib fallback on the same attempt.

        Side effects: posts ``DownloadProgress`` messages; terminates process
        and returns early on cancel.
        """
        cmd = [
            "wget", "--progress=dot:mega", "-c", "--timeout=20", "--tries=1",
            "--user-agent=Mozilla/5.0 (Windows NT 10.0; Win64; x64)",
            "-e", "robots=off", "-O", str(target_file), item["game_url"],
        ]
        # A8: Use shared bucket rate, divided across concurrent workers
        bucket = getattr(self.app, "_bandwidth_bucket", None)
        effective_rate = bucket.rate if bucket and bucket.rate > 0 else speed_limit_bps
        if effective_rate > 0:
            # Divide evenly across max threads so aggregate ≈ cap
            q_settings = self.app.state.get_queue_settings(self.app.state.active_queue_name)
            n_threads = q_settings.get("max_concurrent",
                                       self.app.state.settings.get("max_concurrent", 4))
            per_thread = max(1, effective_rate // n_threads)
            cmd.insert(1, f"--limit-rate={per_thread}")
        proc = subprocess.Popen(
            cmd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
            text=True, env=_WGET_ENV,
        )
        self.app._register_process(proc)

        stderr_log    = deque(maxlen=5)
        last_ui_update = 0.0

        try:
            for line in proc.stderr:
                if self.app.cancel_flag.is_set():
                    proc.terminate()
                    return False, size_bytes

                stderr_log.append(line.strip())

                len_match = WGET_LENGTH_REGEX.search(line)
                if len_match:
                    reported = int(len_match.group(1))
                    if reported > 0:
                        size_bytes = reported

                match = WGET_PROG_REGEX.search(line)
                if match:
                    current_time = time.monotonic()
                    if current_time - last_ui_update > _UI_UPDATE_INTERVAL:
                        pct = float(match.group(1))
                        current_bytes = int((pct / 100.0) * size_bytes)
                        spd, eta = self._compute_speed(current_bytes, size_bytes, speed_samples)
                        self.app.post_message(
                            DownloadProgress(item["id"], item_name, current_bytes,
                                             size_bytes, "Downloading", spd, eta)
                        )
                        last_ui_update = current_time
        finally:
            try:
                proc.wait(timeout=10)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait()
            self.app._unregister_process(proc)

        if self.app.cancel_flag.is_set():
            return False, size_bytes

        if proc.returncode == 0:
            return True, size_bytes

        error_msg = " | ".join(stderr_log)
        self.app.post_message(SystemLog(
            f"wget failed for {item_name}. "
            f"Falling back to urllib… ({error_msg})", True
        ))
        return False, size_bytes

    # ── Phase 1b: urllib fallback ────────────────────────────────────────

    def _run_urllib_fallback(
        self,
        item: QueueItem,
        target_file: Path,
        item_name: str,
        size_bytes: int,
        speed_limit_bps: int,
        speed_samples: "deque[tuple[float, int]]",
    ) -> tuple[bool, int]:
        """Stream the download via urllib with optional token-bucket throttling.

        Supports HTTP range-resume if *target_file* already exists and is
        smaller than *size_bytes*.

        Returns ``(True, updated_size_bytes)`` on success.
        Returns ``(False, size_bytes)`` and lets the caller handle the exception
        (i.e. the retry-loop ``last_error`` is set by the caller's try/except).
        """
        req = urllib.request.Request(
            item["game_url"],
            headers={"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64)"},
        )

        if target_file.exists():
            existing_size = target_file.stat().st_size
            # B5: When size is unknown (size_bytes <= 1), always attempt resume
            # by sending the Range header regardless of existing_size comparison.
            # Let the server decide whether to honour the range (206) or restart
            # (200).
            if existing_size > 0 and (size_bytes <= 1 or existing_size < size_bytes):
                req.add_header("Range", f"bytes={existing_size}-")
                open_mode      = "ab"
                downloaded     = existing_size
                _resume_offset = existing_size   # used to verify 206 below
            else:
                open_mode      = "wb"
                downloaded     = 0
                _resume_offset = 0
        else:
            open_mode      = "wb"
            downloaded     = 0
            _resume_offset = 0

        with urllib.request.urlopen(req, timeout=30) as response:
            # If we sent a Range header but the server returned 200 (not 206),
            # it is sending the full file from byte 0.  Opening in "ab" would
            # prepend the already-downloaded bytes, corrupting the file.
            # Detect this and restart the write from scratch.
            actual_status = response.status
            if _resume_offset > 0 and actual_status != 206:
                open_mode  = "wb"
                downloaded = 0
            cl = response.headers.get("Content-Length")
            if cl and cl.isdigit() and int(cl) > 0:
                size_bytes = downloaded + int(cl)
            with open(target_file, open_mode) as file:
                last_ui_update = 0.0
                while True:
                    if self.app.cancel_flag.is_set():
                        return False, size_bytes
                    chunk = response.read(_DL_CHUNK_BYTES)
                    if not chunk:
                        break
                    file.write(chunk)
                    downloaded += len(chunk)

                    # ── Shared bandwidth throttle ─────────────────────────────
                    bucket = getattr(self.app, "_bandwidth_bucket", None)
                    if bucket is not None:
                        bucket.consume(len(chunk))

                    current_time = time.monotonic()
                    if current_time - last_ui_update > _UI_UPDATE_INTERVAL:
                        spd, eta = self._compute_speed(
                            downloaded, max(size_bytes, downloaded), speed_samples
                        )
                        self.app.post_message(
                            DownloadProgress(
                                item["id"], item_name, downloaded,
                                max(size_bytes, downloaded), "Downloading", spd, eta,
                            )
                        )
                        last_ui_update = current_time

        return True, size_bytes

    # ── Phase 3b: post-download DAT verification ───────────────────

    def _run_post_verify(
        self,
        item: QueueItem,
        item_name: str,
        dest_dir: Path,
        size_bytes: int,
    ) -> None:
        """F2: Verify extracted files against the console's DAT after download.

        Uses the app's DAT infrastructure to hash files in *dest_dir* and
        check them against the Redump/No-Intro DAT.  Updates library status
        to 'validated' or 'corrupted' based on the result.  Failures are
        logged but never raise — verification is best-effort and must not
        block the download pipeline.
        """
        from .constants import _DAT_AUDITABLE_EXTS, _HASH_CHUNK_BYTES

        console_name = (
            item["name"].split(" / ")[0].strip()
            if " / " in item["name"]
            else ""
        )
        if not console_name:
            return

        self.app.post_message(DownloadProgress(
            item["id"], item_name, size_bytes, size_bytes, "Verifying"
        ))

        # Lightweight adapter — DAT helpers expect a LibraryOperation-like
        # object but only call .log() and .progress().
        app = self.app

        class _Ctx:
            cancelled = False
            def log(self, msg, error=False):
                app.post_message(SystemLog(msg, error))
            def progress(self, label, detail, current, total):
                pass  # suppress noisy progress for single-game verify

        ctx = _Ctx()

        try:
            dat_ttl = app.state.settings.get("dat_cache_ttl_hours", 168) * 3600.0
            dat_index = app._dat_fetch_index(ctx)
            if not dat_index:
                return
            dat_path = app._dat_resolve_dat_file(
                console_name, dat_index, dat_ttl, ctx,
            )
            if not dat_path:
                return
            parsed = type(app)._dat_parse_xml(dat_path)
            if not parsed:
                return
            dat_by_sha1, ambiguous_sha1s, _ = parsed

            all_ok = True
            checked = 0
            for f in dest_dir.iterdir():
                if not f.is_file() or f.suffix.lower() not in _DAT_AUDITABLE_EXTS:
                    continue
                sha1 = hashlib.sha1(usedforsecurity=False)
                with open(f, "rb") as fh:
                    while chunk := fh.read(_HASH_CHUNK_BYTES):
                        sha1.update(chunk)
                file_hash = sha1.hexdigest().lower()
                checked += 1
                if file_hash in ambiguous_sha1s:
                    continue
                if file_hash not in dat_by_sha1:
                    all_ok = False
                    app.post_message(SystemLog(
                        f"Verify [{item_name}]: {f.name} not found in DAT"
                    ))

            if checked == 0:
                return

            if all_ok:
                app._lib_status.set_status(dest_dir, "validated")
                app.post_message(SystemLog(
                    f"Verify [{item_name}]: All {checked} file(s) match DAT"
                ))
            else:
                app._lib_status.set_status(dest_dir, "corrupted")
                app.post_message(SystemLog(
                    f"Verify [{item_name}]: Some files do not match DAT", True
                ))
        except Exception as exc:
            logging.debug("Post-download verify failed for %s: %s", item_name, exc)
            app.post_message(SystemLog(
                f"Post-download verify skipped for {item_name}: {exc}"
            ))

    # ── Phase 3: extraction ──────────────────────────────────────────────

    def _run_extraction(
        self,
        target_file: Path,
        dest_dir: Path,
        item_name: str,
    ) -> bool:
        """Extract *target_file* (ZIP) into *dest_dir*.

        Tries the ``unzip`` system binary first for speed; falls back to
        Python's ``zipfile`` module on timeout or non-zero exit.

        Updates ``_lib_status`` to ``"validated"`` on success or
        ``"corrupted"`` on failure.  Posts ``SystemLog`` on errors.

        Returns ``True`` on success, raises ``Exception`` on failure.
        """
        if not (target_file.exists() and target_file.suffix.lower() == ".zip"):
            # Non-zip payload (e.g. bare ISO/CHD): mark validated and return
            if target_file.exists():
                self.app._lib_status.set_status(dest_dir, "validated")
            return True

        extracted_ok  = False
        unzip_err_msg = ""

        if self.app._unzip_available:
            unzip_proc = subprocess.Popen(
                ["unzip", "-q", "-o", str(target_file), "-d", str(dest_dir)],
                stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True,
            )
            self.app._register_process(unzip_proc)
            try:
                _, unzip_err_msg = unzip_proc.communicate(timeout=_UNZIP_TIMEOUT)
                if unzip_proc.returncode == 0:
                    extracted_ok = True
                else:
                    self.app.post_message(SystemLog(
                        f"unzip failed for {item_name} (rc={unzip_proc.returncode}), "
                        "falling back to Python zipfile…"
                    ))
            except subprocess.TimeoutExpired:
                unzip_proc.kill()
                unzip_proc.wait()
                self.app.post_message(SystemLog(
                    f"unzip timed out for {item_name}, falling back to Python zipfile…"
                ))
            finally:
                self.app._unregister_process(unzip_proc)

        if not extracted_ok:
            try:
                with _zf.ZipFile(target_file, "r") as zf:
                    _safe_extractall(zf, dest_dir)
                extracted_ok = True
            except (_zf.BadZipFile, OSError, ValueError) as zf_err:
                unzip_err_msg = str(zf_err)

        if extracted_ok:
            try:
                target_file.unlink()
            except OSError as ose:
                self.app.post_message(SystemLog(
                    f"Extraction succeeded but could not delete zip "
                    f"{target_file.name}: {ose}", True
                ))
            self.app._lib_status.set_status(dest_dir, "validated")
            return True
        else:
            self.app._lib_status.set_status(dest_dir, "corrupted")
            raise Exception(f"Extraction failed: {unzip_err_msg}")

    # ── Phase 4: auto-CHD conversion ─────────────────────────────────────

    def _run_chd_auto(
        self,
        item: QueueItem,
        item_name: str,
        dest_dir: Path,
        size_bytes: int,
    ) -> None:
        """Trigger auto-CHD conversion if enabled in settings.

        No-ops when ``auto_convert_chd`` is False or chdman is not available.
        Posts a ``DownloadProgress`` message with action "Converting CHD" so
        the progress bar shows the conversion phase while chdman runs.
        """
        if not self.app.state.settings.get("auto_convert_chd", False):
            return
        # Resolve locally rather than writing back to the shared Toolchain attribute —
        # multiple concurrent workers calling this method would race on that write.
        chdman = self.app.toolchain.chdman_path or Toolchain.find_chdman()
        if chdman:
            self.app.post_message(
                DownloadProgress(item["id"], item_name, size_bytes, size_bytes, "Converting CHD")
            )
            self.app._convert_to_chd(dest_dir, silent=True)
        else:
            self.app.post_message(SystemLog(
                f"Auto-CHD skipped for {item_name}: chdman not found. "
                "Run 'Setup chdman' in Settings."
            ))

    # ── Main entry point ─────────────────────────────────────────────────

    def run(self) -> dict[str, Any]:
        """Orchestrate a single download: skip-check -> retry-loop -> extract -> CHD.

        Each network phase is delegated to a focused sub-method:
          * ``_run_wget``           -- wget subprocess with progress parsing
          * ``_run_urllib_fallback`` -- urllib streaming with token-bucket throttle
          * ``_run_extraction``     -- ZIP extraction (unzip binary or zipfile fallback)
          * ``_run_chd_auto``       -- optional post-download CHD conversion

        Returns ``{"success": True}`` on completion, ``{"success": False}`` on
        unrecoverable error, or ``{"success": False, "cancelled": True}`` when
        the cancel flag fires.
        """
        # Resolve the app class once — needed for static helper methods
        # (_parse_size_bytes, _format_size) without importing MyrientTUI at
        # module level (which would create a circular import).
        AppClass = type(self.app)

        item = self.item
        dest_dir = self.dest_dir
        target_file = self.target_file
        item_name = self.item_name

        if self.app.cancel_flag.is_set():
            return {"success": False, "cancelled": True}

        try:
            _is_resume = target_file.exists() and target_file.stat().st_size > 0
        except (FileNotFoundError, OSError):
            _is_resume = False

        try:
            dest_dir.mkdir(parents=True, exist_ok=True)

            # ── Fast-skip if the game is already in good shape ───────────────
            if any(dest_dir.rglob("*.chd")) or target_file.with_suffix(".chd").exists():
                self.app.post_message(SystemLog(f"Skipped (CHD exists): {item_name}"))
                return {"success": True}
            if self.app._lib_status.get(dest_dir) == "validated":
                # Verify game files still exist — a stale "validated" entry
                # persists after files are deleted or the directory is recreated
                # empty (common with multi-disc games where individual discs are
                # re-queued after partial deletion).
                try:
                    has_game_files = any(
                        f.suffix.lower() in _GAME_EXTS
                        for f in dest_dir.iterdir()
                        if f.is_file()
                    )
                except (PermissionError, OSError):
                    has_game_files = False
                if has_game_files:
                    self.app.post_message(SystemLog(f"Skipped (Already validated): {item_name}"))
                    return {"success": True}
                # Stale validated status — game files are missing; clear and re-download.
                self.app._lib_status.remove(dest_dir)
                self.app.post_message(SystemLog(
                    f"Cleared stale validation for {item_name} — re-downloading."
                ))

            # ── Stale-zip cleanup for corrupted games ────────────────────────
            if self.app._lib_status.get(dest_dir) == "corrupted":
                for stale_zip in dest_dir.glob("*.zip"):
                    try:
                        stale_zip.unlink()
                        self.app.post_message(SystemLog(
                            f"Removed stale zip before retry: {stale_zip.name}"
                        ))
                    except OSError as ose:
                        self.app.post_message(SystemLog(
                            f"Could not remove stale zip {stale_zip.name}: {ose} "
                            "(file may be locked — retry may fail)", True
                        ))

            size_bytes = max(AppClass._parse_size_bytes(item["size_str"]), 1)

            # ── Resolve per-queue speed limit (convert MB/s → B/s) ───────────
            q_settings      = self.app.state.get_queue_settings(self.app.state.active_queue_name)
            speed_limit_bps = (q_settings.get("speed_limit_mbps", 0) or
                               self.app.state.settings.get("speed_limit_mbps", 0))
            speed_limit_bps = int(speed_limit_bps * 1024 * 1024)

            speed_samples: deque[tuple[float, int]] = deque()

            # ── Retry loop with exponential backoff + jitter ─────────────────
            attempt          = 0
            download_success = False
            last_error: Exception | None = None

            while attempt < _RETRY_MAX_ATTEMPTS:
                if self.app.cancel_flag.is_set():
                    return {"success": False, "cancelled": True}

                if attempt > 0:
                    delay = min(
                        _RETRY_BASE_DELAY * (2 ** (attempt - 1)) + random.uniform(0, 1),
                        _RETRY_MAX_DELAY,
                    )
                    self.app.post_message(SystemLog(
                        f"Retry {attempt}/{_RETRY_MAX_ATTEMPTS - 1} for {item_name} "
                        f"(backoff {delay:.1f}s)…"
                    ))
                    deadline = time.monotonic() + delay
                    while time.monotonic() < deadline:
                        if self.app.cancel_flag.is_set():
                            return {"success": False, "cancelled": True}
                        time.sleep(0.2)

                attempt += 1
                speed_samples.clear()

                if _is_resume and attempt == 1 and target_file.exists():
                    existing_bytes = target_file.stat().st_size
                    if existing_bytes > 0:
                        self.app.post_message(SystemLog(
                            f"Resuming {item_name} from {AppClass._format_size(existing_bytes)}"
                        ))
                        self.app.post_message(DownloadProgress(
                            item["id"], item_name, existing_bytes, size_bytes, "Resuming"
                        ))

                # ── Phase 1: wget ────────────────────────────────────────────
                # Skip entirely when wget is not installed — avoids a failing
                # Popen call (FileNotFoundError) on every retry attempt.
                if self.app._wget_available:
                    ok, size_bytes = self._run_wget(
                        item, target_file, item_name, size_bytes,
                        speed_limit_bps, speed_samples,
                    )
                    if self.app.cancel_flag.is_set():
                        return {"success": False, "cancelled": True}
                    if ok:
                        download_success = True
                        break
                # ── Phase 2: urllib fallback ─────────────────────────────────
                try:
                    ok, size_bytes = self._run_urllib_fallback(
                        item, target_file, item_name,
                        size_bytes, speed_limit_bps, speed_samples,
                    )
                    if self.app.cancel_flag.is_set():
                        return {"success": False, "cancelled": True}
                    if ok:
                        download_success = True
                        break
                except Exception as err:
                    last_error = err
                    # Loop continues — next iteration retries with backoff

            if not download_success:
                raise Exception(
                    f"All {_RETRY_MAX_ATTEMPTS} attempts failed: {last_error}"
                ) from last_error

            if self.app.cancel_flag.is_set():
                return {"success": False, "cancelled": True}

            # ── Phase 3: extraction ──────────────────────────────────────────
            self.app.post_message(
                DownloadProgress(item["id"], item_name, size_bytes, size_bytes, "Extracting ZIP")
            )
            self._run_extraction(target_file, dest_dir, item_name)

            if self.app.cancel_flag.is_set():
                return {"success": False, "cancelled": True}

            # ── Phase 3b: optional post-download DAT verification (F2) ───────
            if self.app.state.settings.get("verify_after_download", False):
                self._run_post_verify(item, item_name, dest_dir, size_bytes)

            if self.app.cancel_flag.is_set():
                return {"success": False, "cancelled": True}

            # ── Phase 4: optional auto-CHD conversion ────────────────────────
            self._run_chd_auto(item, item_name, dest_dir, size_bytes)

            # B1: Record in download history with clean display name
            console_name = item["name"].split(" / ")[0].strip() if " / " in item["name"] else ""
            game_part = item_name.split(" / ", 1)[-1] if " / " in item_name else item_name
            self.app.state.record_download(
                normalize_game_title(game_part),
                console_name,
                item["size_str"],
            )
            return {"success": True}

        except Exception as err:
            logging.exception("Worker error for %s", item_name)
            self.app.post_message(SystemLog(f"Worker Error {item_name}: {err}", True))
            return {"success": False}
