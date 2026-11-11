#!/usr/bin/env python3
"""Trough-gated typecheck of the §C14 module (lake env lean, no olean write).

Same reaper arithmetic as build_c14.py: the free_low arm fires below 3.0GB, and a
lean typecheck of this module peaks ~3GB, so start only when free clears the sum.
"""
import os
import re
import signal
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

LANE = Path("/Volumes/Substrate-1/bigo/kapila-row-lane")
FILE = sys.argv[1] if len(sys.argv) > 1 else "SubsetSumL25/Row/KapilaCmpSegStrideProg.lean"
RECEIPT = LANE / "receipts" / ("check-" + datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ"))

MIN_FREE_GB = 3.0
PEAK_RSS_GB = 1.5
NEED = MIN_FREE_GB + PEAK_RSS_GB
SWAP_UNUSED_FLOOR = 0.5
BUDGET = int(os.environ.get("KAPILA_BUDGET", "5400"))

signal.signal(signal.SIGTERM, signal.SIG_IGN)
signal.signal(signal.SIGHUP, signal.SIG_IGN)
RECEIPT.mkdir(parents=True, exist_ok=True)
log = open(RECEIPT / "run.log", "w")


def say(m: str) -> None:
    log.write(f"{datetime.now().strftime('%H:%M:%S')} {m}\n")
    log.flush()


def free_gb() -> float:
    vm = subprocess.run(["vm_stat"], capture_output=True, text=True).stdout
    for line in vm.splitlines():
        m = re.match(r"Pages free:\s+(\d+)\.", line)
        if m:
            return int(m.group(1)) * 4096 / 1e9
    return 0.0


def swap() -> tuple[float, float]:
    o = subprocess.run(["sysctl", "-n", "vm.swapusage"], capture_output=True, text=True).stdout
    return (float(re.search(r"used = ([\d.]+)M", o).group(1)) / 1024,
            float(re.search(r"total = ([\d.]+)M", o).group(1)) / 1024)


def swapouts() -> int:
    """The swap_growth arm's signal: kernel page-out count (R2125608674)."""
    vm = subprocess.run(["vm_stat"], capture_output=True, text=True).stdout
    for line in vm.splitlines():
        if line.startswith("Swapouts:"):
            return int(line.split()[-1].strip("."))
    return -1


def ok() -> bool:
    """Trough = free headroom AND swap not running away.

    MEASURED 21:37: bound only on free_gb and the checker was killed by the OTHER
    arm -- swap_growth (16.5 -> 20.32GB in one pass) at free=50.76GB.  A high free
    page count can itself be the ARTIFACT of the kernel pushing everything to swap,
    so free alone doesn't mean the box is calm.  Require the swapouts delta flat too.
    """
    f = free_gb()
    u, t = swap()
    s0 = swapouts()
    time.sleep(12)
    s1 = swapouts()
    delta = s1 - s0
    good = f >= NEED and (t - u) >= SWAP_UNUSED_FLOOR and delta == 0
    say(f"  free={f:.2f}GB (need {NEED:.2f}) swap_unused={t-u:.2f} swapouts_d12s={delta} good={good}")
    return good


say(f"gate: need free >= {NEED:.2f}GB, swap_unused >= {SWAP_UNUSED_FLOOR}, swapouts flat; typecheck {FILE}")
t_start = time.time()
ATTEMPTS = int(os.environ.get("KAPILA_ATTEMPTS", "12"))
env = dict(os.environ)
env["PATH"] = "/opt/homebrew/bin:" + env.get("PATH", "")
import fcntl  # noqa: E402

LOCKF = "/Volumes/Substrate-1/bigo/.build.lock"

for attempt in range(1, ATTEMPTS + 1):
    # ---- gate: a confirmed calm window
    cand = None
    while time.time() - t_start < BUDGET:
        if ok():
            if cand is None:
                cand = time.time()
            elif time.time() - cand >= 10:
                say(f"attempt {attempt}: TROUGH CONFIRMED")
                break
        else:
            cand = None
        time.sleep(10)
    else:
        (RECEIPT / "STATUS").write_text("ABORT budget exhausted waiting\n")
        sys.exit(2)

    # ---- fleet lock, then typecheck
    lf = open(LOCKF, "w")
    t_lk = time.time()
    held = False
    while time.time() - t_lk < int(os.environ.get("KAPILA_LOCK_WAIT", "900")):
        try:
            fcntl.flock(lf, fcntl.LOCK_EX | fcntl.LOCK_NB)
            held = True
            break
        except BlockingIOError:
            time.sleep(2)
    say(f"lock: {'acquired' if held else 'UNLOCKED (deviation)'} after {time.time()-t_lk:.0f}s")
    say(f"attempt {attempt}: TYPECHECK {FILE}")
    t1 = time.time()
    try:
        r = subprocess.run(["lake", "env", "lean", FILE], cwd=str(LANE), capture_output=True,
                           text=True, env=env, start_new_session=True)
    finally:
        try:
            fcntl.flock(lf, fcntl.LOCK_UN)
        except OSError:
            pass
        lf.close()
    (RECEIPT / f"check.{attempt}.log").write_text(r.stdout + r.stderr)
    say(f"attempt {attempt}: exit={r.returncode} in {time.time()-t1:.0f}s")

    if r.returncode == 0:
        (RECEIPT / "STATUS").write_text(f"OK typecheck clean (attempt {attempt})\n")
        sys.exit(0)
    if r.returncode > 0:
        # Lean REPORTED errors -- a real proof failure, not a reap. Do not retry.
        (RECEIPT / "STATUS").write_text(f"FAIL compile exit={r.returncode} (attempt {attempt})\n")
        sys.exit(1)
    say(f"attempt {attempt}: killed by signal {-r.returncode} -- backoff and retry")
    time.sleep(30)

(RECEIPT / "STATUS").write_text("ABORT attempts exhausted\n")
sys.exit(2)
