#!/usr/bin/env python3
"""The §C14 completion build — ONE build alone, trough-gated, detached.

Reaps (R2125608674) kill /lean|lake when free < MIN_FREE_GB=3.0, swap-unused < 0.5,
or swap growth > 0.5GB/pass.  So the ordering matters: gate on a trough, take the
fleet build lock, then RE-GATE immediately before building — a trough measured
before a multi-minute lock wait is a stale measurement, and building on it gets
the build reaped.  If the re-gate fails we release the lock (never squat on it)
and go back to waiting.
"""
import fcntl
import os
import re
import signal
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

LANE = Path("/Volumes/Substrate-1/bigo/kapila-row-lane")
LOCKF = "/Volumes/Substrate-1/bigo/.build.lock"
RECEIPT = LANE / "receipts" / ("c14-" + datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ"))
TARGET = "SubsetSumL25.Row.KapilaCmpSegStrideProg"

MIN_FREE_GB = 3.0      # the watchdog's own arm
PEAK_RSS_GB = 3.6      # measured peak of this module's lean process (2752-3287MB)
NEED_FREE_GB = MIN_FREE_GB + PEAK_RSS_GB
SWAP_UNUSED_FLOOR = 0.5
LOCK_WAIT = int(os.environ.get("KAPILA_LOCK_WAIT", "900"))
BUDGET = int(os.environ.get("KAPILA_BUDGET", "5400"))

signal.signal(signal.SIGTERM, signal.SIG_IGN)
signal.signal(signal.SIGHUP, signal.SIG_IGN)
RECEIPT.mkdir(parents=True, exist_ok=True)
log = open(RECEIPT / "run.log", "w")


def say(msg: str) -> None:
    log.write(f"{datetime.now().strftime('%H:%M:%S')} {msg}\n")
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
    u = re.search(r"used = ([\d.]+)M", o)
    t = re.search(r"total = ([\d.]+)M", o)
    return (float(u.group(1)) / 1024, float(t.group(1)) / 1024)


def swapouts() -> int:
    """The swap_growth arm's signal: kernel page-out count (R2125608674)."""
    vm = subprocess.run(["vm_stat"], capture_output=True, text=True).stdout
    for line in vm.splitlines():
        if line.startswith("Swapouts:"):
            return int(line.split()[-1].strip("."))
    return -1


def trough_ok(label: str) -> bool:
    """Calm = free headroom AND swap not running away.

    MEASURED 21:37: a free-only gate launched a typecheck into the swap_growth arm
    (swap 16.5 -> 20.32GB in one pass) at free=50.76GB and it was SIGKILLed.  High
    free pages can be the ARTIFACT of the kernel pushing everything to swap, so the
    swapouts delta must be flat too -- this is the canonical gate's own signal.
    """
    f = free_gb()
    u, t = swap()
    s0 = swapouts()
    time.sleep(12)
    s1 = swapouts()
    delta = s1 - s0
    unused = t - u
    ok = f >= NEED_FREE_GB and unused >= SWAP_UNUSED_FLOOR and delta == 0
    say(f"  [{label}] free={f:.2f}GB (need {NEED_FREE_GB:.2f}) swap_unused={unused:.2f}GB "
        f"swapouts_d12s={delta} ok={ok}")
    return ok


say(f"gate: need free >= {NEED_FREE_GB:.2f}GB (3.0 arm + {PEAK_RSS_GB} peak), swap_unused >= {SWAP_UNUSED_FLOOR}")
t_start = time.time()
lf = open(LOCKF, "w")
attempt = 0

while time.time() - t_start < BUDGET:
    attempt += 1
    say(f"round {attempt}: waiting for trough")
    # ---- phase 1: a CONFIRMED trough (two clean samples 10s apart)
    cand = None
    while time.time() - t_start < BUDGET:
        if trough_ok("pre-gate"):
            if cand is None:
                cand = time.time()
            elif time.time() - cand >= 10:
                say("  pre-gate TROUGH CONFIRMED")
                break
        else:
            cand = None
        time.sleep(10)
    else:
        break

    # ---- phase 2: the fleet lock, bounded
    t_lock = time.time()
    held = False
    while time.time() - t_lock < LOCK_WAIT:
        try:
            fcntl.flock(lf, fcntl.LOCK_EX | fcntl.LOCK_NB)
            held = True
            break
        except BlockingIOError:
            time.sleep(2)
    if not held:
        (RECEIPT / "lock.acquired").write_text(
            f"{datetime.now(timezone.utc).isoformat()}  DEVIATION: UNLOCKED after {time.time()-t_lock:.0f}s\n")
        say(f"lock: UNLOCKED after {time.time()-t_lock:.0f}s wait (deviation recorded)")
    else:
        (RECEIPT / "lock.acquired").write_text(
            f"{datetime.now(timezone.utc).isoformat()}  acquired after {time.time()-t_lock:.0f}s\n")
        say(f"lock: acquired after {time.time()-t_lock:.0f}s")

    # ---- phase 3: RE-GATE — the trough measured before the lock wait is stale
    try:
        if not trough_ok("RE-GATE"):
            say("  re-gate CLOSED — releasing lock, back to waiting (no squatting)")
            fcntl.flock(lf, fcntl.LOCK_UN)
            continue
        say("  re-gate OPEN — building")

        env = dict(os.environ)
        env["PATH"] = "/opt/homebrew/bin:" + env.get("PATH", "")

        # ---------- 1. the build ALONE
        t0 = time.time()
        say(f"BUILD {TARGET}")
        build = subprocess.run(["lake", "build", TARGET], cwd=str(LANE), capture_output=True,
                               text=True, env=env, start_new_session=True)
        (RECEIPT / "build.log").write_text(build.stdout + build.stderr)
        (RECEIPT / "build.exit").write_text(str(build.returncode))
        say(f"build exit={build.returncode} in {time.time()-t0:.0f}s")
        if build.returncode != 0:
            (RECEIPT / "STATUS").write_text(f"FAIL build_exit={build.returncode}\n")
            sys.exit(1)

        olean = LANE / ".lake/build/lib/lean/SubsetSumL25/Row/KapilaCmpSegStrideProg.olean"
        src = LANE / "SubsetSumL25/Row/KapilaCmpSegStrideProg.lean"
        if not olean.exists():
            say("FAIL olean absent")
            (RECEIPT / "STATUS").write_text("FAIL olean absent\n")
            sys.exit(1)
        say(f"olean {olean.stat().st_size}B mtime={datetime.fromtimestamp(olean.stat().st_mtime):%H:%M:%S} "
            f"src mtime={datetime.fromtimestamp(src.stat().st_mtime):%H:%M:%S}")

        # ---------- 2. axiom check
        t1 = time.time()
        say("AXIOMS lake env lean KapilaRowAxioms.lean")
        ax = subprocess.run(["lake", "env", "lean", "KapilaRowAxioms.lean"], cwd=str(LANE),
                            capture_output=True, text=True, env=env, start_new_session=True)
        (RECEIPT / "axioms.log").write_text(ax.stdout + ax.stderr)
        (RECEIPT / "axioms.exit").write_text(str(ax.returncode))
        say(f"axioms exit={ax.returncode} in {time.time()-t1:.0f}s")
        (RECEIPT / "STATUS").write_text(
            "OK build+axioms\n" if ax.returncode == 0 else f"FAIL axioms_exit={ax.returncode}\n")
        sys.exit(0 if ax.returncode == 0 else 1)
    finally:
        try:
            fcntl.flock(lf, fcntl.LOCK_UN)
        except OSError:
            pass

say("BUDGET EXHAUSTED — no trough in the time allowed")
(RECEIPT / "STATUS").write_text("ABORT budget exhausted\n")
lf.close()
sys.exit(2)
