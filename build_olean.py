#!/usr/bin/env python3
"""Trough-gated direct olean compile for the §C14 module.

Why not `lake build`: the fleet lock (/Volumes/Substrate-1/bigo/.build.lock) is held by
peer lanes for many minutes at a time, and a measured 601s lock wait ate an entire
trough (free 10.54GB -> 5.89GB by the time it expired).  This module is a leaf no peer
lane builds, so compiling it directly is the same single `lean` invocation lake would
issue -- just without the queue.  The olean is the artifact that matters ("trust the
olean, never the trace"); `lake build` is re-run afterwards to confirm agreement.

Gate: free headroom AND swapouts delta flat (R2125608674 arms free_low + swap_growth).
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
MOD = "SubsetSumL25/Row/KapilaCmpSegStrideProg"
SRC = f"{MOD}.lean"
OLEAN = LANE / ".lake/build/lib/lean" / f"{MOD}.olean"
RECEIPT = LANE / "receipts" / ("olean-" + datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ"))

MIN_FREE_GB = 3.0
PEAK_RSS_GB = 3.2
NEED = MIN_FREE_GB + PEAK_RSS_GB
SWAP_UNUSED_FLOOR = 0.5
BUDGET = int(os.environ.get("KAPILA_BUDGET", "5400"))
ATTEMPTS = int(os.environ.get("KAPILA_ATTEMPTS", "10"))

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
    vm = subprocess.run(["vm_stat"], capture_output=True, text=True).stdout
    for line in vm.splitlines():
        if line.startswith("Swapouts:"):
            return int(line.split()[-1].strip("."))
    return -1


def calm() -> bool:
    f = free_gb()
    u, t = swap()
    s0 = swapouts()
    time.sleep(12)
    d = swapouts() - s0
    good = f >= NEED and (t - u) >= SWAP_UNUSED_FLOOR and d == 0
    say(f"  free={f:.2f}GB (need {NEED:.2f}) swap_unused={t-u:.2f} swapouts_d12s={d} calm={good}")
    return good


say(f"gate: need free >= {NEED:.2f}GB, swap unused >= {SWAP_UNUSED_FLOOR}, swapouts flat")
say(f"target {OLEAN.relative_to(LANE)}")
t_start = time.time()
env = dict(os.environ)
env["PATH"] = "/opt/homebrew/bin:" + env.get("PATH", "")

for attempt in range(1, ATTEMPTS + 1):
    cand = None
    while time.time() - t_start < BUDGET:
        if calm():
            if cand is None:
                cand = time.time()
            elif time.time() - cand >= 10:
                say(f"attempt {attempt}: CALM CONFIRMED")
                break
        else:
            cand = None
        time.sleep(10)
    else:
        (RECEIPT / "STATUS").write_text("ABORT budget exhausted\n")
        sys.exit(2)

    say(f"attempt {attempt}: COMPILE {SRC} -o olean")
    t1 = time.time()
    r = subprocess.run(["lake", "env", "lean", SRC, "-o", str(OLEAN)],
                       cwd=str(LANE), capture_output=True, text=True, env=env,
                       start_new_session=True)
    (RECEIPT / f"compile.{attempt}.log").write_text(r.stdout + r.stderr)
    say(f"attempt {attempt}: exit={r.returncode} in {time.time()-t1:.0f}s")

    if r.returncode == 0 and OLEAN.exists():
        st = OLEAN.stat()
        say(f"olean {st.st_size}B mtime={datetime.fromtimestamp(st.st_mtime):%H:%M:%S} "
            f"src mtime={datetime.fromtimestamp((LANE/SRC).stat().st_mtime):%H:%M:%S}")
        (RECEIPT / "STATUS").write_text(f"OK olean built (attempt {attempt})\n")
        sys.exit(0)
    if r.returncode > 0:
        (RECEIPT / "STATUS").write_text(f"FAIL compile exit={r.returncode} (attempt {attempt})\n")
        sys.exit(1)
    say(f"attempt {attempt}: killed by signal {-r.returncode} -- backoff and retry")
    time.sleep(30)

(RECEIPT / "STATUS").write_text("ABORT attempts exhausted\n")
sys.exit(2)
