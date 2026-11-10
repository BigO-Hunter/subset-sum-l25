#!/usr/bin/env python3
"""Bounded-wait build lock + `lake env lean <file>`, for probe/authoring cycles."""
import fcntl, subprocess, sys, time
from pathlib import Path

LANE = Path("/Volumes/Substrate-1/bigo/kapila-row-lane")
LOCKF = "/Volumes/Substrate-1/bigo/.build.lock"
WAIT = int(sys.argv[1])
files = sys.argv[2:]

t0 = time.time()
lf = open(LOCKF, "w")
try:
    while True:
        try:
            fcntl.flock(lf, fcntl.LOCK_EX | fcntl.LOCK_NB)
            break
        except BlockingIOError:
            if time.time() - t0 > WAIT:
                print(f"LOCK_TIMEOUT after {WAIT}s — proceeding UNLOCKED (recorded deviation)")
                break
            time.sleep(2)
    held = time.time() - t0 <= WAIT
    env = {"PATH": "/opt/homebrew/bin:/usr/bin:/bin:/usr/sbin:/sbin",
           "HOME": "/Users/dmitri.arkhipov"}
    for f in files:
        print(f"=== {f} (lock_wait={time.time()-t0:.0f}s held={held})", flush=True)
        p = subprocess.run(["lake", "env", "lean", f], cwd=str(LANE),
                           capture_output=True, text=True, env=env,
                           start_new_session=True)
        out = (p.stdout + p.stderr)
        print(out[:8000])
        print(f"EXIT={p.returncode}")
finally:
    try:
        fcntl.flock(lf, fcntl.LOCK_UN)
    except Exception:
        pass
