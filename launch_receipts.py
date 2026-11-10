#!/usr/bin/env python3
"""Detached launcher for receipts_run.py (macOS has no setsid binary).

start_new_session=True puts the run in its own session/process group so a
harness process-group kill cannot reach it. The Python runner itself holds the
flock, so this launcher returns immediately.
"""
import subprocess
from pathlib import Path

LANE = Path("/Volumes/Substrate-1/bigo/o1-lane")
log = open(LANE / "receipts" / "launch.log", "a")
subprocess.Popen(
    ["/usr/bin/env", "python3", str(LANE / "receipts_run.py")],
    cwd=str(LANE),
    stdout=log,
    stderr=subprocess.STDOUT,
    start_new_session=True,
)
print("launched detached")
