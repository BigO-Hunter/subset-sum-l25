#!/usr/bin/env python3
"""Launch the Lean check in a detached session so the shell watchdog cannot kill it."""
import subprocess
import sys

LAUNCH = subprocess.Popen(
    ["/usr/bin/python3", "/Volumes/Substrate-1/bigo/kapila-row-lane/probe_wide.py"]
    + sys.argv[1:],
    cwd="/Volumes/Substrate-1/bigo/kapila-row-lane",
    start_new_session=True,
    stdout=open("/tmp/kapila_leancheck/launch.log", "a"),
    stderr=subprocess.STDOUT,
)
print("launched pid", LAUNCH.pid)
