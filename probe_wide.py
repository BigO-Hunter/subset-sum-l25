#!/usr/bin/env python3
"""Detached single-file Lean check (survives the 250 s shell watchdog)."""
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

LANE = Path("/Volumes/Substrate-1/bigo/kapila-row-lane")
FILE = sys.argv[1] if len(sys.argv) > 1 else "SubsetSumL25/Row/KapilaWide.lean"
OUT = Path("/tmp/kapila_leancheck")
OUT.mkdir(exist_ok=True)
STEM = Path(FILE).stem

log = open(OUT / f"{STEM}.log", "w")
(OUT / f"{STEM}.start").write_text(datetime.now(timezone.utc).isoformat() + "\n")
t0 = time.time()
p = subprocess.run(
    ["/opt/homebrew/bin/lake", "env", "lean", FILE],
    cwd=str(LANE), capture_output=True, text=True, start_new_session=True,
)
log.write(p.stdout + p.stderr)
log.close()
(OUT / f"{STEM}.exit").write_text(f"{p.returncode}\n")
(OUT / f"{STEM}.secs").write_text(f"{round(time.time() - t0, 1)}\n")
print("done", p.returncode)
