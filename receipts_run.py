#!/usr/bin/env python3
"""O1-isolation landing receipts — Python port of the pr52-3sum harness pattern.

Holds /Volumes/Substrate-1/bigo/.build.lock (fcntl, 7200s deadline) for the
full run; swap-gates (<=12GB, 300s loops, 60-min cap); then emits three
receipts: (1) full `lake build` exit 0, (2) named Isolation oleans,
(3) #print axioms banner on both O1 theorems (house triple, no sorryAx /
native_decide) + sorry sweep. Detached launch survives harness restarts:
nohup ./receipts_run.sh
"""
import fcntl
import json
import os
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

LANE = Path("/Volumes/Substrate-1/bigo/o1-lane")
LOCK = Path("/Volumes/Substrate-1/bigo/.build.lock")
REC = LANE / "receipts" / ("o1-" + datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ"))

REC.mkdir(parents=True, exist_ok=True)


def log(name: str, text: str) -> None:
    (REC / name).write_text(text)


def run(name: str, argv: list[str], cwd: Path = LANE, timeout: int = 7000) -> int:
    p = subprocess.run(argv, cwd=cwd, capture_output=True, text=True, timeout=timeout)
    log(name, p.stdout + p.stderr)
    return p.returncode


# -- lock: exclusive for the whole run, wait up to 7200 s ---------------------
lock_fh = open(LOCK, "w")
deadline = time.time() + 7200
while True:
    try:
        fcntl.flock(lock_fh, fcntl.LOCK_EX | fcntl.LOCK_NB)
        break
    except OSError:
        if time.time() > deadline:
            log("fatal.txt", "flock timeout 7200s")
            sys.exit(3)
        time.sleep(10)

# -- swap gate: sleep 300 s per loop until used <= 12288 MB, cap 12 loops -----
swap_lines = []
for i in range(1, 13):
    out = subprocess.run(["sysctl", "vm.swapusage"], capture_output=True, text=True).stdout
    used_mb = int(float(out.split("used = ")[1].split("M")[0]))
    stamp = datetime.now(timezone.utc).strftime("%H:%M:%SZ")
    swap_lines.append(f"{stamp} iter={i} used={used_mb}MB")
    log("swap.log", "\n".join(swap_lines) + "\n")
    if used_mb <= 12288:
        break
    if i == 12:
        log("fatal.txt", "swap gate not cleared in 60min")
        sys.exit(43)
    time.sleep(300)

# -- receipt 1: full build, exit 0 required ------------------------------------
build_exit = run("build.log", ["lake", "build"])
log("build.exit", str(build_exit))

# -- receipt 2: named oleans ----------------------------------------------------
olean_rel = [
    ".lake/build/lib/lean/SubsetSumL25/Statements/Isolation.olean",
    ".lake/build/lib/lean/SubsetSumL25/Proofs/Isolation.olean",
]
olean_lines = []
for rel in olean_rel:
    p = LANE / rel
    if p.exists():
        st = p.stat()
        olean_lines.append(f"{rel} {st.st_size} bytes mtime={datetime.utcfromtimestamp(st.st_mtime)}")
    else:
        olean_lines.append(f"{rel} MISSING")
log("oleans.txt", "\n".join(olean_lines) + "\n")

# -- receipt 3: axiom banner ----------------------------------------------------
axioms_exit = run("axioms.txt", ["lake", "env", "lean", "o1_axiom_probe.lean"])
log("axioms.exit", str(axioms_exit))

# -- sweep: sorry / native_decide / sorryAx --------------------------------------
grep = subprocess.run(
    ["grep", "-rn", "sorry\\|native_decide", "SubsetSumL25/"],
    cwd=LANE, capture_output=True, text=True,
)
hits = [ln for ln in (grep.stdout or "").splitlines() if ln.strip()]
sweep = ["=== sorry/native_decide grep over SubsetSumL25/:", *(hits or ["NONE"])]
axiom_lines = (REC / "axioms.txt").read_text().splitlines()
sorry_ax_hits = [f"line {i+1}: {ln}" for i, ln in enumerate(axiom_lines) if "sorryAx" in ln]
sweep += ["", "=== sorryAx occurrences in axiom banner:", *(sorry_ax_hits or ["NONE"])]
log("sweep.txt", "\n".join(sweep) + "\n")


def sha(rel: str) -> str:
    return subprocess.run(["shasum", "-a", "256", rel], cwd=LANE, capture_output=True, text=True).stdout.split()[0]


summary = {
    "receipt": REC.name,
    "lane": "o1-isolation",
    "branch": subprocess.run(["git", "rev-parse", "--abbrev-ref", "HEAD"], cwd=LANE,
                             capture_output=True, text=True).stdout.strip(),
    "commit": subprocess.run(["git", "rev-parse", "HEAD"], cwd=LANE,
                             capture_output=True, text=True).stdout.strip(),
    "toolchain": (LANE / "lean-toolchain").read_text().strip(),
    "mathlib_rev": subprocess.run(["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"],
                                  cwd=LANE, capture_output=True, text=True).stdout.strip(),
    "build_exit": build_exit,
    "axioms_exit": axioms_exit,
    "sha_Proofs_Isolation": sha("SubsetSumL25/Proofs/Isolation.lean"),
    "sha_Statements_Isolation": sha("SubsetSumL25/Statements/Isolation.lean"),
}
(REC / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
(REC / "STATUS").write_text(f"DONE {REC.name}\n")
print(f"DONE {REC.name}")
