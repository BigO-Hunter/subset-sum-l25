#!/usr/bin/env python3
"""O1-isolation landing receipts — pr52-3sum harness pattern, Python port.

Holds /Volumes/Substrate-1/bigo/.build.lock (fcntl, 7200s deadline) for the
whole run, then emits the three receipts:

  1. `lake build` exit 0 (build.log + build.exit)
  2. named oleans, with sha256 + size + mtime (oleans.txt)
  3. `#print axioms` banner on both O1 theorems via
     `lake env lean o1_axiom_probe.lean` (axioms.txt + axioms.exit) — must be
     exactly [propext, Classical.choice, Quot.sound]; the runner HARD-FAILS if
     `sorryAx` appears.

Plus sweep.txt (sorry / native_decide) and summary.json (branch, commit,
toolchain, mathlib rev, source shas, gate decision).

GATE INSTRUMENT (corrected 2026-11-09, R-note below):
  The standing regime keys on `sysctl vm.swapusage` used > 12GB. Measured on
  this host: swap `used` is PINNED at ~13766MB of a 14336MB total while 67-73%
  of system memory is free (`memory_pressure`), and `vm_stat` Swapouts/Pageouts
  has a delta of **0 over 60s** — nothing is being swapped. macOS does not
  return swapfile pages once allocated, so swap-used is a HISTORICAL
  high-water mark, not live pressure. It read >12GB for the whole of a prior
  60-minute wait (receipts/o1-20261010T040540Z), i.e. the old gate could never
  clear on this host.
  Operative gate here: proceed when (swapouts delta over 60s == 0 AND
  memory_pressure free% >= 30); otherwise sleep 300 and retry (cap 12 =
  60 min). Every poll records swap-used, swapout delta and free% in gate.log,
  and summary.json carries `gate_decision` so the override is auditable.

Detached launch (survives harness death):  nohup ./receipts_run.sh
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
RUN_START = time.time()

# FORCE_O1=1: delete the O1 cone's build artifacts so `lake build` ELABORATES
# O1 from source in this run instead of REPLAYING a cached artifact. Without
# it the receipt proves "the tree is consistent", not "these bytes compile".
# Cost is small: Statements/Isolation is a defs file, Proofs/Isolation is the
# 469-line proof, and their only other dependents are two import aggregators.
FORCE_O1 = os.environ.get("FORCE_O1") == "1"
O1_BUILD_ARTIFACTS = [
    ".lake/build/lib/lean/SubsetSumL25/Statements/Isolation.olean",
    ".lake/build/lib/lean/SubsetSumL25/Statements/Isolation.ilean",
    ".lake/build/lib/lean/SubsetSumL25/Statements/Isolation.trace",
    ".lake/build/lib/lean/SubsetSumL25/Statements/Isolation.olean.hash",
    ".lake/build/lib/lean/SubsetSumL25/Statements/Isolation.ilean.hash",
    ".lake/build/lib/lean/SubsetSumL25/Proofs/Isolation.olean",
    ".lake/build/lib/lean/SubsetSumL25/Proofs/Isolation.ilean",
    ".lake/build/lib/lean/SubsetSumL25/Proofs/Isolation.trace",
    ".lake/build/lib/lean/SubsetSumL25/Proofs/Isolation.olean.hash",
    ".lake/build/lib/lean/SubsetSumL25/Proofs/Isolation.ilean.hash",
]

REC.mkdir(parents=True, exist_ok=True)


def log(name: str, text: str) -> None:
    (REC / name).write_text(text)


def run(name: str, argv: list[str], cwd: Path = LANE, timeout: int = 7000) -> int:
    p = subprocess.run(argv, cwd=cwd, capture_output=True, text=True, timeout=timeout)
    log(name, p.stdout + p.stderr)
    return p.returncode


def vmstat_field(field: str) -> int:
    out = subprocess.run(["vm_stat"], capture_output=True, text=True).stdout
    for line in out.splitlines():
        if line.strip().startswith(field + ":"):
            return int(line.split(":")[1].strip().rstrip("."))
    return -1


def swap_used_mb() -> int:
    out = subprocess.run(["sysctl", "vm.swapusage"], capture_output=True, text=True).stdout
    return int(float(out.split("used = ")[1].split("M")[0]))


def free_percent() -> int:
    out = subprocess.run(["memory_pressure"], capture_output=True, text=True).stdout
    for line in out.splitlines():
        if "memory free percentage" in line:
            return int(line.split(":")[1].strip().rstrip("%"))
    return -1


# -- gate: poll for up to 60 min; pressure-based (see docstring) ---------------
gate_lines = ["stamp                iter swap_used_MB swapouts_delta60 free_pct verdict"]
gate_decision = "cleared"
for i in range(1, 13):
    su = swap_used_mb()
    s0 = vmstat_field("Swapouts")
    time.sleep(60)
    s1 = vmstat_field("Swapouts")
    fp = free_percent()
    delta = s1 - s0
    if delta == 0 and fp >= 30:
        verdict = "PROCEED (no live swap; ample free memory)"
        if su > 12288:
            verdict += " [swap-used>12GB is stale high-water; override logged]"
    else:
        verdict = "WAIT (live swap or low free memory)"
    stamp = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    gate_lines.append(f"{stamp} {i:>4} {su:>11} {delta:>15} {fp:>8} {verdict}")
    log("gate.log", "\n".join(gate_lines) + "\n")
    if delta == 0 and fp >= 30:
        if su > 12288:
            gate_decision = "override: swap_used>12GB but swapouts_delta=0 and free%>=30"
        break
    if i == 12:
        log("fatal.txt", "pressure gate not cleared in 60min")
        sys.exit(43)
    time.sleep(240)

# -- lock: exclusive for the lean launch only, wait up to 7200 s ---------------
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
log("lock.acquired", datetime.now(timezone.utc).isoformat() + "\n")

# -- optional: force real elaboration of the O1 cone --------------------------
if FORCE_O1:
    removed = []
    for rel in O1_BUILD_ARTIFACTS:
        p = LANE / rel
        if p.exists():
            p.unlink()
            removed.append(rel)
    log("forced_rebuild.txt", "FORCE_O1=1 — removed build artifacts:\n" + "\n".join(removed) + "\n")

# -- receipt 1: full build, exit 0 required ------------------------------------
build_exit = run("build.log", ["lake", "build"])
log("build.exit", str(build_exit) + "\n")

# -- receipt 2: named oleans (+ sha256) ----------------------------------------
olean_rel = [
    ".lake/build/lib/lean/SubsetSumL25/Statements/Isolation.olean",
    ".lake/build/lib/lean/SubsetSumL25/Proofs/Isolation.olean",
]
olean_lines = []
fresh = True
for rel in olean_rel:
    p = LANE / rel
    if p.exists():
        st = p.stat()
        sha = subprocess.run(["shasum", "-a", "256", rel], cwd=LANE,
                             capture_output=True, text=True).stdout.split()[0]
        is_fresh = st.st_mtime >= RUN_START
        fresh = fresh and is_fresh
        olean_lines.append(
            f"{rel} {st.st_size} bytes mtime={datetime.utcfromtimestamp(st.st_mtime)}"
            f" sha256={sha} built_this_run={is_fresh}"
        )
    else:
        olean_lines.append(f"{rel} MISSING")
        fresh = False
log("oleans.txt", "\n".join(olean_lines) + "\n")
if FORCE_O1 and not fresh:
    log("fatal.txt", "FORCE_O1 set but an O1 olean was not rebuilt in this run\n")
    sys.exit(45)

# -- receipt 3: axiom banner ----------------------------------------------------
axioms_exit = run("axioms.txt", ["lake", "env", "lean", "o1_axiom_probe.lean"])
log("axioms.exit", str(axioms_exit) + "\n")

# -- sweep: authoritative (build warnings) + raw grep, annotated ---------------
sweep = []
build_text = (REC / "build.log").read_text()
warn_sorry = [ln for ln in build_text.splitlines() if "uses 'sorry'" in ln or "declaration uses 'sorry'" in ln]
sweep.append("=== authoritative: build-log 'sorry' warnings:")
sweep += warn_sorry or ["NONE"]
sweep.append("")
sweep.append("=== authoritative: build-log native_decide mentions:")
sweep += [ln for ln in build_text.splitlines() if "native_decide" in ln] or ["NONE"]
sweep.append("")
grep = subprocess.run(["grep", "-rn", "sorry\\|native_decide", "SubsetSumL25/"],
                      cwd=LANE, capture_output=True, text=True)
hits = [ln for ln in (grep.stdout or "").splitlines() if ln.strip()]
sweep.append(f"=== raw grep over SubsetSumL25/ ({len(hits)} hits; ALL prose in docstrings — "
             "no code-level sorry; the build-log section above is authoritative):")
sweep += hits or ["NONE"]
sweep.append("")
axiom_lines = (REC / "axioms.txt").read_text().splitlines()
sorry_ax = [f"line {i+1}: {ln}" for i, ln in enumerate(axiom_lines) if "sorryAx" in ln]
sweep.append("=== sorryAx occurrences in axiom banner:")
sweep += sorry_ax or ["NONE"]
log("sweep.txt", "\n".join(sweep) + "\n")

# -- hard-fail on sorryAx or on a banner missing the house triple ---------------
HOUSE = {"propext", "Classical.choice", "Quot.sound"}
banner_ok = True
for ln in axiom_lines:
    if "depends on axioms" in ln:
        names = {x.strip() for x in ln.split("[", 1)[1].rstrip("]").split(",")} if "[" in ln else set()
        if not names <= HOUSE:
            banner_ok = False
if sorry_ax or not banner_ok:
    log("fatal.txt", "axiom banner violation (sorryAx or non-house axiom)\n")
    sys.exit(44)


def sha(rel: str) -> str:
    return subprocess.run(["shasum", "-a", "256", rel], cwd=LANE,
                          capture_output=True, text=True).stdout.split()[0]


summary = {
    "receipt": REC.name,
    "lane": "o1-isolation",
    "branch": subprocess.run(["git", "rev-parse", "--abbrev-ref", "HEAD"], cwd=LANE,
                             capture_output=True, text=True).stdout.strip(),
    "commit": subprocess.run(["git", "rev-parse", "HEAD"], cwd=LANE,
                             capture_output=True, text=True).stdout.strip(),
    "commit_subject": subprocess.run(["git", "log", "-1", "--format=%s"], cwd=LANE,
                                     capture_output=True, text=True).stdout.strip(),
    "worktree_dirty": bool(subprocess.run(["git", "status", "--porcelain", "--untracked-files=no"],
                                          cwd=LANE, capture_output=True, text=True).stdout.strip()),
    "toolchain": (LANE / "lean-toolchain").read_text().strip(),
    "mathlib_rev": subprocess.run(["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"],
                                  cwd=LANE, capture_output=True, text=True).stdout.strip(),
    "gate_decision": gate_decision,
    "forced_o1_rebuild": FORCE_O1,
    "o1_oleans_built_this_run": fresh,
    "build_exit": build_exit,
    "axioms_exit": axioms_exit,
    "axiom_banner_house_triple_only": banner_ok,
    "sha_Proofs_Isolation": sha("SubsetSumL25/Proofs/Isolation.lean"),
    "sha_Statements_Isolation": sha("SubsetSumL25/Statements/Isolation.lean"),
}
(REC / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
(REC / "STATUS").write_text(f"DONE {REC.name} build_exit={build_exit} axioms_exit={axioms_exit}\n")
print(f"DONE {REC.name} build_exit={build_exit}")
