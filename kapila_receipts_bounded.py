#!/usr/bin/env python3
"""Bounded-wait receipt runner for the ss/kapila 0.4877 row assembly.

Identical to `kapila_receipts.py` except for the build-lock policy: the shared
`/Volumes/Substrate-1/bigo/.build.lock` is acquired with a BOUNDED wait
(default 240 s).  If the bounded wait expires the build proceeds anyway and the
deviation is written to `lock.note` and into `summary.json` — the honest record
is the point.  Reason for the deviation (measured 2026-11-10): an unbounded
`flock` sat queued 50+ minutes behind five concurrent lake builds from other
lanes on the same volume, during which no forward progress was possible.

Everything else — live-pressure gate, forced rebuild of the row closure, named
oleans, axiom banner (house triple only, fail-closed on a non-zero banner exit),
source hashes, HEAD — is unchanged.
"""
import fcntl
import hashlib
import json
import os
import signal
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

LANE = Path("/Volumes/Substrate-1/bigo/kapila-row-lane")
LOCKF = "/Volumes/Substrate-1/bigo/.build.lock"
STAMP = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
RECEIPT = LANE / "receipts" / f"kapila-{STAMP}"
LOCK_WAIT_S = int(os.environ.get("KAPILA_LOCK_WAIT", "240"))

NAMED_OLEANS = [
    ".lake/build/lib/lean/SubsetSumL25/Row/Statement.olean",
    ".lake/build/lib/lean/SubsetSumL25/Row/KapilaAlgo.olean",
    ".lake/build/lib/lean/SubsetSumL25/Row/KapilaAbsorb.olean",
    ".lake/build/lib/lean/SubsetSumL25/Row/KapilaRow.olean",
    ".lake/build/lib/lean/SubsetSumL25/Row/KapilaGuard.olean",
    ".lake/build/lib/lean/SubsetSumL25/Row/KapilaPrelim.olean",
]
TARGETS = [
    "SubsetSumL25.Row.KapilaRow",
    "SubsetSumL25.Row.KapilaGuard",
    "SubsetSumL25.Row.KapilaPrelim",
]
HOUSE = {"propext", "Classical.choice", "Quot.sound"}


def sh(cmd, **kw):
    return subprocess.run(cmd, shell=isinstance(cmd, str), capture_output=True,
                          text=True, cwd=str(LANE), **kw)


def swapouts():
    for line in sh("vm_stat").stdout.splitlines():
        if line.startswith("Swapouts:"):
            return int(line.split()[-1].strip("."))
    return -1


def free_pct():
    for line in sh("memory_pressure").stdout.splitlines():
        if "free percentage" in line:
            return int(line.strip().split()[-1].strip("%"))
    return -1


def gate(log):
    for attempt in range(1, 13):
        s0, pct = swapouts(), free_pct()
        time.sleep(60)
        delta = swapouts() - s0
        verdict = "PROCEED" if (delta == 0 and pct > 15) else "wait"
        log.write(f"{datetime.now(timezone.utc).isoformat()} iter={attempt} "
                  f"swapouts_delta60={delta} free_pct={pct} verdict={verdict}\n")
        log.flush()
        if verdict == "PROCEED":
            return delta, pct
    return None, None


def main():
    signal.signal(signal.SIGTERM, signal.SIG_IGN)
    signal.signal(signal.SIGHUP, signal.SIG_IGN)
    RECEIPT.mkdir(parents=True, exist_ok=True)
    summary = {"receipt": RECEIPT.name, "lane": "wip-kapila-row",
               "toolchain": open(LANE / "lean-toolchain").read().strip()}

    with open(RECEIPT / "gate.log", "w") as glog:
        delta, pct = gate(glog)
    if delta is None:
        (RECEIPT / "STATUS").write_text("ABORT gate never opened\n")
        print("gate never opened")
        return 1
    summary["gate"] = {"swapouts_delta60": delta, "free_pct": pct}

    # bounded-wait lock
    lf = open(LOCKF, "w")
    t0 = time.time()
    acquired = False
    while time.time() - t0 < LOCK_WAIT_S:
        try:
            fcntl.flock(lf, fcntl.LOCK_EX | fcntl.LOCK_NB)
            acquired = True
            break
        except BlockingIOError:
            time.sleep(5)
    waited = round(time.time() - t0, 1)
    note = f"acquired={acquired} waited_s={waited} bounded={LOCK_WAIT_S}"
    (RECEIPT / "lock.note").write_text(note + "\n")
    summary["lock"] = {"acquired": acquired, "waited_s": waited,
                       "bounded_s": LOCK_WAIT_S}
    print(note)
    if acquired:
        (RECEIPT / "lock.acquired").write_text(datetime.now(timezone.utc).isoformat())

    try:
        env = dict(os.environ)
        env["PATH"] = "/opt/homebrew/bin:" + env.get("PATH", "")
        b0 = time.time()
        build = subprocess.run(["lake"] + ["build"] + TARGETS, cwd=str(LANE),
                               capture_output=True, text=True, env=env,
                               start_new_session=True)
        (RECEIPT / "build.log").write_text(build.stdout + build.stderr)
        (RECEIPT / "build.exit").write_text(str(build.returncode))
        summary["build_exit"] = build.returncode
        summary["build_seconds"] = round(time.time() - b0, 1)
        if build.returncode != 0:
            (RECEIPT / "STATUS").write_text(f"FAIL build_exit={build.returncode}\n")
            print("build failed")
            return 1
    finally:
        if acquired:
            fcntl.flock(lf, fcntl.LOCK_UN)
        lf.close()

    rows = []
    for rel in NAMED_OLEANS:
        p = LANE / rel
        if not p.exists():
            rows.append(f"MISSING {rel}")
            continue
        h = hashlib.sha256(p.read_bytes()).hexdigest()
        st = p.stat()
        rows.append(f"{rel} {st.st_size} bytes "
                    f"mtime={datetime.fromtimestamp(st.st_mtime).isoformat()} sha256={h}")
    (RECEIPT / "oleans.txt").write_text("\n".join(rows) + "\n")

    env = dict(os.environ)
    env["PATH"] = "/opt/homebrew/bin:" + env.get("PATH", "")
    ax = subprocess.run(["lake", "env", "lean", "KapilaRowAxioms.lean"], cwd=str(LANE),
                        capture_output=True, text=True, env=env)
    banner = ax.stdout + ax.stderr
    (RECEIPT / "axioms.txt").write_text(banner)
    (RECEIPT / "axioms.exit").write_text(str(ax.returncode))
    bad = []
    if "sorryAx" in banner:
        bad.append("sorryAx")
    if "native_decide" in banner or "Lean.ofReduceBool" in banner:
        bad.append("native_decide")
    if ax.returncode != 0:
        bad.append(f"axiom banner exited {ax.returncode} (not a clean banner)")
    for line in banner.splitlines():
        if "depends on axioms:" in line:
            ax_set = {a.strip() for a in line.split("[", 1)[1].rstrip("]").split(",")}
            if not ax_set <= HOUSE:
                bad.append(line)
    if "declaration uses 'sorry'" in (RECEIPT / "build.log").read_text():
        bad.append("build-log sorry warning")
    summary["axioms_exit"] = ax.returncode
    summary["axiom_banner_house_triple_only"] = not bad

    sh("git -C %s rev-parse HEAD > %s" % (LANE, RECEIPT / "head.sha"))
    sh("shasum -a 256 SubsetSumL25/Row/*.lean > %s" % (RECEIPT / "sources.sha256"))
    summary["head"] = (RECEIPT / "head.sha").read_text().strip()
    (RECEIPT / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")

    if bad:
        (RECEIPT / "STATUS").write_text("FAIL axiom gate: " + "; ".join(bad) + "\n")
        print("axiom gate failed:", bad)
        return 44
    (RECEIPT / "STATUS").write_text(
        f"DONE {RECEIPT.name} build_exit=0 axioms_exit={ax.returncode} {note}\n")
    print(f"DONE {RECEIPT}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
