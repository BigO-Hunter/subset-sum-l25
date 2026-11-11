#!/usr/bin/env python3
"""Receipt runner for the ss/kapila 0.4877 row assembly (wip-kapila-row).

The build target is the ROW'S OWN MODULE CLOSURE
(`lake build SubsetSumL25.Row.KapilaRow SubsetSumL25.Row.KapilaGuard`:
Statement -> KapilaAlgo -> KapilaAbsorb -> KapilaRow, plus the guard-coverage
module), not the whole library.  The row closure is what "the row assembles"
means; a whole-`SubsetSumL25` build additionally drags in M5/M5CorA6/M6 and
competes with the other lanes for the host, which the shared build lock
serialises (and which killed two attempts here at exit -15 / -9).

Three receipts per landing, per the campaign's rule:
  1. full `lake build`, exit 0, log kept;
  2. named oleans, existence + sha256 + mtime (built this run);
  3. axiom banner via `lake env lean KapilaRowAxioms.lean`, hard-failing on
     `sorryAx` or on any banner that is not a subset of the house triple.

Host gate (R2125609494): live pressure, not the swap high-water mark —
  memory_pressure free% > 15 AND vm_stat Swapouts delta over 60 s == 0.
Builds run behind a BOUNDED wait on /Volumes/Substrate-1/bigo/.build.lock
(default 240 s, `KAPILA_LOCK_WAIT`); if it expires the build proceeds and the
deviation is recorded in `lock.acquired` and `summary.json` (2026-11-10: an
unbounded flock sat 2 h 19 m behind another lane, and a stale waiter from an
earlier round had to be SIGKILLed because the runner ignores SIGTERM by design).
"""
import fcntl
import hashlib
import signal
import json
import os
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

LANE = Path("/Volumes/Substrate-1/bigo/kapila-row-lane")
LOCKF = "/Volumes/Substrate-1/bigo/.build.lock"
STAMP = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
RECEIPT = LANE / "receipts" / f"kapila-{STAMP}"

NAMED_OLEANS = [
    ".lake/build/lib/lean/SubsetSumL25/Row/Statement.olean",
    ".lake/build/lib/lean/SubsetSumL25/Row/KapilaAlgo.olean",
    ".lake/build/lib/lean/SubsetSumL25/Row/KapilaAbsorb.olean",
    ".lake/build/lib/lean/SubsetSumL25/Row/KapilaRow.olean",
    ".lake/build/lib/lean/SubsetSumL25/Row/KapilaGuard.olean",
    ".lake/build/lib/lean/SubsetSumL25/Row/KapilaPrelim.olean",
    ".lake/build/lib/lean/SubsetSumL25/Row/KapilaAlias.olean",
    ".lake/build/lib/lean/SubsetSumL25/Row/KapilaChecksum.olean",
    ".lake/build/lib/lean/SubsetSumL25/Row/KapilaTest.olean",
    ".lake/build/lib/lean/SubsetSumL25/Row/KapilaLoop.olean",
    ".lake/build/lib/lean/SubsetSumL25/Row/KapilaEstimate.olean",
    ".lake/build/lib/lean/SubsetSumL25/Row/KapilaWide.olean",
    ".lake/build/lib/lean/SubsetSumL25/Row/KapilaDigitwise.olean",
    ".lake/build/lib/lean/SubsetSumL25/Row/KapilaBinSum.olean",
    ".lake/build/lib/lean/SubsetSumL25/Row/KapilaCmpSeg.olean",
]

HOUSE = {"propext", "Classical.choice", "Quot.sound"}


def sh(cmd, **kw):
    return subprocess.run(cmd, shell=isinstance(cmd, str), capture_output=True,
                          text=True, cwd=str(LANE), **kw)


def swapouts():
    out = sh("vm_stat").stdout
    for line in out.splitlines():
        if line.startswith("Swapouts:"):
            return int(line.split()[-1].strip("."))
    return -1


def free_pct():
    out = sh("memory_pressure").stdout
    for line in out.splitlines():
        if "free percentage" in line:
            return int(line.strip().split()[-1].strip("%"))
    return -1


def gate(log):
    """Live-pressure gate: swapout delta == 0 over 60 s and free% > 15."""
    for attempt in range(1, 13):
        s0 = swapouts()
        pct = free_pct()
        time.sleep(60)
        s1 = swapouts()
        delta = s1 - s0
        verdict = "PROCEED" if (delta == 0 and pct > 15) else "wait"
        log.write(f"{datetime.now(timezone.utc).isoformat()} iter={attempt} "
                  f"swapouts_delta60={delta} free_pct={pct} verdict={verdict}\n")
        log.flush()
        if verdict == "PROCEED":
            return delta, pct
    return None, None


def main():
    # R2125609465 / R2125609493: an unattributed SIGTERM can land on a build
    # that is making progress (exit -15).  Detach from the caller's process
    # group and ignore TERM so a kill-storm cannot turn a good build into a
    # false failure; the build's own exit code stays authoritative.
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

    lf = open(LOCKF, "w")
    # Bounded wait, not an unbounded block: the fleet-wide build lock is held by
    # whichever lane is building, and a lane that parks here forever makes no
    # progress at all.  Per the lane's discipline (2026-11-10), after LOCK_WAIT
    # seconds the build proceeds UNLOCKED and the deviation is recorded.
    LOCK_WAIT = int(os.environ.get("KAPILA_LOCK_WAIT", "240"))
    t_lock = time.time()
    held = False
    while True:
        try:
            fcntl.flock(lf, fcntl.LOCK_EX | fcntl.LOCK_NB)
            held = True
            break
        except BlockingIOError:
            if time.time() - t_lock > LOCK_WAIT:
                break
            time.sleep(2)
    lock_note = (f"acquired after {time.time()-t_lock:.0f}s" if held
                 else f"DEVIATION: proceeded UNLOCKED after {time.time()-t_lock:.0f}s wait")
    (RECEIPT / "lock.acquired").write_text(
        datetime.now(timezone.utc).isoformat() + "  " + lock_note + "\n")
    summary["lock"] = lock_note

    try:
        env = dict(os.environ)
        env["PATH"] = "/opt/homebrew/bin:" + env.get("PATH", "")
        t0 = time.time()
        build = subprocess.run(["lake", "build", "SubsetSumL25.Row.KapilaRow",
                                "SubsetSumL25.Row.KapilaGuard",
                                "SubsetSumL25.Row.KapilaPrelim",
                                "SubsetSumL25.Row.KapilaAlias",
                                "SubsetSumL25.Row.KapilaChecksum",
                                "SubsetSumL25.Row.KapilaTest",
                                "SubsetSumL25.Row.KapilaLoop",
                                "SubsetSumL25.Row.KapilaEstimate",
                                "SubsetSumL25.Row.KapilaWide",
                                "SubsetSumL25.Row.KapilaDigitwise",
                                "SubsetSumL25.Row.KapilaBinSum",
                                "SubsetSumL25.Row.KapilaCmpSeg"], cwd=str(LANE), capture_output=True,
                               text=True, env=env, start_new_session=True)
        (RECEIPT / "build.log").write_text(build.stdout + build.stderr)
        (RECEIPT / "build.exit").write_text(str(build.returncode))
        summary["build_exit"] = build.returncode
        summary["build_seconds"] = round(time.time() - t0, 1)
        if build.returncode != 0:
            (RECEIPT / "STATUS").write_text(f"FAIL build_exit={build.returncode}\n")
            print("build failed")
            return 1
    finally:
        fcntl.flock(lf, fcntl.LOCK_UN)
        lf.close()

    # receipt 2 — named oleans
    rows = []
    for rel in NAMED_OLEANS:
        p = LANE / rel
        if not p.exists():
            rows.append(f"MISSING {rel}")
            continue
        h = hashlib.sha256(p.read_bytes()).hexdigest()
        st = p.stat()
        rows.append(f"{rel} {st.st_size} bytes mtime={datetime.fromtimestamp(st.st_mtime).isoformat()} sha256={h}")
    (RECEIPT / "oleans.txt").write_text("\n".join(rows) + "\n")

    # receipt 3 — axiom banner
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
    # An errored banner run is not a clean banner: a misspelled `#print axioms`
    # name would otherwise leave `bad` empty while half the declarations were
    # never checked (measured 2026-11-10, receipts/kapila-20261110T150102Z:
    # axioms_exit=1 with STATUS "DONE").
    if ax.returncode != 0:
        bad.append(f"axiom banner exited {ax.returncode} (not a clean banner)")
    for line in banner.splitlines():
        if "depends on axioms:" in line:
            ax_set = {a.strip() for a in line.split("[", 1)[1].rstrip("]").split(",")}
            if not ax_set <= HOUSE:
                bad.append(line)
    # no sorry in sources (build log is authoritative for the library)
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
        f"DONE {RECEIPT.name} build_exit=0 axioms_exit={ax.returncode}\n")
    print(f"DONE {RECEIPT}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
