#!/usr/bin/env python3
"""Receipt runner for `SubsetSumL25.Row.JV1000Instance` (jv1000 row).

Same receipt discipline as `kapila_receipts_bounded.py` (SHARED.md §3 + lane practice):

  * live-pressure gate (swapout delta over 60 s == 0 and free_pct > 15)
  * the shared build lock `/Volumes/Substrate-1/bigo/.build.lock`, BOUNDED wait
    (default 240 s); expiry is recorded as a deviation in `lock.note` + `summary.json`
  * detached `lake build` (start_new_session) of one target
  * named-olean hashes, source hashes, HEAD
  * axiom banner `lake env lean JV1000Axioms.lean`, fail-closed on `sorryAx`,
    `native_decide`/`Lean.ofReduceBool`, a non-house axiom set, or a non-zero banner exit
  * **double-compile determinism**: the target is rebuilt a second time (source
    touched between runs) and the two olean sha256s are compared
  * `build_exit ∈ {-9, -15}` with a progressing log is a host kill, not a compile
    failure: recorded as such, never "fixed" in sources
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
RECEIPT = LANE / "receipts" / f"jv1000-{STAMP}"
LOCK_WAIT_S = int(os.environ.get("JV_LOCK_WAIT", "240"))
TARGET = "SubsetSumL25.Row.JV1000Instance"
SRC = LANE / "SubsetSumL25/Row/JV1000Instance.lean"
OLEAN = LANE / ".lake/build/lib/lean/SubsetSumL25/Row/JV1000Instance.olean"
AXFILE = LANE / "JV1000Axioms.lean"
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


def build(tag):
    env = dict(os.environ)
    env["PATH"] = "/opt/homebrew/bin:" + env.get("PATH", "")
    b0 = time.time()
    r = subprocess.run(["lake", "build", TARGET], cwd=str(LANE), capture_output=True,
                       text=True, env=env, start_new_session=True)
    (RECEIPT / f"build{tag}.log").write_text(r.stdout + r.stderr)
    (RECEIPT / f"build{tag}.exit").write_text(str(r.returncode))
    return r.returncode, round(time.time() - b0, 1)


def olean_sha():
    if not OLEAN.exists():
        return None, None
    b = OLEAN.read_bytes()
    return hashlib.sha256(b).hexdigest(), len(b)


def main():
    signal.signal(signal.SIGTERM, signal.SIG_IGN)
    signal.signal(signal.SIGHUP, signal.SIG_IGN)
    RECEIPT.mkdir(parents=True, exist_ok=True)
    summary = {"receipt": RECEIPT.name, "lane": "wip-kapila-row", "target": TARGET,
               "toolchain": open(LANE / "lean-toolchain").read().strip()}

    with open(RECEIPT / "gate.log", "w") as glog:
        delta, pct = gate(glog)
    if delta is None:
        (RECEIPT / "STATUS").write_text("ABORT gate never opened\n")
        print("gate never opened")
        return 1
    summary["gate"] = {"swapouts_delta60": delta, "free_pct": pct}

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
    summary["lock"] = {"acquired": acquired, "waited_s": waited, "bounded_s": LOCK_WAIT_S}
    print(note)

    try:
        code, secs = build("1")
        summary["build_exit"] = code
        summary["build_seconds"] = secs
        sha1, size1 = olean_sha()
        if code != 0:
            (RECEIPT / "STATUS").write_text(f"FAIL build_exit={code} host_kill="
                                            f"{code in (-9, -15)}\n")
            print("build failed")
            return 1
        # determinism: touch the source, rebuild, compare olean hashes
        time.sleep(1)
        os.utime(SRC, None)
        code2, secs2 = build("2")
        sha2, size2 = olean_sha()
        summary["determinism"] = {"sha_run1": sha1, "sha_run2": sha2,
                                  "size_run1": size1, "size_run2": size2,
                                  "identical": sha1 == sha2,
                                  "build2_exit": code2, "build2_seconds": secs2}
        (RECEIPT / "oleans.txt").write_text(
            f"{OLEAN.relative_to(LANE)} size={size1} sha256={sha1}\n"
            f"rebuild      size={size2} sha256={sha2}\n"
            f"identical={sha1 == sha2} build2_exit={code2}\n")
    finally:
        if acquired:
            fcntl.flock(lf, fcntl.LOCK_UN)
        lf.close()

    env = dict(os.environ)
    env["PATH"] = "/opt/homebrew/bin:" + env.get("PATH", "")
    ax = subprocess.run(["lake", "env", "lean", "JV1000Axioms.lean"], cwd=str(LANE),
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
    nprinted = 0
    for line in banner.splitlines():
        if "depends on axioms:" in line:
            nprinted += 1
            ax_set = {a.strip() for a in line.split("[", 1)[1].rstrip("]").split(",")}
            if not ax_set <= HOUSE:
                bad.append(line)
    if "does not depend on any axioms" in banner:
        nprinted += banner.count("does not depend on any axioms")
    summary["axioms"] = {"exit": ax.returncode, "banners_parsed": nprinted,
                         "house_triple_only": not bad}
    buildlog = (RECEIPT / "build1.log").read_text()
    if "declaration uses 'sorry'" in buildlog:
        bad.append("build-log sorry warning")

    sh("git -C %s rev-parse HEAD > %s" % (LANE, RECEIPT / "head.sha"))
    sh("shasum -a 256 SubsetSumL25/Row/JV1000Instance.lean JV1000Axioms.lean > %s"
       % (RECEIPT / "sources.sha256"))
    summary["head"] = (RECEIPT / "head.sha").read_text().strip()
    (RECEIPT / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")

    if bad:
        (RECEIPT / "STATUS").write_text("FAIL axiom gate: " + "; ".join(bad) + "\n")
        print("axiom gate failed:", bad)
        return 44
    (RECEIPT / "STATUS").write_text(
        f"DONE {RECEIPT.name} build_exit=0 banners={nprinted} {note}\n")
    print(f"DONE {RECEIPT} banners={nprinted} determinism={summary['determinism']['identical']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
