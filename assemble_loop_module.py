#!/usr/bin/env python3
"""Assemble `SubsetSumL25/Row/KapilaCmpSegLoop.lean` from its parts.

  parts/c10_transfer_gen.lean  — the §C10 replay of §C4–§C6 for an abstract `P`
                                 (written by `gen_transfer.py`; do not hand-edit)
  parts/c11_loop.lean          — §C11: the counting tail, its charge, and the
                                 induction on `p` (hand-written)

The assembled module is what `lake build` sees, so the receipt's hash names the whole
thing.
"""
from pathlib import Path

LANE = Path("/Volumes/Substrate-1/bigo/kapila-row-lane")
OUT = LANE / "SubsetSumL25/Row/KapilaCmpSegLoop.lean"

PRELUDE = '''/-
`KapilaCmpSeg`'s two named residuals — (**A**) the `getD`-agreement transfer of
§C4–§C6 to the composed program, and (**B**) the loop induction on the comparison
counter — in one module.

§C9 left both open by name, with the seam stated: `cmpSeg_reaches` is proved on
`cmpSeg cont`, the program that executes is `cmpSegmentProgram tail = cmpSeg 29 ++ tail`,
and the two differ at position `29`, which is exactly where the segment's last step
jumps.  So the composition is *not* a congruence of `exec`; it is a replay of the
chain against an abstract program agreeing with `cmpSeg 29` on `0…28` (§C10), and then
an induction that consumes that replay plus the re-entry once per comparison (§C11).

The two rounds' corrections are carried, not absorbed: §C9's `+4 → +5` (a terminating
loop pays the advance) and this round's `+5 → +6` (a *counting* loop pays the
accumulate, `scan_loop`'s shape — the row's verdict is `0 < hitCount`, so a count is
what the loop is for).  Per comparison: `cmpSegCost + 6 ≤ 20 + 9p`.

Nothing here touches `Statement.lean`, `KapilaAlgo.cost`, `D7.agrees`'s horizon
(residual (iv)) or `PayloadCarries` (residual (ii)'s named premise, still named).
-/
import Mathlib
import SubsetSumL25.Row.Statement
import SubsetSumL25.Row.KapilaDigitwise
import SubsetSumL25.Row.KapilaCmpSeg

set_option autoImplicit true
set_option maxHeartbeats 1600000

namespace SubsetSumL25.Row

open BigOSpeedrun.SubsetSum

'''


def main():
    gen = (LANE / "parts/c10_transfer_gen.lean").read_text()
    loop = (LANE / "parts/c11_loop.lean").read_text()
    out = PRELUDE + gen.rstrip() + "\n\n" + loop.rstrip() + "\n\nend SubsetSumL25.Row\n"
    OUT.write_text(out)
    print(f"wrote {OUT} ({len(out.splitlines())} lines)")
    names = [l.split()[1] for l in out.splitlines() if l.startswith("theorem ")]
    print(f"{len(names)} theorems")


if __name__ == "__main__":
    main()
