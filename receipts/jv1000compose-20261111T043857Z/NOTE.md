# NOTE — the DONE receipt, and two things it does not prove by itself

This is the receipt of record for `SubsetSumL25.Row.JV1000Compose` (jv1000 row, C6 round 20,
the composition passage).  `STATUS`: `DONE … build_exit=0 banners=35`.

## 1. Lock deviation (recorded, not hidden)

`lock.note`: `acquired=False waited_s=240.3 bounded=240`.  The shared build lock
`/Volumes/Substrate-1/bigo/.build.lock` was held for the **entire** bounded window by
**another lane's project**: the holder was a `lake build StacksFrontier.AlgebraicGeometry.Chow.…`
process (a different tree, `leanprover--lean4---v4.34.0-rc2`), not a build in this worktree.
So the builds in this receipt ran **unlocked**, which is the deviation the lock exists to
prevent — and it is recorded here rather than left as a silent success.  Checked at the time:
no second `lake build` was running in `/Volumes/Substrate-1/bigo/kapila-row-lane`, so nothing
in this directory was compiled concurrently.

## 2. The runner's determinism step is weak; a real from-scratch double compile was run

The runner "touches" the source with `os.utime` and rebuilds.  Lake keys on content, so a pure
`utime` need not trigger a recompile — `build2_seconds = 6.1` against `build1 = 5.5` is the
signature of two *no-op* builds, and `identical=True` then says nothing.

A **genuine** from-scratch double compile was therefore run by hand, after the receipt:

| run | wall | olean sha256 | size |
|---|---|---|---|
| 1 (artifacts deleted first) | 52 s | `e3f40d9fac0ca02ad67ca41845eed8502aa31c53cc12031ee627fd010fb76b95` | 1 650 968 B |
| 2 (artifacts deleted first) | 40 s | `e3f40d9fac0ca02ad67ca41845eed8502aa31c53cc12031ee627fd010fb76b95` | 1 650 968 B |

Both runs are independent compilations of the same source, and both reproduce the runner's
traced hash — so the determinism claim holds on the real content, not only on the trace.

## 3. Banner

`axioms.txt`: exit 0, **35** `depends on axioms` lines, every one the house triple
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no `native_decide`, no other axiom.
`house_triple_only: true` in `summary.json`.

`head` at receipt time `faad906389efbb6d46beb23f77cfaa12151bc309` is the **peer Kapila lane's**
commit, not this round's: the worktree is shared, and this round commits after the receipt.
