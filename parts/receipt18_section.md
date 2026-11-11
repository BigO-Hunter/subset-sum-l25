### Receipt

**`receipts/kapila-20261111T025151Z`** — gate `swapouts_delta60=0 free_pct=57`; build exit 0 in
**44.9 s**, which is a **replay** (the closure was already current from this round's own
from-scratch rebuilds) and is therefore *not* the compile of record.  The compiles of record are
the two from-scratch rebuilds: `KapilaCmpSegLoop`'s `.olean`/`.ilean`/`.trace` deleted and rebuilt
twice to the identical sha256 `68f20b76…21eb0e` (4 463 752 bytes) — the determinism double-compile
— and `KapilaRow`'s deleted and rebuilt to `b1ec5186…ab8dd9`.  Axiom banner exit 0, 247 lines, 231
`depends on axioms` lines, `axiom_banner_house_triple_only: true`.  The five new declarations:
`sum_range_shift` and `cmpLoopFuel_eq_sum` on `[propext, Classical.choice, Quot.sound]`;
`cmpLoopFuel_le_mul`, `cmpLoopFuel_le_tight`, `cmpLoopFuel_fits` on `[propext, Quot.sound]` — the
same pair as `cmpLoopFuel_le`, which is the marker of pure arithmetic.  No `sorryAx`, no
`native_decide`.  Lock: **DEVIATION, recorded** — bounded 240 s wait expired, build proceeded
UNLOCKED (`lock.acquired`, `summary.json`).  `head` at receipt time = `3c29c99`, the **peer's**
`jv1000` commit, which landed in this shared worktree during the round; my commit stacks on it.

### Measurements for the next author

1. **`rw` can close a goal, and then the next tactic errors "No goals to be solved".**  The
   successor step of `cmpLoopFuel_eq_sum` was closed by its three rewrites; the trailing `omega`
   was the only error in the round.  When a `rw` chain ends a proof, delete the finisher — do not
   add `try`.
2. **A detached build can still be killed.**  `start_new_session=True` (new process group) did
   not protect a `lake build` launched that way: the process vanished ~10 s in, leaving the
   `.olean.hash`/`.trace` written and the `.olean` absent, with **no error line** in the log.  A
   foreground shell call with a long timeout ran the same build to completion.  Trust the olean,
   never the trace.
3. **Lake replays cached *warnings*.**  A log full of `if_pos has been deprecated` lines from
   `KapilaCmpSeg.lean` means the dependency was **replayed**, not recompiled — the `⚠ [n/m]
   Replayed <Module>` lines are the tell, and the module you actually care about appears after
   them.  Reading the warnings as "it is compiling the deps" wastes a cycle.
4. **The last dependency step is the only one that costs.**  With the closure cached, the receipt
   build is 44.9 s (replay) while one module compiles in ~46 s and the whole `Row` closure from
   scratch is minutes under the fleet's load (140 at the time).  Delete-and-rebuild is the only
   compile evidence; the receipt says so in its own words now.

Next single action: **`PayloadCarries`** (`Row/KapilaBinSum.lean`) — the accumulation stage the
checksum program does not contain, and now the *last* named premise of the test/checksum path that
has a concrete obligation attached (the early-exit variant and the M-series goals are the other
residuals, both recorded as unproved/false-as-stated respectively).
