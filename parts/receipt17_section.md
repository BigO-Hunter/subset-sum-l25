
### Receipt

**Receipt `receipts/kapila-20261111T021745Z`** — gate `swapouts_delta60=0 free_pct=60`;
build exit 0 in **6.6 s**, and that is a **replay, not a compile**: the oleans were
already current because this session's own `lake build SubsetSumL25.Row.KapilaCmpSegLoop`
had produced them.  The receipt alone is therefore *not* evidence that the final bytes
compile, so the module's `.olean`, `.ilean` and `.trace` were deleted and it was rebuilt
**from scratch**: the same sha256 `63894d53…56228b`, 4 290 304 bytes.  That rebuild is
the compile of record.

Axiom banner exit 0, **242 banner lines**, `axiom_banner_house_triple_only: true`.  The
three load-bearing declarations are on the house triple —
`cmpSeg_reaches_program`, `cmpSeg_hitIter`, `cmpSeg_loop` each `[propext,
Classical.choice, Quot.sound]`; `cmpLoopFuel_le` is on `[propext, Quot.sound]` alone; the
definitions (`cmpHitTail`, `CmpLoopFrame`, `cmpLoopHits`, `cmpLoopFuel`) and the sixteen
`_gen` copies print "does not depend on any axioms" or a subset.  No `sorryAx`, no
`native_decide`; `sorry`/`admit` do not occur in the module at all.

`Statement.lean` is still `3dc6567e…34aa` and `KapilaCmpSeg.lean` still `6f00b833…6dc3` —
this round is purely additive, which is also why the landed module's olean hash did not
move.  `head` = `4da99e7`.  Lock: the bounded 240 s wait expired and the build proceeded
UNLOCKED, deviation recorded in `lock.acquired` / `summary.json` — the policy working,
not a stall.

**Peer coordination.**  `JV1000Quadrature.lean` and `JV1000Instance.lean` are the
**jv1000 mind's** files, both in flight in this shared worktree and both untouched here.
No manifest moves: `sources.sha256` is regenerated over `SubsetSumL25/Row/*.lean`, so
that mind's drift will show up in it and is that mind's business.

### Measurements for the next author

1. **`rw` does not see through a `def`.**  Writing the loop's program as
   `def cmpHitProgram := cmpSegmentProgram cmpHitTail` made every `getD` step fail with
   "did not find an occurrence of `(cmpSegmentProgram ?tail).getD (29 + ?i)`" while the
   term it names was literally in the goal.  Name the term, or `unfold` inside the proof.
2. **The `getD`-agreement hypothesis must take `i` explicitly.**  `cmpSegment_getD`'s `i`
   is *implicit*, so passing it where `∀ i, i ≤ 28 → …` is expected fails with an
   argument-position message that blames the wrong thing; pass
   `fun i hi => cmpSegment_getD tail hi`.
3. **`rw [hf n, hg n]` before the `by_cases` destroys the condition.**  Lean normalises
   `f' x = f' x` to `True` and collapses the `if`, so the subsequent `if_pos` matches
   nothing and the goal is left as `12 = if … then …`.  Case-split on the `f'` form
   first, then rewrite *both* sides with the derived `'` versions (`if_pos hc'`,
   `if_pos hc`).
4. **`Nat` addition's associativity is not definitional.**  `addrV + (p0 + 1 + m)` is not
   the goal's `addrV + (p0 + (m + 1))`; `by omega` at the `refine` slot costs nothing.
5. **The accumulator's word room is a hypothesis, not a detail.**  `upFit` needs
   `f 15 + f 6 < 2^w`, which `hfit 15` and `hfit 6` do **not** give — the first attempt's
   `omega` counterexample was exactly that sum overflowing.  Hence `acc + m < 2^w`, room
   for one increment per remaining comparison, and the loop carries it.
6. **`lake build` for this module is ~46 s once the dependencies are up**, and a
   foreground shell that kills at ~250 s makes a two-minute build look like a hang.
   Background it; the verdict is in the log, not in the exit of the wrapper.
7. **`induction m generalizing p0 acc st` reorders the IH's binders**, and the failure
   (`hfitH` expected to be `st 0 = addrV + (p0 + 1)`) reads as an insane argument order.
   Quantify the run *inside* the statement (`∀ m p0 acc st, …`), then `intro m` and
   `induction m`; the hypothesis order is then exactly the statement's.

Next single action: **residual (iv)** — restate `D7.agrees`'s horizon per comparison at
`20 + 9p` (`cmpLoopFuel_le` is the sum), decide the count-vs-early-exit variant (both
`+6`; the count is proved and is what `hitCount_pos_iff` reads), and keep
`PayloadCarries` as the *named* accumulation premise rather than re-proving absorption.
