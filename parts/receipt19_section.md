## Round 21 — §C14: the stride tail as a program, and the estFuel reach

**VERDICT: GREEN.**  SubsetSumL25/Row/KapilaCmpSegStrideProg.lean type-checks with exit
0 — twice, from scratch, byte-identical (/tmp/c14_final/lean_rc.txt: LEAN_RC_1=0,
LEAN_RC_2=0, DOUBLE_COMPILE=identical).  The only diagnostics are two warnings (an
if_neg deprecation at :86; unused binder h14 at :156).  **The olean and the axiom banner
are NOT part of this landing** — the lake build was killed by the host (BUILD_RC=-15), so
no .olean was emitted and KapilaRowAxioms.lean failed closed on exactly that ('object
file … does not exist'), not on any axiom.  That is the residual.

### The D2b counter-role flip, as a program

The landed reload (cmpSegReload_couples_roles, §C13) reloads the walk's digit position
from the counter, which is the digit address offset; at stride = 1 they coincide, at
stride = k they do not.  §C14 separates them — six instructions, pinned entry for entry
by sim_stride.py **D7**:

| cell | role | set by |
|---|---|---|
| 13 | counter i·k + p, advanced by the STRIDE | .add 13 13 16 |
| 16 | stride constant k | — |
| 17 | digit-position constant p — the walk reloads HERE | .add 2 17 7 |
| 14 | walk limit blockLen·k + p | — |
| 15 | accumulator acc + verdict | .add 15 15 6 |

The tail names CELLS, not the stride: the instruction text is (k, p)-independent, which
is why one program serves every stride and the charge stays cmpSegCost + 6 per
comparison instead of growing with it.

### Theorems (all green)

* cmpSegStride_reads — the tail adds no load; the variant reads where the segment did.
* cmpSegStride_getD / _getD_tail — positions 0…28 are cmpSeg's, 29…34 strideTail's.
* cmpSegStride_reaches_program — **§C10's reach, transferred**: the segment reaches 29
  in exactly cmpSegCost steps with the verdict in cell 6.  One line — the transfer is
  free exactly because the prefix is untouched, and this module says so.
* cmpSegStride_tail_step — 29 → 0 in exactly 6 steps: counter c + k, cell 2 back at p,
  cells 0/1 at the next estimate's digit addresses, acc + verdict.
* cmpSegStride_guard_taken / _guard_exit — the loop back-edge at 0, or the exit at 35.
* cmpSegStride_iter — one comparison end to end: cmpSegCost + 6.
* cmpSegStride_loop — **the estFuel reach**: m comparisons cost exactly
  estFuel h (baseV + j·k) (baseA + j·k) k p r m and accumulate strideHits; with
  strideHits_le the accumulator never exceeds m.

### Honest bookkeeping

Two type-check passes were needed.  The **first** produced 7 errors, all plumbing, none in
a statement: the left-associative parse of a 3-way ++ broke two getElem?_append_left
patterns; a nested rw [show … from by rw […]]; a refine with one placeholder short on a
nine-conjunct conclusion; cmpLoopFrame_fit given the wrong fit at p := c; and an
accumulator bound stated on the wrong cell.  The **second** produced 2 (h15 already
consumed by subst; a missing z argument).  Both fixed; third pass green.

Statement.lean sha256 3dc6567e…34aa, measured this round, unchanged.  No family file
edited; the new module is a leaf of the import DAG; the JV1000 composition lane's
JV1000Compose.lean was not touched.  sim_stride.py ALL ARMS PASS (D1–D7).
