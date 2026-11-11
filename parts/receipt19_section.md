## Round 21 — §C14: the stride tail as a program, and the estFuel reach

**State at the time of writing: the module is authored; the type-check verdict for the
second (post-fix) pass is PENDING.**  Read `/tmp/c14b.log` (probe_lean, lock wait 900 s)
and `/tmp/c14_final/` (build + double-compile + banner) before trusting anything below.

### What was built — `SubsetSumL25/Row/KapilaCmpSegStrideProg.lean` (§C14)

The D2b counter-role flip, as a program and not only as arithmetic.  The landed reload
(`cmpSegReload_couples_roles`, §C13) reloads the walk's digit position from the counter,
which is the digit address offset; at `stride = 1` those coincide, at `stride = k` they do
not.  §C14 separates them:

| cell | role | value |
|---|---|---|
| 13 | counter | `i·k + p` — advanced by `.add 13 13 16` (the STRIDE constant) |
| 16 | stride constant | `k` |
| 17 | digit-position constant | `p` — the walk reloads from HERE (`.add 2 17 7`) |
| 14 | walk limit | `blockLen·k + p` |
| 15 | accumulator | `acc + verdict` per comparison |

The six-instruction tail `strideTail` is pinned entry-for-entry by `sim_stride.py` **D7**,
which also runs it and measures `estFuel + 1` steps (the +1 is the halting step) and the
per-estimate `digHalf` accumulator.

### Theorems

* `cmpSegStride_getD` — positions 0…28 of the variant ARE `cmpSeg`'s: the prefix is untouched.
* `cmpSegStride_reaches_program` — §C10's reach transferred: the segment reaches 29 in
  exactly `cmpSegCost` steps with the verdict in cell 6.
* `cmpSegStride_tail_step` — the six tail instructions: 29 → 0 in exactly 6 steps, counter
  `c + k`, cell 2 back at `p`, cells 0/1 at the next estimate's addresses.
* `cmpSegStride_iter` — one comparison, end to end: `cmpSegCost + 6`.
* `cmpSegStride_loop` — **the estFuel reach**: m comparisons cost exactly
  `estFuel h (baseV + j·k) (baseA + j·k) k p r m` and accumulate `strideHits`.
* `strideHits_le` — the accumulator never exceeds m.

### Honest uncertainty at the time of writing

The **first** type-check produced 7 errors, all in the mechanical layer, all fixed:

1–2. `cmpSegStrideProgram` was written as a 3-way `++`; the parse is left-associative, so
   the `getElem?_append_left` pattern could not match.  Fixed with explicit parentheses
   `cmpSeg 29 ++ (strideTail ++ tail)`.
3.   A nested `rw [show … from by rw […]]` — pre-stated instead.
4.   `refine ⟨…⟩` on the nine-conjunct tail conclusion was one placeholder short.
5.   `cmpLoopFrame_fit` at `p := c` needs `c < 2^w` then `acc < 2^w` — `hpw` was the wrong fit.
6.   The accumulator bound in `cmpSegStride_tail_step` is stated on `acc`, not on `st 15`.

None of these touch a statement; they are plumbing.  **What has NOT been established yet:**
the second-pass verdict, the built olean, and the axiom banner.  Nothing in this file is a
claim that they landed — check the logs.

### Discipline bookkeeping

* `Statement.lean` sha256 `3dc6567e…34aa` — measured this round, unchanged.
* `sim_stride.py` extended, ALL ARMS PASS (D1–D7).
* No family file edited; the new module is a leaf of the import DAG and the JV1000
  composition lane's files were not touched.
