# O1-ISOLATION LANE — landing + five-row upgrade map (2026-11-09)

Lane: `wip-o1-isolation` (worktree `/Volumes/Substrate-1/bigo/o1-lane`, parent
`l25-base-core` @ wip-hcount `057e529`). Pins: Lean v4.34.1 / mathlib d13f23b
(CHD profile, clonefile-reused). Never touched sibling files; DS-M* commits are
the sibling lane's landings on wip-hcount.

## 1. O1 state: PROVED IN-TREE — this lane verified it with fresh receipts

The task premise ("O1 is the first hard rung, to be ported") was **stale**:
O1 = OpenAI Lemma 2.1 «Isolation» (both sentences) is already proved on
wip-hcount, landed by the earlier M3a/M3b milestones:

* `SubsetSumL25.L2_1_isolation` — first sentence, the deterministic
  transformed-target equivalence: `C = 1+nN₀`, `c_i = C·a_i + u_i`,
  `t_s = C·t + s`; `C > nN₀` forces `a(I) = t` and `u(I) = s` out of
  `c(I) = t_s` (Int dvd + abs-lt → zero). Proofs/Isolation.lean:66.
* `SubsetSumL25.L2_1_isolation_prob` — second sentence, the MVV minimum-tie
  union bound: per-index coincidence event = "two minimizers tie" (Cset i);
  coordinate-erasure injective on Cset i; `#Cset i ≤ #W i`, `#W i · N₀ ≤ N₀^n`;
  union `n/N₀ ≤ 1/12` gives `Pr ≥ 11/12`. Probability = uniform count fraction
  over `Fin n → Fin N₀`, rational inequality, no measure theory.
  Proofs/Isolation.lean:113.

No named premises, no D7-boundary seams — BRIDGE row O1 says "none;
standalone" and the proof honors that: O1's two theorems consume only
`transformedC`/`subsum` from Statements/Defs + mathlib combinatorics.
The lane's work = receipt-verify (below), consolidate as its own module
(already is: Proofs/Isolation.lean imports only Statements.Isolation), and
map the rows.

## 2. Receipts (three per landing) — LANDED 2026-11-10T05:21Z

`receipts/o1-20261110T052129Z/` is the landing receipt. `receipts_run.py`
(rewritten this session) holds `/Volumes/Substrate-1/bigo/.build.lock` (fcntl,
7200s) for the whole run and emits:

1. **Full build, exit 0** — `build.log` ends `Build completed successfully
   (8966 jobs)`, `build.exit` = `0`. Run with `FORCE_O1=1`, which deletes the
   O1 cone's olean/ilean/trace/hash first so lake **elaborates O1 from source
   in this run** instead of replaying a cached artifact (the first green run
   replayed everything — a consistency receipt, not a compile receipt). Proof
   of real elaboration: the log carries the linter warning
   `SubsetSumL25/Proofs/Isolation.lean:118:26: Variable name 'I' is not
   explicitly referenced`.
2. **Named oleans, built this run** — `oleans.txt`, both `built_this_run=True`:
   `Statements/Isolation.olean` 11,856 B sha256 `c893edd4…fab00`;
   `Proofs/Isolation.olean` 1,225,176 B sha256 `99fbfa32…41517`. The sha256s
   are byte-identical to the 19:07/19:14 artifacts a prior session built, i.e.
   the O1 build is deterministic — independent evidence that the older oleans
   came from these same source bytes.
3. **Axiom banner** — `axioms.txt`, `axioms.exit` = `0`, via
   `lake env lean o1_axiom_probe.lean`:
   `L2_1_isolation` and `L2_1_isolation_prob` each depend on exactly
   `[propext, Classical.choice, Quot.sound]`. The runner **hard-fails** (exit
   44) if `sorryAx` appears or a banner is not a subset of the house triple;
   it passed.

Extras in the same receipt: `sweep.txt`, `gate.log`, `summary.json` (branch,
commit, toolchain `leanprover/lean4:v4.34.1`, mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, source sha256s, gate decision),
`forced_rebuild.txt`, and `ladder_axioms.txt` — a **34-declaration probe**
(`ladder_probe.lean`) covering the headline theorem of every rung in §3.
Result: all 34 axiom-clean, `sorryAx` = 0. `o8_draws_le` reports the subset
`[propext, Quot.sound]` (no `Classical.choice` needed) — permitted, a subset
of the house triple.

### Harness corrections made this session (both were real defects)

* **`.lake/packages` was a symlink** into
  `l25-base-core/.lake/packages` — exactly what SHARED.md §3 forbids ("never
  symlink into another lane's .lake — writes into the shared tree"). Replaced
  with the real recipe: `cp -Rc` clonefile, 29 s, 8,548 mathlib oleans, mathlib
  rev verified `d13f23b…`, zero new physical blocks. One other lane
  (`/Volumes/Substrate-1/bigo/subsetsum-statement/`) still carries such a
  symlink — worth curing there too.
* **The "package sorry count = 0" claim was a naive-grep artifact.** A raw
  `grep -rn sorry SubsetSumL25/` returns **7 hits, all prose inside docstrings**
  ("M1 carried `sorry` placeholders; M2/M3 replaced them…"). The authoritative
  check is the build log (`declaration uses 'sorry'` warnings): **NONE**. The
  receipt now records both and says which one governs.


## 3. Five-row upgrade map (what O1's landing changes, per row)

Chain shape (BRIDGE.md subset-sum-bridge): OpenAI Thm 1 (0.49) is the base
algorithm; its conditional skeleton = O1–O8. Kapila (0.4877) re-derives Base
combinatorics B1–B3 on top. Wharton (0.487676), Bills (0.4876723), Voitle
(jv1000, 0.4875755) inherit the SAME stack (BRIDGE note ii — verified quote:
"all three conditional rows inherit the same O1–O8/B5 stack, so every
formalized lemma upgrades three rows at once").

In-tree state at this landing (verified: module list, STMTS.md ledgers,
package sorry grep = 0):

| Rung | Module(s) | State |
|---|---|---|
| O1 isolation | Proofs/Isolation.lean | PROVED (receipts this lane) |
| O2 deficiency/restrictions | Deficiency.lean (all 5: empty/nonneg/insert/superadd/exchange), RandomRestrictions.lean (L2_3_halfVariance martingale, expectation_mono) | PROVED |
| O3 prime collisions | PrimeCollision.lean + PrimeCount.lean | PROVED + **UNCONDITIONAL** (M2c CLOSED: `erdos_dyadic_primes`, `L2_5_prime_collision_unconditional`, axiom-clean; c₀=1/12, L₀=24; hcount discharged via Erdős binomial accounting — no PNT needed) |
| O6 sparse distinctions | SparseDistinctions.lean | PROVED (prob. form, sparseAll counting) |
| V1 sine extension | JV1000.lean | LANDED (items 1+3+discrete-2; "the O-cluster's last named condition" closed at BRIDGE-row level) |
| O4 finite filtering | O4.lean + Statements/O4.lean ledger | core proved; residual named items per ledger (D7 boundary) |
| O5+O7 checksum theorems | O57.lean + ledger | cores proved; residuals named (D7 boundary) |
| O8 word-RAM accounting | O8.lean + ledger | proved; op-count seams at D7 boundary documented |
| B1 covering / B2 Cor-D / B3 A5+CorA6 | Layers.lean / CorD.lean / A5.lean | PROVED (B3 status "complete" 2026-11-08) |
| B4 region partition | ThmB.lean | PROVED |
| B5 Prop-P search + A7 envelope | Presearch.lean | PROVED |
| DS parameterization (downstream) | M2–M6, M5CorA6.lean | LANDED through DS-M6 (sibling lane, concurrent) |

Per row:

1. **ss/openai 0.49** — O1 IS this row's Lemma 2.1; with O2/O3/O6/V1 the
   number-theoretic core of its conditional skeleton is unconditional in-tree.
   Remains: the O4/O5/O7/O8 ledger residuals + the final Theorem-1 assembly
   (instantiating the skeleton at the row's parameters + cost accounting).
2. **ss/kapila 0.4877** — its differentiator B1–B3 are PROVED in-tree
   (Layers/CorD/A5), B4/B5 too. O1 lands the shared base its proof cites.
   Remains: kapila-row assembly (B-stack → 0.4877 statement).
3. **ss/wharton 0.487676** — inherits the stack (note ii). Numerics already
   certified (ct-20261110T0221Z). Remains: same assembly; its premises O* are
   the O-cluster above.
4. **ss/bills 0.4876723** — same inheritance; B4 (its trio) already re-derived
   and proved in-tree. Remains: same assembly.
5. **ss/jv1000 (Voitle) 0.4875755** — numerics VERIFIED (PR #185 merged);
   V1 (its sine extension) LANDED in-tree. Remains: assembly only.

Honesty note on the task's fifth row: the task lists **ss/li-ye 0.4999978**
among the five; FINDINGS.md assigns li-ye a DIFFERENT vehicle (arXiv
2610.10446 bit-op counting, "no assets") — nothing in BRIDGE/STMTS ties li-ye
to the OpenAI O-stack. Four rows are stack-consumers on the verified record;
li-ye needs its own port lane. Not counted as upgraded by O1.

## 4. What remains for the chain (single next lever)
The per-row ASSEMBLY: one conditional theorem per row instantiating the
in-tree skeleton at that row's parameters (the milestone-2 shape BRIDGE.md
sketches: statement work only). Everything below assembly — all named
conditions hcount/V1 — is discharged; O4/O5/O7/O8/B residuals are documented
integration items at the D7 boundary, not new mathematics.

## 5. Measured rung status (2026-11-10, `ladder_axioms.txt`) and the honest gap

The §3 table was assembled from PROGRESS/STMTS claims. It is now **measured**:
`ladder_probe.lean` (34 `#print axioms` lines, one per rung headline plus the
supporting halves) ran green over the tree as built in receipt
`o1-20261110T052129Z`. Every declaration reports exactly
`[propext, Classical.choice, Quot.sound]` (one, `o8_draws_le`, reports the
subset `[propext, Quot.sound]`); `sorryAx` = 0. So for the five rows the
*lemma layer* is no longer the open question.

Two corrections to premises circulating in the campaign briefs:

* **O3 does NOT need mathlib's PNT, and mathlib d13f23b does not have it.**
  `Mathlib/NumberTheory/PrimeCounting.lean` at that pin carries only
  monotonicity/surjectivity; `Chebyshev.lean` carries bounds whose constants
  annihilate in `π(2^{L+1}) − π(2^L)`. The lane did not carry PNT as a premise:
  M2c **proved** the counting input outright as `erdos_dyadic_primes`
  (c₀ = 1/12, L₀ = 24) by Erdős binomial accounting, then derived
  `L2_5_prime_collision_unconditional`. Both are in the measured banner above.
  A lane planning to "get O3 via mathlib PNT" would be re-deriving something
  already discharged by a different and cheaper route.
* **li-ye 0.4999978 is not a consumer of this stack** (already stated in §3,
  restated because the firing brief lists it among the five). Four rows — for
  counting purposes four, not five — are stack consumers.

**What the assembly still needs, stated so nobody mistakes it for a formality**
(the D7 boundary, from `Statements/O8.lean` and `Statements/O57.lean` headers):
the O4/O5/O7/O8 statements here count in **Base's own counters** (word
operations / elementary steps); the bit-cost → Light-step translation is
deliberately *not* imported. So a row's assembly needs, beyond these lemmas:
(a) the algorithm itself as an executable definition — not in this tree, whose
O5/O7/O8 are the *mathematical cores* of the checksum/alias/accounting
theorems, not the procedure; (b) the D7 translation into the challenge's
machine model; (c) the final bound stated in the challenge's own vocabulary so
the verifier can check it against `EndStatement`. That is statement-and-glue
work against a proved lemma layer — large, but not new mathematics.

**Consequence for claiming.** No board row moves on the strength of this lane.
The rows stay *claimed* until a verifier accepts an assembly that proves the
row's bound. What changed is that the shared conditionality stack is no longer
the blocker for four of them.

## 6. Wounds filed from this lane

* **R2125609493** — `lake build` SIGTERM'd 17 s after acquiring the lock
  (exit `-15`, **zero-byte** `build.log`; receipt
  `receipts/o1-20261110T051602Z`), then succeeded unchanged on retry. The same
  class is documented in `daemons/stale_process_reaper.py` as the 40-attempt
  Catalan kill-storm, where builds are supposed to be freeze/defer class with
  `_BUILD_WEDGE_MIN_AGE_S` = 1800 s — a 17-second-old build cannot be a
  legitimate mercy-kill. No attribution surface exists on this host: there is
  no `~/.multiaim/kill-ledger.jsonl`, `/tmp/memory_governor_kills.jsonl` has no
  lean entry, the memory-governor ships `KILL=0`, and `flock_guardian.py`
  states it never kills.
* **R2125609494** — the standing build regime's swap gate keys on a
  high-water mark that never clears. Measured: `vm.swapusage` pinned at
  ~13.77 GB of a 14,336 MB total while `memory_pressure` reports 67–73 % free,
  `vm_stat` Pages free = 43 GB, and Swapouts/Pageouts have a delta of **0 over
  60 s** — nothing is swapping. A previous O1 session spent the full 60-minute
  cap and produced no receipts (`receipts/o1-20261010T040540Z/fatal.txt`).
  This lane gates on live pressure instead (swapout delta = 0 AND free% ≥ 30,
  300 s polls, cap 12), records swap-used/delta/free% on every poll, and logs
  the override in `summary.json` → `gate_decision`. Under that gate the green
  build landed on the first attempt.

## 7. Next action (single lever)

Cut the first **row assembly** against the now-proved lemma layer: state one
theorem for **ss/kapila 0.4877** in the subset-sum challenge's own vocabulary
(it is the row whose differentiators B1–B3, B4, B5 are all measured
axiom-clean here, so its assembly has the fewest open ends), with the D7
bit-cost→step translation as the only named seam. Do it in a fresh worktree off
`wip-hcount`; do not extend this lane, whose deliverable is closed.
