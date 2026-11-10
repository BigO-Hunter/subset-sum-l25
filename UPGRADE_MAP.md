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

## 2. Receipts (three per landing)

`receipts/o1-<TS>/`: (1) `build.log` + `build.exit` = 0 (full package,
8958-job shape); (2) `oleans.txt` — named
`SubsetSumL25/Proofs/Isolation.olean` + `Statements/Isolation.olean` with
sizes/mtimes; (3) `axioms.txt` — `#print axioms` banner on both theorems via
`lake env lean o1_axiom_probe.lean`, must be exactly
`'propext, Classical.choice, Quot.sound'` — plus `sweep.txt`
(sorry/native_decide grep = NONE; package sorry count = 0) and `summary.json`
(source shas, toolchain, mathlib rev, commit).

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
