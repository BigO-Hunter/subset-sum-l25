# `ss/kapila 0.4877` — the first row assembly

Lane: `wip-kapila-row`, worktree `/Volumes/Substrate-1/bigo/kapila-row-lane`,
cut from `l25-base-core` @ `wip-hcount` (`8a416ff`). Pins: Lean
`v4.34.1` / Mathlib `d13f23b` (the subset-sum profile; clonefile-reused from
`l25-base-core`, 27 s, no new blocks). Never touched sibling files
(`M7.lean` is the sibling's WIP and is *not* imported).

Primary source: `a-kapila/maths-proofs` @ 44c34961,
`subset-sum/PROOF_0.4877.tex`, sha256 `b397531c…298` (§2.2 parameters, §5
Theorem A, §6 Theorem B, §7 the algorithm and its running time).

## What this lane is

The campaign's next lever: turn the proved conditional stack (O1–O8, B1–B5,
measured axiom-clean by the O1 lane, receipt `o1-20261110T052129Z`) into **one
board row's statement + glue**. Not new mathematics. Three pieces, exactly as
the brief names them:

| piece | file | state |
|---|---|---|
| (a) the algorithm as an executable definition | `SubsetSumL25/Row/KapilaAlgo.lean` | **landed** |
| (b) the D7 bit-cost → `Instr`-step translation | `SubsetSumL25/Row/KapilaRow.lean` (`structure D7`) | **named seam**, documented |
| (c) the bound in the challenge's vocabulary | `SubsetSumL25/Row/KapilaRow.lean` (`kapila_row`) | **landed**, conditional on (b) + `CorrectAt` |
| — the challenge statement, byte-exact | `SubsetSumL25/Row/Statement.lean` | **landed** (sha256 `3dc6567e…34aa`, verifier commit `4cfb6db`) |
| — §1's exponent gap, proved | `SubsetSumL25/Row/KapilaAbsorb.lean` | **landed** |

### (a) The algorithm

`Routines` is a record of **computable** functions: the exact MITM fallback
(§6.3), Proposition P (§4), the isolation transform (§2.1), Theorem A's alias
phase sums (§5.2), Theorem B's checksum (§6). `Routines.run` is §7's dispatch
written executably — guard → fallback; tie weights and transform; Prop P;
prime and phases; Theorem A; Theorem B; the `|B̂_s| ≥ 1/2` test — returning a
`Bool`, no `noncomputable`, no `Classical.choice` in the data. The estimates
are `List ℚ` (the `nN₀+1` values at §6.2's `n²` fractional bits), which is what
makes step 7's test `decide`-able: the paper's «compare the sum of the squares
of the dyadic real and imaginary parts with 1/4» is integer arithmetic on
dyadics, not a real-number oracle.

`Routines.cost` is §7's «Running time» accounting in **Base's own counter**
(word operations), and `Routines.WithinEnvelope c` is §7's paragraph as a
proposition: on inputs with `b ≤ n^c`,
`cost ≤ K₀ · 2^{(τ₀+20ε)n + 2n^{0.7}} · (n+b+2)^K`.

### (b) The D7 seam — the one named assumption

```lean
structure D7 (R : Routines) where
  program : List Instr
  agrees_fallback : ∀ n x ρ, R.fallback n x = true  →
    run program x ρ (R.cost n x) = some (R.run n x (fun r => (ρ r).toNat))
  agrees_main : ∀ n x ρ, R.fallback n x = false →
    run program x ρ (R.cost n x) = some (R.run n x (fun r => (ρ r).toNat))
```

Three fields, no correctness, no probability, no cost arithmetic. The guard is a
`Bool` decided by `n` and `x` alone, so `D7.agrees` reassembles the single
equation from the two branch fields (`cases` on the guard is exhaustive) and
every consumer sees what it always saw. The translation, outcome for outcome, at
the abstract cost horizon, carries the instruction selection, the cell
allocation, indirect addressing, balanced trees, finite-precision dyadic
arithmetic and the `cap`'s fail-fast, because those are *what a program does*
between step 0 and step `cost`.

The seam's shape is not speculative: the verified `α = 1/2` package
(`subsetsum-v2-snapshot`, `Race.bound : SolvedInTime (1/2)`, ~17k lines across
24 modules) is a worked instance of the *fallback* half — one `List Instr`, no
advice, no dependence on `c`, proved segment by segment (`pro_segA23`, the
prologue walk, Phase A's sorted half-sums, Phase B's candidate × binary-search
cascade, then the budget composition).

### (c) The bound

```lean
theorem kapila_row (R : Routines)
    (hcorr : ∀ n x, 2 ≤ n → CorrectAt R n x)
    (henv : ∀ c, R.WithinEnvelope c)
    (hD7 : D7 R) :
    SolvedInTime (4877 / 10000 : Rat)
```

Everything except the two hypotheses is proved here:

* **§1's gap.** `tau0_eps_slack : τ₀ + 20ε + slack = alphaRow` (with
  `slack = 49/5000000 = 9.8·10⁻⁶`), then `runtime_absorb`:
  `2^{(τ₀+20ε)n} · 2^{2n^{0.7}} · (n+n^c+2)^K ≤ 2^{0.4877 n}` eventually — the
  paper's «the gap absorbs every factor `2^{O(n^{0.7})} poly(n+n^c)`», in Lean.
  Two legs: `eventually_rpow_le_mul` (sub-linear power below any multiple of
  `n`, via `tendsto_rpow_atTop`) and `eventually_pow_le_two_rpow` (a fixed power
  below any positive exponential rate, via `Real.isLittleO_log_id_atTop`).
* **The `BigO` at the literal.** `rowHorizon C₀ n = 2^(⌈0.4877·n⌉ + C₀)` and
  `rowHorizon_bigO : BigO (rowHorizon C₀) (4877/10000)` with
  `K = 2^(10000·C₀ + 10000)`. The `1` of the ceiling and §7's `K₀` are both
  absorbed into `C₀` (taken as `K₀ + ⌈K₀·envE N⌉ + 2`, so the finitely many `n`
  below the absorption threshold are covered without a finite-sup argument).
* **The tape/`count` transfer.** `count_congr` + `D7.agrees` turn `CorrectAt`'s
  `R.run` predicate into the program's `run` predicate, so the statement's own
  `Correct` follows at the same horizon.
* **The horizon glide.** `exec_eq_of_halted`: once `exec` returns `some b`,
  extra fuel does not change it. This is what lets *one* `T n` serve every
  random outcome, which is exactly what `SolvedInTime` demands.

### `CorrectAt` — the second hypothesis, and why it is a hypothesis

`CorrectAt` is §7's correctness paragraph, stated in the statement's own `tape`
vocabulary: at the procedure's horizon, ≥ 2/3 of the `2^(w·t)` prefixes give the
right verdict.

Every *mathematical* ingredient is measured axiom-clean in-tree: Proposition P
(`prop_p_chebyshev`), Theorem A part 1 (`thmA_part1_fail_le`, consuming
`cor_A6_per_alias` and the cap's Markov tail), Theorem B (B4's
`lem_B2_domination`, `row_errors_le_six_eps`), isolation
(`L2_1_isolation_prob`, 11/12). What is **not** in-tree is the composition
across this procedure's sample space — the union of §7's five failure events
and the identification of the abstract draws with the `Draws` stream. That
identification is the same exec-refinement boundary as `D7`. Stating it as a
hypothesis keeps the row's remaining obligation visible instead of burying it
in a proof term.

## Receipts

`receipts/kapila-<stamp>/`: `build.log` + `build.exit` (the row's module
closure: `lake build SubsetSumL25.Row.KapilaRow`), `oleans.txt` (named oleans,
size/mtime/sha256), `axioms.txt` + `axioms.exit` (`#print axioms` banner, hard
gate on `sorryAx` / `native_decide` / non-house-triple), `gate.log`
(live-pressure gate: `swapouts_delta60` and `memory_pressure` free %),
`summary.json`, `sources.sha256`, `head.sha`. Runner: `kapila_receipts.py`.

First landing: **`kapila-20261110T070814Z`** — `Build completed successfully
(8927 jobs)`, `build.exit = 0`; the axiom banner below. Forced rebuild (all four
row oleans deleted first, then rebuilt from the committed sources):
**`kapila-20261110T073335Z`** — `build.exit = 0`, 41.5 s, and every olean's
sha256 is **byte-identical** to the first receipt's (`Statement 81720a73…`,
`KapilaAlgo f99f3876…`, `KapilaAbsorb 2dc0d994…`, `KapilaRow 6e3d3295…`), i.e.
the assembly builds reproducibly from these sources.

```
'SubsetSumL25.Row.kapila_row'      depends on axioms: [propext, Classical.choice, Quot.sound]
'SubsetSumL25.Row.rowHorizon_bigO' depends on axioms: [propext, Classical.choice, Quot.sound]
'SubsetSumL25.Row.runtime_absorb'  depends on axioms: [propext, Classical.choice, Quot.sound]
'SubsetSumL25.Row.envE_absorb'     depends on axioms: [propext, Classical.choice, Quot.sound]
'SubsetSumL25.Row.exec_eq_of_halted' depends on axioms: [propext, Quot.sound]
'SubsetSumL25.Row.count_congr'     depends on axioms: [propext]
'SubsetSumL25.Row.const_le_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, no `native_decide`, every banner a subset of the house triple.

### Host observations (for the campaign, not for this lane's fix)

* Live-pressure gate opened first poll on every attempt
  (`swapouts_delta60 = 0`, free 57–66 %) while `vm.swapusage` sat at ~13 GB
  used — confirming R2125609494: the high-water number is not a gate.
* Two receipt attempts died on **unattributable kills** — `build_exit = -15`
  (SIGTERM, receipt `-070128Z`) and `build_exit = -9` (SIGKILL, receipt
  `-070449Z`) — while the build was making progress (first log line: 8932/8971
  replayed). This is the R2125609493 class, now observed with SIGKILL as well,
  which `trap "" TERM` cannot absorb. Host load average was 140–160 throughout
  (other lanes compiling); the surviving runs are the ones that started when a
  slot was free.
* Consequence for anyone reading receipts: `build_exit ∈ {-9, -15}` with a
  non-empty, progressing log is a kill, not a compile failure. Retry; do not
  "fix" the sources.

### Statement hash trap (measured)

The trusted statement has two byte-forms that hash differently and are both
correct: CRLF on disk `3dc6567e…34aa` (the verifier's checkout, and this lane's
copy) and LF git blob `80bc6d28…7517` (`text=auto`, and `subsetsum-v2-snapshot`'s
vendored copy). Compare content, not one literal.

## Filing

`submission/KAPILA_ROW_FILING_DRAFT.md` — form headings exact-order, canonical
bound string `4877/10000`, body ends at `Bound`, package layout, attribution.
**Not posted, and not postable yet**: posting a conditional theorem as
unconditional is the one failure this lane must not commit.

## What is next (single lever)

**Landed 2026-11-10** — `SubsetSumL25.Row.KapilaRow` (the seam) and the new
`SubsetSumL25.Row.KapilaGuard` (the arithmetic):

* **`D7` is cut per branch.** `program` plus two fields —
  `agrees_fallback` (the guard routes to §6.3's exact MITM, so the obligation
  *is* «`program` computes the MITM verdict at the MITM cost», which
  `fallback_agrees_iff` records mechanically) and `agrees_main` (the inputs the
  guard admits). `D7.agrees` reassembles the single equation every consumer
  already used, so `kapila_row`'s statement and proof are untouched;
  `D7.ofBranches` is the constructor.
* **The fallback branch's correctness is free.** `correctAt_of_fallback_det`:
  exactness there collapses `CorrectAt`'s two-thirds majority to «every tape
  agrees» (`count_const`), so §7's five failure events, the `2/3`, and the
  sample-space identification all live strictly on the main branch.
* **The guard's coverage is done.** `guardOk_eventually`:
  `∀ c, ∃ N, ∀ n ≥ N, ∀ b, b ≤ n^c → guardOk n b` — the statement's
  polynomial-bit class eventually satisfies §7's bit-guard, so the uncovered set
  is finite in `n` per `c` and is absorbed exactly like the small-`n` branch
  `kapila_row` already absorbs. Its one analysis input is
  `log2_mul_le_self : (Nat.log2 n) * k ≤ n` past `2k²`, from
  `two_mul_sq_lt_two_pow`.

**`agrees_main` — measured, both routes, and the cheaper one landed
(2026-11-10).** The two named routes were measured before any program was
written, and the measurement changed the shape of the obligation rather than
discharging it. Result: **route 2 is vacuous; route 1 is not yet well-posed; the
obligation is now four instruction-segment leaves, each with its worked
reference where one exists.**

* **Route 2 (prove the fallback shadow unreachable above the guard threshold) is
  vacuous.** `fallback_eq_false_iff` (`KapilaAlgo`) unfolds `agrees_main`'s own
  hypothesis: `R.fallback n x = false ↔ n_* ≤ n ∧ guardOk n x.bits`. The shadow's
  absence above the threshold *is the premise*, so proving it adds nothing to
  the main obligation. What coverage does buy is the location of the branch:
  `fallback_false_eventually` (`KapilaGuard`) turns `guardOk_eventually` into
  «on the routed class, every `n ≥ max N n_*` takes the main branch», so the
  exact fallback is confined to finitely many `n` per `c`.
* **Route 1 (write §7's main-branch program) is not yet well-posed.** Three of
  the main branch's four segments — `prelim` (§4 Prop P), `aliasA` (Thm A),
  `checksumB` (Thm B) — are *opaque fields of an arbitrary `Routines`*. No fixed
  `List Instr` computes an arbitrary total function `Instance n → Draws →
  Option Bool`, so no program can be written against the statement as it stands:
  `Routines` must first gain those three programs (and `mitm`'s) with their own
  agreement hypotheses. The missing lever is that refinement — not a longer
  proof of the same equation. (The `α = 1/2` reference is 17k lines for the
  *deterministic* MITM alone, so the program text was never the cheap half.)
* **Landed instead — the cut per instruction-segment.**
  `agrees_main_iff_leaves`: the single equation is *equivalent* to four leaves
  (`LeafP`, `LeafAnone`, `LeafBnone`, `LeafTest`) with **concrete verdicts** and
  no `Option` plumbing, one per §7 phase of the dispatch; `agrees_main_of_leaves`
  is the consumer form. `D7.agrees` + `kapila_row` carry it with no other
  change — `kapila_row`'s statement and proof are byte-untouched.
* **The test segment's worked reference** (the one segment §7 fully specifies):
  `rowTest_cons_cons` / `rowTest_nil_left` / `rowTest_nil_right` are the loop
  rules a scan over the stored estimate list needs, and `abs_ge_half_iff`
  (`|B̂_s| ≥ 1/2 ↔ |B̂_s|² ≥ 1/4` on `ℚ`) puts the in-tree test in the **paper's
  own squared vocabulary** — «the sum of the squares … exceeds 1/4».
* **Two requirements on `Routines` that the statement of `D7` hid**, now
  recorded in the module docstring: (i) the per-field programs above; (ii) the
  concrete program is a **multi-word** program — §6.2's estimates carry `n²`
  fractional bits while the statement's word is `w = 4(n+b)+⌈log₂((n+2)⁴)⌉ =
  O(n+b)` (at `b = 1` the two cross at `n = 7`), and the statement itself
  contemplates this («arithmetic exceeding these limits is implemented by
  multiple word operations and charged accordingly») — so `Routines.cost` must
  bound the **word-operation** count, which `WithinEnvelope` alone does not say.
* **Also landed:** `exec_mono_halted` (halting at `t` transports to `t + k`) —
  the direction a segment proof needs, so no segment has to count the whole run.

Next (single lever): **the `Routines` refinement** — reify `mitm`, `prelim`,
`aliasA`, `checksumB` as `List Instr` programs with per-field agreement
hypotheses, then discharge the four leaves against them (textbook-first:
`mitm` is the snapshot's `prog2`, then `LeafTest`, then the three phases).
Nothing else in the row is open: `CorrectAt` remains the documented correctness
assumption, and it is now provably *vacuous* on the branch the guard isolates.

## Row lane 2026-11-10 (3) — `Routines` reified: the first field's program landed, its seam field discharged, the multi-word charge proved absorbable (LANDED)

The refinement named as the blocker is now in the structure, and its first field
is *discharged* rather than merely named.

* **`Routines` carries programs and agreements.** Each decision field gained its
  instruction text and its agreement hypothesis: `mitmProg` + `mitm_agrees`,
  `prelimProg` + `prelim_agrees`, `aliasProg` + `alias_agrees`, `checksumProg` +
  `checksum_agrees`. The phase agreements are stated through `failToNo` (§7's
  own «If it fails, return NO») so that each is a claim about **its phase's
  verdict only** — which of `none`/`some false` happened is a control-flow fact
  the leaves supply, not something a segment's accumulator can carry. That is
  what makes each leaf have exactly one program premise.
* **`agrees_fallback` is no longer an assumption.** `Routines.mitm_agrees` has
  exactly the right-hand side of `fallback_agrees_iff`, so
  `fallback_agrees_of_mitmProg` proves the seam's fallback field from it, and
  `D7.ofMitmProg` assembles `D7` from `R.mitmProg` + the main branch alone. The
  seam is **two obligations, not three**. It is a *port*, not a re-derivation:
  `prog2`'s `smalln2_run2`/`smalln3_run2`/`bign_run2` are `mitm_agrees` at
  `α = 1/2`. (`mitm_agrees` is unconditional — stronger than the branch needs —
  because the fallback is deterministic and would halt on every input.)
* **`LeafTest`'s loop rules now *characterise* the test.** `rowTest_eq_of_rules`:
  any `f` satisfying nil/nil and cons/cons **is** `rowTest`. So an
  instruction-level proof of §7 step 7 never reasons about `rowTest` itself — it
  establishes three equations at the segment's exit. Verdict: `LeafTest` is
  reduced to (i) those three rules, (ii) control flow (reach the segment's entry
  with both estimate lists laid out at `n²` bits), and (iii) the multi-word
  charge. It is **not** discharged: no segment text exists yet, and (ii)/(iii)
  are the same seam the phases carry.
* **The multi-word charge is now a theorem, and the seam names its side.**
  `WithinEnvelope` speaks on the **word-operation** side (it counts `Routines.cost`,
  the paper's unit); `D7` is the translation into `Instr` steps at
  `w = wordLength n b`, and the two units meet only there. `wordOpFactor n = n²+1`
  bounds the expansion `⌈n²/w⌉+1` per dyadic operation (covers both regimes: for
  `b ≤ n`, `n ≥ 10` the word is narrower than `n²`, so the ratio exceeds 1; for
  large `b` it is 1). `withinEnvelope_wordop_absorb` proves the expansion is
  absorbed by raising the envelope's existentially quantified `K` by three — so
  multi-word arithmetic does **not** move the row's `2^{(τ₀+20ε)n}` exponent.
  (Correction recorded: the previous round's «`n²` stays ahead thereafter» is
  only true at fixed `b`; with `b ≤ n^c` the word can exceed `n²`, which is why
  the charge is stated as the uniform bound rather than as an always-on factor.)

Receipt: `receipts/kapila-20261110T150641Z` (build exit 0, five named oleans,
axiom banner ⊆ `[propext, Classical.choice, Quot.sound]` including the four new
declarations). `Statement.lean` still `3dc6567e…34aa`.

Next (single lever): **`prelimProg`** — Proposition P's instruction text, the
first phase leaf with both a landed mathematical core (`prop_p_chebyshev`) and a
landed program shape (`prog2`'s prologue/dispatch skeleton) to port. `LeafP` is
its consumer; `aliasProg`/`checksumProg` follow the same pattern.

