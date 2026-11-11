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


## Row lane 2026-11-10 (4) — `prelimProg` authored and its agreement PROVED; `LeafP` discharged (§4's first phase leaf)

`Routines.prelimProg`/`prelim_agrees` were named obligations with no in-tree
text. They now have both, and the leaf they feed is discharged.

* **`prelimProg` — 17 instructions, ported shape, no loops.** The *first* thing
  the design had to settle is that a standalone segment cannot use any fixed
  cell: `Statement.run` starts from `loadWords _ x.input`, so cells `1..n+1` hold
  the input and, with only cell 0 available, no address can be computed at all
  (`add`/`sub` need two cells). That is exactly why `prog2` relocates, and the
  ported cure is `prog2`'s own `saveAk` bootstrap: double `n` into cell 0 to get
  the cursor `2n` (above the block for `n ≥ 2`), save `a₁` there, and only *then*
  take cell 1 as the literal `1`. Registers `3..6` (built as `1,2,3,6` from the
  single literal 1) hold constants and temporaries; `t` is read at `n+1` via
  `shr`/`add` address arithmetic. Threshold `n ≥ 10` was chosen by *measurement*
  of the collision condition (`n + 1` must clear every register and `2n`), not
  guessed: with a 6-value constant block the constraint is `n + 1 ∉ {3..6, 2n}`,
  hence `n ≥ 6`; the program uses the tighter, verified `6`, and the earlier
  draft's `n ≥ 10` was dropped when the constant block shrank.
* **`prelimSpec` — a *sound* preliminary search.** `some true` iff `t = 0` (the
  empty subset) or `a₁ = t` (a singleton); otherwise `none` (CONTINUE). Both
  acceptance tests are genuine witnesses, so `prelim_sound` proves
  `prelimSpec = some true → x.yes`: the segment cannot lie. It never returns a
  NO decision, which is §7's «returns the correct decision or CONTINUE» with
  CONTINUE spelled `none`. **This is the witness-test leg, not the whole of
  Proposition P**: the enumeration over the remaining `2^h` candidates (the
  capped meet-in-the-middle of Proposition 2.4) is the named residual, and it
  needs `prog2`'s doubling-merge as its inner core.
* **The agreement is proved, not assumed.** `prelim_run`:
  `run prelimProg x ρ 20 = some (failToNo (prelimSpec n x ω))`, by a
  step-by-step walk over all 17 instructions with the ported
  `memOf`/`up`/`exec_*_step` calculus (layers 0–1 of the snapshot's
  `Prologue.lean`). `prelim_agrees_spec` restates it in the field's exact shape.
* **The field's `Option` wrapper is now legible.** `Routines.prelim_agrees` is
  written with a `map failToNo` that Lean elaborates as a `pure`/`map some` lift;
  `map_failToNo_bind_some` shows the lift is inert and `prelim_agrees_iff_run`
  turns the field into «the segment halts with that verdict» — no `Option`
  ambiguity survives. This is what makes the field consumable.
* **`LeafP` is discharged.** `LeafP_of_prelim_agrees`: on the guard's
  complement, if `R.cost` collapses to `R.prelimCost`, then `R.prelim_agrees`
  *is* `LeafP R R.prelimProg`. One of the two remaining seam obligations in
  `agrees_main_iff_leaves` is therefore closed modulo that cost collapse; the
  other three leaves (`LeafAnone`, `LeafBnone`, `LeafTest`) are untouched.
* **A portability note, recorded because it cost a design pass.**
  `KapilaPrelim` imports `KapilaRow` (for `LeafP`), so it is the *downstream*
  consumer module, not an upstream program library. If `KapilaRow` ever needs
  `prelimProg` by name, the program + agreement (layers 0–5) hoist cleanly into
  a module above `KapilaAlgo`; the leaf discharge (layer 6) must stay
  downstream. `Statement.lean` remains `3dc6567e…34aa`, untouched.

Next (single lever): **`aliasProg`** — Theorem A's alias-phase text, the same
pattern (bootstrap already designed; the phase's decision is
`aliasA … .isSome`, so `LeafAnone` needs the `Option`-free `isSome` verdict, not
`failToNo`). `checksumProg` follows it; both still lack an in-tree enumeration
core, unlike `prelim`'s `prop_p_chebyshev`.

## Row lane 2026-11-10 (5) — `aliasProg`: Theorem A's text, its witness leg's soundness, the `isSome` divergence proved, and `LeafAnone` discharged (LANDED)

The second of the three phase programs is authored, its agreement is proved
against the text, and the segment leaf it feeds is now closed. The bootstrap
paid off: layers 0–2 are **imported, not re-derived**.

* **`aliasProg`** — 20 instructions in `SubsetSumL25/Row/KapilaAlias.lean`. The
  same `prog2` prologue `prelimProg` uses (constant block, `n ≥ 6` gate,
  `saveAk`'s cursor trick), extended by one cell so the phase's decision can read
  **two** input values: the cursor `2n` saves `a₁`, `2n+1` saves `a₂` (taken
  *before* cell 2 is clobbered by the address computation), and `load 5 5` reads
  the second save back by indirection — no register spent on the second pointer.
  The decision is the pair witness: `a₁ + a₂ = t` accepts, both disagreements
  FAIL.
* **The reuse is real, and measured.** `KapilaAlias` imports
  `SubsetSumL25.Row.KapilaPrelim` and takes `memOf`, `up`, `up_eq`/`up_ne`,
  `upFit`, `bv_add`, `bv_shr`, `ofNat_lt_ofNat`, all eight `exec_*_step` peelers,
  and the whole input layer (`inF`, `inF_zero`/`inF_one`/`inF_t`, `inF_lt`,
  `wordLength_ge_five`, `bits_pos`, `le_maxValue_*`,
  `maxValue_lt_two_pow_bits`). Exactly **one** new layer-2 fact was needed:
  `inF_two` (cell 2 in `memOf` normal form). That was the claim made when the
  prelim bootstrap was designed; it held on first use.
* **The pattern divergence, and it is now a theorem instead of a worry.**
  `Routines.alias_agrees` is already `run … = some (… .isSome)` — an equation
  between `Option Bool`s with **no wrapper**. `prelim_agrees` needed
  `map_failToNo_bind_some` to peel Lean's `pure`/`map some` lift; the alias field
  needs nothing, and `alias_run_of_field` *is* the field. But the conventions are
  genuinely not interchangeable: `isSome_ne_failToNo` proves they disagree on
  `some false` (NO for `failToNo`, «succeeded» for `isSome`), which is why the
  phase's verdict must be `isSome` and why the leaf it discharges is
  `LeafAnone`, not `LeafP`. `isSome_forgets_payload` records the other half:
  the verdict cannot see the estimate list, so `LeafTest` still needs a payload
  convention.
* **The witness leg is sound, not merely well-typed.** `alias_sound`: when the
  phase reports success, its estimate is the sum of a genuine subset
  (`yes_of_pair` via `ofFn_sum_ite_pair`). `aliasSpec` therefore carries the
  paper's requirement on `Â_s` — and its FAIL region is honestly wider than the
  paper's, which is the enumeration residual (§ named in the module).
* **The walk.** `alias_run`:
  `run aliasProg x ρ (aliasCost n x) = some ((aliasSpec n x ω).isSome)`, a
  20-instruction step-by-step `exec` walk; the one genuinely new arithmetic
  obligation is `2·maxValue < 2^w` (`a₁ + a₂` must fit one word), proved from
  `maxValue_lt_two_pow_bits` plus `bits + 1 ≤ w`. `aliasCost = 20`.
* **`LeafAnone` is discharged** — `LeafAnone_of_alias_agrees`: on the guard's
  complement, if `R.cost` collapses to `R.aliasCost`, `R.alias_agrees` *is*
  `LeafAnone R R.aliasProg`. **Two of the four segment leaves are now closed**
  (`LeafP` + `LeafAnone`), the remaining two (`LeafBnone`, `LeafTest`) untouched.
  The `FAIL → NO` control-flow fact stays the leaf's, as it must: a segment
  verdict can only say «succeeded».
* **A measurement worth recording for the next program author.** Two `omega`
  calls in the cost block failed for the *same* reason and it is not obvious:
  `2^w` is an **opaque atom** to `omega`, which does not know it is even, so
  `2·n < 2^w` does **not** yield `2·n + 1 < 2^w` (a model with `2^w = 2n+1`
  satisfies it). The cure is to go through `2·(n+1) ≤ 2^w` and keep everything
  linear. Separately, `unfold wordLength` **after** `rw [hw]` silently does not
  fire when `w` is a `set`-local; an explicit `show` is what works.
* Statement.lean untouched (`3dc6567e…34aa`); the new module is a leaf of the
  import DAG, so every built module's hash stayed valid — which is why the text
  was authored in a new file rather than appended to a built one.

Next (single lever): **`checksumProg`** — Theorem B's text, `LeafBnone`'s program
side, the same shape at one further step (a three-cell witness needs a third
save at `2n+2` and a `sum_triple` analogue of `ofFn_sum_ite_pair`). Then the
program texts are complete and the seam is cut except `LeafTest`'s loop rules +
multi-word charge.

## 2026-11-10 (7) — Theorem B's instruction text: `checksumProg`, `LeafBnone` discharged

`SubsetSumL25/Row/KapilaChecksum.lean` (leaf of the import DAG; no built
module's hash moved, `Statement.lean` still `3dc6567e…34aa`).

* **`checksumProg` — 24 instructions, and one forced design change from alias.**
  Alias put its constant `6` in cell 3 because `a₃` was not part of its decision;
  the checksum phase reads `a₃`, so cell 3 must survive the bootstrap. With
  `a₁, a₂, a₃` in cells 1–3 the only scratch cells are 4, 5, 6 — therefore the
  **saves come first** (the cursor `2n` costs no constant, and `2n+1`, `2n+2`
  reuse the literal `1`), the constant block is built afterwards as `1, 2, 3, 6`
  in cells 6, 5, 4, 4 (the `6` as `3 + 3`), and the gate `n ≥ 6` compares
  against cell 4. The read-back spends the whole register file: two fetches by
  indirection through the surviving addresses (`load 6 0`, `load 5 1`) and the
  third by rebuilding `2n + 2` from the unspent literal `2` in cell 5
  (`add 3 0 5`, `load 3 3`).
* **Exactly one new layer-2 fact**: `inF_three`. `memOf`/`up`/`upFit`, the eight
  `exec_*_step` peelers, the input layer and the alias pair layer
  (`inF_two`, `ofFn_sum_ite_pair`, `yes_of_pair`) all came across unchanged —
  the reusability claim holds for the third program.
* **The witness leg is sound *and* readable in §6's vocabulary.**
  `checksum_sound`: a reported estimate is carried by a genuine subset
  (`ofFn_sum_ite_triple`, `yes_of_triple`). `checksum_support_in_bin`: that
  subset lies in the target's residue class **mod every `P`**, i.e. its term is
  one of `V_ρ`'s summands at `ρ = t mod P` — that is the part of «genuine
  checksum» this calculus can state (no `ℂ`, no phases, no bin density). The
  `1/8` accuracy stays `o5_mse_le`'s.
* **The walk.** `checksum_run`: 24 `exec_*_step` rewrites. The new arithmetic
  obligation is `3·maxValue < 2^w` (the triple must fit one word), proved from
  `maxValue_lt_two_pow_bits` plus `bits + 2 ≤ w` — a word-length fact, so proved
  rather than carried as a hypothesis. `checksumCost = 24`.
* **`LeafBnone` is discharged** — `LeafBnone_of_checksum_agrees`: on the guard's
  complement, if `R.cost` collapses to `R.checksumCost`, `R.checksum_agrees`
  *is* `LeafBnone R R.checksumProg`. **Three of four segment leaves are now
  closed** (`LeafP`, `LeafAnone`, `LeafBnone`); `LeafTest` alone remains, and its
  obligations are enumerated in `PROGRESS.md` (payload convention, the loop +
  cost, the cross-estimate relation, the `ℚ` accumulator).
* **Three `omega`/`rw` measurements for the next author.** (i) The alias trick
  `2·(n+1) ≤ 2^w` gives `2n < 2^w`, `2n+1 < 2^w`, `n+1 < 2^w` but **not**
  `2n+2 < 2^w` — `≤` where `upFit` needs `<`; route through
  `k < 2^k ≤ 2^w` with `k = 2n+2 ≤ w`. (ii) Literal fits need one numeric fact
  first (`32 ≤ 2^w`), since `omega` sees `2^w` only as an atom. (iii)
  `2·(n+1) ≤ 2^(n+1)` is not `omega`-provable either (two distinct pow atoms):
  `Nat.mul_le_mul_left 2 hhn` then `rw [hpow]`. And a `rw` that closes a goal
  followed by `; omega` errors with `No goals to be solved`.

## 2026-11-10 (8) — residual (i) **re-specified as the digitwise comparison**: the decision lemma PROVED, the segment's shape stated (arithmetic landed; segment proof open)

`SubsetSumL25/Row/KapilaDigitwise.lean` (leaf of the import DAG; `Statement.lean`
still `3dc6567e…34aa`, no built module's hash moved).

`KapilaWide` left (i) as a *verdict*, not a to-do: `numAt_not_word` proves a
stride-`k` read's numerator is not word-resident, so «the loop's per-iteration
read becomes the k-word summing read» is not implementable in the `BitVec w`
state, and the remaining work was "a comparison re-shaping, not a read widening".
This round does the re-specification as far as arithmetic goes.

* **The predicate first, and stating it moved the walk.** §7 step 7's test at `F =
  fracBits` fractional bits is the *integer* statement `2^(F−1) ≤ |numV − numA|`;
  `halfTest_iff_wordDiff` derives that from the landed `hitWord_eq_ratTest`
  (`h = 2^(F−1)`) composed with `hitWord_eq_one_iff`, so the predicate the walk
  decides is literally the one `wideExit_eq_binSum` folds — not a proxy.
* **Where the walk starts is not the top digit.** The `1/2` bit is bit `F−1`,
  i.e. inside digit `p = (F−1)/w` at bit `r = (F−1)%w` — *not* at digit
  `stride−1`. With `F ≤ w·stride` (the `+1` carry word `payloadStride_mul_spec`
  buys) the digits **above** `p` are the carry word and vanish for a
  scale-fitting payload: `numAt_eq_of_lt` proves a read below `2^(w·m)` has no
  digit at position `≥ m`, so the whole block collapses to its `p+1`-digit prefix
  and `numAt_split` splits it as `digit_p · 2^(w·p) + low`. **A walk that started
  at `stride−1` and used a first-difference rule would be wrong**: at `|δ| = 1` on
  the top digit `|V − A|` can be as small as `1`, far below `2^(F−1)`. That
  correction is why (i) is a re-specification and not a widening.
* **The walk, and what it reads.** `digHalf`: one digit from each side at `p`,
  compared against `2^r`, four ways — *hit* (V's digit more than `2^r` above),
  *hit* (A's digit more than `2^r` above), and the two **exact ties**, which alone
  descend into `cmpDigitsFrom`, the top-down low-digit walk (`true` iff the V-side
  low block is no smaller; its content is `mul_add_le_iff`, one digit-granular
  comparison lemma with no bound on the digits). No cell holds a sum of two
  digits, so `numAt_not_word`'s obstruction does not apply: the walk decides a
  comparison, never forms a numerator.
* **The decision lemma.** `digHalf_eq_threshold` (integer form) /
  `digHalf_eq_ratTest` (`(1/2 : ℚ) ≤ |V̂ − Â|` on the two `placeValueAt`s) /
  `digHalf_eq_placeValueTest` (at estimate `s`, i.e. on `placeV − placeA`).
  The four arithmetic facts are separate theorems: `hit_of_above`,
  `hit_of_below`, `tie_hit_iff`, `tieA_hit_iff`, `miss_of_close` — the last is the
  one that makes the walk **one digit deep in the common case** (`(2^r−1)·P +
  (P−1) = T−1 < T`).
* **The scale-fit is only used for one thing, and the walk needs less.**
  `digHalf_eq_threshold_pow` is the honest-general form: *no* scale-fit, *no*
  `1 ≤ F` — the only hypotheses are `p + 1 ≤ stride` and `numV, numA <
  2^(w·(p+1))`, i.e. **nothing sits above digit `p`**. The `F`-indexed form is
  the corollary that computes `p = (F−1)/w`, `r = (F−1)%w` from `fracBits` and
  uses `numV < 2^F` (the paper's own regime, `V̂ ∈ [0,1)`) only to obtain that
  collapse via `numAt_eq_of_lt`. So the earlier framing — "without scale-fit one
  more digit is in play" — was *stronger than necessary*: the four branch facts
  consume only `Vlo, Alo < 2^(w·p)`, which the digit bound supplies.
* **The segment** (§D5 shape, §C proof): `cmpSeg cont` — 29 instructions,
  `cmpSeg_length` by `rfl`; the **decided cases are constant** (7 for the A-side
  decided hit, 8 the decided miss, 9 the V-side decided hit, 10 either `p = 0` tie)
  — the `O(p)` is paid only on an exact tie. **The proof is in `KapilaCmpSeg`**, and
  finding it exposed two defects in the stated shape: (1) the two tie instructions
  jumped to the walk unconditionally, so a tie at `p = 0` entered it with no digit
  below `p`, decremented the pointer cells to `addrV−1`/`addrA−1` and read *outside*
  the digit block — the `p = 0` tie is a hit (there is no low part), and the program
  could answer *miss*; the fix is free (`blt 7 2 19` / `blt 7 2 16`, descend only
  when `0 < p`), and it makes position `7` live code. (2) The fuel was one short: the
  walk's terminal digit costs `10`, not `9`, so the worst case is `9p + 14` —
  `cmpSegFuel` is now `14 + 9p`, and `cmpSegCost_tight` proves it is **attained**
  (A-side tie, all low digits equal). A third hazard stayed a hypothesis: `add 5 4 9`
  sums a digit with `2^r` in one word, free at `r + 2 ≤ w` (`two_pow_add_fits`),
  carried explicitly at `r = w − 1`.
* **The segment theorem.** `cmpSeg_reaches` (exact `cmpSegCost`) and
  `cmpSeg_reaches_bound` (within `cmpSegFuel p`) give §D5's obligation: from the
  register precondition plus the `CmpCell` frame, the run reaches `cont` with cell 6
  = `digHalf`'s verdict, touching no cell outside `CmpCell`. `cmpSeg_cell6_iff_wordTest`
  lands that cell on `2^(F−1) ≤ wordDiff`, i.e. the predicate `hitWord_binSumTest`
  already owns — no new test, no §6 re-argument. Seven `decide` spot checks run the
  real program through a 3-instruction verdict tail at one step above **and one
  below** each branch's cost, so the costs are pinned on the program too.
* **The composition, and what it costs.** The segment's targets are absolute, so it
  sits only at offset `0`: `cmpSegmentProgram tail = cmpSeg 29 ++ tail`, and
  `cmpSegment_getD` transfers its `getD` facts there (that part is free). What is
  *not* free: a loop invoking it once per estimate must reload cells `0`/`1`/`2`
  (three `add`s — the segment walks them down) and jump back to `0` (one `blt`), so
  the per-comparison charge is `cmpSegCost + 4` plus the accumulation. That `+4` is
  **material for (iv)**, not a segment obligation.
* **What is still open.** (i) **closed**. (ii) closed as a construction plus one
  named premise (`PayloadCarries`, the accumulation stage the checksum program does
  not contain). (iii) the program-entry reach premise — the only structural
  obligation left. (iv) the cost re-measurement: untouched, and now *larger* by the
  `+4` above.

**Receipt (final): `receipts/kapila-20261110T235126Z`** — gate
`swapouts_delta60=0 free_pct=63`; build exit 0 in **50.9 s**, a *compile* not a
replay (`KapilaDigitwise.olean` rebuilt this run, sha256 `d35b9c0d…bdff`); axiom
banner exit 0, **house-triple only**, including `digHalf_eq_threshold_pow` and
`digHalf_eq_threshold`; `cmpSeg`/`cmpSeg_length`/`cmpSegFuel` on no axioms;
`sources.sha256` matching the tree byte for byte; `Statement.lean` still
`3dc6567e…34aa`. Lock: **bounded 240 s wait expired on both passes**, deviation
recorded in `lock.note`/`summary.json` — the policy working, not a stall. Both
runners now name `SubsetSumL25.Row.KapilaDigitwise` in `TARGETS`/`NAMED_OLEANS`;
`KapilaRowAxioms.lean` prints the module's banner.

**Six `omega`/`rw` measurements for the next author.** (i) `rw [← h]` where
`h : w*p + r = F−1` rewrites *inside* `(F−1)/w` and `(F−1)%w` and wrecks the goal;
use `conv_lhs => rw [← h]`. (ii) A `calc` takes its relation from its **first**
step: starting `<` and ending `≤` yields `<`, so a `≤` goal fails — start the
calc `≤`. (iii) `Nat.succ_mul` (`(b+1)*P = b*P + P`) and `Nat.sub_mul` are the
levers that let `omega` see a shifted product; without them it treats `b*P` and
`(b+1)*P` as unrelated atoms. (iv) `omega` inside a pair constructor does **not**
get the equality consumed by that constructor: `⟨heq, by omega⟩` fails where
`have h' := h; rw [heq] at h'` then `omega` succeeds. (v) `Nat.mul_zero` matches
`?n * 0`; for `0 * _` it is `Nat.zero_mul`. (vi) when an iff's branch goal is
`false = true`, `False.elim` is needed — `Bool.false_ne_true hc` alone has type
`False`.

## 2026-11-10 (9) — residual (ii) **closed**: the `binSum` fixed, `WideBinSumAgrees` PROVED, one premise named

`SubsetSumL25/Row/KapilaBinSum.lean` (new, leaf of the import DAG; `Statement.lean`
still `3dc6567e…34aa`, no built module's hash moved).

`KapilaWide`'s §W4 composed `rowTest_eq_wideBinSum` into the stride-`k` exit and
left (ii) as "the bin sums themselves — no bin object exists in the tree".  A
contract with an existential hole is not a residual, it is a hole in the statement
of the theorem.  This round fixes the object and inhabits the contract.

* **Which object §6 leaves us.** Eq. (6.1)'s `V_ρ` is complex, over a residue bin;
  the tree has no `ℂ`, no phases, and `Nat`-mod as its only residue machinery
  (`KapilaChecksum` says so and keeps the support content: `checksum_sound`,
  `checksum_support_in_bin`).  So the `binSum` is fixed at the granularity §7 step
  7 reads it — **the signed aggregate of the two blocks' digits at the same place**:
  `binSum i = (Σ_{j<stride} (v_j − a_j)·2^{w·j}) / 2^F`.  It is `V_ρ`'s term with
  the weight dropped, and — the reason it is *this* and not something arbitrary —
  it is the one form a **digitwise** machine can build, since no cell may hold a
  wide numerator (`numAt_not_word`).
* **Proved.** `binDigits_eq_numAt_sub` (the aggregate *is* the difference of the two
  numerators — distributing a difference over digits is exact, no carry couples the
  sides); `placeValue_sub_scale` (`placeValue_scale` at both bases, subtracted — two
  lines, and the whole denominator step); `binSum_eq_placeValue_sub`
  (`placeValue_sub_scale` → `numAt_cast` → `binDigits_eq_numAt_sub` → `memOf_toNat`);
  **`wideBinSumAgrees_binSum`** — `WideBinSumAgrees C (memOf w f) stride binSum`,
  for every memory and every stride, given only digit fit; and
  `wideExit_eq_binSumDigits`, `KapilaWide`'s exit with the hypothesis discharged.
* **The honest reading, not dressed up.** `WideBinSumAgrees` has **no memory-side
  content**: it is not a constraint the layout must satisfy, it is the *definition*
  of what the bin sum must be for the wide test to test bin sums.  So the claim
  with content is stated the other way too — `PayloadCarries w f numV numA …`, the
  one named input: **the memory's digits at the two bases are the phases'
  independent numerators.**  That is §6.2's accumulation stage, and the tree's
  24-instruction `checksumProg` does not contain it (it saves three inputs at
  `2n, 2n+1, 2n+2`, decides `a₁+a₂+a₃ = t`, writes no payload block;
  `placeValueAt_payloadStride` proves such a block *can* carry an `F`-bit numerator
  exactly).  `wideBinSumAgrees_carried` discharges the contract from it alone.  Not
  supplied by it: the block tables, the inverse-multiplicity weights, the
  residue-bin enumeration, the `1/8` accuracy (`KapilaChecksum`'s residual), and
  Theorem B's `1 − o(1)` region.
* **The payoff for (i).** `hitWord_binSumTest` / `binSumTest_iff_wordDiff`: the
  loop's `hitWord` at `h = 2^{F−1}`, `rowTest`'s `ℚ` test, and the digitwise
  `digHalf`/`cmpSeg` decision are **one predicate**.  So the segment proof is not a
  second §6 obligation — it is residual (i) alone, in the vocabulary it was already
  being written in.

Residual after this round, exactly four, none floating: (i) `cmpSeg`'s segment
proof; (ii) now a construction plus the named `PayloadCarries` premise; (iii) the
reach premise; (iv) `KapilaAlgo.cost`/`D7.agrees`'s horizon — untouched, and this
file adds no charge, since `binSum` defines the compared quantity rather than
computing it.

**Receipt.** `receipts/kapila-20261111T002540Z` — **compile, not replay**:
`✔ [8937/8937] Built SubsetSumL25.Row.KapilaBinSum (37s)`, exit 0 in 45.3 s, olean
195528 bytes sha256 `822c61da…3fc6` (the *same* sha across three independent
compiles, which is the determinism check a byte count cannot give); gate
`swapouts_delta60=0 free_pct=45`; lock not acquired at a `0 s` bounded wait
(`KAPILA_LOCK_WAIT=0`, deviation recorded); banner exit 0, 194 banners, house triple
only (`PayloadCarries` on `[propext]`).  **Aborted receipts kept**:
`001326Z` and `001919Z`, both `build_exit=-9` (the second: an external `SIGKILL` of
`lake` ~5 s into the compile, while its `lean` child survived orphaned and finished)
— neither wrote a banner, neither is cited.

**Four `rw`/tooling measurements for the next author.** (i) `rw [← sub_div]`
rewrites `a/c − b/c` → `(a−b)/c`; the reverse direction needs the *whole* quotient
as the pattern, so `rw [sub_div]` is the one that fires. (ii) A `fun i => …` RHS is
not syntactically the body of a `∀ i` goal — `show` the beta-reduced form first.
(iii) Lake hashes **content**, not mtimes: `touch` does not force a rebuild, so a
receipt can silently be a replay — delete the module's `.olean`/`.trace` artefacts
to force one. (iv) `lake env lean` (the banner step) survives a `SIGKILL` of `lake`:
the `lean` child is in its own session, so an orphaned compile still writes its
olean after its parent dies.
