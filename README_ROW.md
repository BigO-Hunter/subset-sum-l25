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
  agrees : ∀ n x ρ,
    run program x ρ (R.cost n x) = some (R.run n x (fun r => (ρ r).toNat))
```

Two fields, no correctness, no probability, no cost arithmetic. `agrees` is
the translation, outcome for outcome, at the abstract cost horizon: it carries
the instruction selection, the cell allocation, indirect addressing, balanced
trees, finite-precision dyadic arithmetic and the `cap`'s fail-fast, because
those are *what a program does* between step 0 and step `cost`.

The seam's shape is not speculative: the verified `α = 1/2` package
(`subsetsum-v2-snapshot`, `Race.bound : SolvedInTime (1/2)`) is a worked
instance of it — one `List Instr`, no advice, no dependence on `c`.

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
(8927 jobs)`, `build.exit = 0`, and

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

Write `D7.program` for the *fallback branch first*, not the whole algorithm:
`Routines.run` with `needsFallback = true` is §6.3's exact MITM, whose
`List Instr` twin already exists (`subsetsum-v2-snapshot`'s `prog2`, 17k lines
of glue, axiom-clean at `α = 1/2`). Pinning `D7.agrees` on the fallback branch
first converts the seam from "everything, at once" into a sequence of
per-branch obligations, each with a worked reference implementation — and it
immediately buys the guard's coverage, which is where `b ≤ n^c` and the
`10⁶⌈log₂(b+1)⌉ ≤ n` boundary live.
