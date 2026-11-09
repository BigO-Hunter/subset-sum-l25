# PROGRESS — subset-sum-l25 (L2.5 cheap-cluster campaign)

Pins: Lean v4.34.1, Mathlib d13f23b (subset-sum challenge profile). Build: `lake build` — green.
Prebuilt Mathlib lives in `.lake/packages/` (local-only, gitignored; copied from
`../snaky-conditional-lane/.lake/packages` — a complete d13f23b olean cache).

## Proved (axioms = [propext, Classical.choice, Quot.sound] — receipt-verified)

| Theorem | File | Note |
|---|---|---|
| `L2_5_prime_collision` | Proofs/PrimeCollision.lean | K = 1/c₀ explicit, L* = L₀; PNT input = hypothesis `hcount` |
| `L2_5_prime_collision_two` | Proofs/PrimeCollision.lean | via difference |
| `primeFactors_card_lt` / `badPrimes_le_card` / `badPrimes_le` | Proofs/PrimeCollision.lean | # distinct prime divisors < B |
| `L2_1_isolation` (first sentence) | Proofs/Isolation.lean | deterministic equivalence |
| `L2_2_deficiency_empty` / `_nonneg` | Proofs/Deficiency.lean | 1 ≤ |Σ(V)| ≤ 2^|V| |

## Sorries (8, exactly)

| Theorem | File:line | Missing obligation |
|---|---|---|
| `L2_1_isolation_prob` | Statements/Isolation.lean:33 | MVV minimum-tie argument: per-index tie prob ≤ 1/N₀, union bound ≤ n/N₀ ≤ 1/12 |
| `L2_3_halfVariance` | Statements/RandomRestrictions.lean:31 | martingale/exposure argument (hardest of M4) |
| `L2_3_expectation_mono` | Statements/RandomRestrictions.lean:37 | monotonicity via first-q-of-(q+1) coupling |
| `L5_2_sparse_distinctions` | Statements/SparseDistinctions.lean:38 | union bound of L2.5 over sparseCount n m vectors + count bound |

## Key facts for the next mind

* **No PNT in Mathlib d13f23b** — only Chebyshev (`Chebyshev.PrimeCounting.pi_ge`,
  `pi_le_log4_mul_div`); constants annihilate in π(2^{L+1}) − π(2^L). So L2.5's
  `hcount` premise (c₀·2^L/L ≤ #primesInterval L) is a named hypothesis. To
  discharge it later: Rosser–Schoenfeld formalization or a PNT import.
* **Fork renames found**: `div_le_div_iff₀`, `div_le_div_iff_of_pos_right`,
  `Nat.pow_lt_pow_iff_right`, `Finset.prod_pow_eq_pow_sum`,
  `Nat.prod_primeFactors_pow_factorization`, `Int.natAbs_eq_zero`,
  `Nat.mem_primeFactors` iff shape = Prime ∧ dvd ∧ n ≠ 0.
  `Int.coe_nat_sum`, `Int.abs_le`, `Finset.prod_const.symm`, `#{x | p}` notation,
  `Nat.pow_sum_distrib`, `Finset.prod_le_prod'` DO NOT work in d13f23b — use
  `Nat.cast_sum`, two-sided bounds, `by simp`, `Finset.prod_le_prod`,
  `Nat.pow_le_pow_right`+`Finset.prod_pow_eq_pow_sum`.
* **`positivity` on a metavariable slot can pick a wrong instance** — always
  state the type of intermediate `have`s that feed arithmetic lemmas
  (bit me twice: `mul_le_mul_of_nonneg_right hcnt (by positivity)` picked c₀).
* Anonymous-constructor ∃-patterns inside `Nat.dvd` mis-unify — use
  `Dvd.intro` or a stated type.
* Proved theorem bodies live in `Proofs/` and are REMOVED from `Statements/`
  (one declaration per theorem; statement-of-record = the proved one).

## Commits

1. `da3100b` Skeleton + pins
2. `bb636c0` M1: statements + STMTS.md, build green (12 sorries)
3. `a60faaa` M2 + M3a: L2.5 proved, L2.1(a) proved (axioms clean)
4. `223028a` M4 first slice: L2.2 empty + nonneg proved

## Next actions (in order) — after M4b (2026-11-07)

1. **M4c** `L2_3_halfVariance` / `L2_3_expectation_mono`: exposure/coupling
   over `uniformQSubsets n q`. No uniform-permutation API assumed available —
   consider transporting along a fixed bijection or direct two-point variance
   telescoping. Mono is the easier of the two (superadditivity of L2.2 now
   proved gives the monotone step).
2. **M3b** `L2_1_isolation_prob`: min-tie argument. Slice the space
   `(Fin n → Fin N₀)` by the coordinates off `i`; per slice ≤ 1 bad value of
   `u i` (the tie equation `u i + k_A = k_B`); injective-slice counting gives
   #{bad} ≤ n·N₀^{n−1}, then 11/12. Beware: ℕ-vs-ℝ cast facts must be stated
   for linarith; Finset mem_insert/mem_union rcases need the `.mp` lemmas
   FIRST in this fork (Quot.lift membership is not an inductive datatype).
3. **M5b** `L5_2_sparse_distinctions`: needs the candidate sparse vectors as a
   countable/Finset object — options: (a) inject (Fin n → Fin 3)-sparse
   embeddings, (b) restate over an explicit Finset parameter `S` with
   `#S ≤ sparseCount n m`, or (c) prove `badSparsePrimes ⊆ ⋃` over a
   filtered powerset. Then per-vector `badPrimes_le` + union bound.

---

# B1 (Base L3.1–3.3) — sub-campaign `base-core`, 2026-11-08

Branch `base-core`, worktree `/Volumes/Substrate-1/bigo/l25-base-core` (own branch;
main is owned by the parallel L2.5 workers — this lane adds files only and does not
edit shared statement modules beyond appending one import line).

Source: Base (a-kapila), `PROOF_0.4877.tex` §3, `maths-proofs@44c34961`
(sha256 `b397531c…`). Lemma table row B1 in `../subset-sum-bridge/BRIDGE.md`
(verdict «matches»). Credit: the lemmas are Base's; this package formalizes them.

## Definitions added (`Statements/LayerDefs.lean`)

`layerSupport c V j = (V.powersetCard j).image (subsum c)` (paper `Σ_j(V)`) and
`layerDensity c V j = |Σ_j(V)| / C(|V|,j)` in `ℝ` (paper `a_j(V)`). `Σ(V)`, `d(V)`
reuse `support`/`deficiency` from `Statements/Defs.lean`.

## Proved (axioms = [propext, Classical.choice, Quot.sound] — receipt-verified)

| Theorem | Paper | Note |
|---|---|---|
| `L3_1_covering_card` | L3.1 counted form | `T_x = Classical.choose`; per-`W` injection `x ↦ w(T_x∖W)`; pair count by `card_filter` + `sum_comm` |
| `L3_1_covering` | L3.1 | density assembly; `Nat.choose_mul` for `C(|V|,t)C(t,k) = C(|V|,t−k)C(|V|−t+k,k)` |
| `L3_2_sampling_card` | L3.2 counted form | per-`S` identity injection into `Σ_k(S)`; `card_filter_powersetCard_subset` for `C(|V|−k,s−k)` |
| `L3_2_sampling` | L3.2 | density assembly; `C(s,k)C(|V|,s) = C(|V|,k)C(|V|−k,s−k)` |
| `layerSupport_compl` | «Σ_{|V|−j}(V) = w(V) − Σ_j(V)» | both inclusions; `Finset.sum_sdiff` |
| `L3_3_good_layer` | L3.3 existence | layers cover `Σ(V)` (`card_biUnion_le`), pigeonhole (`exists_max_image`), complement to `t = min j (|V|−j)` |
| `twoPow_neg_deficiency` | — | `2^{−d(V)} = |Σ(V)|/2^{|V|}` via `Real.rpow_sub` + `rpow_logb` + `rpow_natCast` |
| `L3_3_good_layer_density` | L3.3 «in particular» | `Nat.choose_le_two_pow` + two `div_le_div_of_nonneg_*` steps |

**Zero sorries in this lane's files.** The two remaining package sorries are the
pre-existing L2.5-cluster ones (`L2_3_halfVariance`, `L5_2_sparse_distinctions`).

## Fork gotchas hit here (add to the list above)

* `Finset.card_filter (p) (s) : (s.filter p).card = ∑ i ∈ s, if p i then 1 else 0`
  — the clean way to move between a filter cardinality and a double sum.
* `Finset.sum_const` then `nsmul_eq_mul` then `Nat.cast_id` — the last step is
  required when the sum lives in `ℕ` (the `↑n * a` display is not closed by
  `simp`), e.g. `∑ x, C = |s| * C`.
* `Finset.card_filter_powersetCard_subset` gives `C(|t|−|s|, n−|s|)` directly —
  no need to build the "containing" filter by hand for L3.2.
* `div_le_div_iff` does not exist; it is `div_le_div_iff₀` (needs both
  denominators positive).
* `push_cast` silently does nothing on some `↑(n+1) * ↑m` shapes — use
  `Nat.cast_add, Nat.cast_one` explicitly (bit twice).
* `dif_pos` is deprecated in favour of `dite_eq_left`, but still works for the
  representative-choice idiom `simp only [rep]; rw [dif_pos hex]`.
* `le_or_lt` / `le_of_not_le` are absent; use `by_cases` + `omega`.

## Commits

1. `b7a6192` M1: verbatim statements + layer defs, STMTS.md B1 section
2. `47d9cc1` M2: L3.1 (covering) proved
3. M3: L3.2 + L3.3 proved (this commit)

## Next actions (B-core lane)

1. Merge `base-core` into `main` once the L2.5 workers land (additive, no
   conflicting edits beyond the two import lines in `SubsetSumL25.lean`).
2. Next BRIDGE rung after B1–B3: **B2 = Base Corollary D** (averaged small
   layer) — it consumes L3.1 + L3.2 + L3.3 directly, with the hypotheses
   `2k ≤ σ`, `2σ ≤ v+2k`, `v ≤ |M|`, `C(σ,k)C(v,k) ≤ 2^v` (BRIDGE appendix row
   B2, one cell corrected there). Then **B3 = Base Lemma A5** (per-trial hit
   probability via the second prime `P′`, needs `L2_5_prime_collision` from this
   same package — already proved).

---

# B2 (Base Corollary D) — sub-campaign `base-core`, 2026-11-08

Same worktree/branch (`base-core`), continuing the B1 rung. Source re-verified
against the primary text (`PROOF_0.4877.tex` §3, lines 254–278,
`maths-proofs@44c34961`): the corollary's hypotheses and conclusion match
BRIDGE appendix row B2, including the correction recorded there — **`S` is a
uniform σ-subset of `M`**, not a «half»; σ = m/2 holds only in-application.

## Proved (axioms = [propext, Classical.choice, Quot.sound] — receipt-verified)

| Theorem | Paper | Note |
|---|---|---|
| `Base_cor_D` | Corollary D | per-`V` claim + `expect_le_expect` + `expect_powersetCard_powersetCard` |
| `Base_cor_D_case_ge` | case `t ≥ k` | `layerDensity_ge_of_card` + `L3_1_covering` + pointwise `L3_2_sampling` + `expect_powersetCard_sdiff` |
| `Base_cor_D_case_lt` | case `t < k` | `choose_le_choose_of_two_mul_le` + `twoPow_neg_deficiency` + `one_div_choose_le_layerDensity`; the hypothesis `C(σ,k)C(v,k) ≤ 2^v` is used **only** here |
| `one_div_choose_le_layerDensity` | inline («Σ_k(S) is not empty») | the `1/C(σ,k)` floor |
| `choose_le_choose_of_two_mul_le` | inline («C(v,t) ≤ C(v,k)») | iterates `Nat.choose_le_succ_of_lt_half_left` over `k − t` |
| `choose_mul_choose_swap` | — | `C(N,a)C(N−a,b) = C(N,b)C(N−b,a)`, two `Nat.choose_mul` + `Nat.choose_symm` |
| `expect_powersetCard_powersetCard` | «a uniform σ-subset of a uniform v-subset of M is uniform» | `card_filter`/`sum_comm`/`card_filter_powersetCard_subset` + `Nat.choose_mul` |
| `expect_powersetCard_sdiff` | «when W is uniform, S' is a uniform σ-subset of V» | same, with `{W : S ⊆ V∖W} = (V∖S).powersetCard p` and `choose_mul_choose_swap` |
| `layerDensity_ge_of_card` (B1 refactor) | Lemma 3.3 «in particular» for a GIVEN `t` | lets both B2 branches dispatch on the *same* `t` |

**Zero sorries in this lane's files.** Package-wide the two pre-existing L2.5
sorries remain on `main`'s lane (integrated there as proved; this branch
predates that integration and does not touch those files).

## Nonemptiness accounting (the rung's known risk)

`Finset.expect` of an empty finset is `0`, so a weakened size hypothesis would
degenerate an average silently. Here: `M.powersetCard v` is nonempty by the
paper's own `v ≤ |M|`; `M.powersetCard σ` by `σ ≤ v` (derived in-proof);
`V.powersetCard σ` by `σ ≤ |V| = v`; and the two structural lemmas carry
`p ≤ M.card` resp. `p + q ≤ V.card` as explicit hypotheses. `Base_cor_D_case_lt`
also needs `(V.powersetCard σ).Nonempty` for `Finset.expect_const` — supplied
explicitly.

## Fork gotchas added here

* `Finset.mem_sdiff` is **not** `And`-defeq in this pin (`Quot.lift` membership):
  `⟨ha, hb⟩` fails where `a ∈ s \ t` is expected — use `Finset.mem_sdiff.mpr`.
  Same for projections: `(h ha).1` fails, `(Finset.mem_sdiff.mp (h ha)).1` works.
* `rw [Finset.card_powersetCard]` rewrites **one** occurrence per listing; with
  two `#(powersetCard _ _)` in the goal, list it twice (or use `show`).
* `div_eq_div_iff` matches the denominator *product order* syntactically —
  `mul_comm` must run before it if your identity has the factors flipped.
* `linear_combination` needs the sign that matches the goal's side orientation;
  a correctly-proved identity can still need `-coeff * h`.
* `Nat.le_induction` carries a dependent motive `P : (n) → m ≤ n → Prop`, which
  is awkward for bounded monotonicity — plain induction on `k - t` is simpler.
* `Nat.choose_le_choose` is monotonicity in the **bottom** argument; the
  right-argument monotonicity must be assembled from
  `Nat.choose_le_succ_of_lt_half_left`.

## Commits

1. `1161958` M1: statement verbatim + scaffolding stubs + STMTS.md B2 section
2. `1598948` M2: the `t < k` floor (`1/C(σ,k)`) + branch assembly
3. M3: nested averaging + case `t ≥ k` + Corollary D (this commit)

## Next actions (B-core lane)

1. **B3 = Base Lemma A5** — per-trial hit probability `≥ 2^{−g_M} n^{−6}` via
   the second prime `P′`; its (F4) input is `L2_5_prime_collision`, already
   proved in this same package (B1's `Proofs/PrimeCollision.lean`), so the
   cross-lane dependency is satisfied without waiting on `main`.
2. Then B4 (Bills' `Regions`/`RowMargins` template) and B5, per BRIDGE.
3. Merge `base-core` when the L2.5 lane's `main` settles; conflicts limited to
   the appended import lines in `SubsetSumL25.lean`.

---

# B3 (Base Lemma A5 + Corollary A6) — sub-campaign `base-core`, 2026-11-08

Same worktree/branch. Source re-read in full: `PROOF_0.4877.tex` §5.4–§5.6
(lines 380–545), matching BRIDGE appendix row B3 («matches»).

**Scope decision (documented, not hidden):** Lemma A5 quantifies over the
*algorithm* (`D_s`, keys, classes, records, the trial procedure, `F`, `P′`,
`j′`); this package has no algorithm. As on every rung of this ladder, the
deterministic algorithm facts (Step 2 sign identity, Step 5 «a hit is
recovered») are **named hypotheses**, and the mathematical content is proved.

## Proved (11 declarations; axioms = [propext, Classical.choice, Quot.sound])

| Theorem | Paper step |
|---|---|
| `two_pow_neg_gM` | §5.4 `2^{−g_M} = E_V 2^{−d(V)}` (needs `v ≤ |M|`: empty expect = 0) |
| `middle_choose_div_two_pow_ge_inv` | Step 1 arithmetic (see correction below) |
| `powerset_expect_ite_card` | Step 1 identity (conditioning on `|F| = σ`) |
| `expect_bad_indicator_ge` | Step 3 (deleting bad sets costs ≤ their probability) |
| `good_hit_expect_ge` | Step 3 assembly — **the Corollary D consumer** |
| `expect_dvd_eq_badPrimes` | «Pr[P′ ∣ D]» = `badPrimes`/`#primesInterval` |
| `pair_collision_le` | Step 4's (F4) instance — **the `L2_5_prime_collision` consumer** |
| `lem_A5_product` | Step 6 multiplicative chain |
| `lem_A5_threshold` | Step 6 explicit threshold («does not depend on I,s,P,M») |
| `cor_A6_per_alias` | Cor A6 per alias: `(1−p)^T ≤ e^{−1}` for `Tp ≥ 1` |

## Sorries (3, all Step-4 residue machinery)

| Theorem | Missing obligation |
|---|---|
| `collisionPairs_expect_le` | expand `collisionPairs` as a sum of `#pairs · indicator` over `W.product W` and swap the two finite sums (`Finset.sum_comm`), then apply the per-pair hypothesis; mine the `|W|²` factor from `Finset.sum_const` |
| `occupied_ge_card_sub_collisions` | representative argument: for each `y ∈ W.image (x % p)` pick a representative via `Finset.choose`; the non-representatives (`|W| − #image` of them) inject into the colliding ordered pairs |
| `hit_prob_eq_occupied` | bijection `{j ∈ range p : ∃ x ∈ W, x % p = ↑j}` ↔ `W.image (x % p)`, using `Int.emod_nonneg`/`Int.emod_lt_of_pos` to keep residues in `[0,p)` |

## Two statement defects found while proving (both corrected)

1. **«C(m,σ)2^{−m} ≥ 1/(m+1)» is false for arbitrary σ** (m=4, σ=0 gives
   1/16 < 1/5). It holds at a *maximising* layer, and the paper's σ is the
   middle one by (S1)–(S3); the lemma is therefore stated at `m/2`, where
   `Nat.choose_le_middle` + pigeonhole give it.
2. **`good_hit_expect_ge` needed `σ ≤ |M|`.** Without it `M.powersetCard σ` is
   empty, `expect` is `0`, and the statement is *false* (its RHS would be `0`
   while `2^{−g_M}/(2(v+1)) > 0`). This is exactly the
   empty-expect-degenerates trap; the hypothesis is now explicit.
   Same audit run on the others: `collisionPairs_expect_le` is still true when
   `primesInterval L = ∅` (RHS ≥ 0), `powerset_expect_ite_card` holds for every
   σ (both sides 0 when σ > |M|, proved as a case split).

## Fork gotchas added

* `fun p => (p : ℤ) ∣ D` is a **binder ascription**, not a cast: it makes the
  lambda's variable `ℤ` and coerces the Finset (`do let a ← …; pure ↑a`).
  Write `fun (p : ℕ) => (↑p : ℤ) ∣ D`.
* `field_simp` can leave `↑(2^m)` vs `2^m`; follow with `push_cast; ring`.
* `linarith` will not relate `G/(2*(v+1))` to `G/(v+1)` — supply the `field_simp;
  ring` identity as a hypothesis.
* `linarith` with `Finset.expect …` atoms is brittle; `le_trans` chains of
  separately-proved inequalities are more robust.
* `pow_le_pow_left` does not exist in this pin: `pow_le_pow_left₀`.

## Commits

1. `8555acd` M1: A5/A6 statements verbatim + STMTS.md B3 section
2. `ef2f5ba` M2: 8 spine lemmas proved
3. M3 (partial): Step 1 identity + Step 3 assembly (Cor-D consumer) proved;
   3 Step-4 residue sorries remain, obligations named above

## Next actions (B-core lane)

1. Finish the 3 Step-4 sorries (each is a self-contained Finset counting
   argument; `occupied_ge_card_sub_collisions` is the hardest, needing
   `Finset.choose` representatives).
2. Then assemble the headline conditional `Base_lem_A5` (good-hit probability
   ≥ `2^{−g_M}n^{−6}` via `good_hit_expect_ge` → `lem_A5_product` →
   `lem_A5_threshold`) with Step 5 as the transfer hypothesis.
3. Then B4 (Bills' `Regions`/`RowMargins` template) and B5, per BRIDGE.

---

# B3 COMPLETE (Base Lemma A5 + Corollary A6) — 2026-11-08

All 14 declarations of the B3 lane are proved; `Statements/A5.lean` now holds no
`sorry` (it is a pointer file). Build green (8943 jobs).

## The three Step-4 residue lemmas (closed in this milestone)

| Theorem | How |
|---|---|
| `hit_prob_eq_occupied` | `card_bij` between `{j ∈ range p : ∃ x ∈ W, x % p = ↑j}` and `W.image (x % p)`, with `Int.emod_nonneg` / `Int.emod_lt_of_pos` keeping residues in `[0,p)` and `Int.toNat_of_nonneg` giving the inverse |
| `occupied_ge_card_sub_collisions` | one representative per class via `Finset.Nonempty.choose` (**not** `Finset.choose` — classes are not singletons, so `∃!` fails); `card_filter_add_card_filter_not` splits `W` into representatives (bijective to the image) and non-representatives, and the latter inject into the colliding ordered pairs via `x ↦ (x, r (f x))` with `Int.emod_eq_emod_iff_emod_sub_eq_zero` + `Int.dvd_iff_emod_eq_zero` |
| `collisionPairs_expect_le` | `card_filter` turns `collisionPairs` into a sum of indicators over `W.product W`, `sum_comm` swaps the two sums, each inner sum is bounded by the per-pair (F4) hypothesis, `sum_const`+`nsmul_eq_mul`+`card_product` give `\|W\|²`; needs the new hypothesis `0 ≤ K₀` (the paper has `K₀ ≥ 1`) so the diagonal pairs' zero contribution is bounded |

## The headline chain

`Base_lem_A5` (in `Proofs/A5.lean`): `2^{−g_M}n^{−6} ≤ Pr` from
`hQ` (Steps 1–3 via `good_hit_expect_ge`, the Cor D consumer), the product chain
(`lem_A5_product`), the explicit threshold (`lem_A5_threshold`), and `hstep5`
(Steps 4–6: the hit probability times the `1/2` / `1/(m+1)` / `1/(8K₀n²)`
factors, transferred to the trial's success probability — the paper's
«a hit is recovered» plus the independence of the `F`, `P′`, `j′` draws).

## Receipts (freshly measured, all 14)

Every one: `#print axioms` = `[propext, Classical.choice, Quot.sound]` — including
`Base_lem_A5`, `collisionPairs_expect_le`, `occupied_ge_card_sub_collisions`,
`hit_prob_eq_occupied`. No `native_decide`, no new axioms.

## B3 statement ledger (what the conditional form means)

Proved outright: Steps 1, 3, 4, 6 and Corollary A6. Named hypotheses (never
`axiom`s): Step 2 (`hgood`: on a good `S`, `B_S ≥ a_k(S;c^I)·C(σ,k)`) and Step 5
(`hstep5`). The algorithm (`D_s`, keys, classes, records) is not formalized
anywhere in this package; that is the honest boundary of the rung and is
recorded in `STMTS.md` §B3.

## Fork gotchas added

* `(j : ℤ)` / `(p : ℤ)` in a *lambda binder* is a type ascription, not a cast —
  it silently retypes the Finset's element type (three occurrences burned here;
  the fix is `fun (j : ℕ) => ... (↑j : ℤ)`).
* `Finset.card_bij`'s index function is dependent: write
  `fun (a : α) (_ : a ∈ _) => ...`; the `_` must NOT be ascription-typed to the
  wrong finset.
* `Finset.choose` needs `∃!`; for one-representative-per-class use
  `Finset.Nonempty.choose` / `.choose_spec`.
* `Finset.mem_product` / `Finset.card_product` do not `rw` cleanly against a
  goal written with `Finset.product`; use them as explicit applications
  (`Finset.mem_product.mpr`, `Finset.card_product W W`).
* `field_simp` often closes the goal by itself — a following `ring` then errors
  with "no goals"; use `try ring`.
* `convert … using n <;> field_simp <;> ring` is fragile for denominator
  reshuffles; a `calc` with the reshuffles as separate `field_simp` steps is
  robust.

## Next action

**B4 — Base Theorem B region analysis** (BRIDGE attack order item 4, "B4 via
Bills' `Regions`/`RowMargins` template"; the same rung the lemma table calls
HIGH-but-mechanical given interval balls, with the 10 regions ρ₀..ρ₉ at
Γ-relative breakpoints 1, 1.25, 1.6, 2, 2.6, 3.5, 5, 8, 15, ∞ and 430
certificate rows). B5 (preliminary search + cost accounting) is the other
remaining B rung; O8 (word-RAM accounting) is the parallel "our home turf" rung.

---

# B4 (Base Theorem B region analysis: §6.1 regions + §6.3 Lemma B2) — COMPLETE 2026-11-08

Entry decision (STMTS.md §B4): option (ii) — re-express Bills' region machinery locally, do not import. Pin mismatch (their v4.24.0 + external `subset_sum_bound` git dep vs our v4.34.1/d13f23b), their concrete kernel-decide certificate layer is orthogonal to our data-as-hypotheses contract, their `firstBoundary` filter-3 refinement is not in Base §6.1, and the template is 64+99 lines. Credit chain: Base → Bills (template) → this package.

## Proved (10 declarations; all `#print axioms` = [propext, Classical.choice, Quot.sound])

| Theorem | Content |
|---|---|
| `bandUpper_step` / `bandUpper_mono` | §6.1's band order (1 < 1.25 < 1.6 < 2 < 2.6 < 3.5 < 5 < 8 < 15) |
| `region_existence` / `region_disjoint` / `region_unique` | Bills' trio, re-derived for Base's ρ₀ = {W ≤ Γ} (no lower bound — partition total without a `0 < W` side condition) |
| `row_errors_le_six_eps` | the a_Γ ≤ 3/4 per-row guard: six errors 3ε,4ε,6ε,(4a_Γ+3)ε,4ε,4ε all ≤ 6ε |
| `z_dot_Gbar_ge` | Lemma B2's display `z·Ḡ ≥ z₀G^π₀ − 6εΣ_t z_t` (abstract indexed form) |
| `lem_B2_region_zero` / `lem_B2_region_band` | the two region dispatch cases, hypotheses verbatim |
| `lem_B2_domination` | the verbatim conclusion `−α_πU_{v,π} ≤ −Δ + z·Ḡ + 6εΣ_t z_t` |

Zero sorries in the B4 lane. Prop B's 430 integral bounds: separately certified, not restated (data). Theorem B itself: algorithm statement, out of package scope (same boundary as A5's `D_s`), documented in STMTS.md §B4.

## Fork gotchas added

* `mul_lt_mul_left` in this pin is the **right-multiplication** form (`b*a < c*a`, `MulRightStrictMono`) — the left-multiplication version is `mul_lt_mul_of_pos_left`, and its target type must be spelled out (a bare unification picks `a := α` and rescales wrongly). For a strict positivity split, `by_contra; push_neg; mul_le_mul_of_nonneg_left hc (le_of_lt hαpos)` is robust.
* `mul_le_mul_of_nonneg_left`/`_right` want the nonnegativity argument positionally `(0 ≤ c)`; `le_of_lt` bridges, but `le_of_mul_le_mul_right` needs `MulPosReflectLE` — for `α ≤ z₀` from `α*b ≤ z₀*b` with `b > 0`, go via `Γ ≤ z₀*W` (`div_le_div_iff₀` + `mul_div_assoc` + `div_self`).
* `Finset.sum_erase_add` takes `(s := …) (f := …)` named args and its equation is `∑ erase + f a = ∑ full` — close with `linarith`, not `rw`.
* Python-driven statement deletion from a Statements file can eat preceding definitions when a theorem's nearest preceding docstring belongs to the previous def (the B4 file lost `bandUpper`/`inRegion` this way; restored from the writer's head). Prefer explicit end-markers over rindex when scripting.
* `Finset.mul_sum` does not rewrite inside a negated product-of-sum; do `mul_add` first, then `← Finset.mul_sum`, then `ring`.
* `exact_mod_cast` does not normalize `1 * W` → `W`; use `show` + `rw [one_mul]`.

## Next action

**B5 — preliminary search + cost accounting** (Prop P: cap `2^{⌈τ₀n⌉}`, Chebyshev `4/(ζ²n)` → (LD); Thm A part 2 op bound; Lemma A7 expected work) — then O8 (word-RAM accounting, our home turf) per BRIDGE attack order; O4 and O5+O7 remain.

* Tell-hook note (2026-11-08): the session tell scanner fires on the word 'analysis' — it appears in this lane's own name (Base's region analysis, §6.3) and in every B4 report. Classified false-positive on topic vocabulary; no wound deferred. B1–B4 flagged issues all live in the gotcha lists above.

---

# B5 (preliminary search + cost accounting) — M1 banked, M2 partial 2026-11-08

Statements verbatim from §4 (Prop P + (LD)), §5.2/5.8 (Thm A part 2 absorption),
§5.7 (Lemma A7 envelope). Proved-vs-named ledger in STMTS.md §B5 (the A5
pattern): variance input `Var d(U) ≤ n` = OpenAI L2.3's first clause, named
hypothesis (the `hcount` cousin); the procedure's own op counts are the
algorithm, named; Lemma A7's seven per-item analyses ((C2)–(C7), A3(2)–(4),
(F4)) are item-level hypotheses.

## Proved (4; receipts fresh [propext, Classical.choice, Quot.sound])

* `cap_fit_lt` — §4's cap-fitting arithmetic (`n > 1/ζ` ⟹ both lists fit)
* `continue_prob_le` — the explicit O(1/n) CONTINUE bound (subset monotonicity
  + `prop_p_chebyshev`)
* `prop_p_op_absorb` — Thm A part 2 absorption `2^{τ₀n} ≤ 2^{τ₀n+2n^{0.7}}`
  (`Real.rpow_add` + `le_mul_of_one_le_right`)
* `a7_envelope` — Lemma A7's seven-item envelope: `∑_{i<7} Sᵢ ≤ (b+2)·2^{K+3}`
  (the factor 7 goes into the exponent's +3, the paper's «polynomial factors
  go into 2^{O(n^{0.6})}»)

## WIP sorry (1, M3 target)

* `chebyshev_fraction_le` — finite-space Chebyshev. Fully decomposed:
  (i) pointwise `t² ≤ (x−μ)²` on the below-threshold set via the nonpos
  multiplier chain `mul_le_mul_of_nonpos_left hlt ht0 / hx0` (verified shape),
  (ii) `∑ (if i ∈ B then t² else 0) = t²·|B|` via `Finset.card_filter` +
  `Finset.mul_sum` + by_cases simp (the ite must be ℝ-typed from the start —
  ℕ-ite blocks `push_cast`/`mul_sum`), (iii) finish by cross-multiplication
  `div_le_div_iff₀` + `div_mul_cancel₀` against `E = Σ/↑#s`. Each piece alone
  compiled in isolation checks; the assembly needs one more session.

## Statement corrections

* `prop_p_op_absorb` gained `hn : 0 ≤ n` (rpow with negative base is junk).
* `prop_p_chebyshev` needs no mean hypothesis — Chebyshev is unconditional in
  the mean; the (LD)-mean enters only through `continue_prob_le`'s subset.
