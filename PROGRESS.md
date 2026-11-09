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

---

# B5 chebyshev CLOSED (2026-11-08) — the residual was an assembly artifact

`chebyshev_fraction_le` is **PROVED** (no sorry). Root cause of the "bare
mul_comm that would not close": it never was an order problem — the previous
route built `hsum` through `Finset.card_filter`'s ℕ-ite sum + cast bridging,
and the two `t ^ 2` / `↑{...}.card` atoms ended up elaborated from different
terms (hence `rw [mul_comm]` and `linear_combination` both failing). The cure
was a route that never produces that shape:

1. `set E := s.expect x` (one mean atom everywhere) and `set B := filter`.
2. Per-point `t² ≤ (x i − E)²` on B (`mul_le_mul_of_nonneg_right/left` + ring).
3. `↑#B·t² = ∑ i ∈ B, t²` via `Finset.sum_const, nsmul_eq_mul` (no ite, no
   card_filter — the ℝ monoid family sum directly).
4. `∑ i ∈ B ≤ ∑ i ∈ s` via `Finset.sum_le_sum_of_subset_of_nonneg hsub
   (sq_nonneg)` — **NOT** `sum_le_sum_of_subset`, which in d13f23b requires
   `[CanonicallyOrderedAdd M]` and does not apply to ℝ (new gotcha).
5. `Finset.expect_eq_sum_div_card` unfolds the expect; `div_le_div_iff₀` with
   `d := t ^ 2` pinned by an explicit `have ht2` (passing bare `ht` pins
   `d := t` — elaboration-order trap); cancel `↑s` by a local
   `field_simp` have; close with `exact hmain`.

Fresh receipts: `chebyshev_fraction_le`, `prop_p_chebyshev`,
`continue_prob_le` all `[propext, Classical.choice, Quot.sound]`. Build green
8947 jobs; package sorries now 2 (the pre-existing L2.5 pair only).

Everything in the B5 lane is proved (6/6): chebyshev_fraction_le,
prop_p_chebyshev, cap_fit_lt, continue_prob_le, prop_p_op_absorb, a7_envelope.

---

# O8 (word-RAM accounting, Base §5.2) — M1 banked 2026-11-08

Statements verbatim from §5.1 (Thm A part 2), §5.2 (Steps 3 and 6 + the
closing accounting paragraph), §5.8 (bullet 5 «2^{O(n)} draws»). Proved-vs-
named ledger in STMTS.md §O8. **D7 boundary held**: everything counts word
operations in Base's own counters; the bit-cost → Light-step translation is
D7 (L5's) and is not imported. Credit: Base.

## The six O8 statements (`Statements/O8.lean`; 6 sorries, build green)

* `o8Cap` — §5.2 Step 6's cap `2^{⌈τ₀n⌉+⌈n^{0.7}⌉}` as a def (noncomputable ℝ).
* `o8_cap_absorb` — cap ≤ `2^{τ₀n+2n^{0.7}}` (two `⌈x⌉ ≤ x+1` absorbed).
* `o8_cap_envelope` — ten counted categories ≤ C ⟹ ∑ ≤ 10·C.
* `o8_time_bound` — part 2's display with the `poly(n+b+2)` slot as named `P`:
  ten categories ≤ cap·P ⟹ ∑ ≤ 16·P·2^{τ₀n+2n^{0.7}}.
* `o8_trial_count_bound` — §5.2 Step 3's verbatim `n⁷2^{F̂} ≤ T ≤ 2n⁷2^{F̂}`
  (needs only `0 < Ŝ ≤ 1`; the `e_n` integer range is Lemma A3's input, noted).
* `o8_trials_le_cap` + `o8_draws_le` — «halts every execution»'s checkable
  core (K ≤ cap from per-trial ≥ 1 counted step) and «2^{O(n)} draws»
  explicit (`2+n²+3K ≤ (n²+5)·cap`).

## O8 statement hygiene notes

* **`Ŝ` is not a Lean identifier** (combining circumflex) — the Lean name is
  `Shat`. Cost one failed build to find.
* `o8Cap` needs `noncomputable` (ℝ division dependency).
* Empty-expect audit: no `Finset.expect` in any O8 statement; `1/Ŝ` guarded by
  explicit `0 < Ŝ`; `n ≥ 0` stated on every rpow consumer (no negative-base
  junk). `Ŝ ≤ 1` follows in-application from proved L2.2 (`d ≥ 0`), carried as
  hypothesis because the `V_j` draws are algorithm data.

## Next actions (O8 lane)

1. **M2**: `Proofs/O8.lean` — the proofs are elementary (ceil bounds,
   `Real.rpow_le_rpow_left_iff`, `rpow_logb`, `Finset.sum_const`); names
   pre-verified in this pin. Then receipts, commit, push.
2. Then B4/B5-style close-out for O8 and the report.

# O8 COMPLETE (word-RAM accounting, Base §5.2) — M2 2026-11-08

All six O8 theorems PROVED in `Proofs/O8.lean` (statement-of-record;
`Statements/O8.lean` is the quotes-only pointer file). Build green 8949 jobs;
package sorries 2 (the pre-existing L2.5 pair only — not this lane's).

## Proved (receipts freshly measured)

| Theorem | Receipt |
|---|---|
| `o8_cap_absorb` — cap ≤ 2^{τ₀n+2n^{0.7}}, hyp. `2 ≤ n^{0.7}` | [propext, Classical.choice, Quot.sound] |
| `o8_cap_envelope` — ten categories ≤ C ⟹ ∑ ≤ 10·C | [propext, Classical.choice, Quot.sound] |
| `o8_time_bound` — ∑ ≤ 16·P·2^{τ₀n+2n^{0.7}} (P named) | [propext, Classical.choice, Quot.sound] |
| `o8_trial_count_bound` — Step 3's n⁷2^{F̂} ≤ T ≤ 2n⁷2^{F̂} | [propext, Classical.choice, Quot.sound] |
| `o8_trials_le_cap` — halts-every-execution core (K ≤ cap) | [propext, Classical.choice, Quot.sound] |
| `o8_draws_le` — «2^{O(n)} draws»: 2+n²+3K ≤ (n²+5)·cap | [propext, Quot.sound] |

## O8 fork gotchas added (two cost failed builds each)

* **`⌈x⌉` for `x : ℝ` is ℤ-valued in this pin** (`Int.ceil`). So
  `2 ^ (⌈τ₀n⌉ + …)` is integer-exponent **zpow**, and every `Real.rpow` lemma
  fails to unify against it. Bridge: `rw [← Real.rpow_intCast]`
  (`x ^ ↑n = x ^ n`), then `Real.rpow_le_rpow_of_exponent_le`. The ceil bound
  lemmas are namespaced `Int` even when used on ℝ (`Int.le_ceil` — lower bound
  only! — and `Int.ceil_lt_add_one` for the upper).
* **The cap absorption is FALSE for small n** (n = 1/2, τ₀ = 0.487: cap 2² >
  2^{1.46}). The paper's «for all sufficiently large n» is load-bearing; made
  explicit as `hn07 : 2 ≤ n ^ (0.7:ℝ)` (n ≥ 2^{10/7}) on `o8_cap_absorb` and
  `o8_time_bound`.
* Postponed-`by` elaboration: a lemma with metavariable-typed args
  (`Real.rpow_le_rpow_of_exponent_le h02 (by linarith …)`) elaborates the
  tactic block against unmet metavariables and guesses garbage — pre-type the
  side condition as a `have`.
* `mul_le_mul_of_nonneg_right h hcp`'s second arg is the *whole product* factor
  (`c` in `a*c ≤ b*c`), not a co-factor.

## BRIDGE row O8 scorecard (per the row's three properties)

* *exact uniform finite draws bounded* → `o8_draws_le` (+ `o8_trials_le_cap`)
* *halts every execution* → `o8_trials_le_cap` (the FAIL rule is the named
  mechanism; its arithmetic consequence is proved)
* *per-outcome time bound* → `o8_time_bound` (+ `o8_cap_absorb`,
  `o8_cap_envelope`), part 2's display with the `poly(n+b+2)` slot named `P`

D7 boundary held throughout: Base's own word-op counters only.

---

# O4 (OpenAI L3.2 finite filtering data) — M1 banked 2026-11-08

Statements verbatim: OpenAI `sections/filtering.tex` Lemma 3.2 + the Riemann
estimate + the effective version; Base (F7), Lemma B1, App. B.2. Ledger in
STMTS.md §O4. D7 boundary held (procedure named, certified numerics are
data-not-restated). Formalizable core identified and stated: Riemann estimate
(Lipschitz form `2πB/P`), Gibbs for the finite order (3.3) via Jensen, the
P₀+slack assembly (`o4P₀` explicit), log/quotient boundedness primitives.

## The six O4 statements (`Statements/O4.lean`; 6 sorries, build green)

o4_avg_err_le, o4_gibbs, o4_finite_from_continuous, o4_log_abs_le,
o4_div_le, o4_le_div; defs o4Avg, o4P₀.

## Next actions (O4 lane)

1. **M2** `Proofs/O4.lean`: Riemann via
   `intervalIntegral.sum_integral_adjacent_intervals` + Lipschitz slicing;
   Gibbs via `ConcaveOn.le_map_sum` + `strictConcaveOn_log_Ioi`; P₀ assembly
   arithmetic; the rest linarith/`div_le_div_iff₀`. All names pre-verified.
2. Receipts, commit, push; then the O4→O5+O7 handoff report.

# O4 COMPLETE (OpenAI L3.2 finite filtering data) — M2 2026-11-08

All six O4 theorems PROVED in `Proofs/O4.lean`. Build green 8951 jobs;
receipts (fresh): all six `[propext, Classical.choice, Quot.sound]`. The
Riemann-sum estimate (`2π‖∂H‖_∞/P` in Lipschitz form) is the load-bearing
piece: grid split via `intervalIntegral.sum_integral_adjacent_intervals`,
per-slice `norm_integral_le_of_norm_le_const` with the in-slice Lipschitz
bound, `len = 2π/P` algebra closed by field_simp + ring. Gibbs (3.3) via
`ConcaveOn.le_map_sum` on `strictConcaveOn_log_Ioi`. P₀ assembly: `o4P₀` is
the explicit ceiling threshold; the strict-slack argument (0.5168 → 0.5169,
resp. Prop B → Lemma B1) is the paper's own, made formal.

## M2 statement corrections (disclosed, the hn07 pattern)

1. o4_div_le / o4_le_div: M1 directions were false; corrected to the paper's
   `K_x = f·g/Q` use (denominator lower bound ⟹ upper quotient bound and the
   dual), with `0 < d` explicit (correction 3: `d ≤ den` + `0 < den` does not
   give `0 < d`).
2. Log-divergence hypotheses: `Real.log_div` takes `≠ 0` at this pin.

## O4 fork gotchas added (each cost ≥1 failed build)

* `∫ x in a..b, H x - c` parses the subtraction INSIDE the integral —
  parenthesize `(∫ …)` before subtracting.
* `Finset.sum_le_sum` with a `?_` body cannot synthesize the implicit `g` —
  pre-type the per-element proof as a typed `have`.
* `Real.log_div` takes `≠ 0`; `norm_integral_le_of_norm_le_const` takes
  `uIoc` + concludes `C * |b − a|`; `neg_le_abs_self` is absent (use
  `le_abs_self (-a)` + `abs_neg` + linarith).
* field_simp distributes and clears denominators but leaves atom-identity
  residues (`B ≤ B`, `len·P = 2π` gaps) — close with `le_refl`/an explicit
  `have` + rw, not bare ring.

## O4→O5+O7 handoff shape

O5+O7 (flat enumeration + op-bound, BRIDGE attack order item 7, «the
mountain» ~18–35k) consume: the O4 finite-circle convergence for the
checksum's numeric claims (this rung's o4Avg/Riemann/P₀ machinery transfers
directly), O8's cap/budget accounting pattern (o8Cap/o8_time_bound), and the
B5 Chebyshev chain. Source: OpenAI §5 (flat enumeration) + Base §5 context.
The named-boundary pattern (procedure = named, arithmetic = proved) is now
established across B1–B5, O4, O8 — O5's statement work should open with the
same ledger table.

---

# O5+O7 (OpenAI Thm 4.1 + 5.1) — M1 banked 2026-11-08

The tail rung. Statements verbatim: Thm 4.1 (checksum estimator: 1/8
accuracy + every-run `2^{(τ+20ε)n+O(√n)}poly` op bound) and Thm 5.1 (alias
extraction: complete lists w.p. 1−o(1) + `2^{⌈τn⌉}poly(n)` records every
run). Ledger in STMTS.md §O5/§O7. Consumers wired per the handoff: O8's
cap/envelope/running-below-cap pattern, B3's cor_A6_per_alias for O7's
union bound. Five theorems + two defs (`o5Cap`, `o7Cap`); 5 sorries, build
green. `X̄` gotcha: combining macron → `Xbar` (the `Ŝ`-class, second hit).

## Next actions (O5+O7 lane)

1. **M2** `Proofs/O57.lean`: o5_cap_absorb via the O8 zpow bridge
   (`Real.rpow_intCast`) + `Int.ceil_lt_add_one` twice; o5_time_bound =
   o8_time_bound pattern; o5_mse_le = div arithmetic + empty-expect guard;
   o7_records_le_cap = o8_trials_le_cap shape; o7_union_le consumes
   `cor_A6_per_alias` (import Proofs.A5). All names pre-verified.
2. Receipts, commit, push; then the LADDER CLOSE-OUT summary.

# O5+O7 COMPLETE + LADDER CLOSE-OUT — 2026-11-08

All five O5+O7 theorems PROVED (`Proofs/O57.lean`; quotes-only pointer in
`Statements/O57.lean`). Build green 8953 jobs; receipts all
[propext, Classical.choice, Quot.sound]. **The BRIDGE attack order items
3–7 are now all banked on base-core: O8, B4, B5, O4, O5+O7.**

## M2 notes

* o5_mse_le needed an μ = 0 case split (positivity cannot give 0 < μ from
  0 ≤ μ) and eq_or_lt_of_le gives the REVERSED equation (0 = μ, so rw needs
  ←); `0 / b = 0` is zero_div, not div_zero (second occurrence of the
  div-lemma-name trap).
* Full-build vs module-target caching: an interrupted build can leave the
  trace claiming built while the olean is missing — the FULL lake build is
  the receipt of record (hit twice this rung).

## LADDER CLOSE-OUT — proved-vs-named across the campaign

**Proved on base-core (all receipts [propext, Classical.choice,
Quot.sound] unless noted; zero sorries in any lane file; no
native_decide; source sha256 b397531c… re-verified per rung):**

* **L2.5 cluster (pre-existing, two sorries remain there by design:**
  `L2_3_halfVariance`, `L5_2_sparse_distinctions` — the OpenAI-side
  variance/sparse-distinction inputs, owned by the main lane).
* **B1** L3.1 covering (counted form), L3.2 sampling (counted form), L3.3
  good layer + density, layerSupport complement.
* **B2** Corollary D (both branches + the nested-averaging and
  complement-transfer lemmas; the C(σ,k)C(v,k) ≤ 2^v hypothesis used only
  in the t < k branch, as in the paper).
* **B3** Lemma A5 spine (Steps 1, 3, 4, 6 + Cor A6 per-alias) — 14
  declarations; Step 2/Step 5 named; consumes the B1 L2.5 prime-collision
  formalization as (F4).
* **B4** Theorem B region machinery (band order, region trio, the a_Γ ≤ 3/4
  guard, Lemma B2 domination); the 430 certificate rows = certified data.
* **B5** Prop P chain: chebyshev_fraction_le, prop_p_chebyshev,
  cap_fit_lt, continue_prob_le, prop_p_op_absorb, a7_envelope — 6/6.
* **O8** word-RAM accounting: o8Cap, o8_cap_absorb (hyp. 2 ≤ n^0.7 — the
  paper's «sufficiently large n» explicit), o8_cap_envelope,
  o8_time_bound, o8_trial_count_bound, o8_trials_le_cap, o8_draws_le —
  Base's own word-op counters; D7 (bit-cost → Light-step) not imported.
* **O4** L3.2 finite-circle core: o4Avg, o4P₀, o4_avg_err_le (the
  2π‖∂H‖_∞/P Riemann estimate), o4_gibbs (finite order 3.3),
  o4_finite_from_continuous (the strict-slack assembly),
  o4_log_abs_le/o4_div_le/o4_le_div. Approximability procedure named.
* **O5+O7** Thm 4.1 + 5.1 cores: o5Cap/o5_cap_absorb/o5_time_bound (the
  (τ+20ε)n+O(√n) budget with the O(√n) explicit as 2√n+2 — unconditional,
  unlike O8), o5_mse_le (MSE ≤ 1/8), o7Cap/o7_records_le_cap,
  o7_union_le (completeness union bound consuming B3's cor_A6_per_alias).

**Named/external (never axioms — the honest boundary):** every procedure
(D_s, the checksum tables/patterns/phases, alias extraction + dedup +
subtraction, the L3.2 approximability routine); per-category op counts and
word-cost polys; certified numerics (Prop B's 430 rows, the 0.5168/0.5169
quadrature pair); the PNT/Rosser-Schoenfeld count input (hcount); the o(1)
ratios; Base's (F1)-(F8) external inputs as documented per rung.

**Corrections table (all caught-by-proving, disclosed in ledgers):**
1. B3: C(m,σ)2^{−m} ≥ 1/(m+1) stated at the middle layer (arbitrary σ was
   false); good_hit_expect_ge gained σ ≤ |M| (empty-expect trap).
2. B3: collisionPairs_expect_le gained 0 ≤ K₀ (diagonal pairs' zero).
3. B5: prop_p_op_absorb gained 0 ≤ n (rpow negative-base junk).
4. O8: o8_cap_absorb/o8_time_bound gained 2 ≤ n^{0.7} («sufficiently large
   n» explicit — false below 2^{10/7}).
5. O4: the quotient-boundedness pair restated (M1 directions false) with
   0 < d explicit; log-divergence hypotheses ≠ 0 at this pin.
6. O5+O7: none — statements landed clean (first rung with zero
   corrections; the pattern is mature).

**What the bridge now proves:** the full conditional chain from the L2.5
cluster through Base's combinatorial core (B1–B5), Theorem B's region
machinery (B4), the finite-circle data (O4), the word-RAM accounting (O8),
and the checksum/alias-extraction cores (O5+O7) — with the procedures and
certified numerics as named data, exactly the staged-ladder architecture
BRIDGE milestone 1 prescribed. Three conditional rows inherit every rung.

---

# ROWS opened (conditional board rows) — M1 2026-11-08

`Statements/Rows.lean`: rev8g Thm 1 (0.4875755) stated with the hypothesis
map (kernel-checked ladder = theorems, still-named = opaque Props); the
T′-absorption tail is the row's first WIP obligation.  JoshuaQFEX/Bills
rows are pointer entries (external sources).  rev8g source verified:
paper_2026-11-06_rev8g.tex sha256 18899a6e… (PROVENANCE_rev8g.md).

## Next actions (ROWS lane)

1. **M2**: the absorption tail (2√n+2+poly = 2^{o(n)} into the fixed gap
   T′ − (τ₀+20ε)) — then the full row composition (instantiate the named
   procedures, compose the ladder lemmas under the hypotheses).
2. Fetch JoshuaQFEX's paper + Bills' supplement statement verbatim for
   their rows.
3. The merge landed: main @ 3692143 (merge 603ed2e + the O-rung import
   fixup) — base-core's whole ladder is on main, 0 sorries, receipts
   spot-checked (B3/B4/O8/O4/O5+O7 + the formerly-sorry L2.5 pair).

## ROWS M2 — the absorption tail: COMPLETE PROOF PLAN (executed next session)

The proof is fully designed and lemma-name-verified; the session budget ran
out mid-write (the M1 sorry stands, precisely reported — build-or-don't-
claim). Structure:

1. **Crux lemma `o57_poly_le_pow`** `∃ n₁, ∀ n ≥ n₁, c·(n+1)² ≤ r^n` for
   `0 ≤ c`, `1 < r` (all names probed ✓):
   - `r^{1/4} > 1` (`Real.one_lt_rpow hr (by positivity)`).
   - `N₂ := ⌈1/(√r−1)⌉ + 1`: for n ≥ N₂, `(n+2)² ≤ √r·(n+1)²` — from
     `(n+2)/(n+1) ≤ √r` ⟸ `(√r−1)(n+1) ≥ 1` ⟸ `n+1 ≥ 1/(√r−1)` via
     `exists_nat_gt` + `Nat.le_ceil` + cast juggling (the O8/O4 pattern).
   - Geometric decay: `b_n := c(n+1)²/q^{2n}` (q := √r) satisfies
     `b_{n+1} ≤ b_n/q` for n ≥ N₂ (from `(n+2)² ≤ q(n+1)²`, i.e. the
     √r-ratio form); invariant `c(n+1)² ≤ A·q^n` with
     `A := c(N₂+1)²/q^{N₂}` via `Nat.le_induction` (step:
     `c(n+2)² ≤ q·c(n+1)² ≤ q·A·q^n = A·q^{n+1}` ✓).
   - Constant absorption: `A ≤ q^{N₃}` for
     `N₃ := ⌈log A / log q⌉ + 1 + N₂` — via `exists_nat_gt (log A / log q)`
     + `Real.log_le_log_iff` + `Real.log_pow (0 < q)`; then
     `c(n+1)² ≤ q^n·q^n = q^{2n} = r^n` (`pow_add`, `pow_mul`, `hqq`).
   - Case split `c = 0` at the top (trivial).
2. **√-slack lemma `o57_sqrt_le`** `∃ n₂, ∀ n ≥ n₂, 2^{2√n+2} ≤ 2^{(δ/2)n}`:
   `n₂ := ⌈(8/δ)²⌉ + 1`; `√n ≥ 8/δ` via
   `Real.le_sqrt_of_sq_le ((8/δ)² ≤ n)`; `2√n ≤ n` for n ≥ 4 via
   `2 ≤ √n` (`Real.le_sqrt_of_sq_le (4 ≤ n)`) + `nlinarith [Real.sq_sqrt]`;
   `2√n + 2 ≤ 4√n` (n ≥ 1); `4√n ≤ (δ/2)n ⟺ 8 ≤ δn` ⟸ `δn ≥ δ·(8/δ)² ≥ 8`
   (δ ≤ 8; the δ > 8 case: n ≥ 1 ⟹ δn > 8) — `nlinarith`.
3. **Assembly**: `ops n ≤ c·poly·2^{2√n+2}·2^{(τ₀+20ε)n}` (rpow_add split)
   `≤ 2^{(δ/2)n}·2^{(δ/2)n}·2^{(τ₀+20ε)n} = 2^{T'n}` (`hδdef`; ring; and
   `(n:ℝ)` vs n cast via `Real.rpow_le_rpow_of_exponent_le` + le_refl).

Estimated ~90 lines, ~3 build rounds. The δ > 8 sub-case in step 2's `8 ≤
δn`: case-split or use `nlinarith [hn8' : (8/δ) ≤ 1 ∨ ...]` — see text.

## ROWS M2 — transcription attempt + REFINED plan (2026-11-08, second pass)

The mechanical transcription hit layered pin traps and was ROLLED BACK to
the honest M1 state (git checkout; the sorry stands). New pin facts
discovered (cost the attempt, banked for the next execution):

1. `⌈x⌉` for `x : ℝ` is ℤ-VALUED (the O8 discovery, again): `(⌈1/(q−1)⌉ :
   ℕ)` fails — use `(⌈x⌉ : ℤ).toNat` (the `o7Cap` pattern) or keep the
   threshold existentially via `exists_nat_gt` (which avoids ⌈⌉ entirely —
   RECOMMENDED: `obtain ⟨N, hN⟩ := exists_nat_gt (1/(√q−1))` gives
   `1/(√q−1) < ↑N` directly, no ceil, no cast).
2. `Real.rpow_pos` is ABSENT — use `Real.rpow_nonneg` (O8) or `Real.rpow_pos_of_pos` if present (probe).
3. `eq_or_lt_of_le hc` gives the REVERSED `0 = c` (third occurrence of this
   trap) — `rw [← hc0]` or match with `hc0.symm`.
4. `lt_of_mul_lt_mul_left` expects the multiplied form — for `1 < √r` use
   `lt_of_mul_lt_mul_left (h : 1·1 < √r·√r)` after
   `Real.mul_self_sqrt`.
5. The refined structure (v2, with the ℤ-trap avoided):
   - `obtain ⟨N, hN⟩ := exists_nat_gt (1/(√q−1))` — the ratio threshold
     WITHOUT ceil.
   - hstep: `(n+2)² ≤ q(n+1)²` for `n ≥ N` (from `hN : 1/(√q−1) < ↑N ≤ ↑n`).
   - invariant `c(n+1)² ≤ A·q^n`, `A := c(N+1)²/q^{2N}` — base TRIVIAL
     (`A·q^N = c(N+1)²/q^N ≤ c(N+1)²` since `q^N ≥ 1`), step via the
     q-ratio hstep.
   - conclusion: `A ≤ q^n` for `n ≥ N₃` (`exists_nat_gt (log A/log q)` +
     `Real.log_le_log_iff` + `Real.log_pow`) ⟹ `c(n+1)² ≤ A·q^n ≤ q^{2n} =
     r^n` — NO ceil anywhere, NO N-offset needed.
   - then the √-slack lemma and assembly as in the previous plan entry.
Estimated ~60 lines with the exists_nat_gt form (SHORTER than v1 — the ceil
elimination removes the whole cast-juggling layer).

## ROWS M2 — plan v2 transcription attempt + plan v3 (2026-11-08, third pass)

The v2 transcription hit NEW traps and was ROLLED BACK again (the M1 state
stands). Four new pin facts (banked):

1. **Application-bind parse trap**: `exists_nat_gt ((8:ℝ)/δ)^2` parses as
   `(exists_nat_gt ((8:ℝ)/δ)) ^ 2` — `^` binds tighter than application
   AFTER the paren-group. Fix: `exists_nat_gt (((8:ℝ)/δ)^2)` — wrap the
   whole squared term.
2. **∃-body `(2:ℝ)` annotations are REQUIRED** when no expected type
   propagates: `∃ n₂, ∀ n ≥ n₂, 2 ^ (...) ≤ 2 ^ (...)` elaborates the bases
   as ℕ (`HPow ℕ ℝ` fails). Write `(2:ℝ) ^ (...)` in ∃-bodies.
3. `Real.rpow_pos_of_pos (h : 0 < x) (y)` WORKS at this pin (hrpos built
   ✓); `Real.rpow_nonneg`'s h-slot form needs probing before use.
4. `eq_or_lt_of_le` reversed-equation trap: third occurrence — the M1
   pattern `rw [hc0.symm, zero_mul]` is correct as written.

**Plan v3 (the deltas from v2 — everything else in v2 stands):**
- `obtain ⟨n₂, hn₂⟩ := exists_nat_gt (((8:ℝ)/δ)^2)` (extra parens).
- ∃-bodies: `(2:ℝ) ^ (…)` annotations on both sides.
- `hrpos := Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _` (proven form).
- `hqq := Real.mul_self_sqrt (le_of_lt hr1)` — worked in O4, but if the
  0 < / 0 ≤ form fights at the set-fvar, `rw [hq]` first then
  `exact Real.mul_self_sqrt (le_of_lt hr1)`.
- The invariant/conclusion/√-slack structure of v2 stands unchanged.

## ROWS M2 — plan v3 attempt + THE COMPLETED ROUTE (2026-11-08, fourth pass)

Plan v3's transcription surfaced the FINAL blocker: the polynomial-vs-
exponential crux `c(n+1)² ≤ q^{2n}` eventually (for 1 < q, c > 0) — the
explicit-threshold constructions spiral (three attempts: the q^n/r^n
invariant error, the ℤ-⌈⌉ trap, the (k+1)+1/k+2 calc-syntax mismatch, the
∃-body (2:ℝ) annotation requirement, the application-bind parse of
`f ((x)/δ)^2`, the `neg_le_abs_self`/`one_le_pow₀`/`pow_le_pow_right` name
drifts). ROLLED BACK to the honest M1 state (the sorry stands).

**THE COMPLETED ROUTE (Mathlib-verified this round):** the crux via
`Asymptotics` — `Real.isLittleO_log_id_atTop : log =o[atTop] id` EXISTS
(Log/Base.lean:450 ✓) — the chain:
1. `hloglittle : (fun n : ℕ => Real.log ((n:ℝ) + 1)) =o[atTop]
   (fun n : ℕ => (n:ℝ))` — transported via
   `Asymptotics.IsLittleO.trans_tendsto` +
   `tendsto_natCast_atTop_atTop` (probe the exact forms).
2. From `Asymptotics.isLittleO_iff` (∀ c > 0 form): for ε := δ/(2·log 2)
   (δ := T′ − (τ₀+20ε)), ∃ n₁, ∀ n ≥ n₁: `Real.log ((n:ℝ)+1) ≤ (δ/2)·(n:ℝ)`
   — then `Real.log_le_iff...`-family → `(n:ℝ)+1 ≤ 2^{(δ/2)·(n:ℝ)}` via
   `Real.log_le_rpow`-form (probe) ⟹ `((n:ℝ)+1)² ≤ 2^{δ·(n:ℝ)}`.
3. `c ≤ 2^{δn/3}` similarly (log c ≤ log 2 + log(c)/... — the
   `Real.log_le_self`-family), and `2^{2√n+2} ≤ 2^{δn/3}` via √n ≤ n (n ≥ 4
   — explicit `Real.le_sqrt_of_sq_le` ✓ verified).
4. Product: `c·(n+1)²·2^{2√n+2} ≤ 2^{δn/3+δn/3+δn/3} = 2^{δn}` ✓.
The v3 structure (invariant/conclusion) is REPLACED by this — shorter and
every step Mathlib-grounded. Plus the verified-from-this-round forms:
`Real.rpow_pos_of_pos (h : 0 < x) (y) : (0:ℝ) < x ^ y` ✓ (hrpos built),
`exists_nat_gt (((8:ℝ)/δ)^2)` (the wrapped parse), the `(2:ℝ)` ∃-body
annotations.

## ROWS M2 — plan v4: PLAN-ONLY (2026-11-08, per the binding stop rule)

The Asymptotics-route draft reached the build with **known gaps of my own
making** (piece 3's c<1/c≥1 case split unfinished, an unverified
`Real.log_neg_iff`, an undefined reference) — a fourth distinct trap family
(draft-incompleteness under budget pressure). Rolled back per the binding
stop rule. **Plan v4 = the Asymptotics route (previous entry) + the
piece-3 completion:** the log c ≤ (δ/8)n·ln2 piece splits `rcases lt_or_le
c 1` — for c < 1: `Real.log_neg_iff`-family (probe) gives log c < 0 ≤ the
budget; for c ≥ 1: `Real.log_le_self`-family (probe) gives log c ≤ c ≤
(δ/8)n·ln2 for n ≥ 8c/(δ·ln2) (exists_nat_gt ✓). Everything else in the
previous entry stands (the transport ✓ verified in two probe rounds, the
isLittleO_iff extraction form ✓ verified: `(isLittleO_iff.mp hlittle) ε
hεpos`, the four-piece log-budget ✓ arithmetically closed).

**The row's WIP sorry stands, precisely reported.** Next session: execute
v4 mechanically (~90 lines, the transport verified, the piece-3 split
specified above).

## POINTER ROWS — verbatim statements fetched (2026-11-08)

**Bills 0.4876723** (`subset-sum-subclassic/yannouli-ss` @ 590bb68 ✓ the
supplement commit; paper.tex sha256 c116de491a401af943e3): «Assume the
inherited algorithmic claims specified above and the original moment
inequalities (eq:oldmom). The fixed rational construction parameters in
Section (sec:admissible), with the filter-3 certificate boundary rule of
Lemma (lem:new), yield a single randomized classical word-RAM program that
halts on every input and is correct with probability at least 2/3. For
each fixed positive integer c, there are C_c,N_c>0 such that every random
execution on n ≥ N_c, b ≤ n^c, uses at most C_c·2^{0.4876723n} word
operations in the stated model. The program does not depend on c.»

**JoshuaQFEX 0.487676** (`audit-joshuaqfex` paper.tex sha256
e480f374cefccd6e368a): «Assume these inherited premises of Base are valid.
There is a single uniform randomised classical word-RAM program which
halts on every input and is correct with probability at least 2/3. For
each fixed positive integer c, there are constants C_c,N_c>0 such that,
for every input with n ≥ N_c and b ≤ n^c, every random execution uses at
most C_c·2^{0.487676n} word operations. Here b is the largest bit length
of an input integer or the target, with the conventions of Base, and the
word length is w_RAM = ⌈4(n+b+log₂(n+2))⌉. The program does not depend on
c.»

Both pointer rows' conditions are the inherited-premises form — the same
proved-vs-named discipline applies when (if) their rows are formalized
here: their stacks are THEIRS (Bills' verification supplement @ 590bb68;
JoshuaQFEX's audit tree), not this package's to prove.

## ROWS M2 — v4 write status (2026-11-08, session close)

The v4 write (the full Asymptotics-route proof, ~170 lines) reached the
build with **39 errors — all diagnosed, none conceptual**: (1) hpolyle's
q-block: `Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _` arg-form, the
`mul_self_sqrt (le_of_lt hr1)` slot, `sqrt_lt_sqrt (le_of_lt hq1)` first
slot, the invariant's N/A/(n:ℝ) cast-juggling; (2) hsqrtle: the
`mul_self_sqrt hnpos.le` slot (needs `0 ≤ ↑n` — positivity ✓) and the
`le_trans (Nat.le_succ n₂) hn` middle-term mismatch (omega instead);
(3) the hA/hbig region: `n`-scoping after the obtains (the hA uses the
outer n — verify scoping), the calc's `(n:ℝ)`/n cast bridge. All are
mechanical; the mathematical structure is COMPLETE and correct (the crux
via isLittleO transport + the A·q^n invariant + the √-slack + the
log-threshold absorption). ROLLED BACK to the honest M1 state per
build-or-don't-claim (a 39-error tree must not land). The next session:
restore the draft from this description + the error file, fix the
mechanical forms (~3 rounds), receipts, and the row closes.
