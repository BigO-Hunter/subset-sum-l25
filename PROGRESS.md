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
| `L5_2_sparse_distinctions` | Proofs/SparseDistinctions.lean | union bound of L2.5 over `sparseAll`; K = 1/c₀ explicit, L* = max(L₀, 1); counting proved (`sparseAll_card_le`) |
| `L2_3_halfVariance` | Proofs/RandomRestrictions.lean | Var d(V_q) ≤ q — one-step conditional-mean recursion, no measure theory |
| `martingale_var` / `var_step` / `total_variance_finset` / `stepMean*` / `sum_erase_pair` | Proofs/RandomRestrictions.lean | private support lemmas of the above |

## Sorries (0) — cluster complete (2026-11-08)

All three formerly-open obligations are PROVED (statements of record live in
Proofs/ per the one-declaration convention):
`L2_1_isolation_prob` — MVV minimum-tie union bound (main, 0b85da2);
`L5_2_sparse_distinctions` — union bound over sparseAll, count bound proved (1f894cd);
`L2_3_halfVariance` — one-step conditional-mean recursion (e1bb50c).

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
* **M5b fork names** (all `#check`-verified on the pin): `Finset.biUnion` (NOT
  `bUnion`), `Finset.card_biUnion_le`, `Finset.mem_biUnion`;
  `dite_eq_left` / `dite_eq_right` (replace `dif_pos` / `dif_neg`);
  `ite_eq_left` (replaces `if_pos`); `nsmul_eq_mul` for `card • x` (plain
  `smul_eq_mul` does NOT fire on ℕ-smul of ℝ); `Nat.cast_id` for the ℕ↔ℕ
  coercion after `nsmul_eq_mul`; `Fintype.card_bool`, `Fintype.card_coe`;
  `Fintype.card_pi`. **`Fintype ℤ` does not exist (ℤ is infinite)** — never
  write `Finset.univ` over `Fin n → ℤ`; build finite candidate sets from an
  explicit encoding instead (`decode`/`sparseAll` in
  Proofs/SparseDistinctions.lean).
* Proved theorem bodies live in `Proofs/` and are REMOVED from `Statements/`
  (one declaration per theorem; statement-of-record = the proved one).
* **M4d gotchas (variance proof)**: (1) `set X := e` REWRITES the local
  context — hypotheses stated before the `set` keep `e`, hypotheses after it
  mention `X`; mixing the two directions (`rw [hX]` vs the explicit term)
  produces "pattern N not found" on goals that display unfolded. State the
  counting identities (hNtot1/hNtot2) AFTER `set` so they speak about `X`.
  (2) `field_simp` alone often closes `a/b = c/d`-style goals — a trailing
  `ring` then errors "No goals to be solved".
  (3) A ratio identity needing hrel : A*C1 = B*C0 inside products is NOT
  provable by nlinarith (degree-3): use `div_div` + `div_eq_div_iff h1 h2`
  (as an iff, via `refine (…).mpr`) + a two-step `calc` with `rw [hrel]`.
  (4) Host-level `ENFILE` ("Too many open files in system") appears under
  parallel campaign load — retry the build in a bounded loop; `ulimit -n
  10240` alone does not clear it (it is a kernel table limit).

## Commits

1. `da3100b` Skeleton + pins
2. `bb636c0` M1: statements + STMTS.md, build green (12 sorries)
3. `a60faaa` M2 + M3a: L2.5 proved, L2.1(a) proved (axioms clean)
4. `223028a` M4 first slice: L2.2 empty + nonneg proved
5. M5b: L5.2 sparse distinctions proved — `sparseAll` (support × sign-pattern
   encoding) counting + L2.5 union bound; statement fixed to probability form
   (STMTS.md note 7); axioms [propext, Classical.choice, Quot.sound]

## Next actions (in order) — after M4d (2026-11-08)

1. **M3b** `L2_1_isolation_prob`: min-tie argument. Slice the space
   `(Fin n → Fin N₀)` by the coordinates off `i`; per slice ≤ 1 bad value of
   `u i` (the tie equation `u i + k_A = k_B`); injective-slice counting gives
   #{bad} ≤ n·N₀^{n−1}, then 11/12. Beware: ℕ-vs-ℝ cast facts must be stated
   for linarith; Finset mem_insert/mem_union rcases need the `.mp` lemmas
   FIRST in this fork (Quot.lift membership is not an inductive datatype).
3. ~~M5b `L5_2_sparse_distinctions`~~ **DONE** (see Proved table): the
   candidate set is built explicitly as `sparseAll n m` from the
   (support, sign-pattern) encoding, the counting `#sparseAll ≤ sparseCount`
   is proved, and the union bound is `badSparsePrimes ⊆ ⋃_{d} {p ∣ d.natAbs}`
   with `L2_5_prime_collision` applied per nonzero sum. Remaining for the
   cluster: M4c (item 1) and M3b (item 2).

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

# DS-M5 COMPLETE — Step 6 product + Corollary A6 (the e^{−n} coverage union bound) — 2026-11-09

Fourteen theorems across `Proofs/M5.lean` + `Proofs/M5CorA6.lean`, all
receipts `[propext, Classical.choice, Quot.sound]`, no sorryAx, no
native_decide.  **M4's recorded seam is discharged** (`min_two_pow_neg_ge_div`):
`min(B_S 2^{−γm}, 1) ≥ B_S/C(σ,k)` by two-case arithmetic on C̄'s shape with
`2^{γm} ≤ C(σ,k)` (S4) and `B_S ≤ C(σ,k)`.

Chain: `sq_div_ge_min_div` (two-case second moment: `B²/C ≥
min(B,2^{γm})/(4c·2^{γm})`) → `occupied_ge_min_div` (the paper's occupancy
display via M4's Cauchy–Schwarz) → `hit_prob_ge_min_display` (M4's
`hit_prob_ge_of_sum_sq_le` + `P′ < 2^{1+γm}`: hit ≥
`min(B 2^{−γm},1)/(8c·2^{γm})` — the paper's `min(B_S 2^{−γm},1)/(8K₀n²)`) →
`hit_prob_ge_seam` (≥ `B/(8c·2^{γm}·C(σ,k))`, the per-good-S leaf) →
`step6_product_expect` (the Step-6 display line through the expectation) →
`step6_threshold` / `step6_pr_ge_threshold` (consuming B3's
`lem_A5_product` + `lem_A5_threshold` under the instance bridge
`c·2^{γm} = K₀·N²`) → per-trial ≥ `2^{−g_M}n^{−6}`.

Corollary A6: `exp_one_sub_pow_le` (`(1−p)^T ≤ e^{−pT}`, cor_A6_per_alias's
engine generalized) → `cor_A6_miss_le` (`Tp ≥ n ⟹ ≤ e^{−n}`) →
`cor_A6_coverageTp` (consuming M2's `trial_count_ge`: `T·p ≥ n`) →
`cor_A6_union_le` + `cor_A6_union_o1` (the paper's
«(nN₀+1)2^n e^{−n} = o(1)» as a Tendsto — `summable_pow_mul_geometric_of_norm_lt_one`
at 2/e, `squeeze_zero`; `2 < e` via `Real.exp_one_gt_two`).

Named (unchanged): the trial transfer (independence of the F, P′, j′ draws +
«a hit is recovered» — D7), the Step-3 input as `hQ`, the instance bridge and
the bit bound through `c = KBL/2^L`, the exec-side count constant N₀.

Structure note: `cor_A6_coverageTp` + `cor_A6_union_o1` live in
`Proofs/M5CorA6.lean` so each module compiles inside the host's lean-kill
window (wound 2125609440); M5.lean documents the ladder position.  The
direct-`lean` route (LEAN_PATH from lake's trace line) was the working
build form under contention; full `lake build` receipt banked at landing.

Next: DS-M6 per the ladder — Lemma A7 (expected work — the seven-step cost
ledger with (C2)–(C7); the v2-snapshot op-bound style applies).

# DS-M6 COMPLETE — Lemma A7 (expected work, the (C2)–(C7) cost ledger) — 2026-11-09

Thirteen theorems in `Proofs/M6.lean`, all receipts
[propext, Classical.choice, Quot.sound], no sorryAx, no native_decide; full
`lake build` green (8966 jobs). Structure: `a7_item_form` (the shared
poly·2^{exp·n} ≤ (b+2)·2^{K·n+δ} discharge) → seven item theorems (items 1–6
+ the item-8 exec mop-up, D7) → `a7_expected_work` (consuming B5's proved
`a7_envelope` by name: seven items within (b+2)·2^K sum to (b+2)·2^{K+3}).
Proved content: the (C6)/(C7) clause chain (μ(1−2a) ≤ l ≤ τ₀ − ε₀) for item 1;
the (S5)-pair derivation of the per-trial mask display 2^{h(1/2−a)m+2} plus
the (C5) discharge for item 2; the A3(3) F̂↔d(L) cancellation (the paper's
2^{ln+O} first summand) plus the hnum4-consumption for item 4; the same
cancellation carrying (S5)'s C(m,k) ≤ 2^{h(a)m} into the (C2) exponent
l + (h(a)−γ)μ for item 5; the A3(2) cancellation into the (C3) exponent for
item 6a. Named (the ledger): the per-trial expectation transfers (items 5/6),
the n³ candidate count (item 3), `hnum3`/`hnum4`/`hmu` (the §2.2 numeric rows
not among the eight Arb-certified clauses — the (C1)-routed item-3 derivation
left at the D7 boundary), and item 8's exec-side count. STMTS.md banked the
round's gotchas (rpow_add's explicit y z; ℕ-pow ascription; no-positivity-on-
rpow; the flattened-helper rule — nested a7_right/a7_left applications break
metavariable propagation; multiline show..from inside rw fails to parse).

Next: DS-M7 per the ladder — the Theorem A assembly (§5.8: five failure
events, Markov on the cap, the 1/16 finite-precision bound).


## Row lane 2026-11-10 — D7 cut per branch + guard coverage (LANDED)

* `D7` (`SubsetSumL25/Row/KapilaRow.lean`) is now `program` +
  `agrees_fallback` + `agrees_main`; `D7.agrees` reassembles the old single
  equation (so `kapila_row` is unchanged), `D7.ofBranches` reconstructs the
  seam, and `fallback_agrees_iff` proves the fallback half is *exactly*
  «`program` computes §6.3's MITM verdict at `mitmCost`» — the shape
  `subsetsum-v2-snapshot`'s `prog2` already proves at `α = 1/2`.
* `correctAt_of_fallback_det` (+ `count_const`): on guard-routed inputs the
  two-thirds majority is vacuous — exactness ⇒ every tape agrees ⇒ count = N.
  §7's union bound lives strictly on the main branch.
* `SubsetSumL25/Row/KapilaGuard.lean`: `guardOk_eventually`
  (`∀ c ∃ N, ∀ n ≥ N, ∀ b, b ≤ n^c → guardOk n b`), on top of
  `log2_mul_le_self` (threshold `2k²`) and `two_mul_sq_lt_two_pow`.
  This is where `b ≤ n^c` meets `10⁶⌈log₂(b+1)⌉ ≤ n`.
* Open: `agrees_main` (no in-tree program yet) and `CorrectAt` (documented,
  now provably vacuous on the fallback branch).

## Row lane 2026-11-10 (2) — `agrees_main` measured: route 2 vacuous, route 1 not yet well-posed, the obligation cut into four segment leaves (LANDED)

Both routes named at the D7 cut were measured *before* any program text was
written; the measurement changed the shape of the obligation rather than
discharging it.

* **Route 2 is vacuous, and now provably so.** `fallback_eq_false_iff`
  (`KapilaAlgo`, next to the routing definition) unfolds `agrees_main`'s own
  hypothesis: `R.fallback n x = false ↔ n_* ≤ n ∧ guardOk n x.bits`. «The
  fallback shadow is absent above the guard threshold» *is the premise*, so
  proving it cannot reduce the main obligation. Coverage still earns its place
  by locating the branch: `fallback_false_eventually` (`KapilaGuard`) composes
  `guardOk_eventually` with `fallback_false_of_guard` into «for each `c`, every
  routed input with `n ≥ max N n_*` takes the main branch» — so the exact
  fallback (`correctAt_of_fallback_det`, free correctness) is confined to
  finitely many `n` per `c`.
* **Route 1 is not yet well-posed.** Three of the main branch's four segments
  (`prelim`, `aliasA`, `checksumB`) are opaque fields of an *arbitrary*
  `Routines`; no fixed `List Instr` computes an arbitrary total function
  `Instance n → Draws → Option Bool`. `agrees_main` therefore cannot be
  discharged for arbitrary `R` by writing a program: `Routines` must gain those
  programs (and `mitm`'s) with per-field agreement hypotheses first. The
  missing lever is that refinement. (Scale check: the `α = 1/2` reference —
  `subsetsum-v2-snapshot` — is ~17k lines across 24 modules for the
  *deterministic* MITM alone, proved segment by segment.)
* **Landed — the cut per instruction-segment.** `agrees_main_iff_leaves`
  (`KapilaRow`): the single equation is *equivalent* to four leaves with
  concrete verdicts and no `Option` plumbing — `LeafP` (Prop P decides → that
  verdict), `LeafAnone` (Thm A `FAIL` → NO), `LeafBnone` (Thm B `FAIL` → NO),
  `LeafTest` (both phases estimate → `rowTest`). `agrees_main_of_leaves` is the
  consumer form; `D7.agrees` + `kapila_row` carry it with no other change —
  `kapila_row`'s statement and proof are byte-untouched (the only deleted line
  in the diff is the old `agrees_main` docstring's terminator). The four
  value lemmas (`run_eq_of_prelim_some`, `run_eq_false_of_alias_none`,
  `run_eq_false_of_checksum_none`, `run_eq_rowTest`) name the main branch's
  value case by case.
* **The test segment's worked reference** (the one segment §7 fully specifies):
  `rowTest_cons_cons` + `rowTest_nil_left`/`rowTest_nil_right` are the loop rules
  a scan over the stored estimate list consumes; `abs_ge_half_iff`
  (`(1/2:ℚ) ≤ |d| ↔ (1/4:ℚ) ≤ d*d`) puts the in-tree test in the **paper's own
  squared vocabulary**.
* **Two requirements on `Routines` the statement of `D7` hid** (recorded in the
  module docstring, «The main branch, cut into instruction-segments»):
  (i) per-field programs; (ii) the concrete program is a **multi-word** program
  — §6.2's `n²` fractional bits against a word `w = 4(n+b)+⌈log₂((n+2)⁴)⌉`
  (at `b = 1` the curves cross at `n = 7`) — and the trusted statement
  contemplates exactly this («multiple word operations and charged
  accordingly»), so `Routines.cost` must bound the **word-operation** count.
  `WithinEnvelope` alone does not say so.
* **Also landed:** `exec_mono_halted` — halting at `t` transports to `t + k`,
  so a segment proof never has to count the whole run at once.

Receipt: `receipts/kapila-20261110T<stamp>Z` (build exit 0, both named oleans,
axiom banner: every new declaration `⊆ [propext, Classical.choice,
Quot.sound]`; several report only `[propext, Quot.sound]`). `Statement.lean`
still `3dc6567e…34aa`.

Next (single lever): the `Routines` refinement — reify `mitm`/`prelim`/`aliasA`/
`checksumB` as `List Instr` programs with per-field agreement hypotheses, then
discharge the four leaves against them (`mitm` first: the snapshot's `prog2` is
the worked reference; then `LeafTest`; then the three phases).

## Row lane 2026-11-10 (3) — `Routines` reified: `mitmProg` landed and its seam field discharged; `LeafTest`'s loop rules now characterise the test; the multi-word charge proved absorbable (LANDED)

The refinement the previous round named as the blocker is in the structure, and
its first field is *discharged*, not merely named.

* **Structure.** `Routines` (`SubsetSumL25/Row/KapilaAlgo.lean`) gained, per
  decision field, its instruction text and its agreement hypothesis:
  `mitmProg : List Instr` + `mitm_agrees`; `prelimProg` + `prelim_agrees`;
  `aliasProg` + `alias_agrees`; `checksumProg` + `checksum_agrees`. The phase
  agreements are stated through `failToNo` (§7's «If it fails, return NO»), so
  each is a claim about *its phase's verdict only*. `failToNo` is deliberately
  non-injective: `none` and `some false` agree, and which one happened is the
  **control-flow** fact `LeafAnone`/`LeafBnone` carry, not something a segment's
  accumulator can encode. That is why each leaf now has exactly one program
  premise.
* **The fallback branch is proved, not assumed.** `Routines.mitm_agrees` has
  verbatim the right-hand side of `fallback_agrees_iff`, so
  `fallback_agrees_of_mitmProg` derives `D7.agrees_fallback` from it and
  `D7.ofMitmProg` assembles the seam from `R.mitmProg` + the main branch. The
  seam is **two obligations, not three**. `mitm_agrees` holds unconditionally
  (the fallback is deterministic and halts on every input), so the branch's
  guard premise is discarded at that step and used only by the cost collapse.
  Port, not re-derivation: `prog2`'s `smalln2_run2`/`smalln3_run2`/`bign_run2`
  are `mitm_agrees` at `α = 1/2`.
* **`LeafTest`, measured.** `rowTest_eq_of_rules`: any `f` obeying nil/nil and
  cons/cons *is* `rowTest` — the loop rules do not merely hold of `rowTest`, they
  determine it, so a segment proof establishes three equations at its exit and
  cannot get the test wrong while obeying them. What remains of `LeafTest` is
  (i) those three rules, (ii) control flow to the segment's entry with both
  estimate lists laid out at `n²` bits, (iii) the multi-word charge. Not
  discharged: no segment text exists.
* **Which side of the accounting each half speaks — and the multi-word charge as
  a theorem.** `WithinEnvelope` is a **word-operation** envelope (it counts
  `Routines.cost`, §7's own unit; the statement's «a fresh independent uniform
  w-bit random word costs one operation» fixes it). `D7` is the translation into
  `Instr` steps at `w = wordLength n b`; the two units meet there and nowhere
  else. `wordOpFactor n = n² + 1` bounds the per-operation expansion
  `⌈n²/w⌉ + 1`, covering both regimes; `withinEnvelope_wordop_absorb` proves the
  expansion is absorbed by raising the envelope's existential `K` by three, so
  multi-word arithmetic does not move the row's `2^{(τ₀+20ε)n}` exponent.
  **Correction to the previous round's note:** «`n²` stays ahead thereafter» is
  true only at fixed `b`. With `b ≤ n^c` the word `w = 4(n+b)+O(log n)` can
  *exceed* `n²` (for `b ≈ 2^{n/10⁶}`), making the ratio 1 — so the charge is
  stated as the uniform bound `wordOpFactor`, not as an always-on factor. The
  narrower-than-a-word claim holds for `b ≤ n`, `n ≥ 10`.

Receipt: `receipts/kapila-20261110T150641Z`. `Statement.lean` still `3dc6567e…34aa`.

Next (single lever): `prelimProg` — Proposition P's instruction text; `LeafP` is
its consumer, and both its mathematical core (`prop_p_chebyshev`) and its program
skeleton (`prog2`'s prologue/dispatch) are in-tree.

# `prelimProg` landed, `prelim_agrees` PROVED, `LeafP` discharged (2026-11-10, lane 4)

Module: `SubsetSumL25/Row/KapilaPrelim.lean` (new; imports `KapilaRow`).

## What is proved (no sorry, house triple)

| declaration | content |
|---|---|
| `prelimProg` | 17 instructions — `prog2`'s ported bootstrap + the witness test |
| `prelimSpec` / `prelimYes` / `prelimCost` | the phase's value, gate, and 20-step charge |
| `prelim_sound` | `prelimSpec = some true → x.yes` (the segment cannot lie) |
| `prelim_run` | `run prelimProg x ρ 20 = some (failToNo (prelimSpec n x ω))` |
| `prelim_agrees_spec` | the same in `Routines.prelim_agrees`'s exact shape |
| `map_failToNo_bind_some` | the field's `map`/`pure` wrapper is inert |
| `prelim_agrees_iff_run` | the field ⇔ «halt with that verdict» |
| `run_of_prelim_agrees` | any `Routines`' field peeled to the `Option`-free equation |
| `LeafP_of_prelim_agrees` | `LeafP R R.prelimProg` from the field + cost collapse |

Supporting kit (ported, deliberately duplicated rather than imported — the
snapshot's `Prologue.lean` is behind a 16k-line dependency chain):
`memOf`, `up`, `up_eq`, `up_ne`, `upFit`, `bv_add`, `bv_shr`, `ofNat_lt_ofNat`,
`exec_{one,add,shr,load,store,blt_lt,blt_ge,accept,reject}_step`, and the input
block as a `ℕ`-valued state (`inF`, `inF_zero`, `inF_succ`, `inF_one`, `inF_t`,
`inF_lt`) with the arithmetic `n < 2^w`, `aᵢ < 2^w`, `t < 2^w`, `2n < 2^w`.

## Design decision that mattered (measured, not assumed)

`Statement.run` starts from `loadWords _ x.input`, so cells `1..n+1` hold the
input and **no fixed cell is free**. With only cell 0 available nothing can
compute an address, because `add`/`sub` take two cells. Hence the ported
`prog2` bootstrap is *forced*, not stylistic: `[0] := 2n` (cursor above the
block), `[2n] := a₁`, and only then `[1] := 1`. All later writes go to fixed
cells `0..6`; the decision reads only `t` (at `n+1`) and `a₁` (from `2n`), so
clobbering `a₃..a₆` is harmless — and the gate `n ≥ 6` is exactly the
collision condition `n + 1 ∉ {3,4,5,6,2n}`.

First draft used `n ≥ 10` and cells up to 9; the walk's collision audit shrank
it to `n ≥ 6` with the constant block `1,2,3,6`. (Recorded because the gate is
a *derived* constraint, not a free parameter.)

## Proof-engineering note (for the next segment)

The walk is 17 `exec_*_step` rewrites. Two things made it tractable and are
worth reusing:
1. `hS := by decide` (literal fuel) instead of `omega` — `omega` over the
   accumulated local definitions blew a 2M-heartbeat budget at `whnf`.
2. Never `show` a defeq goal at an intermediate state. Normalise the written
   value with an explicit `have hval : <produced expr> = <clean value>` and
   `rw [hval]`, then `set` the clean state. `show`/`set` on an unnormalised
   `up`-composition times out; `rw` does not.

## Residual, stated plainly

`prelimSpec` is the **witness-test leg** of Proposition P (`t = 0`, `a₁ = t`),
sound and non-lying, but not Prop P's capped enumeration. The enumeration
(Proposition 2.4's MITM with cap `2^{⌈τ₀n⌉}`) is the residual, and it is the
piece that carries `prop_p_chebyshev`'s probability content via `CorrectAt`.
`LeafP`'s discharge is *conditional on the cost collapse* `R.cost = R.prelimCost`
on the main branch, which is a property of the `Routines` value the row
eventually instantiates, not of this module.

Next single lever: `aliasProg` (Theorem A's alias phase), same pattern.

## Row lane 2026-11-10 (6) — `aliasProg` authored: Theorem A's text, its witness leg proved sound, the `isSome` divergence isolated as a theorem, `LeafAnone` discharged (LANDED)

New module `SubsetSumL25/Row/KapilaAlias.lean` (a leaf of the import DAG, so no
built module's hash moved). `prelimProg`'s bootstrap layers 0–2 were **imported,
not re-derived** — the reusability claim made when the prelim bootstrap was
designed held on first use: `memOf`/`up`/`upFit`, `bv_add`/`bv_shr`/
`ofNat_lt_ofNat`, all eight `exec_*_step` peelers, and the whole input layer
came across unchanged. Exactly one new layer-2 fact was needed: `inF_two`.

## What is proved (no sorry, house triple)

| Declaration | Note |
|---|---|
| `aliasProg` | 20 instructions: `prog2` prologue + a second saved cell + the pair-witness decision |
| `aliasSpec`, `aliasCost` | the phase's value (`Option (List ℚ)`), 20 word operations |
| `inF_two` | cell 2 in `memOf` normal form (the only new layer-2 fact) |
| `alias_run` | `run aliasProg x ρ 20 = some ((aliasSpec n x ω).isSome)` — 20-instruction walk |
| `alias_sound`, `yes_of_pair`, `ofFn_sum_ite_pair` | every estimate reported is a genuine subset sum |
| `aliasSpec_isSome` | the spec's `Bool` is its `isSome` |
| `alias_run_of_field` | the field *is* the `Option`-free halt equation (nothing to peel) |
| `isSome_ne_failToNo` | the two conventions disagree at `some false` — measured, not asserted |
| `isSome_forgets_payload` | the verdict cannot see the estimate list (`LeafTest`'s residual) |
| `LeafAnone_of_alias_agrees`, `LeafAnone_of_alias_run` | the leaf, modulo the cost collapse |

**Two of four leaves closed** (`LeafP` + `LeafAnone`); `LeafBnone`, `LeafTest`
untouched.

## The divergence, resolved

`Routines.alias_agrees` is `run … = some (… .isSome)`: an equation between
`Option Bool`s with **no wrapper**, so unlike `prelim_agrees` it needs no
`map_failToNo_bind_some`-style peel — the shape does not fight. What *does* need
stating is that the conventions are not interchangeable:
`isSome_ne_failToNo` proves `isSome (some false) = true` while
`failToNo (some false) = false`. The phase succeeds or fails; it does not decide
YES/NO, so `isSome` is the only faithful reading and `LeafAnone` the only leaf it
can feed.

## Proof-engineering notes (both cost a build cycle)

1. **`omega` does not know `2^w` is even.** `2 * n < 2^w` does **not** give
   `2 * n + 1 < 2^w` from it: a model with `2^w = 2n+1` satisfies the hypothesis.
   The cure is to route through `2 * (n + 1) ≤ 2^w` and keep every step linear in
   the opaque power atoms.
2. **`unfold wordLength` after `rw [hw]` silently does not fire** when `w` is a
   `set`-local; an explicit `show` of the unfolded form is what works.

## Residual, stated plainly

`aliasSpec` is the **witness-test leg** of Theorem A (the pair `{a₁, a₂}`), sound
and entitled to FAIL — but its FAIL region is far wider than the paper's, whose
`o(1)` failure probability is what `cor_A6_per_alias` / `o7_union_le` spend.
Closing it is a backward jump (the first loop in this calculus) plus a word-op
cost model, not a longer proof of the same equation. Also uncomputed: the `ℚ`
accumulator with `n²` fractional bits, and the payload convention `LeafTest`
needs.

Next single lever: `checksumProg` (Theorem B), the same shape one step further.

## Row lane 2026-11-10 (7) — `checksumProg` authored: Theorem B's text, its witness leg proved sound *and read in §6's bin vocabulary*, `LeafBnone` discharged (LANDED)

New module `SubsetSumL25/Row/KapilaChecksum.lean` (a leaf of the import DAG, so
no built module's hash moved; `Statement.lean` still `3dc6567e…34aa`). The
prelim/alias bootstrap layers were imported, not re-derived, and exactly one new
layer-2 fact was needed (`inF_three`) — the reusability claim holds for the third
time.

## What is proved (no sorry, house triple)

| Declaration | Note |
|---|---|
| `checksumProg` | 24 instructions: cursor-first saves of all three inputs, then the constant block, then a three-cell read-back |
| `checksumSpec`, `checksumCost`, `checksumYes` | the phase's value (`Option (List ℚ)`), 24 word operations |
| `inF_three` | cell 3 in `memOf` normal form (the only new layer-2 fact) |
| `checksum_run` | `run checksumProg x ρ 24 = some ((checksumSpec n x ω).isSome)` — 24-instruction walk |
| `ofFn_sum_ite_triple`, `yes_of_triple` | the three-element indicator sums to `a₁+a₂+a₃`, so the triple witnesses `t` |
| `checksum_sound` | every estimate reported is carried by a **genuine subset** (Theorem B's requirement on `V̂_ρ`'s support) |
| `checksum_support_in_bin` | the same subset lies in the target's residue class **mod every `P`** — §6's eq. (6.1) bin, in the vocabulary this calculus has |
| `checksum_agrees_spec`, `checksum_run_of_field` | the field shape, `Option`-free, nothing to peel |
| `LeafBnone_of_checksum_agrees`, `LeafBnone_of_checksum_run` | the leaf, modulo the cost collapse |

**Three of four leaves closed** (`LeafP` + `LeafAnone` + `LeafBnone`); `LeafTest`
alone remains.

## The design change that mattered (forced, not stylistic)

Alias built its constant block into **cell 3** (`add 3 4 4` → `[3] = 6`) because
`a₃` played no part in its decision. The checksum phase reads `a₃`, so cell 3
must survive the bootstrap — and with `a₁, a₂, a₃` occupying cells 1–3 and `n` in
0, the only scratch cells are 4, 5, 6. Consequences, both forced:

1. **The saves come first, the constants after.** `2n` costs no constant
   (`add 0 0 0`), and the two successors reuse the literal `1` still in cell 6
   (`add 1 0 6`, `add 2 1 6`) — so each input cell is read on the instruction
   that clobbers it and on no earlier one. The level `6` is then built *after*
   the saves as `3 + 3` in cell 4 (`add 4 4 4`) and the gate compares against
   cell 4, which is why the gate moved from `pc 3`/cell 3 to `pc 4`/cell 4.
2. **The read-back spends the whole register file.** Cells 0 and 1 still hold the
   addresses `2n` and `2n+1` when the saves finish, so two fetches are single
   indirections (`load 6 0`, `load 5 1`); the third address is rebuilt as
   `2n + 2` from the *unspent literal* `2` still in cell 5 (`add 3 0 5`) and
   then self-loaded (`load 3 3`). The `2` in cell 5 is an address constant, not a
   value — that is why it survives to `pc 15` and a₃'s fetch comes before a₂'s.

## Proof-engineering notes (each cost one build cycle)

1. **The strict/non-strict cliff is where the alias trick runs out.**
   `2·(n+1) ≤ 2^w` (the alias `hfin`) proves `2n < 2^w`, `2n+1 < 2^w` and
   `n+1 < 2^w`, but **not** `2n+2 < 2^w`: `≤` is all it gives, and `upFit` needs
   `<`. The cure is a different route: `k < 2^k ≤ 2^w` with `k = 2n+2 ≤ w`
   (which the word length supplies: `4(n+b) + 1 ≥ 2n+2`). `Nat.lt_two_pow_self`
   then `Nat.pow_le_pow_right`.
2. **`omega` cannot see `2^·` at all**, only atoms — so every *literal* fit
   (`1, 2, 3, 6 < 2^w`) needs one numeric fact first (`hbig : 32 ≤ 2^w`, from
   `5 ≤ w`). Without it `omega` reports a counterexample with `2^w ≤ 1`.
3. **`2·(n+1) ≤ 2^(n+1)` is not omega-provable** either: the goal's
   `2^(n+1)` and the hypothesis' `2^n` are distinct opaque atoms, so the
   associativity that would join them is invisible. `Nat.mul_le_mul_left 2 hhn`
   followed by `rw [hpow]` is the proof.
4. **Peeling depth follows the *read* register's write distance, not the
   instruction count.** `[6]` is written at `pc 14` (not `pc 13` as in alias), so
   `s17 6 = a₁` needs three peels where the alias analogue needed one; a chain
   copied from the alias file without re-counting the `up` layers is the failure
   mode here.
5. **`rw [...]` can close a goal**, after which a trailing `; omega` reports
   `No goals to be solved` — an *error*, not a warning. `s14 0 + s14 5 = 2n+2`
   by `rw [v140, v145]` is one such goal.

## The §6 semantics, stated honestly

`V_ρ` is a complex sum over a residue bin, one term per subset, with retained
phases. The in-tree calculus has no `ℂ`, no phases (`Draws` is a word stream and
this leg ignores it) and no bin density. What the leg certifies is the
**support** of a checksum term — a subset in the bin exists — and
`checksum_support_in_bin` states that in §6's own vocabulary
(`∑ aᵢ ≡ t (mod P)` for every `P`). The magnitudes are `o5_mse_le`'s; nothing
here touches them. That is the whole of the "genuine checksum" claim this text
can carry, and it is stated as such rather than as the paper's `1/8`.

## `LeafTest`'s obligations in final form (the residual seam, enumerated)

Not proved, stated so the remaining work is exactly bounded. With
`Â = R.aliasA n x ω` and `V̂ = R.checksumB n x ω` both `some`-valued, on
`R.fallback n x = false`, the segment must establish **four** things:

1. **Two payload programs.** `aliasProg` and `checksumProg` must leave their
   estimate lists in memory — `isSome` (what both current fields certify)
   *forgets* the payload (`isSome_forgets_payload`), so `LeafTest` needs the
   payload convention both modules deliberately declined.
2. **The scan's loop rules.** `rowTest_eq_of_rules` already reduces the test
   itself to nil/nil, nil/cons, cons/nil and cons/cons — three equations at the
   segment's exit, no reasoning about `rowTest` required. What is missing is the
   loop: the first backwards jump in this calculus, plus a word-op cost model
   for it.
3. **The estimates' arithmetic relation.** The difference `V̂_s − Â_s` must be
   the bin sum the test compares against `1/2`. Neither leg pins that relation —
   alias certifies `Â`'s support, checksum certifies `V̂`'s — so this is a
   *joint* obligation on the two payloads, not a consequence of either.
4. **The multi-word accumulator.** Both estimate lists are `ℚ` values at `n²`
   fractional bits while `w = O(n+b)`; the expansion is absorbed
   (`withinEnvelope_wordop_absorb`) but the `ℚ` layout is not written.

`LeafTest` therefore needs: the payload convention (1), the loop + cost (2),
the cross-estimate relation (3), the accumulator layout (4) — and then
`agrees_main` is assembled from four leaves.

### Addendum — the barrel import was verified after the receipt

The receipt's build targets are the row closure (the lane's rule: a whole-
`SubsetSumL25` build drags in the sibling's WIP `M7`). The **barrel edit**
(`SubsetSumL25.lean` + `import SubsetSumL25.Row.KapilaChecksum`) is therefore
not covered by that receipt, so it was verified separately:
`lake build SubsetSumL25` → `✔ Built SubsetSumL25`, with the only failure being
`SubsetSumL25.Proofs.M7` — the sibling's WIP module, which imports no `Row`
module (`Statements.DS`, `M6`, `O8`) and was never in this lane's targets. That
build also ran with the lock expired (181 s bounded wait, deviation recorded
here); no sources were touched by it.

## Row lane 2026-11-10 (8) — the payload convention landed: `LeafTest`'s first obligation is statement-complete (LANDED)

New module `SubsetSumL25/Row/KapilaTest.lean` (a leaf of the import DAG, so no
built module's hash moved; `Statement.lean` still `3dc6567e…34aa`).
Statement-and-definition work only: **no walk, no loop, no cross-estimate
relation** — exactly the boundary the round was scoped to.

The obligation it closes is the one `isSome_forgets_payload` named. The three
landed legs agree with their `Routines` fields through `Option.isSome`, which
records *that* a phase succeeded and discards *what it left behind*; `LeafTest`
consumes the lists themselves. `KapilaTest` supplies them from the one place
they can honestly come from — the segment's exit memory.

## What is landed (no sorry, house triple)

| Declaration | Note |
|---|---|
| `payloadBlock` | `len` words from `base` read as fixed point at `2^-fracBits` — the layout §6.2's `n²` fractional bits live in |
| `PayloadConvention` | the exit contract: `fracBits`, `blockLen`, `baseA`, `baseV`, the exit `mem`, the verdict function, and the three `rowTest` rules |
| `.Ahat` / `.Vhat` | **defs**, not fields: the two payload lists as the exit memory holds them |
| `.aAt` / `.vAt` / `.dAt` | per-word reads and the estimate `d = V̂_i − Â_i` §7 step 7 actually compares |
| `.Ahat_eq_map`, `.Vhat_eq_map`, `.Ahat_length`, `.Vhat_length`, `payloadBlock_getElem?` | well-formedness (the accumulator obligation's per-word shape) |
| `.dAt_eq` | **the payload survives**: `d` is two words and a scale, nothing else |
| `.verdict_eq_rowTest`, `.verdict_Ahat_Vhat` | the three exit equations *determine* the verdict (`rowTest_eq_of_rules`) |
| `payload_rules_iff` | and the rule set is *exactly* `rowTest` — neither too weak nor stronger |
| `rowTest_separates_payloads`, `isSome_not_enough` | the test consumes the payload; equal `isSome`s are still separable, so no `isSome` field can supply `LeafTest`'s input |
| `LeafTest_of_payload_exit` | sufficiency, statement only: reach such an exit *carrying the field payloads* ⇒ `LeafTest`, verbatim |

## The design change that mattered (forced, not stylistic)

**The payloads are `def`s and the structure has no equation asserting them.**
The tempting shape is a pair of fields `Ahat Vhat : List ℚ` plus
`hA : Ahat = payloadBlock …`. That shape lets the convention *lie*: `hA` is an
obligation that can be false, and a `Routines` builder could satisfy it with a
list threaded beside the state rather than in it — the `isSome` gap one level
down. As defs, `Ahat`/`Vhat`/`dAt` are definitionally the memory read, so the
`ℚ` accumulator layout obligation has exactly one shape to prove (the exit
memory holds these words at this scale) and nothing else to be talked out of.

**Three rules, not four.** `rowTest_eq_of_rules` takes three hypotheses, because
`rule_nil_left : ∀ V, verdict [] V = false` subsumes both empty cases; the
"nil/nil and cons/cons" phrasing in the paper's reading is the segment-level
view of the same three. `payload_rules_iff` pins that this is not a loss.

## What this does not touch (the seam, still bounded)

`LeafTest`'s remaining three items are unchanged and now each has a named place:
the loop + its word-op cost (item 2 — `payload_rules_iff` says exactly which
three equations an instruction-level proof must establish, and
`payloadBlock` is deliberately *static*, so the loop is what fills an arbitrary
number of blocks), the cross-estimate relation `d_i = bin sum` (item 3 — `dAt`
is now the object such a statement is about), and the multi-word accumulator's
word arithmetic (item 4 — `fracBits`/`blockLen` are §6.2's `n²` and
`⌈n²/w⌉ + 1`, and `dAt_eq` is the two-word form).

## Lane rule: every waiter carries a hard expiry (measured this round)

Two builds this round, both behind `/Volumes/Substrate-1/bigo/.build.lock`, both
deviating: the receipt build proceeded **UNLOCKED after 301 s**, the barrel build
**after 241 s**. Measured contention at the time: **2 foreign lock-fd holders**
(zeta's `locked_run.py`, weil's `closure_supervisor.py`) plus **4 foreign lean
processes** (a Stacks build). The barrel build then died at `[8971/8976]` with
**exit -9, zero error lines** — the documented class: a runner that
`SIG_IGN`s TERM by design gets SIGKILLed when something wants the host back.

The precedent is the 2 h 19 m stale waiter: an *unbounded* `flock` parked a lane
for two hours and nineteen minutes, and the stale waiter had to be SIGKILLed
because these runners ignore SIGTERM. So the rule, now lane discipline:

> **Every waiter carries a hard expiry.** A TERM-ignoring runner cannot be
> asked to leave, so its *owner* timeout is the only thing that bounds it. The
> wait bound is what guarantees both that the lane makes progress and that no
> waiter outlives its purpose; the deviation is recorded in `lock.acquired`
> rather than silently absorbed.

## Receipts

`receipts/kapila-20261110T182651Z`: gate `swapouts_delta60=0 free_pct=69`;
build exit 0 in 55.1 s (`✔ Built SubsetSumL25.Row.KapilaTest` at
`[8932/8932]`, 8932 jobs); `KapilaTest.olean` 250600 bytes, sha256
`afb4844d…24b1ad`, mtime this run; axiom banner exit 0 with
`axiom_banner_house_triple_only: true` (every new declaration in
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`, no `native_decide`);
no `declaration uses 'sorry'` in the build log.

**Barrel edit, verified separately** (the receipt's targets are the row closure,
so the `SubsetSumL25.lean` import is not covered by it — the same lane rule as
the previous round). The check is `lake build SubsetSumL25`, and this round it
was **killed**: reach `[8971/8976]`, exit -9, zero `error:` lines. What it
established before dying is the thing the check asks: **the barrel module
compiled** — `.lake/build/lib/lean/SubsetSumL25.olean`, written 10:40:25 during
that run (the source is 10:26:36). *Which* jobs it never reached is
**unmeasured** — the
log stops at the replay line for `Row.KapilaChecksum` and the buffered tail was
lost with the process — and it is not re-run here: a whole-`SubsetSumL25` build
drags in glob-matched modules outside this lane's targets, and the barrel's own
compilation is the question this check exists to answer.

## Row lane 2026-11-10 (9) — §7 step 7's scan: the loop, its three exit equations, the backwards jump (LANDED)

New module `SubsetSumL25/Row/KapilaLoop.lean` (~960 lines, a leaf of the import DAG;
`Statement.lean` still `3dc6567e…34aa`). This is the lane's **first backwards jump**
and it is a *proved* loop, not a sketched one.

## Landed (no sorry, house triple)

| declaration | content |
|---|---|
| `selfLoop_never_halts` | the calculus's only termination mechanism is fuel: a program that jumps to itself unconditionally returns `none` at every fuel. Stated because the lane's previous texts had no backwards jump and the semantics were implicit. |
| `bv_sub`, `exec_sub_step`, `bv_div`, `exec_div_step` | the two peelers the lane lacked (`sub`, `div`) |
| `wordDiff`, `hitOf`, `hitWord` | `|v − a|` by one `blt`; and `(d/h)/(d/h)` — the branchless `1 iff h ≤ d` (division by a larger word is `0`, which is the `d < h` case; no sign test, no extra branch) |
| **`hitWord_eq_ratTest`** | the computed word *is* the paper's test: with `h = 2^(fracBits−1)` and words at `fracBits` fractional bits, `hitWord = 1 ↔ 1/2 ≤ |V̂ − Â|` |
| **`scan_fold_rules`** | **the three exit equations** of `payload_rules_iff` (nil/nil, nil/cons, cons/cons) proved of the object the instruction text computes, in the `ℚ` vocabulary |
| **`anyHit_eq_rowTest`** | those three equations give `rowTest` on the two blocks |
| `scanProg` | §7 step 7 as 21 instructions; the backwards jump is `pc 17 → pc 4` |
| `scan_head`, `scan_branch_lt`, `scan_branch_ge`, `scan_suffix`, **`scan_body`** | one iteration walked: 12 steps, uniform across the data because the two `pc 8` paths are length-balanced; the invariant (`LoopInv`) re-established |
| **`scan_loop`** | the loop rule: `m` iterations consume `12·m` steps and exit at `pc 18` with the accumulator `acc + hitCount` over the remaining block |
| `scan_epilogue` | the exit test `0 < acc` → accept/reject, 2 steps |
| `payloadBlock_memOf`, `wordList_one`, `agree_up`, `Scratch`/`Layout`/`LoopInv` | the layout vocabulary: the loop writes only `{0,3} ∪ 7…13`, so it is transparent on the payload blocks at `14` and above |

## Design decisions that mattered (measured)

1. **The iteration cost must not depend on the data.** The first draft branched
   on `v < a` and then conditionally skipped the accumulator write, giving
   per-iteration costs of 9–11 steps — which makes the loop's fuel a *sum of
   data-dependent terms* instead of a multiplication. Two changes fixed it: the
   accumulator became a **count** (`add`, never `or`, so no branch is needed to
   set it) and the two branch paths were padded to equal length (both land on
   `pc 13` after 7 steps). Result: exactly 12 steps per iteration, for every input.
2. **The branchless comparison is `(d/h)/(d/h)`.** This calculus's division by a
   larger word is `0` (`[j]/0 = 0` and `d/h = 0` for `d < h`), so the two-division
   form is `1` exactly when `h ≤ d` and `0` otherwise — no sign test, no padding.
3. **`Scratch` must enumerate the written cells, not bracket them.** The first
   version was `{0,3} ∪ [7,13]`, which contains cell `12` — a *read-only constant*
   (the zero the unconditional jumps use) — so the transparency lemma was proved
   about the wrong region and `12` fell out of the invariant. The enumeration
   `{0,3,7,8,9,10,11,13}` is the correct one.

## Proof-engineering notes (each cost ≥1 build cycle)

* `List.map_map` does not match this pin's `Functor.map` presentation of
  `List.map`; `map_map'` (by induction) does. Same for the library's `zipWith`
  commutations (`zipWith_map_map'`, `any_zip_with_congr`).
* `(S + 4) - 1` is *defeq* to `S + 3` but not syntactically, so a peeler's
  `S - 1` does not match the next peeler's `S` under `rw`. The cure is
  `rw [show S + 4 - 1 = S + 3 from rfl]` after each step (or instantiating the
  step at a fuel that already has the right shape).
* `simp [up]` closes ground cell equalities (`up g 9 v 12` → `g 12`), so the
  invariant's cell facts are one-liners once the state is `set`.
* Section variables for `f0`/`N`/`h`/`baseA`/`baseV` must be passed **by name**
  (`(f0 := f0)`) at the call site: with two `Nat → Nat` parameters in scope the
  wrong one is inferred, and the failure surfaces as a `rewrite` "pattern not
  found" two lines later.

## The residual, exactly (three pieces, each named at the bottom of the module)

1. Four-instruction **prologue** (`pc 0 → pc 4`) + the **run assembly**
   (`12·N + 6` steps).  Removed from this landing for want of a `1 ≤ w`
   hypothesis (the literal `1 < 2^w`); `scan_epilogue` (the exit) *is* landed.
2. The **`rowTest` verdict at the exit** = (1) + `hitCount_pos_iff` +
   `anyHit_eq_rowTest` + `payloadBlock_memOf`.  Every ingredient proved here.
3. The **word-op cost model**: `blockLen·(2·wordOpFactor n + 3) ≤ (n+b+2)^7` and
   `scan_cost_absorbed` with the envelope's `K` raised by **seven** (not three —
   the nested multi-word loop squares `wordOpFactor`).  Stated, not proved.

Also untouched (as before): `LeafTest`'s items 3 and 4 (the estimates'
arithmetic relation and the multi-word accumulator layout).

## Receipts

`receipts/kapila-20261110T201147Z`: gate `swapouts_delta60=0 free_pct=72`;
build exit 0 in 37.5 s (8933 jobs); `KapilaLoop.olean` 2085280 bytes, sha256
`509a1517…6e98e`; axiom banner exit 0, `axiom_banner_house_triple_only: true`
(76 banners, none outside `[propext, Classical.choice, Quot.sound]`); no
`declaration uses 'sorry'`. Lock: **DEVIATION, proceeded UNLOCKED after 241 s**
(recorded in `lock.acquired` and `summary.json`), per the lane's hard-expiry rule.
The receipt's targets are the row closure; the `SubsetSumL25.lean` barrel import
is *not* covered by it (same lane rule as the previous rounds) — the line is one
import, mirroring `KapilaTest`'s.

Next single action: the prologue + `scan_run` (add `hw : 1 ≤ w`, then compose
`scan_loop` at `m = N`), then its `rowTest` form, then the cost pair.

## Row lane 2026-11-10 (10) — the prologue, the run at `12·N + 6`, and §7 step 7's verdict at the exit (LANDED)

Same module (`SubsetSumL25/Row/KapilaLoop.lean`, now §L8 appended, a leaf of the
import DAG; `Statement.lean` still `3dc6567e…34aa`; the barrel already imported
`KapilaLoop`, so no barrel line moved this round). Two of the three residual pieces
named at the bottom of round (9) are closed; the third is now stated in one place
(the module's closing comment) instead of two.

## Landed (no sorry, house triple)

| declaration | content |
|---|---|
| `wordLength_ge_one` | **`1 ≤ w` is free at the lane's word length**: `1 ≤ wordLength n b` for every `n`, `b` — the definition's last summand is `+ 1`, so no `1 ≤ b` side condition (contrast `wordLength_ge_five`). Depends only on `[propext, Quot.sound]`. |
| `one_lt_two_pow` | the step from the hypothesis to the literal `1 < 2^w` the prologue's `[1] := 1` needs |
| `Layout.baseA_ge`, `Layout.baseV_ge` | the two payload bases past the scratch window, as accessors (`hL.2.2.2.2.2.2.1` no longer spelled at call sites) |
| **`scan_prologue`** | `pc 0 → pc 4` in 4 steps: `[1] := 1`, `[12] := 0`, `acc := 0`, `k := 0`, leaving `LoopInv w f0 fp 0 0` |
| **`scan_run`** | **the run assembly**: `exec scanProg ρ (12·N + 6) 0 0 (memOf w f0) = some (decide (0 < hitCount h (wordList f0 baseV N) (wordList f0 baseA N)))` — prologue (4) + `scan_loop` at `m = N` (12 each) + epilogue (2), composed at `S = 12·N + 2` / `S = 2` / `S = 0` |
| **`scan_run_eq_rowTest`** | **§7 step 7's verdict at the exit**: the same run equals `some (Routines.rowTest (payloadBlock fracBits baseA N (memOf w f0)) (payloadBlock fracBits baseV N (memOf w f0)))`, by `hitCount_pos_iff` + `anyHit_eq_rowTest` + `payloadBlock_memOf` |

## The `hw` question, answered twice

The round (9) residual said the prologue was removed "for want of a `1 ≤ w`
hypothesis (the literal `1 < 2^w`)". Two answers, and both are now in the module:

1. **Carried, as the arithmetic hypothesis the statement contemplates.** `scan_run`
   and `scan_prologue` take `hw : 1 ≤ w`; nothing else in the lane's loop statements
   needed it, because the loop body only ever writes `0`, sums and quotients of
   fitting words. The prologue is the only place a *literal* enters the state.
2. **Proved free at the lane's own word, so the hypothesis never has to be supplied
   by hand.** `wordLength n b = 4·(n+b) + log2((n+2)^4 − 1) + 1`, so
   `1 ≤ 4·(n+b) + … + 1` is `omega` on the shape of the definition alone:
   `wordLength_ge_one n b` holds for **every** `n`, `b`, with no `bits_pos` input.
   The row's instance therefore discharges `hw` by `wordLength_ge_one` — unlike the
   lane's other modules, which need `wordLength_ge_five (bits_pos x)`.

So the honest verdict is: *not* an extra assumption on the row; it is a fact the
definition already carries, stated once.

## `1 ≤ N` is genuinely needed, and it is a fact about the program

Found while assembling the run, and worth recording because it is not a proof
nuisance: **`scanProg` is a do-while.** The jump is at the *bottom* (`pc 17`), so the
body at `pc 4` runs at least once and `k = 0` always reads the block's first word.
`scan_loop` records exactly this (`1 ≤ m`), so `scan_run` carries `hN1 : 1 ≤ N`
rather than pretending an empty block has a run. A `for`-shaped reading of §7 step 7
would have been wrong here.

## Proof-engineering notes (each cost one typecheck cycle, ≈35 s)

* **`simpa` will not close `1 < 2^w`.** The library's own `pow` simp set normalizes
  `1 < 2^w` to `¬ w = 0`, so `simpa using hp` fails with *"expected `¬w = 0`"*.
  The literal is closed by `rw [show (2:ℕ)^1 = 2 from rfl] at hp` then `omega`.
* **`have hV := wordList f0 baseV N` does not abstract anything.** It is a local
  definition, and `rw` matches syntactically — the goal keeps the expanded term and
  `rw [hstep]` reports "did not find an occurrence". Either write the terms out or
  use `set … with h`. (Written out here: four occurrences per line, but no trap.)
* **`scan_loop` asks for `LoopInv w f0 f (N - m)`**, so instantiating at `m = N`
  demands `LoopInv w f0 fp (N - N) 0`, while the prologue supplies `… 0 0`. One
  `Nat.sub_self` transport (`hinvp'`) spans the two spellings. The statement is
  contravariant in exactly this way; expect it at every composition.
* **`scratch_twelve` is `scratch_const_twelve`.** The two families are named
  differently (`scratch_zero`/`scratch_three`/`scratch_seven`… vs
  `scratch_const_one`/`…_twelve`), and the error is `unknown identifier`.
* **Agreement comes out *total* here, not just off-scratch.** The prologue writes
  cell `1` with the value it already holds (`Layout` fixes `f0 1 = 1`) and cell `12`
  with `0` (`Layout` fixes `f0 12 = 0`), so `s4 z = f0 z` for **every** `z`; only the
  two cells `0` and `3` are genuinely overwritten, and both are scratch.

## The residual, now one piece (plus `LeafTest`'s untouched two)

1. **The word-op cost model** — stated in the module's closing comment with its call
   site: `KapilaAlgo.withinEnvelope_wordop_absorb` raises `K` by **three**, which is
   exactly `wordOpFactor n ≤ (n+b+2)^3` (`wordOpFactor_le_cube`), the *linear* charge.
   The scan's charge is a *different function* of `wordOpFactor` (squared, since a
   comparison loop nests inside an outer `blockLen` loop), so that lemma cannot be
   cited directly; round (9) sketched the replacement's exponent as `K + 7`. Two
   lemmas named, neither proved, and **the `^7`/`K+7` are the residual's target, not
   a checked bound**:
   `scanWordOps_le : blockLen·(2·wordOpFactor n + 3) ≤ (n+b+2)^7` and
   `scan_cost_absorbed : (R.cost + scanWordOps : ℕ) ≤ K₀·2^E·P^(K+7)`.
2. **`LeafTest`'s items 3 and 4** — the estimates' arithmetic relation and the
   multi-word accumulator layout — untouched, as before.

## Receipts

**Final: `receipts/kapila-20261110T212539Z`** — gate `swapouts_delta60=0 free_pct=74`
(iter 1). Build exit 0 in 45.5 s, `⚠ [8933/8933] Built SubsetSumL25.Row.KapilaLoop`:
the changed module **rebuilt**, not replayed (olean mtime = that run, 2250424 bytes,
sha256 `b4daaaff…46efe`; the other nine oleans are replays, as in every previous
round). Axiom banner exit 0, `axiom_banner_house_triple_only: true` (81 banners; the
five new declarations report `[propext, Classical.choice, Quot.sound]`, and
`wordLength_ge_one` only `[propext, Quot.sound]`); no `declaration uses 'sorry'`.
Lock: **DEVIATION, proceeded UNLOCKED after 241 s** (recorded in `lock.acquired` and
`summary.json`) per the lane's hard-expiry rule — the fleet build lock was held
throughout the bounded wait.

That receipt supersedes `receipts/kapila-20261110T210808Z` (the same tree **before** a
doc-only pass to the module's closing comment: the cost residual's `^7`/`K+7` split is
now labelled as round (9)'s sketch rather than as a derivation, because no arithmetic
lemma in the module backs any particular split of the seven). Both receipts are kept;
the second is the one that covers the landed bytes.

**One failed attempt, and why it is kept:
`receipts/kapila-20261110T211651Z` — `STATUS: FAIL build_exit=-9`.** The gate opened
(`delta60=0 free_pct=73`) but the build was SIGKILLed at job `[8931/8933]`, i.e. the
instant it started compiling `KapilaLoop`. Cause is host pressure, not the proof: the
*first* gate iteration of that run measured `swapouts_delta60=22372` (the host was
swapping hard), and two sibling lanes' lake jobs — `Widgets` and a 27-module
`StacksFrontier` list — were live throughout. Exit `-9` is SIGKILL, which the runner's
own SIGTERM/SIGHUP shielding does not cover (it shields itself, not an OOM kill of a
child). Recorded rather than deleted because a `-9` that looks like a gate failure is
exactly the shape that gets misread as a proof failure next time.

## Two facts the next mind should not have to re-derive

* **The fleet build lock is effectively permanently held** by
  `weil-verify-lane/closure_supervisor.py` (measured: 5 h 53 m at 21:02 UTC, still the
  holder at 21:30). Every receipt in this round therefore landed on the 241 s
  hard-expiry, UNLOCKED. That is the lane rule working as designed, not a defect — but
  it means "acquired the lock" is not the signal to wait for; the gate is.
* **The build gate's `swapouts_delta60` is the load-bearing half**, not `free_pct`
  (72–74 % throughout). `22372 → 0` between two gate iterations is the fleet settling;
  a build launched inside that `22372` window is what got SIGKILLed.

Next single action: `scanWordOps_le` — and the first job inside it is to find the
*true* exponent rather than inherit the residual's `^7`. `scanWordOps` is
`blockLen·(2·wordOpFactor n + 3)` with `wordOpFactor n = n² + 1`, so it is a cubic in
`n` (`≈ 2n³`) and `blockLen ≤ n` is the only block fact needed: the `^7` target is
almost certainly loose, and a loose exponent is a weaker absorption than the row can
have. Establish the tight bound first, then `scan_cost_absorbed` follows by the same
argument `withinEnvelope_wordop_absorb` runs with the factor's exponent abstracted
(and the `K + 7` re-derived, not assumed).
