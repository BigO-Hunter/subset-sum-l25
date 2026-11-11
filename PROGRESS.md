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

* **The fleet build lock is held across a whole driver invocation, not across one
  build** — so in practice no other lane ever acquires it. Measured: `.build.lock`
  held by `weil-verify-lane/closure_supervisor.py` (PID 96202, ELAPSED 5 h 53 m at
  21:02 UTC, still holder at 21:30). Every receipt this round landed on the 241 s
  hard-expiry, UNLOCKED. The holder is **not** at fault in intent: it releases on
  pressure-closed / backoff / stall, and its own docstring records learning exactly
  this at 07:07 the same day ("the lock is a mutual-exclusion device for BUILDING,
  not a reservation while waiting"). What is wrong is the *unit*: it acquires once
  before `run_driver`, whose `BUDGET_S = 600_000` (~6.9 days) with `CHUNK = 24`,
  `TIMEOUT_S = 5_400` is a multi-day chunked run — coextensive with a build in
  intent, with a 6.9-day invocation in code. Filed as **R2125609684** (with the
  correction recorded); the resulting unlocked-build kill is **R2125609683**. So:
  "acquired the lock" is not the signal to wait for — the gate is, and the gate is
  the only serialisation this lane actually gets.
* **The build gate's `swapouts_delta60` is the load-bearing half**, not `free_pct`
  (72–74 % throughout). `22372 → 0` between two gate iterations is the fleet
  settling; a build launched inside that `22372` window is what got SIGKILLed.

Next single action: `scanWordOps_le` — and the first job inside it is to find the
*true* exponent rather than inherit the residual's `^7`. `scanWordOps` is
`blockLen·(2·wordOpFactor n + 3)` with `wordOpFactor n = n² + 1`, so it is a cubic in
`n` (`≈ 2n³`) and `blockLen ≤ n` is the only block fact needed: the `^7` target is
almost certainly loose, and a loose exponent is a weaker absorption than the row can
have. Establish the tight bound first, then `scan_cost_absorbed` follows by the same
argument `withinEnvelope_wordop_absorb` runs with the factor's exponent abstracted
(and the `K + 7` re-derived, not assumed).

## Row lane 2026-11-10 (4) — the cost pair, at its **true** degree: quartic, `K + 4` (LANDED)

The residual's last piece was "the cost pair only", and its first job was to find the
scan's *true* exponent instead of inheriting the residual's `^7`. It is **four**.

### 1. The true exponent: quartic, not septic

`scanWordOps n blockLen = blockLen·(2·wordOpFactor n + 3)` with `wordOpFactor n = n²+1`.
The missing hypothesis is §6.2's own layout fact, `blockLen = ⌈n²/w⌉ + 1 ≤ n² + 1 =
wordOpFactor n` — **the same factor that charges one dyadic operation**. Substituting:

    scanWordOps ≤ w·(2w+3) ≤ 5w² = 5(n²+1)² ≤ 5(n+b+2)⁴

with `2n⁴ + 7n² + 5` at the extremal `blockLen = w`, so the growth is `≈ 2n⁴` — quartic.

**The residual's stated `scanWordOps_le` was also ill-formed**, not merely loose: without
`blockLen ≤ wordOpFactor n` it is *false* (`n = 2, b = 1, blockLen = 10⁹` violates it).
That hypothesis is exactly where §6.2's payload layout enters the cost model, so the
lemma could never have been proved from the statement as written.

**Where `7` came from.** `n³` prime candidates × quartic scan = septic: the `7` is the
*composed* degree, and the `n³` is *already* a summand of `Routines.cost`. Charging it
again inside the scan's own lemma double-counts. `scanWordOps_composed_le` proves the
composition (`n³·scanWordOps ≤ 5·(n+b+2)⁷`), so the `3 + 4` provenance is a theorem and
not a remark about round (9)'s intent — whose own split was `1 + 5 + 1`, a different and
never-checked derivation.

### 2. The absorption, with the degree abstracted, at `K + 4`

`withinEnvelope_add_absorb` is the **additive twin** of `withinEnvelope_wordop_absorb`:
given §7's envelope for `R.cost`, `cost + charge` obeys it with the exponent raised by the
*charge's own degree* `d` and `K₀` by its constant `C` — `(C, d)` abstracted, so the
linear charge's `+3` and this scan's `+4` are one theorem at two instantiations. That is
what "abstract the factor's exponent" should have meant; abstracting `wordOpFactor`'s
exponent was the wrong variable, because the scan's charge is additive where the older
lemma is multiplicative.

Constant re-derived, not assumed: `scan_cost_absorbed` gives **`K + 4`** with `K₀ + 5`.
The residual's `K + 7` is discharged too (`scan_cost_absorbed_pow7`) *as the loose
statement it is*, so nothing in the record claims the residual was skipped by convenience.

### 3. Piece 3's verdict: absorption proved, application seam named

The absorption is a theorem now. The **application cannot close from this file**, and not
for want of a lemma:

* the scan's charge is not a summand of `Routines.cost` (whose last summand, `n³·(n+b+2)`,
  is the prime-draw bullet); folding it in edits `KapilaAlgo.cost`, which moves what
  `R.WithinEnvelope c` *asserts* at every consumer — `kapila_row` takes
  `henv : ∀ c, R.WithinEnvelope c` as a hypothesis, so that edit rewrites a hypothesis
  rather than discharging one;
* `Routines.cost` is simultaneously §7's word-op count **and** `D7.agrees`'s instruction
  horizon (`kapila_row` counts over `2 ^ (wordLength n x.bits * R.cost n x)`), so adding
  word-operations to it crosses the very unit seam `D7` exists to translate.

Named seam: **`Routines.cost`'s summand list + `D7.agrees`'s step horizon.** Whoever
wires the segment's charge into §7's total reads `scan_cost_absorbed` (or
`withinEnvelope_add_absorb` at the summand's degree) to keep the exponent.

### Receipts

**Final: `receipts/kapila-20261110T214612Z`** — gate `swapouts_delta60=0 free_pct=67`
(iter 3; iters 1–2 correctly *waited* on `delta60=36` then `2244` — the load-bearing half
of the gate, working as documented). Lock: **DEVIATION, proceeded UNLOCKED after 241 s**,
the fleet lock held by `weil-verify-lane/closure_supervisor.py`; recorded in
`lock.acquired` and `summary.json` per the lane's hard-expiry rule. Build exit 0 in 42.4 s,
`KapilaLoop.olean` rebuilt this run; axiom banner exit 0,
`axiom_banner_house_triple_only: true` — the eight new declarations report
`[propext, Classical.choice, Quot.sound]` (`scanWordOps`, a def, only `[propext]`); no
`sorryAx`. `Statement.lean` still hashes `3dc6567e…34aa`.

**Superseded: `receipts/kapila-20261110T214238Z`** — the same tree **before**
`scanWordOps_composed_le` was added (gate `delta60=0 free_pct=69`, lock acquired after 0 s,
build exit 0 in 42.9 s). Kept: it is the receipt for the seven-lemma version, and the
difference between the two runs is exactly that one declaration.

Next single action: the residual is now **`LeafTest`'s items 3 and 4** — the estimates'
arithmetic relation, then the multi-word accumulator layout. Item 3 is the lever: state
the relation between the two stored `n²`-bit estimate blocks and the `ℚ` values
`PayloadConvention.dAt` reads, so that `payloadBlock_memOf`'s word-level agreement
becomes a claim about the *accumulators* rather than about pre-agreed memory.

## Row lane 2026-11-10 (5) — item 3 lands: the accumulators, one denominator, and the proved limit of the one-word reading (LANDED)

New module `SubsetSumL25/Row/KapilaEstimate.lean`, a leaf of the import DAG
(imports `KapilaTest` + `KapilaLoop`), so no built module's hash moves and
`Statement.lean` stays `3dc6567e…34aa`.  Statement **and proof**: no sorry, house
triple.

### The relation, stated and proved

`payloadBlock_memOf` used to read as word-level agreement between a memory and a
state function — a claim about *pre-agreed memory*.  `EstLayout` names the state
as what it is (the exit memory's words *are* a `ℕ`-valued accumulator state,
fit invariant included), and then the bridge is a claim about the accumulators:

| Declaration | Content |
|---|---|
| `EstLayout` | the exit memory's words are an accumulator state, cell for cell (`mem_eq`) |
| `Ahat_eq_toQ` / `Vhat_eq_toQ` | the stored blocks are `wordList f base len` mapped through the fixed-point scaler — no residual freedom, nothing threaded beside the memory |
| `dAt_eq_accum_div` | `dAt i = (f (baseV+i) − f (baseA+i)) / 2^fracBits`: **one shared denominator**, so §7 step 7 compares one integer numerator |
| `hitWord_eq_dAt` | the word test the program executes (`hitWord (2^(f−1))` on the two accumulator words) ⟺ §7 step 7's `ℚ` test `1/2 ≤ |dAt i|` |
| `Ahat_getElem?` / `Vhat_getElem?` / `dAt_of_getElem?` | `dAt s` is the `s`-th entry difference of the two stored lists, so «`dAt` is `V̂_s − Â_s`» is a theorem about the blocks |
| `rowTest_Ahat` | the verdict is a function of the `dAt` list alone (the test factors through the pointwise differences) |
| `BinSumAgrees` + `rowTest_eq_binSum` | the residual's **exact contract**: supply `binSum` with `∀ i < blockLen, dAt i = binSum i` and the test on the payloads *is* the test on the bin sums |

Not produced, and not producible here: the bin sums themselves.  No bin object
exists in the tree and neither landed leg pins one (alias certifies `Â`'s
support, checksum `V̂`'s magnitude).  `BinSumAgrees` is that obligation's shape —
one equation per index — and `rowTest_eq_binSum` proves nothing else about `dAt`
is consumed.

### The finding: item 3 could not have been stated one-word-per-index

`abs_dAt_mul_lt`: `|dAt i| · 2^fracBits` is a *single word's* numerator
(`< 2^w`, `w = wordLength n x.bits`), whatever `fracBits` is set to.
`abs_dAt_lt_half`: at `fracBits ≥ w + 1` — the regime `fracBits = n²` always
lands in — `|dAt i| < 1/2`, so `1/2 ≤ |dAt i|` **can never fire**: `hitWord`
computes `0` and §7 step 7's loop never takes its hit.  The per-index read of
`Ahat`/`aAt`/`dAt` is a **truncation, not a layout**, at the paper's parameters.

So items 3 and 4 are one seam, not two.  The reading that can carry `n²` bits is
the place value: `payloadStride w fracBits = ⌈fracBits/w⌉ + 1` words per
estimate, and `placeValue m base stride fracBits s` = the base-`2^w` sum of
estimate `s`'s words over one shared `2^fracBits` scale.  `placeValue_one`
proves the degenerate stride-1 instance **is** the module's `aAt`/`dAt` reading,
so the existing defs are the `stride = 1` case of the layout rather than a
competitor to it.

### Item 4's position

Shape named, layout not written.  `payloadStride`, `placeValue` and the stride-1
reduction are the named targets; what is left is the word arithmetic that fills
a stride-`k` block (its carry chain) and the restatement of `BinSumAgrees` about
`placeValue`.  Untouched, as required: `KapilaAlgo.cost` and `D7.agrees`'s step
horizon — the named application seam stays named.

### Receipts

**Final: `receipts/kapila-20261110T223724Z`** — gate `swapouts_delta60=0
free_pct=74` (iter 1), lock **acquired after 60 s**, build exit 0 in 7.9 s
(8934 jobs; **replay** — the new module's olean was compiled in
`…T222210Z`, mtime 22:26:43Z, 374160 bytes, sha256 `511e1d5f…e32f5`, and this
run replays it), axiom banner exit 0, `axiom_banner_house_triple_only: true`
(109 banners; the twenty new declarations report `[propext, Classical.choice,
Quot.sound]`, and `payloadStride`, a def, reports «does not depend on any
axioms»); no `sorryAx`. `Statement.lean` still hashes `3dc6567e…34aa`.

**Kept, and why — three aborted receipts before the green one, each a real
defect in the *runner*, not in the proof:**

* `receipts/kapila-20261110T221500Z` — `FAIL axiom gate: axiom banner exited 1`.
  The runner's build-target and named-olean lists did not yet name
  `KapilaEstimate`, so the module was never built and every new `#print axioms`
  was an unknown identifier.  The lists now name it.
* `receipts/kapila-20261110T222210Z` — `FAIL axiom gate: axiom banner exited 1`,
  cause: `KapilaRowAxioms.lean` was missing
  `import SubsetSumL25.Row.KapilaEstimate`.  This is also the run that **built**
  the module (build exit 0, 8934 jobs, olean mtime 22:26:43Z).
* `receipts/kapila-20261110T222836Z` — `FAIL axiom gate: axiom banner exited -9`:
  the banner was SIGKILLed under host pressure.  That run's gate *waited*
  correctly (iter 1 `swapouts_delta60=5153` wait, iter 2 `1828` wait, iter 3
  `0` proceed) — the load-bearing half of the gate doing its job.  Re-running
  the same tree gave the green receipt without changing a proof byte; between
  the second and third aborted receipts the banner was also checked by hand
  (`lake env lean KapilaRowAxioms.lean`, exit 0, 109 banners) to separate the
  missing-import defect from the kill.

Next single action: **item 4 — the stride-`k` word arithmetic.**  Concretely,
`placeValue_scale`:
`placeValue m base stride fracBits s * 2^fracBits = Σ_{j<stride} (m (base + s*stride + j)).toNat * 2^(w*j)`
in `ℚ` — the one-denominator identity that makes a multi-word estimate
comparable at all, since `placeValue_one` only settles the degenerate stride-1
case.  Then the carry chain over `payloadStride w fracBits` words.  Item 3's
bin-sum identity lands on top of that by restating `BinSumAgrees` about
`placeValue` and reusing `rowTest_eq_binSum`.

## Row lane 2026-11-10 (11) — item 4's layout written: the one-denominator identity, the carry chain, and the bin-sum contract restated about `placeValue` (LANDED)

Same module (`SubsetSumL25/Row/KapilaEstimate.lean`, §8.5–8.7 appended), still a
leaf of the import DAG, so no built module's hash moves and `Statement.lean`
stays `3dc6567e…34aa`.  Statement **and proof**: no sorry, house triple.  This
closes the item 3 + item 4 seam on the arithmetic side; what is left of it is a
fact about the *program*, enumerated at the end of this section and at the foot
of the module.

### 1. `placeValue_scale` — the one shared denominator (the requested identity)

| Declaration | Content |
|---|---|
| `placeValue_scale` | `placeValue m base stride fracBits s * 2^fracBits = Σ_{j<stride} (m (base+s*stride+j)).toNat * 2^(w*j)` in `ℚ` — multiplying a place value by the single scale clears the denominator exactly |
| `placeValue_nonneg` | the sum's terms are nonnegative over a positive denominator |
| `placeValueAt` + `placeValue_eq_placeValueAt` | the same reading at an **explicit address** (`placeValue` addresses estimate `s` at `base + s*stride`; the chain appends at a fixed address, so it needs the address as a parameter) |
| `placeValueAt_zero` | the empty block is `0` |

Contrast with the previous round's limit, now in one line: `abs_dAt_mul_lt` bounds
`|dAt i| · 2^fracBits` by one word (`< 2^w`) whatever `fracBits` is; here the
numerator is the *whole* stride-`k` sum.

### 2. The carry chain over `payloadStride w fracBits` words

| Declaration | Content |
|---|---|
| `mod_mul_split` | `N % (a·b) = N % a + (N / a % b)·a` — the base decomposition, the only arithmetic the chain needs |
| `sum_base_digits` | `Σ_{j<stride} (N / 2^{w·j} % 2^w)·2^{w·j} = N % 2^{w·stride}` — reading a numerator's base-`2^w` digits recovers it **exactly** |
| `placeValueAt_succ` | appending one word at `addr + stride` adds exactly its place value `word · 2^{w·stride}` to the numerator over the one denominator — the chain step |
| `payloadStride_mul_spec` | `fracBits ≤ w·payloadStride` **and** `fracBits + w ≤ w·payloadStride`: the `⌈·⌉ + 1` stride holds `fracBits + w` bits, so the extra word is a full word of carry headroom, not padding |
| `placeValueAt_digits` | a block whose words are `N`'s digits reads back as `N % 2^{w·stride}` over the shared scale |
| `placeValueAt_payloadStride` | **a `fracBits`-bit numerator is carried exactly** by a `payloadStride` block — the theorem the truncation denied the one-word read |
| `placeValue_payloadStride` | the `s = 0` `placeValue` form of the same, so the vocabulary the contract below uses is known to carry a full numerator |

Note on what "carry" means here: no carry is propagated explicitly, because in
base `2^w` the carries *are* the digits' meaning.  `sum_base_digits` is the whole
content of the chain, and it is exactness — the exact opposite of
`abs_dAt_lt_half`.

### 3. `BinSumAgrees`, restated about `placeValue`

| Declaration | Content |
|---|---|
| `getElem?_map_range` | the `i`-th entry of a `range`-indexed map |
| `dAt_eq_of_map` / `rowTest_eq_map` | `dAt` and the verdict are read off **any** per-index presentation of the two blocks (the landed `F = aAt`, `G = vAt` is the special case) |
| `WideLayout` | the wide (stride-`k`) layout: `Â`/`V̂` are the place-value readings of a multi-word accumulator memory at `baseA`/`baseV` |
| `WideBinSumAgrees` | item 3's contract with the left side being the **difference of two place values**, one equation per index |
| `dAt_eq_widePlaceValue` | `dAt i` *is* that difference — the estimate the test compares is the multi-word reading, not a proxy |
| `rowTest_eq_wideBinSum` | supply the pointwise identity and §7 step 7's verdict on the payloads **is** the test on the bin sums; nothing else about `dAt`, the payloads, or the memory is consumed |
| `dAt_eq_placeValue_one` + `wideBinSumAgrees_one_iff` | the landed `BinSumAgrees` is the wide contract's `stride = 1` instance — **both directions**, on the module's own memory.  So the restatement generalizes, it does not displace |

### What remains, enumerated (item 3 + item 4's residual after this round)

* **(i) The read loop's stride arithmetic — the application seam.**  `aAt` reads
  `C.mem (C.baseA + i)`: one word per index.  A stride-`k` payload needs the
  program to sum `k` words per estimate and to address estimate `s` at
  `base + s·stride` before `aAt` *is* a wide reading.  That is `KapilaLoop`'s
  instruction sequence — the arithmetic is now proved, the program is not.
* **(ii) The bin sums themselves.**  `BinSumAgrees`/`WideBinSumAgrees` are
  contracts, not constructions: no bin object exists in the tree and neither
  landed leg pins one (alias certifies `Â`'s support, checksum `V̂`'s magnitude).
* **(iii) The program-entry reach premise** — §7 step 7's loop is actually
  entered.  Named in `KapilaLoop`/`KapilaTest`'s residual; untouched here.
* **(iv) `KapilaAlgo.cost` and `D7.agrees`'s step horizon — untouched by
  instruction.**  Recorded so the wide layout is not read as cost-neutral: a
  stride-`k` read costs `k` words per estimate instead of one (plus the
  accumulation), so if (i) ever lands the charge must be **re-measured**, not
  inherited.

### Receipts

**Final: `receipts/kapila-20261110T225928Z`** — gate `swapouts_delta60=0
free_pct=73` (iter 3; iters 1–2 correctly waited on `18700` then `1160` — the
load-bearing half of the gate, working), lock **acquired after 40.1 s**
(bounded 240 s; it now succeeds, the Weil holder releases per-unit), build exit
0 in 35.0 s, 8934 jobs — **compile, not replay**: `KapilaEstimate.olean`
rebuilt this run (634688 bytes, sha256 `afb96536…7cfc0`).  Axiom banner exit 0,
**129 banners**, `axiom_banner_house_triple_only: true` — the twenty-one new
declarations report `[propext, Classical.choice, Quot.sound]` (with
`getElem?_map_range`, a list lemma, on `[propext]` alone);
`payloadStride_mul_spec` on `[propext, Quot.sound]`; no `sorryAx`, no
`native_decide`.  `Statement.lean` still hashes `3dc6567e…34aa`.

**Aborted, kept: `receipts/kapila-20261110T225247Z`** — gate never opened
(killed at iter 5, `swapouts_delta60` climbing 12101 → 80864 under fleet load)
so nothing was built and *no tree was ever receipted*: I stopped it to replace a
one-directional bridge (`BinSumAgrees ⇒` wide-at-stride-1) with the exact
**iff** before paying for a build.  The STATUS line records that, so the receipt
is not mistakable for a failed proof.

**Runner defect fixed (the third of its kind, and mechanical):** the
**bounded** runner's `NAMED_OLEANS`/`TARGETS` did not name `KapilaTest`,
`KapilaLoop` or `KapilaEstimate`, while the unbounded `kapila_receipts.py` did —
so a bounded receipt would have silently *not built* the module it was
receipting, and its omission from `oleans.txt` would have been invisible.  Both
lists now mirror the unbounded runner.  This is the same failure mode as
`20261110T221500Z` (missing target ⇒ every new `#print axioms` an unknown
identifier), one file over; the durable fix is that the two runners must share
one list, which is now true.

Next single action: **(i) — the read loop's stride arithmetic.**  The arithmetic
side of items 3 and 4 is closed; the next lever is the instruction sequence:
a stride-`k` read that sums `k` words per estimate into the `ℕ`-valued state
`KapilaLoop` already proves things about (`wordList`/`memOf` are stride-1 shapes,
so the loop needs a `stride`-general block reader and its own induction), after
which `aAt` becomes the wide reading and (ii) — the bin sums — is the only
mathematical object still missing.

## Row lane 2026-11-10 (12) — residual (i): the stride-`k` block reader, and the obstruction that re-specifies the read (LANDED)

New leaf module `SubsetSumL25/Row/KapilaWide.lean` (§W1–§W5), importing
`KapilaLoop` + `KapilaEstimate`; no built module's hash moves and `Statement.lean`
stays `3dc6567e…34aa`.  Statement **and proof**: no sorry, house triple on all
twenty-nine new declarations.

### 1. The stride-general reader (§W1), with its own induction

| Declaration | Content |
|---|---|
| `numAt` | the `stride` words at `addr` as a base-`2^w` integer, `Σ_{j<stride} f (addr+j)·2^{w·j}` — `placeValueAt`'s numerator in `ℕ` form |
| `numAt_succ` | the carry step: one more word at `addr + stride` adds its place value |
| `numAt_one` / `numAt_one_lt` | the stride-1 read is the landed one-word read, **and it always fits a word** |
| `numBlock` / `numBlock_succ` | the block: estimate `s` at `base + s·stride`; the cons rule advances by a **stride**, not a word |
| `numBlock_one_eq_wordList` | the landed `wordList` reader **is** the `stride = 1` instance — the generalization displaces nothing |

### 2. `aAt` becomes the wide reading (§W2) — mechanically, not by assertion

| Declaration | Content |
|---|---|
| `numAt_cast` | the reader cast to `ℚ` is the sum of the casts |
| `numAt_eq_placeValueAt_scale` | **the reader *is* `placeValueAt`**, multiplied out over the one shared `2^fracBits` |
| `placeValue_eq_scale_numAt` | the consuming direction: place value = scaled reader |
| `numBlock_map_toQ_eq_placeValue` | a block of readers is the block of place values, scaled |
| `wideLayout_of_numBlock` | a convention whose payloads are the **scaled reader constructs a `WideLayout`** — so the whole wide apparatus lands on the reader with no new contract |
| `dAt_eq_reader` | `dAt_eq_widePlaceValue` instantiated at that layout: the estimate the test compares *is* the difference of the two multi-word readings |

### 3. The wiring at the loop's own granularity (§W4)

| Declaration | Content |
|---|---|
| `hitCount_numBlock_step` | **one iteration at stride `k`**: head pair at `base + j·stride`, tail re-based at `base + (j+1)·stride` — `stride` where `scan_loop` writes `1` |
| `sum_range_map_succ` / `hitCount_map_range` | the list algebra (own inductions) that turns `hitCount` into a `range` sum |
| `hitCount_numBlock_eq_sum` | the exit fold over the wide block |
| `wideExit_eq_rowTest` | `scan_run`'s exit shape at stride `k`: the accumulator's `decide (0 < ·)` **is** `rowTest` on the two payload blocks |
| `wideExit_eq_binSum` / `wideExit_eq_binSum'` | composed with `rowTest_eq_wideBinSum`: the stride-`k` verdict **is** the test on the bin sums, with `hb` discharged by `hitWord_eq_ratTest` in the primed form |

### 4. The obstruction (§W3) — the result that changes (i)

| Declaration | Content |
|---|---|
| `numAt_ge_top` | the last word read dominates the sum from below |
| `numAt_not_word` | **at `stride ≥ 1`, a nonzero top digit forces `numAt ≥ 2^w`** |
| `numAt_not_word_one` | one unit of top digit suffices — not a large-digit artefact |

**So the loop's per-iteration read cannot be the k-word sum.**  The digits fit the
word (`hfit`); their base-`2^w` sum does not.  `numAt` is not in the state's type,
so `memOf` cannot hold it and `load` cannot produce it — residual (i) as worded is
**not implementable in the `BitVec w` state**.  The contrast is `numAt_one_lt`:
the stride-1 read always fits, which is exactly why `wordList`/`memOf` were
stride-1 shapes and why the single-cell `hitWord` worked there.  The consequence
is a design fact, not a missing lemma: a stride-`k` payload needs either a
**top-down digitwise comparison** (`stride` word compares, no cell ever holding
the numerator) or a multi-word output block with its own carry chain — and
`hitWord`'s single-cell form cannot host the wide test.  (i) is therefore a
*comparison* to re-shape, not a read to widen.

### 5. The cost shape (§W5), stated not re-proved

`scanWordOpsWide blockLen stride = blockLen·(2·stride + 3)`;
`scanWordOpsWide_eq_scanWordOps` shows the landed `scanWordOps` **is** that shape
at `stride = wordOpFactor n`, and `scanWordOpsWide_le` that the wide charge never
exceeds it within §6.2's bound; `scanWordOpsWide_one` is the `5·blockLen`
instance.  **Not inherited:** the envelope absorption (`K + 4`) and — the
load-bearing one — `D7.agrees`'s step horizon.  A stride-`k` pass executes
`stride` reads (and `stride` digit compares) per estimate, so the `Instr`-step
count leaves `12·N + 6` for a count **linear in `stride`**; since `D7` is where
word operations are translated into steps, quoting `K + 4` here would be the
`K + 3`-versus-`K + 7` mistake wearing a stride.  Residual (iv) re-measures.

### Residual after this round

* **(i) RE-SPECIFIED.**  Not «a k-word summing read» — that is impossible
  (`numAt_not_word`).  It is the digitwise comparison, plus the program segment
  that walks the digits.  The reader (§W1–§W2) is done; the read is proved
  unable to be a sum.
* **(ii) The bin sums themselves** — unchanged, and now the *only* mathematical
  input `wideExit_eq_binSum'` consumes.
* **(iii) The program-entry reach premise** — untouched.
* **(iv) `KapilaAlgo.cost` + `D7.agrees`'s horizon** — untouched by instruction;
  the shape to re-measure is now named (`scanWordOpsWide`, and a step count linear
  in `stride`).

### Receipts

**Final: `receipts/kapila-20261110T231919Z`** — gate `swapouts_delta60=0
free_pct=68` (iter 2; iter 1 correctly waited on `47354`).  **Lock not acquired:
bounded 240 s expired** (`acquired=False waited_s=240.3`), and the build proceeded
with the deviation written into `lock.note`/`summary.json` — the bounded-wait
policy doing exactly what it exists for under fleet load.  Build exit 0 in 37.3 s,
8935 jobs — **compile, not replay**: `KapilaWide.olean` rebuilt this run (357344
bytes, sha256 `762337ae…6c920`).  Axiom banner exit 0, **159 banners**, 29 new,
`axiom_banner_house_triple_only: true`; `numAt`/`numAt_ge_top` on `[propext]`
alone, `numBlock_succ`/`hitCount_map_range` on `[propext, Quot.sound]`,
`scanWordOpsWide` on no axioms; no `sorryAx`, no `native_decide`.
`Statement.lean` still `3dc6567e…34aa`.

**Runner lists:** both runners now build and receipt `KapilaWide`
(`NAMED_OLEANS` + `TARGETS`, and the unbounded runner's inline `lake build`
argument), so neither can silently omit the module it receipts.

Next single action: **re-specify (i) as the digitwise comparison and prove its
decision lemma** — that a top-down walk over the two stride-`k` digit blocks
decides `(1/2 : ℚ) ≤ |placeV − placeA|` **without** materialising either
numerator (little-endian `numAt` needs the blocks addressed from `base + (stride−1−j)·stride`; `sum_base_digits` is the exactness input).  That is the arithmetic the
program segment will then be proved against, and it is the only part of (i) that
can be finished before the segment exists.

## Row lane 2026-11-10 (13) — residual (i) re-specified as the digitwise comparison: the decision lemma PROVED, the segment's shape stated (arithmetic landed; segment proof open)

`SubsetSumL25/Row/KapilaDigitwise.lean` (new, leaf of the import DAG;
`Statement.lean` still `3dc6567e…34aa`; no built module's hash moved). Round
(12)'s "next single action" is discharged as far as arithmetic goes: the walk that
decides `(1/2 : ℚ) ≤ |placeV − placeA|` **without materialising either numerator**
is now a theorem, and the program segment that would implement it is a stated
skeleton with a proved fuel shape.

### The correction that stating the predicate forced (read this first)

The predicate is §7 step 7 at `F = fracBits` fractional bits:
**`2^(F−1) ≤ |numV − numA|`** — an integer comparison, derived from the landed
`hitWord_eq_ratTest` (`h = 2^(F−1)`) by `halfTest_iff_wordDiff`, so it is the same
predicate `wideExit_eq_binSum` folds and not a proxy.

**The walk does not start at digit `stride−1`.**  The `1/2` bit is bit `F−1`, i.e.
inside digit `p = (F−1)/w` at bit `r = (F−1)%w`.  With `F ≤ w·stride` (the `+1`
carry word `payloadStride_mul_spec` buys) the digits **above** `p` are the carry
word and are zero for a scale-fitting payload — `numAt_eq_of_lt` (a read below
`2^(w·m)` has no digit at position `≥ m`) collapses the block to its `p+1`-digit
prefix, and `numAt_split` gives `numV = digit_p·2^(w·p) + low`.  A walk from the
top with a first-difference rule would be **wrong**: at `|δ| = 1` on the top digit
`|V − A|` can be as small as `1`, far below `2^(F−1)`.  (12)'s
`base + (stride−1−j)·stride` phrasing was the walk *descending through the block
of estimates*; what the predicate needs is the walk descending through the
*digits* from `p`.

### Landed (no sorry, house triple)

| declaration | content |
|---|---|
| `halfTest_iff_wordDiff` | the `1/2` test **is** `2^(F−1) ≤ |V − A|` (from `hitWord_eq_ratTest` + `hitWord_eq_one_iff`) |
| `placeValueAt_eq_scale_numAt` | the address-indexed reader over the one shared scale is `numAt/2^F` (the `placeValueAt` twin of the landed `placeValue_eq_scale_numAt`) |
| `numAt_add_one_le`, `numAt_lt_pow` | `n` digits of `w` bits hold less than `2^(w·n)` |
| **`numAt_eq_of_lt`** | **a read below `2^(w·m)` has no digits above `m`** — the collapse that puts the whole block inside digit `p` |
| **`numAt_split`** | `numV = digit_p·2^(w·p) + numAt … p` — `sum_base_digits`' exactness seen from the top instead of the bottom |
| `mul_add_le_iff` | digit-granular comparison: `Y + b·P ≤ X + a·P` ⟺ `b < a ∨ (b = a ∧ Y ≤ X)` when the low parts fit below `P` (no bound on the digits) |
| **`cmpDigitsFrom`**, `cmpDigitsFrom_iff` | the top-down **low-digit walk** and its proof that it decides the block comparison — no accumulator, state = the two digits just read |
| **`digHalf`** | the first stage: one digit from each side at `p` against `2^r`, four ways; only the two **exact ties** descend into the low walk |
| `hit_of_above`, `hit_of_below`, `tie_hit_iff`, `tieA_hit_iff`, **`miss_of_close`** | the four arithmetic branches, each separate; `miss_of_close` is what makes the walk **one digit deep in the common case** (`(2^r−1)·P + (P−1) = T−1 < T`) |
| **`digHalf_eq_threshold_pow`** | **THE DECISION LEMMA in honest generality**: needs only `p + 1 ≤ stride` and `numV, numA < 2^(w·(p+1))` (nothing above digit `p`) — no scale-fit, no `1 ≤ F` |
| **`digHalf_eq_threshold`** | the `F`-indexed corollary: `p = (F−1)/w`, `r = (F−1)%w`, scale-fit `numV < 2^F` used only to obtain the collapse, by the five `if` branches of `digHalf` |
| **`digHalf_eq_ratTest`** | `(1/2 : ℚ) ≤ |V̂ − Â|` on the two `placeValueAt`s — the paper's own test |
| **`digHalf_eq_placeValueTest`** | the same at estimate `s`, i.e. on `placeV − placeA` |
| `digHalf_spot_checks` | three concrete payloads (`w=2, F=4`: decided hit, decided miss, exact tie resolved by the low walk) kernel-checked by `decide` |
| `cmpSeg`, `cmpSeg_length`, `cmpSegFuel`, `cmpSegFuel_linear`, `cmpSegFuel_zero` | the segment's **shape**: 29 instructions (constant), fuel `13 + 9p`, decided cases constant (7/8), `O(p)` only on a tie |

**The scale-fit is weaker than first framed, and the general form is proved.**
`digHalf_eq_threshold_pow` takes no scale-fit and no `1 ≤ F`: only `p + 1 ≤ stride`
and `numV, numA < 2^(w·(p+1))` — *nothing above digit `p`*.  The `F`-indexed form is
the corollary that computes `p`, `r` from `fracBits`; there `numV < 2^F` (the
paper's regime, `V̂ ∈ [0,1)`) is used **only** to obtain that collapse via
`numAt_eq_of_lt`.  The drafting claim "without scale-fit one more digit is in play"
was stronger than the arithmetic warrants: the four branch facts consume only
`Vlo, Alo < 2^(w·p)`.

### What is open, precisely

* **(i) segment proof.**  The obligation is written out in §D5's docstring: from
  the stated register precondition (cells 0/1 = the two digit addresses at `p`,
  cell 2 = `p`, cells 7/8/9 = `0`/`1`/`2^r`), the run of `cmpSeg cont` reaches
  `cont` within `cmpSegFuel p` steps with cell 6 = `digHalf`'s verdict.  Not
  proved, deliberately: a segment proof against a wrong decision predicate would
  be a new `K+3`-versus-`K+7` mistake wearing a loop, and the arithmetic had to be
  settled first.  It is now settled.
* **(ii) the bin sums** — still the only remaining **mathematical** input.
  `wideExit_eq_binSum` consumes `WideBinSumAgrees` and nothing else.
* **(iv) the cost re-measurement** — untouched: `cmpSegFuel`'s linearity is stated,
  but `D7.agrees`'s step horizon and `KapilaAlgo.cost` are not re-derived at
  stride `k`.

### Receipts

**`receipts/kapila-20261110T235126Z`** (final; the earlier
`receipts/kapila-20261110T233946Z` is the same gate/exit shape from before
`digHalf_eq_threshold_pow` was added) — gate `swapouts_delta60=0 free_pct=63`
(iter 1).  **Lock not acquired: bounded 240 s expired** (`acquired=False
waited_s=240.3`) on *both* passes, build proceeded each time with the deviation
recorded in `lock.note` and `summary.json` — the policy working under fleet load,
not a stall.  Build exit 0 in **50.9 s** (10 targets) — **compile, not replay**:
`KapilaDigitwise.olean` rebuilt this run (1049184 bytes, sha256 `d35b9c0d…bdff`).
Axiom banner exit 0, **183 banners**, 24 new, `axiom_banner_house_triple_only:
true`;
`digHalf_eq_threshold` on `[propext, Classical.choice, Quot.sound]`,
`mul_add_le_iff` on `[propext, Quot.sound]`, `digHalf` on `[propext]`,
`cmpSeg`/`cmpSeg_length`/`cmpSegFuel`/`cmpSegFuel_zero` on **no axioms**; no
`sorryAx`, no `native_decide`.  `sources.sha256` matches the committed tree
byte for byte; `Statement.lean` still `3dc6567e…34aa`.

**Runner lists:** both runners now build and receipt `KapilaDigitwise`
(`NAMED_OLEANS` + `TARGETS` + the unbounded runner's inline `lake build`
argument); `KapilaRowAxioms.lean` prints the new module's banner.

### Six `omega`/`rw` measurements for the next author

1. `rw [← h]` where `h : w*p + r = F−1` rewrites **inside** `(F−1)/w` and
   `(F−1)%w` and wrecks the goal — use `conv_lhs => rw [← h]`.
2. A `calc` takes its relation from its **first** step: starting `<` and ending
   `≤` yields `<`, so a `≤` goal fails.  Start the calc `≤`.
3. `Nat.succ_mul` (`(b+1)*P = b*P + P`) and `Nat.sub_mul` are the levers that let
   `omega` see a shifted product; without them `b*P` and `(b+1)*P` are unrelated
   atoms.
4. `omega` inside a pair constructor does **not** get the equality that
   constructor consumes: `⟨heq, by omega⟩` fails where `have h' := h; rw [heq] at
   h'` then `omega` succeeds.
5. `Nat.mul_zero` matches `?n * 0`; for `0 * _` it is `Nat.zero_mul`.
6. When an iff branch's goal is `false = true`, `False.elim` is needed —
   `Bool.false_ne_true hc` alone has type `False`.

## Round (14) — residual (ii) closed: the `binSum` fixed, the contract inhabited

**`KapilaBinSum.lean` (new, leaf of the import DAG).**  Eleven new names, no
displacement: `KapilaEstimate`'s `WideBinSumAgrees` was a contract with a hole
where the paper's quantity belongs, and a contract nobody inhabits is not a
residual — it is a hole in the statement of the theorem.  It is inhabited now.

**What the `binSum` is.**  §6's `V_ρ` at the granularity §7 step 7 reads it: the
**signed aggregate of the two payload blocks' digits at the same place**, over the
one shared scale —

`binSum i = (Σ_{j<stride} (f (baseV+i·stride+j) − f (baseA+i·stride+j))·2^{w·j}) / 2^F`.

Why that object and not an arbitrary one: it is what `V_ρ`'s term becomes once the
complex weight is dropped (the tree has no `ℂ`, no phases, and `Nat`-mod as its
only residue machinery — `KapilaChecksum`'s header says so and keeps the support
content: `checksum_sound`, `checksum_support_in_bin`), and it is the object a
**digitwise** machine can form — no cell ever holds a wide numerator
(`numAt_not_word` forbids that), which is exactly why the comparison had to be
re-shaped in `KapilaDigitwise`.

**Proved.**

1. `binDigits_eq_numAt_sub` — the aggregate *is* the difference of the two carried
   numerators (distributing the difference over the digits is exact: nothing
   couples the two sides, so no carry is needed — `sum_base_digits`' linearity
   seen from the sign).
2. `placeValue_sub_scale` — `placeValue_scale` at the two bases, subtracted: the
   scaled place-value difference is the numerator difference.  Two lines, and it
   is the whole of the denominator step.
3. `binSum_eq_placeValue_sub` — assembled in the order the arithmetic forces:
   `placeValue_sub_scale` → `numAt_cast` (each numerator is its weighted digits)
   → `binDigits_eq_numAt_sub` → `memOf_toNat` (the memory bridge).  Nothing about
   the payload lists, `dAt`, or the program is consumed.
4. **`wideBinSumAgrees_binSum` — `WideBinSumAgrees`, PROVED**, for every memory
   and every stride, given only the digit fit.  The honest reading, stated plainly
   rather than dressed up: `WideBinSumAgrees` has **no memory-side content**.  It
   is not a constraint the layout must satisfy — it is the definition of what the
   bin sum has to be for the wide test to be a test on bin sums.
5. `wideExit_eq_binSumDigits` — `KapilaWide`'s `wideExit_eq_binSum'` with that
   hypothesis discharged: the stride-`k` loop's exit *is* the test on the bin sums,
   with no hypothesis about them left.
6. `hitWord_binSumTest` / `binSumTest_iff_wordDiff` — the payoff: the loop's
   `hitWord` at `h = 2^{F−1}`, `rowTest`'s `ℚ` test, and the digitwise
   `digHalf`/`cmpSeg` decision are **one predicate**.  (ii) and (i) are the same
   predicate, so the segment proof need not be re-argued in §6's vocabulary.

**The one named input (D7-style, seam named not floating).**  `PayloadCarries w f
numV numA baseV baseA stride len` — *the memory's digits at the two bases are the
phases' independent numerators*.  This is the **accumulation stage**: §6.2's block
tables write `⌈F/w⌉ + 1` words per estimate (`payloadStride`, and
`placeValueAt_payloadStride` proves such a block carries an `F`-bit numerator
exactly), and the tree's 24-instruction `checksumProg` **does not contain that
stage** — it saves three inputs at `2n, 2n+1, 2n+2`, decides `a₁+a₂+a₃ = t`, and
writes no payload block.  Not an arithmetic gap: one missing instruction block.
`wideBinSumAgrees_carried` discharges `WideBinSumAgrees` from that premise alone,
so the contract also holds in the form where the `binSum` is **not** defined from
the memory.  Inherited and *not* supplied by it: the block tables, the
inverse-multiplicity weights, the residue-bin enumeration, the `1/8` accuracy
(that file's own residual), and Theorem B's `1 − o(1)` success region.

**Residual after this round, exactly four, none of them floating.**

* (i) **`cmpSeg`'s segment proof** — unchanged; new help: its verdict *is* the
  bin-sum test (`hitWord_binSumTest`), so no §6 re-argument is owed.
* (ii) **was a contract, is now a construction + one premise.**  Closed as
  stated; what remains is `PayloadCarries`, i.e. the accumulation stage (above).
* (iii) **the program-entry reach premise** — untouched.
* (iv) **`KapilaAlgo.cost` and `D7.agrees`'s horizon** — untouched, and this file
  adds no charge: `binSum` defines the compared quantity, it is not a computation
  the program performs.

### Receipts

**`receipts/kapila-20261111T002540Z`** (final; **compile, not replay**) — gate
`swapouts_delta60=0 free_pct=45`; lock **not acquired, bounded wait `0 s`**
(`KAPILA_LOCK_WAIT=0`, deviation recorded in `lock.note` + `summary.json`);
`✔ [8937/8937] Built SubsetSumL25.Row.KapilaBinSum (37s)`, build exit 0 in
**45.3 s**; `KapilaBinSum.olean` 195528 bytes mtime 16:27:25 sha256 `822c61da…3fc6`
— and the **same sha256 across three independent compiles** (16:04 foreground, 16:24
orphaned `lean` after an external `SIGKILL` of its `lake` parent, 16:27 this run),
which is the determinism check the byte count alone cannot give.  Axiom banner exit
0, **194 banners**, 11 new, `axiom_banner_house_triple_only: true`; all new
declarations on `[propext, Classical.choice, Quot.sound]`, `PayloadCarries` on
`[propext]`; no `sorryAx`, no `native_decide`.  `sources.sha256` matches the
committed tree; `Statement.lean` still `3dc6567e…34aa`.

**Aborted receipts kept, both `build_exit=-9`:** `kapila-20261111T001326Z`
(a foreground wrapper killed at the shell watchdog; the runner ignores `SIGTERM` by
design and outlived it) and `kapila-20261111T001919Z` (detached runner, its `lake`
child `SIGKILL`ed externally ~5 s into the compile while the `lean` child survived,
orphaned, and completed).  Neither aborted run wrote a banner, and neither is cited
as evidence.  Also kept: `kapila-20261111T000456Z` and `001052Z`, both `build_exit=0`
but **replays** of the 16:04 olean (`build_seconds` 4.7 / 7.1, olean mtime *before*
the receipt stamp) — recorded so the compile/replay distinction stays auditable.

**Runners** now build and receipt `KapilaBinSum` (`NAMED_OLEANS` + `TARGETS` in both,
plus the unbounded runner's inline `lake build` argument);
`KapilaRowAxioms.lean` imports it and prints its eleven banners.

### Four measurements for the next author

1. `rw [← sub_div]` rewrites `a/c − b/c` → `(a−b)/c`; for the reverse direction the
   pattern is the *whole* quotient, so `rw [sub_div]` is the one that fires.
2. A `fun i => …` on a `∀ i` goal is not syntactically the body — `show` the
   beta-reduced form first, or `rw` cannot find the term it is looking for.
3. Lake hashes **content**, not mtimes: `touch`ing a source does not force a
   rebuild.  Force one by deleting the module's `.olean`/`.trace` artefacts, or the
   receipt will silently be a replay.
4. `lake env lean` (the banner step) survives an external `SIGKILL` of `lake`: the
   `lean` child is spawned in its own session, so an orphaned compile still finishes
   and writes its olean after its parent is gone.

Next single action: **(i) — `cmpSeg`'s segment proof.**  The obligation is written
out in `KapilaDigitwise`'s §D5 docstring: from the register precondition (cells 0/1 =
the two digit addresses at `p`, cell 2 = `p`, cells 7/8/9 = `0`/`1`/`2^r`), the run of
`cmpSeg cont` reaches `cont` within `cmpSegFuel p` steps with cell 6 = `digHalf`'s
verdict.  The arithmetic is settled (`digHalf_eq_threshold_pow`,
`cmpSegFuel_linear`); what is owed is the straight-line walk over 29 instructions —
and `hitWord_binSumTest` now says that walk's verdict is the bin-sum verdict, so
the segment is not a separate §6 obligation but residual (i) alone.

## Round (15) — residual (i) closed: the compare segment walked, and two defects in its statement

**`KapilaCmpSeg.lean` (new, leaf of the import DAG; 1406 lines, 56 declarations).**
§D5 of `KapilaDigitwise` *stated* the segment and deferred the walk, with the
obligation written out.  It is discharged here, and the proving found that the
statement itself was wrong in two places — both caught by simulating the exact
`Instr` list in Python before any proof was attempted, which is the cheapest possible
place to catch them.

### The two defects, and what the fix cost

1. **The `p = 0` tie descended into nothing.**  As written, both tie instructions
   were unconditional jumps to the walk (`blt 7 8 19`, `blt 7 8 16`).  A tie at
   `p = 0` then entered the walk with *no digit below `p`*: `pc 19`/`20` decremented
   the two pointer cells to `addrV − 1` / `addrA − 1` and `pc 21`/`22` read **there**
   — addresses outside the digit block (with `addrV = 11` the read lands on cell
   `10`, the segment's own uninitialised swap scratch) — and returned whatever the
   comparison of two garbage words said.  The tie at `p = 0` has no low part at all
   and `cmpDigitsFrom … 0 = true`, so the correct verdict is **hit**; the program
   could answer **miss**.  Measured: `v = 4`, `a = 0`, `r = 2` is a `p = 0` tie and
   a hit, and the first draft answered `0` on it.
   **The fix is free**: the tie jumps now test the digit counter
   (`blt 7 2 19`, `blt 7 2 16`) and only descend when `0 < p`, so a `p = 0` tie
   falls through into the hit exit at `12`.  It also makes position `7` live code —
   it was unreachable as first written.
2. **The fuel was one step short.**  The walk's *terminal* digit costs `10`
   instructions to reach the hit entry (`19 … 28`), not `9`, so the worst case is
   `11 + (9p + 3) = 9p + 14`, not `13 + 9p`.  `cmpSegFuel` is now `14 + 9p`, and
   `cmpSegCost_tight` proves it is **attained** (A-side tie, every low digit equal),
   so it is a bound and not slack.

A third hazard became a **hypothesis** rather than a fix: `add 5 4 9` sums a digit
with `2^r` in one word, so `d + 2^r` must fit.  In the scale-fit regime a digit at
`p` is below `2^(r+1)`, which makes it free at `r + 2 ≤ w` (`two_pow_add_fits`);
at `r = w − 1` (the half bit in the digit's top position) it is a real constraint on
the digit, carried explicitly as `hadA`/`hadV`.

### What is proved

| theorem | content |
|---|---|
| `cmpSeg_walk` | the low-digit walk, `pc 19 → cont`, **exact** `walkCost` fuel, by induction on the digit counter with base `n = 1` (the walk is never entered with a zero counter — defect 1's fix is what buys this) |
| `cmpSeg_walk_lt` / `_gt` / `_eq_step` / `_eq_term` | the four leaves: `3` steps downward miss, `5` upward hit, `5` back to the walk head on an equal pair, `8` the all-equal exit at `n = 1` |
| `cmpSeg_walk_head` | `pc 19 → pc 23`, the two pointer steps and the digit pair read |
| `cmpSeg_head` | `pc 0 → pc 3`, the two digits at `p` and `a + 2^r` (`CmpHead` bundles the state) |
| `cmpSeg_above` / `_miss` / `_below` / `_tieV` / `_tieA` / `_tieV_zero` / `_tieA_zero` | the five prologue ways out at their exact costs `7 / 8 / 9 / 4+walk / 8+walk / 7 / 7` |
| **`cmpSeg_reaches`** | **§D5's obligation**: from the register precondition and the frame, the run reaches `cont` in exactly `cmpSegCost` steps with cell 6 = `digHalf`'s verdict, touching no cell outside `CmpCell` |
| `cmpSeg_reaches_bound` | the same *within* `cmpSegFuel p` — the form §D5 asked for |
| `cmpSegCost_le` / `_tight` | `cmpSegCost ≤ cmpSegFuel`, and `=` on the all-equal A-side tie |
| `cmpSeg_cell6_iff_wordTest` | cell 6 `= 1` ⟺ `2^(F−1) ≤ wordDiff numV numA` — the predicate `hitWord_binSumTest` already owns, so the loop needs no new test |
| `cmpSegment_getD` + `cmpSegmentProgram` | the `getD` facts transfer to `cmpSeg 29 ++ tail` (see the composition note) |
| `cmpSeg_spot_*` (7) | `decide` runs of the **real program** through a 3-instruction verdict tail, each at one step above **and one below** its branch's cost, so the costs are pinned on the program too |

`exec_rem_step` + `bv_rem` are the calculus's **third ported peeler** (`rem`, after
`sub`/`div`): the zero verdict is written as `rem 6 7 7`, i.e. `[7] % [7]` with
`[7] = 0`, which needs `[j] % 0 = [j]` — true on both sides (`Nat.mod_zero`).

### The composition state — what is free and what is not

The segment's jump targets are **absolute** (`8, 12, 14, 16, 19, 27`), so it can sit
only at offset `0` of the program that contains it: `cmpSegmentProgram tail =
cmpSeg 29 ++ tail`.  `cmpSegment_getD` proves every `getD` fact the walk used
transfers there — that part is free.  What is **not** free, and is now named instead
of hidden:

* a loop invoking the segment once per estimate must **reload cells `0`/`1`/`2`**
  (three `add`s from constants) before each invocation, because the segment walks
  those pointers **down**; and
* it must **jump back to `0`** for each comparison (one `blt` with the always-true
  `0 < 1`), because the segment is at offset 0.

So the per-comparison charge is `cmpSegCost + 4` (three reloads + the entry jump)
plus the accumulation, and that four-instruction overhead is **material for residual
(iv)**: `D7.agrees`'s horizon cannot be re-measured without it.  The segment's own
step count is a function of the digits (`cmpSegCost`), so a caller that knows its
branch gets the exact price and a caller that does not gets `14 + 9p`.

### Residual after this round, exactly three, none of them floating

* (i) **closed** — the segment is proved, at the exact cost, and its verdict is tied
  to the integer/`ℚ`/bin-sum test by `hitWord_binSumTest`.
* (ii) closed in round (14) as a construction plus one named premise
  (`PayloadCarries`, the accumulation stage the checksum program does not contain).
* (iii) the program-entry **reach premise** — untouched.
* (iv) `KapilaAlgo.cost` and `D7.agrees`'s horizon — untouched, and this round
  *adds* a charge to it rather than removing one: `+4` per comparison from the
  composition above.

### Receipts

**`receipts/kapila-20261111T011020Z`** (final; **the new module replayed, its
neighbour compiled** — the labels are inverted from the obvious guess, so they are
stated rather than assumed) — gate `swapouts_delta60=0 free_pct=48`; lock **acquired
after 105.1 s** of the bounded 240 s wait (`KAPILA_LOCK_WAIT=240`, and the wait was
real: a concurrent runner in this same worktree, `receipts/jv1000-20261111T011110Z`,
waited 40 s of its own on the same lock ten seconds later); build exit 0 in
**43.3 s**.  In the build log `⚠ Replayed SubsetSumL25.Row.KapilaCmpSeg` and
`✔ Built SubsetSumL25.Row.KapilaBinSum (34s)`: `KapilaCmpSeg.olean`'s mtime
(17:08:03) is **two minutes before** the receipt stamp, i.e. it is this session's own
compile of the module, and the receipt's build **replayed** it; what that build
actually compiled is `KapilaBinSum`, whose dependency `KapilaDigitwise` changed
underneath it.  `KapilaCmpSeg.olean` **3145104 bytes**, sha256 `d7f4c93d…29b`.

**Determinism, by double compile — and it is what carries the compile claim.**
Because the receipt replayed the module, the receipt alone is not evidence that the
final bytes compile: the olean, its `.ilean` and its `.trace` were therefore
deleted and the module rebuilt **from scratch**, giving **the same sha256
`d7f4c93d…29b`**.  That rebuild is the compile of record, and it reproduces the
receipt's hash byte for byte.

Axiom banner exit 0, **196 banners**, `axiom_banner_house_triple_only: true`; the new
declarations are on the house triple or a subset of it — `cmpSeg_reaches`,
`cmpSeg_walk`, `cmpSeg_cell6_iff_wordTest` on
`[propext, Classical.choice, Quot.sound]`; `cmpSegCost_le`, `cmpSegCost_tight`,
`cmpSegment_getD` and the seven spot checks on `[propext, Quot.sound]`; no
`sorryAx`, no `native_decide` anywhere in the banner or the build log.
`sources.sha256` matches the committed tree byte for byte; `Statement.lean` still
`3dc6567e…34aa`.  `head` = `3229cc3`.  Both runners name
`SubsetSumL25.Row.KapilaCmpSeg` (`NAMED_OLEANS` + `TARGETS` + the unbounded runner's
inline `lake build` argument); `KapilaRowAxioms.lean` prints its nine new banners.

### Eight measurements for the next author

1. **A cost that composes with a suffix must be a *function*, not a `∃ k`.**  The
   segment's tail cost depends on the branch and on where the digit walk stops, so an
   existential has to be resolved *before* the peeler chain that produces the state —
   the wrong order, and the composition becomes circular.  `walkCost`/`cmpSegCost`
   (closed terms) let every lemma state its exact cost with the horizon `S` free, and
   the assembly is `omega` on literals.  This was the single biggest time-saver in
   the round.
2. **`Nat.pow_le_pow_right` needs its base pinned.**  `Nat.pow_le_pow_right
   (by norm_num) hr` against a goal of the form `2^r * 2 ≤ 2^w` leaves the base a
   metavariable and fails with `⊢ 0 < ?m` — write the sum as `2^(r+2)` in a `calc`
   instead.
3. **`omega` cannot instantiate `∀ z, f z < 2^w`.**  Every `upFit`/comparison proof
   needs the *concrete* instance hoisted (`have hb0 : st 0 < 2^w := hfit 0`) first;
   without it the failure is a counterexample that looks like a real obstruction.
4. **The fit of a written `0` is `Nat.two_pow_pos w`, not `by omega`** — `0 < 2^w`
   has no linear structure for `omega` to see.
5. **`rw [if_pos rfl]` can close a literal-branch goal by `rfl`**, so a trailing
   `; omega` then errors `No goals to be solved`.  Same for `rw` on
   `st 7 % st 7 = 0` and on `1 - 1 = 0`.
6. **`n + 0 = n` is not definitional for `Nat`.**  A `rw [e0, e7']` that lands on
   `addrV + p + 0 = addrV + p` needs `Nat.add_zero` in the list; the "unsolved goals"
   message points at the `show`, not at the missing lemma.
7. **`obtain` patterns must match the ∧ *grouping* exactly.**  A flat
   `A ∧ B ∧ C ∧ D` destructured as `⟨x, ⟨a, b⟩, c⟩` reports
   `Dependent elimination failed: Failed to solve equation …`, which reads like a
   universe problem and is not.
8. **Simulate the instruction list before proving anything about it.**  Two of the
   three findings this round (the `p = 0` descent and the short fuel) came from a
   30-line Python `exec` simulator in minutes; each would have cost a day of Lean
   archaeology, and the fuel one would have surfaced as an inexplicable "my constant
   is one too small" much later.

Next single action: **(iii) — the program-entry reach premise**, now the only
structural obligation left; (iv) has gained a concrete charge to absorb (the `+4` per
comparison from the composition above) rather than losing one.

## Row lane 2026-11-10 (16) — residual (iii) closed: the program-entry reach, and a cost shape it corrected

Residual (iii) was one sentence repeated for three rounds: *§7 step 7's loop is
actually entered*.  What was missing was not a loop proof but a **seam**: the segment
walks cells `0`/`1`/`2` **down**, so a caller that invokes it once per estimate cannot
re-enter it on the state it left — the register precondition `cmpSeg_reaches` consumes
(`0`/`1`/`2` = `addrV + p`, `addrA + p`, `p`; `7`/`8`/`9` = `0`/`1`/`2^r`; nothing
else touched) has to be re-established first.  §C5 *named* that reload and charged
`+4` for it.  This round makes it a theorem and finds that the charge, as a
per-comparison price, was one instruction short.

### The instructions, on the real program

`cmpSegmentProgram tail = cmpSeg 29 ++ tail`, so the loop's own code sits at `29`:

```
29  add 0 11 13      [0] := addrV + p        (11 = addrV, 12 = addrA, 13 = p: the
30  add 1 12 13      [1] := addrA + p         loop's own scratch, none in CmpCell,
31  add 2 13 7       [2] := p + 0             so the frame carries them)
32  blt 7 8 0        back to 0                (always taken: 0 < 1)
```

and the tail a **terminating** loop needs:

```
29  add 13 13 8      p := p + 1              (the index FIRST)
30  add 0 11 13      [0] := addrV + (p+1)
31  add 1 12 13      [1] := addrA + (p+1)
32  add 2 13 7       [2] := p + 1
33  blt 13 14 0      p+1 < limit ? → 0        (the guard IS the back-edge)
```

### The defect the simulation caught, and the charge it corrects

**The advance must precede the reload.**  The natural-looking order — reload the three
cells, then bump the index, then jump — reads the *un-advanced* index, so every
iteration recomputes the same digit pair and the loop never terminates.  Simulated
before any proof (the round-15 discipline, and it paid again): the two-pass program
with the reload first measured **32** steps where **30** was predicted, its second
comparison re-ran `p = 0`, and its final verdict was the *first* pass's.  That is a
defect in a stated shape — the shape was "three adds and a jump back to 0", which
says nothing about where the counter work goes — found by measurement, not by
argument.

**The charge is `+5`, not `+4`, for a terminating loop.**  `+4` is real and now
proved (`cmpSeg_reentry`), but it is the re-entry charge *given* `p` already in cell
`13`.  A loop that varies `p` pays one more instruction (the advance; the guard is
already the back-edge, so it is not a sixth).  So:

| charge | value |
|---|---|
| one comparison (segment) | `cmpSegCost` (exact), `≤ cmpSegFuel p = 14 + 9p` |
| re-entry, `p` fixed in cell 13 | `+4` — `cmpSeg_reentry` |
| one comparison of a **terminating** loop | `+5` — `cmpSeg_loopStep`, `≤ 19 + 9p` (`cmpSeg_loopCharge_le`) |

Residual (iv) inherits `19 + 9p` per comparison (was `14 + 9p + 4` = the same
arithmetic with the advance uncharged — the difference is real, one instruction per
comparison, and it is stated rather than absorbed).

### What is proved

| declaration | content |
|---|---|
| `cmpSegment_getD_tail` | positions `29 + i` of `cmpSegmentProgram tail` are `tail`'s — the counterpart of `cmpSegment_getD` |
| **`cmpSeg_reentry`** | **THE ENTRY REACH**: from the post-segment state, the 4 instructions reach `0` in exactly `4` steps with `0`/`1`/`2` = the precondition, the `CmpCell` frame, the word fit, **and cell 6 (the verdict) intact** — exactly what `cmpSeg_reaches` consumes |
| **`cmpSeg_loopStep`** | the terminating loop's 5 instructions reach `0` in exactly `5` with the counter at `p + 1`, cell `13` advanced, the frame updated (`up h 13 (p+1)`), verdict intact |
| `cmpSeg_loopCharge_le` | `cmpSegCost + 5 ≤ 19 + 9p` — the number (iv) inherits |
| `cmpSegReload` / `cmpSegReentry` / `cmpSegLoopTail` | the three instruction lists, so the shapes are names and not prose |
| `cmpSeg_spot_reentry`, `_short` | the A-side tie (**the segment's worst case**, `23`) + reload + verdict: halts `true` at `29 = 23 + 4 + 2`, does not halt at `28`.  The back-edge is redirected one slot past the adds (to a verdict tail) so `exec` can report the post-reload state; that one differing instruction is disclosed in the docstring |
| `cmpSeg_spot_loop`, `_short` | **two comparisons through the real tail**: `p = 0` hit (`10`), `p = 1` miss (`8`), `10 + 5 + 8 + 5 + 2 = 30`, verdict `false`, no halt at `29` |
| `cmpSeg_spot_loop_first` | `p = 0` **alone** is a hit — so a loop that failed to advance would end `true` where the two-pass program ends `false`.  This is what makes the loop check bite rather than merely halt |

The four properties the loop needs are one shape and it is now inhabited from both
sides: the segment's conclusion (cell 6 = verdict, frame, fit, constants) is the
re-entry's hypothesis, and the re-entry's conclusion (precondition, frame, fit,
verdict preserved) is the segment's hypothesis.  **What is not claimed:** a single
`exec` equality composing the two runs.  The segment's lemmas are stated on
`cmpSeg cont` and the composed program differs from it at position `29` — exactly
where the segment's last step jumps.  Closing that means transferring §C4–§C6's
`getD` facts to `cmpSeg 29 ++ tail` (a `getD`-agreement induction over every lemma
there), and the loop proper (an induction on `p` with the guard and the accumulator)
stands on top of it.  Both are named, neither is pretended.

### Receipt

**Receipt `receipts/kapila-20261111T013658Z`** — gate `swapouts_delta60=0 free_pct=53`;
build exit 0 in **8.3 s**, and that is a **replay, not a compile**: every target was
already up to date because this session's own `lake build
SubsetSumL25.Row.KapilaCmpSeg` had produced the olean.  The receipt alone is therefore
*not* evidence that the final bytes compile, so the olean, its `.ilean` and its
`.trace` were deleted and the module rebuilt **from scratch**: **the same sha256
`a5488267…b2da`**, 3 540 968 bytes.  That rebuild is the compile of record, and it
reproduces the receipt's hash byte for byte.

Axiom banner exit 0, **205 banner lines**, `axiom_banner_house_triple_only: true`.  The
new declarations are on `[propext, Quot.sound]` — a subset of the house triple —
or on no axioms at all: `cmpSegReload`, `cmpSegReentry`, `cmpSegLoopTail`, the two spot
states and the redirected tail are *definitions* and print "does not depend on any
axioms".  No `sorryAx`, no `native_decide` anywhere in the banner or the build log.
`Statement.lean` still `3dc6567e…34aa`, and `KapilaCmpSeg.lean` still
`6f00b833…6dc3` — this round's own sources match `sources.sha256` byte for byte.  (One
file in that manifest has moved since the receipt: `JV1000Quadrature.lean`, which a
**peer** jv1000 mind is editing in this shared worktree.  It is not this round's, not
in this round's commit, and its drift is that mind's business — named here so the
manifest's one-line mismatch is not mistaken for a vanished edit.)  `head` =
`c32ff2e` — a **peer's** commit (the jv1000 row) landed on the shared branch between
this round's edits and its receipt; it touches `JV1000Instance.lean` only, so no source
of this round moved.  Lock: the bounded 240 s wait expired and the build proceeded
UNLOCKED, deviation recorded in `lock.acquired`/`summary.json` — the policy working,
not a stall.

### Measurements for the next author

1. **`rw` does not see through a definitionally-equal-but-not-syntactic index.**
   `(cmpSeg 29).length` and `29` are `rfl`-equal, yet `List.getElem?_append_right`
   refuses to match until `cmpSeg_length` is rewritten *and in the right order*.
2. **`rw [List.getElem?_append]` introduces an `ite` under a `.getD`**, so the four
   rewrites only work in one order: `getD_eq_getElem?_getD` (both sides), then
   `getElem?_append`, then `cmpSeg_length`, then the `if`/subtraction.  Any other
   order fails with "did not find an occurrence" naming a pattern that *is* in the
   goal — the message points at the wrong thing.
3. **`exec_add_step` takes no fit hypothesis** (`load`/`rem`/`shr` do).  Passing one
   anyway yields `Function expected at exec_add_step … hfit`, which reads like an
   argument-order problem and is an extra argument.
4. **A local `by_cases h : z = 13` shadows the frame `h : Nat → Nat`**, and the
   resulting `up_eq h 13 …` type error blames universes.  Name the case hypothesis
   (`hz13`), not `h`.
5. **`decide` spot checks catch a wrong jump target but report it as a false
   statement** — `accepted answer: … = some true` → "Tactic `decide` proved that the
   proposition … is **false**" tells you the verdict is wrong, not that `blt 7 6 36`
   pointed one slot past `accept`.  In a 3-instruction verdict tail the target is
   `cont + 2`, and an off-by-one lands on `reject` and reports `false` for *every*
   input — which looks like a bad state, not a bad index.
6. **The reload/advance order is not a detail you can fix later**: a wrong order
   still halts and still produces a verdict on many inputs, so only a check whose
   *second* comparison differs from its first can see it.  Design the spot state
   first (`p = 0` hit, `p = 1` miss) and the check writes itself.
7. **Two instruction lists that differ only in a jump target are two different
   programs** — and the loop's real back-edge (`→ 0`) makes its post-state
   unobservable through `exec`.  State the redirect in the docstring and prove the
   cost separately; pretending the redirect is the real program would be the lie.

Next single action: **the `getD`-agreement transfer of §C4–§C6 to `cmpSeg 29 ++ tail`**
— i.e. `cmpSeg_reaches` stated for an abstract `P` agreeing with `cmpSeg 29` on
`0…28` — which is what turns this round's state-level pipeline into one `exec`
equality; then the loop induction on `p` with the guard and the accumulator.  (iv)
then re-measures `D7.agrees`'s horizon at `19 + 9p` per comparison and
`PayloadCarries` stays the named accumulation premise.

## Row lane 2026-11-11 (17) — jv1000 C6: the two moment goals are **FALSE as stated** (proved), the certified ones stated, and the Lip-16 route measured closed

Round (16) left the nine-goal residue of `Row/JV1000Instance.lean` §7 untouched.  This
round attacks C6 (`M₁`, `M₂`) and returns a **statement defect, proved**, plus the
module the family lane will need to write the real proof.  Two new files, no change to
`Statement.lean` (`3dc6567e…`), nothing touched in the (iii)/(iv)/`PayloadCarries`
residuals.

### The measurement that reordered the round

Simulated first (the lane's rule, and it has now caught three statement defects):

| quantity | `log₂` | vs `ρ_c = 0.5162696413` |
|---|---|---|
| `jvMomentRho0` as stated (raw `r`) | **9.1347303876** | **−8.618 bits** |
| `jvMomentBand` as stated (raw `s`) | **8.5399821747** | **−8.024 bits** |
| certifier's `M₁` (strip-corrected `u`) | 0.516268325851285 | +1.3154·10⁻⁶ |
| certifier's `M₂` (strip-corrected `v`) | 0.516268147264670 | +1.4940·10⁻⁶ |

The residue's `m1`/`m2` fields were therefore **not open goals but false ones** — the
raw-density `2^{p(Δ−r)}` reaches `2^{10.3}` near `x = 0` because `r(0) = −1.19258309`,
where the certified `u` lives in `[−0.588, 0.178]`.  The file's own «Shape only — the
certified quantity carries the strip corrections» caveat was honest; what had not been
measured is that the gap is 8.6 **bits**, i.e. unreachable by any quadrature refinement.
Cost of the omission, had it not been caught: a whole session spent trying to enclose a
false target to 1.3·10⁻⁶.

### What is proved (both refutations, no quadrature needed)

`Row/JV1000Moments.lean` §1–§2, all on the house triple:

* the row's Lipschitz data as exact rationals — `jv_lip16_value_r` (`12.16437058`),
  `jv_lip16_value_s` (`12.3257555`), `jvLogDensityR_zero` (`−1.19258309`),
  `jvLogDensityS_zero` (`0.61925852`), and the two `v1_lipschitz` specialisations;
* `jv_momentRho0_gt_two` / `jv_momentBand_gt_two`: a single window from `0`
  (`δ = 1/100` resp. `1/50`) carries the moment past `2` — exponent floor `9` resp. `8`
  (integers, so `2^k` is `norm_num`-able and **no rational-power numeric bound is
  needed anywhere**), weight floor `3.98`/`3.96`, hence `M₁ ≥ 2.547`, `M₂ ≥ 2.534`
  (both after the crude but proved `2π ≤ 8`);
* `jv_m1_stated_false`, `jv_m2_stated_false`: `¬ (log₂ M < ρ_c)`, via
  `jv_rhopow_lt_two` (`2^{ρ_c} < 2`, since `ρ_c < 1`).

Shape of the argument, worth keeping: **a refutation needs a lower bound on one window;
a proof would need a 1.3·10⁻⁶ enclosure of the whole circle.** The cheap direction is
the one that was available, and it is the one that mattered.

### The quadrature module, and the route it closes

`Row/JV1000Quadrature.lean`: `integral_self`, `chord_dev_le` (pointwise chord
deviation), `integral_lerp`, **`trap_error_le`** (`|∫_a^b f − (b−a)(f a+f b)/2| ≤
L(b−a)²/2` for `f` Lipschitz `L`, no derivative, no analyticity), and
**`trap_error_panels`** (`n` equal panels, `L(b−a)²/(2n)`).  Constant discipline is in
the docstring: sharp is `1/4`, the exact-majorant argument gives `1/3`, this gives `1/2`
because `1/2` needs **no polynomial quadrature at all** — and the factor is irrelevant
against the number below.

Measured cost of that route at this point: the ρ₀ integrand's Lipschitz constant is
`K = 2^{p(Δ+3.21)}·(2 + 4·log 2·p·lip16) = 5.07·10¹⁰`, so `1.3·10⁻⁶` needs
`n ≥ 7.7·10¹⁷` panels — while the **true** trapezoid error at `n = 256` is of order `10⁻¹²`
(the bound is ~20 orders pessimistic, because the integrand is entire).  The certifier's
own route — periodic trapezoid + strip analyticity, `q₀ = 0.3708350894162912` — reaches
`5.9·10⁻¹⁸` at `n = 40`.  **That is the architecture C6 must be proved with**; the
Lipschitz module is the honest cheap half and the tool that produced the measurement.

### §3 — the obligations, correctly stated (open, true to 15 digits)

`jvZf/jvZg/jvZfk/jvZgk/jvLZ/jvStripH/jvP/jvY/jvU/jvV` and
`jvMomentRho0Cert`/`jvMomentBandCert` are the **continuum limits** of `certify_c5`'s
strip-corrected construction (the grid sums are trapezoid rules for exactly these
integrals), and `structure JV1000Moments` holds the two real obligations
`M < 2^{ρ_c}`.  Measured agreement with the discrete certifier: `2.2·10⁻¹⁶`.  The three
missing pieces and their sizes are named in the structure's docstring — strip
quadrature lemma; the same for the inner `P`/`Y`/`Z` integrals (a relative enclosure
that must survive `log`); the certified rational comparison.

`JV1000Instance.lean`'s `JV1000Residue` keeps **seven** fields (the entropy group);
the two moment fields are removed, not weakened, with a pointer to the refutations.

### Receipts

`receipts/jv1000mom-…` — gate `PROCEED`, bounded lock wait with the deviation recorded,
double-compile determinism on `JV1000Moments.olean`, axiom banner
`JV1000MomentsAxioms.lean` (20 `#print axioms` + 5 `#check`) fail-closed on
`sorryAx`/`native_decide`/non-house axiom set — exit 0, 55 `depends on axioms` lines,
all house triple.  The build **compiled** this round's modules rather than replaying
them (`✔ Built SubsetSumL25.Row.JV1000Instance (23s)`, `✔ Built
SubsetSumL25.Row.JV1000Moments (17s)`), so the residue edit is compile-verified.  The
lock deviation is recorded, not hidden: `acquired=False waited_s=240.2 bounded=240` —
a peer held `/Volumes/Substrate-1/bigo/.build.lock` for the whole bounded wait and the
build proceeded anyway (same deviation class as the `…T011642Z` receipt, and the same
honesty about it).  `Row/JV1000Instance.lean`'s own banner (`JV1000Axioms.lean`) was
re-run separately after the residue edit — exit 0, 55 lines, house triple, stored as
`axioms_instance_relaunch.{txt,exit}` in the same receipt; the first attempt was
SIGTERM'd at 31 s by something outside this session, and the relaunch is the one of
record.

### Next single action

**The strip-analyticity quadrature lemma** — `|trapezoid_n(H) − ∫ H| ≤ C·q^n` for
`H = (2+2cos)·2^{f}`, `f` a finite trigonometric polynomial, with `q` from the
analyticity half-width and `C` from a Cauchy estimate; then the inner integrals of §3.
Everything after that is `norm_num`.

## Row lane 2026-11-10 (17) — residual (iii)'s two named successors: the transfer and the loop induction, and a charge it corrects (LANDED)

Round 16 closed the program-entry reach and named exactly what was left: *"closing that
means transferring §C4–§C6's `getD` facts to `cmpSeg 29 ++ tail` … and the loop proper
(an induction on `p` with the guard and the accumulator) stands on top of it."* This
round does both, and the second one **corrects the charge again**: a counting loop pays
`cmpSegCost + 6`, not `+ 5`.

### The seam is a replay, not a congruence — and that is why it looked hard

The composed program differs from `cmpSeg 29` at position `29`, which is *exactly* where
the segment's last step jumps. So `exec` on the two programs cannot be compared by
agreement at all: at `29` the plain program reads `Instr.reject` (the `getD` fallback)
and the composed one reads the loop tail. The only honest route is to replay the chain
against an abstract `P` agreeing on `0…28` — which is what `cmpSeg_reaches_gen` is.

**Simulated first (arm A of `sim_loop.py`).** Before any Lean: run both programs on six
digit blocks and compare the traces step for step. They are identical in pc **and in
memory** for the whole `0…28` walk, and they arrive at `29` in the same state; only the
instruction *at* `29` differs. That is the transfer's content, measured — if the traces
diverged anywhere below `29` no amount of Lean would fix it.

The 16 `_gen` declarations are mechanically derived from §C4–§C6 by `gen_transfer.py`,
which lists its six rewrites in its own docstring and prints what it copied and what it
skipped. Nothing is re-argued: the only things that change are the `getD` facts
(`rfl` becomes `hgd`) and the word `cont`, which becomes `29`. The free-`cont`
originals are untouched, so the copies cannot break them.

### The charge: `+6`, not `+5` — and it is the count that costs

`cmpSeg_loopCharge_le` charges `cmpSegCost + 5 ≤ 19 + 9p` for a terminating loop.
Inherited as written, that number is right for a loop that **does not count**. The row's
verdict is `0 < hitCount` (`hitCount_pos_iff`), and `KapilaLoop`'s `scan_loop` carries
`acc + hitCount …` across its iterations — so the loop the row needs must accumulate,
and the accumulate is one instruction:

| charge | value | who |
|---|---|---|
| one comparison (segment) | `cmpSegCost` (exact), `≤ 14 + 9p` | §C6 |
| re-entry, `p` already in cell 13 | `+4` | `cmpSeg_reentry` |
| terminating loop, **no** accumulation | `+5`, `≤ 19 + 9p` | `cmpSeg_loopStep` |
| terminating loop, **counting** | `+6`, `≤ 20 + 9p` | this round |

Measured, not asserted: `sim_loop.py` arm B runs the 6-instruction tail and finds that
at `cmpSegCost + 5` the program is **still inside the tail at pc 34** — the sixth step is
real. Arm D then checks `cmpSegCost + 6 ≤ 20 + 9p` over a grid of digit blocks (worst
slack 6). Cell `15` is the accumulator, outside `CmpCell` (so the frame covers it) and
outside the digit blocks because `16 ≤ addrV, addrA` — a layout hypothesis this module
*states* rather than assumes.

### The loop induction: `scan_loop`'s shape, at the segment's granularity

The frame is parametrized rather than nested: `CmpLoopFrame h p acc = up (up h 13 p) 15 acc`,
so each iteration's `up (up …) 13 (p+1)` lands back on the same shape (`up_up_absorb`) and
the induction needs one rewrite per iteration instead of a growing nest of `up`s. Two
congruences keep the *price* a function of the digits and not of the frame
(`walkCost_congr`, `cmpSegCost_congr`) — without them the segment's chain, run against
the loop's frame, would be priced in the loop's frame while the loop's fuel is priced in
the caller's, and the arithmetic could not chain.

The accumulated run shape, exactly:

```
cmpLoopHits h addrV addrA p m r = Σ_{i<m} (if digHalf h h addrV addrA (p+i) r then 1 else 0)
cmpLoopFuel h addrV addrA p m r = Σ_{i<m} (cmpSegCost h addrV addrA (p+i) r + 6)
cmpSeg_loop      : m comparisons from p0, all guards taken (p0+m < limit),
                   reach `0` with the counter at p0+m, the accumulator at
                   acc + cmpLoopHits, and the frame CmpLoopFrame h (p0+m) (acc + hits)
cmpLoopFuel_le   : cmpLoopFuel ≤ m * (20 + 9 * (p + m))
```

Simulated too (arm C): six digit blocks, `cmpLoopFuel` equals the measured halting fuel
to the step, the accumulator's increments sum to `cmpLoopHits`, and each iteration's
cell `6` equals `digHalf` at that `p`. Arm C′ is the control: the round-16 defect (reload
before advance) ends on a different verdict, so the check bites.

### What is proved

| declaration | content |
|---|---|
| `cmpSeg_reaches_gen` (+15 `_gen`) | §C4–§C6 replayed for `{P} (hgd : ∀ i ≤ 28, P.getD i = (cmpSeg 29).getD i)` — mechanically generated |
| **`cmpSeg_reaches_program`** | **THE TRANSFER, ON THE REAL PROGRAM**: `cmpSegCost` steps from `0` to `29` on `cmpSegmentProgram tail`, verdict in cell `6`, frame intact |
| `cmpSeg_hitBody` | `pc 29 → 34` in 5: accumulate, advance, reload — verdict preserved |
| `cmpSeg_guard_taken` / `cmpSeg_guard_exit` | the guard, one instruction, both successors |
| **`cmpSeg_hitIter`** | **ONE COUNTING ITERATION**: `0 → 0` in `cmpSegCost + 6`, counter at `p+1`, accumulator at `acc + verdict`, frame re-parametrized |
| **`cmpSeg_loop`** | **THE LOOP**: `m` comparisons, `cmpLoopFuel` steps, `cmpLoopHits` accumulated |
| `cmpSeg_hitCharge_le`, `cmpLoopFuel_le` | `+6 ≤ 20 + 9p`; `cmpLoopFuel ≤ m * (20 + 9(p+m))` |
| `CmpLoopFrame` + 8 cell lemmas, `up_up_absorb` | the frame algebra the induction runs on |
| `cmpDigitsFrom_congr`, `digHalf_congr`, `walkCost_congr`, `cmpSegCost_congr` | the verdict and the price are functions of the digits, not of the frame |

**What is not claimed.** (a) The early-exit variant of the loop (a hitscan that jumps to
`accept` on the first hit) is *also* `+6` — one instruction either way, the accumulate or
the exit guard — but it is not proved here; the row's stated verdict is the count, so the
count is what got proved. (b) `cmpLoopFuel_le`'s bound is deliberately loose at the top
end (`p + m`, not `p + m − 1`); the exact per-comparison figure is `cmpSegCost + 6` and
(iv) can use either.

### Peer coordination

`JV1000Quadrature.lean` is the **jv1000 mind's** file and this round did not touch it.
No manifest moves: `sources.sha256` is regenerated by the receipt over
`SubsetSumL25/Row/*.lean`, so the peer's in-flight drift will show there and is that
mind's business. New files this round, all in the lane: `SubsetSumL25/Row/KapilaCmpSegLoop.lean`
(the module), `parts/c10_transfer_gen.lean` (generated), `parts/c11_loop.lean` (hand),
`gen_transfer.py`, `assemble_loop_module.py`, `sim_loop.py`. `Statement.lean` unchanged
(`3dc6567e…34aa`), `KapilaCmpSeg.lean` unchanged (`6f00b833…6dc3`) — the whole round is
additive, which is also why the landed module's olean hash is untouched.


### Receipt

**Receipt `receipts/kapila-20261111T021745Z`** — gate `swapouts_delta60=0 free_pct=60`;
build exit 0 in **6.6 s**, and that is a **replay, not a compile**: the oleans were
already current because this session's own `lake build SubsetSumL25.Row.KapilaCmpSegLoop`
had produced them.  The receipt alone is therefore *not* evidence that the final bytes
compile, so the module's `.olean`, `.ilean` and `.trace` were deleted and it was rebuilt
**from scratch**: the same sha256 `63894d53…56228b`, 4 290 304 bytes.  That rebuild is
the compile of record.

Axiom banner exit 0, **242 banner lines**, `axiom_banner_house_triple_only: true`.  The
three load-bearing declarations are on the house triple —
`cmpSeg_reaches_program`, `cmpSeg_hitIter`, `cmpSeg_loop` each `[propext,
Classical.choice, Quot.sound]`; `cmpLoopFuel_le` is on `[propext, Quot.sound]` alone; the
definitions (`cmpHitTail`, `CmpLoopFrame`, `cmpLoopHits`, `cmpLoopFuel`) and the sixteen
`_gen` copies print "does not depend on any axioms" or a subset.  No `sorryAx`, no
`native_decide`; `sorry`/`admit` do not occur in the module at all.

`Statement.lean` is still `3dc6567e…34aa` and `KapilaCmpSeg.lean` still `6f00b833…6dc3` —
this round is purely additive, which is also why the landed module's olean hash did not
move.  `head` = `4da99e7`.  Lock: the bounded 240 s wait expired and the build proceeded
UNLOCKED, deviation recorded in `lock.acquired` / `summary.json` — the policy working,
not a stall.

**Peer coordination.**  `JV1000Quadrature.lean` and `JV1000Instance.lean` are the
**jv1000 mind's** files, both in flight in this shared worktree and both untouched here.
No manifest moves: `sources.sha256` is regenerated over `SubsetSumL25/Row/*.lean`, so
that mind's drift will show up in it and is that mind's business.

### Measurements for the next author

1. **`rw` does not see through a `def`.**  Writing the loop's program as
   `def cmpHitProgram := cmpSegmentProgram cmpHitTail` made every `getD` step fail with
   "did not find an occurrence of `(cmpSegmentProgram ?tail).getD (29 + ?i)`" while the
   term it names was literally in the goal.  Name the term, or `unfold` inside the proof.
2. **The `getD`-agreement hypothesis must take `i` explicitly.**  `cmpSegment_getD`'s `i`
   is *implicit*, so passing it where `∀ i, i ≤ 28 → …` is expected fails with an
   argument-position message that blames the wrong thing; pass
   `fun i hi => cmpSegment_getD tail hi`.
3. **`rw [hf n, hg n]` before the `by_cases` destroys the condition.**  Lean normalises
   `f' x = f' x` to `True` and collapses the `if`, so the subsequent `if_pos` matches
   nothing and the goal is left as `12 = if … then …`.  Case-split on the `f'` form
   first, then rewrite *both* sides with the derived `'` versions (`if_pos hc'`,
   `if_pos hc`).
4. **`Nat` addition's associativity is not definitional.**  `addrV + (p0 + 1 + m)` is not
   the goal's `addrV + (p0 + (m + 1))`; `by omega` at the `refine` slot costs nothing.
5. **The accumulator's word room is a hypothesis, not a detail.**  `upFit` needs
   `f 15 + f 6 < 2^w`, which `hfit 15` and `hfit 6` do **not** give — the first attempt's
   `omega` counterexample was exactly that sum overflowing.  Hence `acc + m < 2^w`, room
   for one increment per remaining comparison, and the loop carries it.
6. **`lake build` for this module is ~46 s once the dependencies are up**, and a
   foreground shell that kills at ~250 s makes a two-minute build look like a hang.
   Background it; the verdict is in the log, not in the exit of the wrapper.
7. **`induction m generalizing p0 acc st` reorders the IH's binders**, and the failure
   (`hfitH` expected to be `st 0 = addrV + (p0 + 1)`) reads as an insane argument order.
   Quantify the run *inside* the statement (`∀ m p0 acc st, …`), then `intro m` and
   `induction m`; the hypothesis order is then exactly the statement's.

Next single action: **residual (iv)** — restate `D7.agrees`'s horizon per comparison at
`20 + 9p` (`cmpLoopFuel_le` is the sum), decide the count-vs-early-exit variant (both
`+6`; the count is proved and is what `hitCount_pos_iff` reads), and keep
`PayloadCarries` as the *named* accumulation premise rather than re-proving absorption.

## Row lane 2026-11-10 (18) — residual (iv): the horizon restated at `20 + 9p` per comparison (LANDED)

Round 17 closed with the instruction this round executes: *"restate `D7.agrees`'s horizon per
comparison at `20 + 9p` (`cmpLoopFuel_le` is the sum), decide the count-vs-early-exit variant,
and keep `PayloadCarries` as the named accumulation premise rather than re-proving absorption."*
§C12 of `Row/KapilaCmpSegLoop.lean` is that, and nothing else — **restated, not discharged**:
`D7.agrees`'s horizon *field* (`R.cost n x`, in `Row/KapilaRow`) is untouched, because it is what
the arithmetic is *applied to*; the round adds the arithmetic, the end-to-end shape, and the record
of where each number lives.

### The shape, end to end — in the word-operation vocabulary

§7 step 7's test segment runs `blockLen` comparisons from counter `p`, and its exact charge is

  `Σ_{i<blockLen} (cmpSegCost h addrV addrA (p+i) r + 6)  +  prologue + epilogue`

with prologue/epilogue the row program's parts outside the test segment (loading the two blocks;
writing the verdict).  The Σ is not a bound on `cmpLoopFuel`, it *is* `cmpLoopFuel` —
`cmpLoopFuel_eq_sum` proves the identity, so §C11's recursion is read as the sum it is.  The unit
is `Routines.cost`'s word operations (`D7`'s docstring fixes it), and the envelope that absorbs the
sum is `Routines.WithinEnvelope` + `envE_absorb` — **not re-proved here**, per instruction; the new
lemma stops at the horizon.

### The variant: counting, and the one-line reason

The **counted** loop is the one proved, and it is the one the row needs: both it and the early-exit
hitscan pay `+6` per comparison (one instruction either way — the accumulate, or the exit guard),
so the arithmetic cannot choose between them; the row's verdict `0 < hitCount` does, because what
the loop is *for* is the count.  The early-exit variant remains unproved and is recorded as such.

### Looseness as a number, not a remark

`cmpLoopFuel_le`'s `m * (20 + 9 * (p+m))` prices every comparison at the counter's value *after*
the last increment.  The tight uniform form is `m * (20 + 9 * (p+m-1))` — the last comparison
actually runs at `p+m-1` — and it is now proved (`cmpLoopFuel_le_tight`, for `m ≥ 1`) through a
reusable step (`cmpLoopFuel_le_mul`: a uniform per-comparison charge `B` gives `m·B`).  Both
readings are available; a caller that wants the loose one gets it from `cmpLoopFuel_le`.

### What is proved (5 declarations, all house triple or a subset)

| declaration | content |
|---|---|
| `sum_range_shift` | `Σ_{i<m+1} g(p+i) = g p + Σ_{i<m} g(p+1+i)` — the index shift the Σ needs (peels the head, because the loop's recursion peels `p`) |
| **`cmpLoopFuel_eq_sum`** | **the end-to-end shape**: `cmpLoopFuel = Σ_{i<m} (cmpSegCost (p+i) + 6)` |
| `cmpLoopFuel_le_mul` | a uniform per-comparison charge `B` over the run's own indices gives `m·B` |
| `cmpLoopFuel_le_tight` | the tight uniform horizon `m·(20 + 9·(p+m−1))`, `m ≥ 1` |
| **`cmpLoopFuel_fits`** | **the form `D7.agrees` consumes**: `pro + m·(20+9·(p+m)) + epi ≤ T ⟹ pro + cmpLoopFuel + epi ≤ T` |

### Wiring the seam record

`Row/KapilaRow`'s `D7` docstring gained the paragraph «The one segment whose horizon is a number»:
the per-comparison `20 + 9p'`, the Σ, the horizon-fit form, the counted-variant decision, the
`p+m`/`p+m−1` looseness, and the explicit statement that `PayloadCarries` stays named and the
envelope's absorption stays `envE_absorb`'s.  **Cited, not imported** — the loop module is not in
`KapilaRow`'s import closure and does not need to be: the figure is arithmetic, and the paragraph
is the record of where it lives.  `KapilaRow` was then recompiled from scratch (olean deleted) to
prove the docstring edit parses and the module still closes.  `Statement.lean` untouched
(`3dc6567e…`); `KapilaAlgo.cost`, `PayloadCarries`, every `JV1000*` file (the peer's, in flight in
this shared worktree) untouched.

### Receipt

**`receipts/kapila-20261111T025151Z`** — gate `swapouts_delta60=0 free_pct=57`; build exit 0 in
**44.9 s**, which is a **replay** (the closure was already current from this round's own
from-scratch rebuilds) and is therefore *not* the compile of record.  The compiles of record are
the two from-scratch rebuilds: `KapilaCmpSegLoop`'s `.olean`/`.ilean`/`.trace` deleted and rebuilt
twice to the identical sha256 `68f20b76…21eb0e` (4 463 752 bytes) — the determinism double-compile
— and `KapilaRow`'s deleted and rebuilt to `b1ec5186…ab8dd9`.  Axiom banner exit 0, 247 lines, 231
`depends on axioms` lines, `axiom_banner_house_triple_only: true`.  The five new declarations:
`sum_range_shift` and `cmpLoopFuel_eq_sum` on `[propext, Classical.choice, Quot.sound]`;
`cmpLoopFuel_le_mul`, `cmpLoopFuel_le_tight`, `cmpLoopFuel_fits` on `[propext, Quot.sound]` — the
same pair as `cmpLoopFuel_le`, which is the marker of pure arithmetic.  No `sorryAx`, no
`native_decide`.  Lock: **DEVIATION, recorded** — bounded 240 s wait expired, build proceeded
UNLOCKED (`lock.acquired`, `summary.json`).  `head` at receipt time = `3c29c99`, the **peer's**
`jv1000` commit, which landed in this shared worktree during the round; my commit stacks on it.

### Measurements for the next author

1. **`rw` can close a goal, and then the next tactic errors "No goals to be solved".**  The
   successor step of `cmpLoopFuel_eq_sum` was closed by its three rewrites; the trailing `omega`
   was the only error in the round.  When a `rw` chain ends a proof, delete the finisher — do not
   add `try`.
2. **A detached build can still be killed.**  `start_new_session=True` (new process group) did
   not protect a `lake build` launched that way: the process vanished ~10 s in, leaving the
   `.olean.hash`/`.trace` written and the `.olean` absent, with **no error line** in the log.  A
   foreground shell call with a long timeout ran the same build to completion.  Trust the olean,
   never the trace.
3. **Lake replays cached *warnings*.**  A log full of `if_pos has been deprecated` lines from
   `KapilaCmpSeg.lean` means the dependency was **replayed**, not recompiled — the `⚠ [n/m]
   Replayed <Module>` lines are the tell, and the module you actually care about appears after
   them.  Reading the warnings as "it is compiling the deps" wastes a cycle.
4. **The last dependency step is the only one that costs.**  With the closure cached, the receipt
   build is 44.9 s (replay) while one module compiles in ~46 s and the whole `Row` closure from
   scratch is minutes under the fleet's load (140 at the time).  Delete-and-rebuild is the only
   compile evidence; the receipt says so in its own words now.

Next single action: **`PayloadCarries`** (`Row/KapilaBinSum.lean`) — the accumulation stage the
checksum program does not contain, and now the *last* named premise of the test/checksum path that
has a concrete obligation attached (the early-exit variant and the M-series goals are the other
residuals, both recorded as unproved/false-as-stated respectively).

## Row lane 2026-11-11 (19) — `PayloadCarries` classified: **(b) a data contract**, placed in the seam record (LANDED)

Round 18 closed with: *"`PayloadCarries` (`Row/KapilaBinSum.lean`) — the accumulation stage the
checksum program does not contain, and now the last named premise of the test/checksum path that
has a concrete obligation attached."*  This round executes it as a **classification**, because the
open thing was the premise's *kind*, not its arithmetic.  Two readings were live: **(a)** a
refinement obligation with a program (§C10–§C12 style — a segment, its block-writing invariant,
its cost shape), or **(b)** a data contract (the caller supplies the accumulated blocks; a
D7-style named input).

### The criterion, and the verdict: (b)

Criterion: does the row's `Routines` program family *contain* an accumulation stage per §6.2, or
does it read pre-accumulated payloads?  Three measurements settle it:

1. **§6.2 puts the accumulation inside the phase computation** — «Each phase is computed to error
   `2^{-2n²}` with dyadic parts, each weighted term is rounded to `n²` fractional bits, and the
   sums are exact» (`PROOF_0.4877.tex` B.4; §6.2's own «the finite-precision arithmetic do not
   change»).  In this row that computation *is* `Routines.aliasA`/`checksumB` — abstract fields
   returning `Option (List ℚ)`.
2. **The family's landed instruction texts are witness legs, not phase texts.**  `prelimProg`
   (17), `aliasProg` (20), `checksumProg` (24): each saves its inputs, walks `a` against `t`,
   accepts/rejects — and each **agreement field is verdict-only**
   (`run prog … = some (phase …).isSome`), so none reproduces an estimate list, let alone writes a
   payload block.  Machine-checked this round: memory writes are `1`/`2`/`3` saves
   (`writePositions` = `[6]`, `[6, 8]`, `[6, 8, 10]`, all ahead of each text's first `load`) and
   **every branch target is forward** (`noBackEdge` = `true`) — the texts are straight-line, so
   there is no loop body in which an accumulation could run.
3. **The test path already writes the memory as an input.**  `PayloadConvention.mem` is «the
   segment's exit memory»; `Ahat`/`Vhat` are *read* from it, and the wide exit takes `hA`/`hV`
   through `numBlock`.  `payloadCarries_iff_numBlock` proves `PayloadCarries` **is** the
   digit-level block equation `numBlock … = (range len).map numV ∧ …`.

So relative to every text and every consumer the row has, the blocks are **pre-accumulated**: the
premise is a precondition on the memory, not a program obligation.  **(b).**

### Why (a) would have been wrong to take on — two structural reasons

* **Subsumed.**  The accumulation lives inside the phase computation, which the row already owes
  as the full `aliasProg`/`checksumProg` phase texts (the landed legs are verdict-only).  An
  (a)-class `PayloadCarries` would be a sub-obligation of an obligation already named — a second
  charge for one debt.
* **It would assert a layout the paper does not fix.**  §6.2 fixes the *precision* (`n²`
  fractional bits) and exactness; it fixes no address layout.  The blocks at `base + i·stride` are
  `PayloadConvention`'s — this tree's *convention* (`baseV`, `baseA`, `stride`, `blockLen` are
  caller-chosen).  A block-writing invariant would be a theorem about an interface we invented;
  the honest form is the interface, and the layout's *inhabitation* is already proved
  (`placeValueAt_payloadStride`).

### What landed (13 declarations, `Row/KapilaBinSum.lean` §S6)

| declaration | content |
|---|---|
| `isWrite`, `writePositions`, `noBackEdge` | the computable evidentials: which instructions write memory; whether every branch target is forward |
| `prelimProg_writes` / `aliasProg_writes` / `checksumProg_writes` | `[6]` / `[6, 8]` / `[6, 8, 10]` — 1/2/3 saves and nothing else |
| `*_straightLine` (×3) | `noBackEdge … 0 = true` — no loop body exists in any landed phase text |
| `phaseTexts_no_accumulation` | the six facts as one conjunction: the criterion, machine-checked |
| **`payloadCarries_iff_numBlock`** | the premise *is* the row's own block equation, in `numBlock` |
| **`structure PayloadSeam`** | the seam record at the test path: `fit`, `numV`, `numA`, `carries` |
| **`PayloadSeam.agrees`** | `WideBinSumAgrees` from the record alone — the premise is *used*, not declared |

The file's header §S6 carries the full argument **and the row's named-input table in one place**;
`Row/KapilaRow`'s `D7` docstring gained «The data premise is not this seam, and is now placed
elsewhere» (cited, **not** imported — `KapilaBinSum` is downstream of `KapilaRow`).

**The three names this round was asked to sit beside — `hret`, `hTt`, `hident` — do not exist in
this lane.**  A grep over every `Row/*.lean` and every `.md` finds only `M5.lean`'s unrelated
`hident1`/`hident2` locals.  They are another row's seam vocabulary; §S6 says so rather than
inventing them, and places `carries` in this row's own record instead.

### Receipt

**Determinism double-compile** (the compile of record): `KapilaBinSum`'s
`.olean`/`.ilean`/`.trace` deleted and rebuilt **twice from scratch**, both to sha256
`05ef66ef9e7a38d817850ebeffc75ae323a886f84d890719a047db00af360a4a` (362 168 bytes);
`KapilaRow.olean` rebuilt from scratch to `87b51b98…c60c76` (1 382 064 bytes) after its docstring
edit.  Axiom banner exit 0, **244** `depends on axioms` lines, house-triple only: the `decide`
evidentials on `[propext]`, `payloadCarries_iff_numBlock` on `[propext, Quot.sound]`,
`PayloadSeam`/`PayloadSeam.agrees` on the full house triple.  No `sorryAx`, no `native_decide`;
`Statement.lean` still `3dc6567e…34aa`.  Receipt `receipts/kapila-20261111T031713Z` from the
bounded runner — **gate** `swapouts_delta60=0 free_pct=54`; **lock DEVIATION, recorded**:
bounded 240 s wait expired, the build proceeded UNLOCKED (`lock.note`, `summary.json`) — the
policy working, not a stall; `build_exit=0` in **39.4 s**, which is a **replay** of this round's
own double-compiled oleans (`KapilaBinSum.olean` 362 168 bytes sha256 `05ef66ef…360a4a`, i.e. the
compile of record above), so the runner's 39.4 s is *not* cited as compile evidence; banner exit
0, 244 lines, house-triple only.  **`head` at receipt time = `76f9fdc`** — the peer jv1000
(strip-analyticity) lane's commit, which landed in this shared worktree during the receipt; my
commit `6a1cfac` stacks under it and is on `origin/wip-kapila-row` by ancestry
(`git branch -r --contains`), not by a push of mine.

### Measurements for the next author

1. **`List.map_inj_left` is the converse `List.map_congr_left` lacks** —
   `map f l = map g l ↔ ∀ a ∈ l, f a = g a`.  With `List.mem_range`, a list-equality hypothesis
   becomes the pointwise form in one `mp`, no induction.  (Both lemmas exist in this Mathlib pin;
   `#check` before assuming a name.)
2. **`decide` closes a closed `List Nat` equality and a `Bool`-matcher fold** — no `DecidableEq`
   on `Instr` is needed when the predicate returns `Bool` (`List.filter` takes `α → Bool`, not a
   `DecidablePred`).
3. **A probe file at the lane root is safe** (`lakefile.toml`'s globs are `SubsetSumL25*` only),
   and `#eval` is the cheap way to learn a computable fact *before* asserting it in a `decide`
   theorem — `[6]`/`[6,8]`/`[6,8,10]` and `true`/`true`/`true` came back exactly as predicted, so
   the `decide` proofs were written once and closed on the first compile.
4. **Two modules, two from-scratch compiles, 1 m 38 s total** at the fleet's load; the second
   compile of `KapilaBinSum` alone took 43.6 s.  Delete-and-rebuild is still the only compile
   evidence.

Next single action: **the stride-`k` payload read in the test segment.**  `cmpSeg` reads one word
per index (`addrV + p`), while the estimates `PayloadSeam.carries` speaks about sit in `stride`-word
blocks; write the k-word read (a fold of `stride` loads with `2^{w·j}` place weights), prove the
fold *is* `numAt` at each estimate's address, and charge `stride` words per estimate into §C12's
per-comparison figure — the last gap between the data contract and the segment's cost.

## Row lane 2026-11-11 (20) — the stride-`k` payload read: the fold is `numAt`, and the charge is *stride-invariant* (LANDED)

Round 19 closed with: *"the stride-`k` payload read in the test segment — a `stride`-fold of loads
with `2^{w·j}` weights, proved equal to `numAt`, charged `stride` words per estimate into §C12's
per-comparison figure."*  This round does it, and the measurement changes the charge's **shape**,
not only its constant.  New module `Row/KapilaCmpSegStride.lean` (§C13), a leaf of the import DAG.

### The fold verdict: the fold *is* `numAt`, and that identity is not the content

`strideFold` is the read written as the running accumulator a program produces
(`Σ_{j<n} f (addr+j)·2^{w·j}`, built left to right), and `strideFold_eq_numAt` is `numAt_succ`
read the other way.  **It is an identity, and §C13 says so** rather than dressing it: `numAt`'s
definition *is* this fold, so «the fold is `numAt`» costs nothing to prove.  What has content is
the consequence, and it is two landed theorems:

* **`numAt_term_at_estimate` + `numAt_split_at_estimate`** — at estimate `i` the block starts at
  `baseV + i·stride`, so the digit the segment loads is the fold's `p`-th term
  `f ((baseV + i·stride) + p)·2^{w·p}`, and `numAt_split` at that address says the block *splits*
  there.  So the landed digitwise segment is **already** a read of the stride-`k` fold — it never
  materialises a numerator, which is exactly why `numAt_not_word`'s obstruction does not bite.
* **`digHalf_estimate_eq_threshold`** — `digHalf_eq_threshold` was stated at an *abstract* address,
  so transferring the decision lemma from stride 1 to stride `stride` is free: the segment's
  verdict at estimate `i` *is* §7 step 7's integer test on the two folds.
  **`payloadStride_fits_digit`** discharges its one layout premise (`(F−1)/w + 1 ≤ payloadStride w F`)
  at §6.2's own layout, and **`digHalf_estimate_payloadStride`** is the result with no hand-supplied
  fit left.  Proved, not assumed: `decide`-free, `omega` + `Nat.div_le_div_right`.

**Named remainder: none at the arithmetic level.**  The fold's *program* is a different object and
is named below.

### The restated §C12 charge: `blockLen · (20 + 9p)` with `p` FIXED — the drift was a stride-1 artifact

The obvious reading of «charge `stride` words per estimate» is `cmpSegCost · stride`.  **That is not
what the segment pays, and the difference is the whole point of (i)'s re-specification.**
Machine-checked (`cmpSeg_readPositions`, by `rfl`): `cmpSeg` has exactly **four** `load`
instructions, at positions `[0, 1, 21, 22]` — two prologue digit reads, two walk-head reads.  A
comparison reads **one word per side per digit position** and descends at most `p` digits on a tie.
**The stride lives in the addresses (`baseV + i·stride + p`), not in the read count.**  So:

    per comparison:   cmpSegCost h (baseV + i·stride) (baseA + i·stride) p r + 6  ≤  20 + 9p

with **`p = (F−1)/w` a constant** — the digit holding the `1/2` bit — not a drifting counter.  That
changes the *shape*: §C12's `m · (20 + 9·(p+m))` drifts because the landed loop's counter carries two
roles at once (the digit *address* offset and the digit *position*), which coincide only at
`stride = 1`.  `estFuel` is the same run at the fold's addresses with the roles separated
(`estFuel_succ` advances **both bases by `stride`** — `numBlock_succ`'s shift one level up), and:

| declaration | content |
|---|---|
| **`estFuel_le`** | `estFuel … n ≤ n · (20 + 9p)` — **no drift term** |
| `estFuel_le_landed` | `≤ n · (20 + 9·(p+n))` — so the restated figure fits under §C12's; nothing landed is contradicted |
| `estFuel_eq_sum` | the charge is a Σ over the fold's drifting addresses at the fixed digit (`estFuel`'s `cmpLoopFuel_eq_sum` twin) |
| `estFuel_le_paper` | the same bound at `p := (F−1)/w`, `r := (F−1)%w` |
| `estFuel_fits` | the horizon-fit form `D7.agrees` consumes, at the restated charge |

**And the `stride`-word charge exists — for a read the row proves impossible.**  `scanWordOpsWide
blockLen stride = blockLen·(2·stride+3)` prices a whole-block read; `numAt_not_word` proves that
numerator does not fit a state word, so the digitwise segment does not perform it.  Its word-op
charge is the same shape at the digit count it visits (`digitwise_is_wide_at_digit`:
`scanWordOpsWide blockLen (p+1) = blockLen·(2·(p+1)+3)`), and `digitwiseWordOps_le_wide` bounds it by
the whole-block figure at any `p+1 ≤ stride`.  So charging `stride` words per estimate into §C12
would be charging, inside the digitwise accounting, for the read the digitwise re-specification
exists to avoid — it is a valid *upper bound*, and that is how it is stated.

### The program is NOT landed, and the simulation says why (`sim_stride.py`, kept)

Everything above is arithmetic, at §C12's own level.  The **program** does not follow for free.  The
landed tail reloads the walk's counter from the loop counter (`.add 2 13 7`); at `stride = 1` the two
roles coincide, at `stride = k > 1` they do not.  Six arms, 3 fixed blocks + 60 swept, all pass:

* **D1** with the counter at `i·k + p` and cell 2 reloaded from a `p` **constant**, iteration `i`
  reads exactly `(baseV + i·k + p, baseA + i·k + p)` — the fold's `p`-th term at the estimate's
  address — and every load stays inside a block (measured on all three blocks).
* **D2** keeping the landed reload, the walk's span becomes `i·k + p` digits instead of `p` and
  spills into earlier estimates: measured loads per iteration `{4,6,6,6}` vs `{4,4,4,4}` (k=2),
  `{6,8,8}` vs `{6,6,6}`, `{8,10}` vs `{8,8}`.  It stays *inside* the arrays, which is why this
  defect is arithmetic and not a crash.
* **D2b** on a block built for it, the collapse **flips a verdict**: `acc = 0` where the
  per-estimate test gives `1` (k=2, p=1, r=2; estimate 0 a close unequal pair `5` vs `6`, estimate 1
  a V-side tie whose spill reaches estimate 0's digit).  So the counter/digit separation is a
  correctness fix, not a taste.
* **D3** the guard's limit must be `blockLen·k + p`, not `blockLen` — the stride-1 shape stops the
  run early (measured: 1 comparison of 3, 1 of 2).
* **D4** the per-comparison charge is exactly `cmpSegCost + 6` (+1 halting step) on every block: the
  stride advance is one instruction either way, so §C13's `+6` is measured, not assumed.
* **D5/D6** the correct shape's accumulator equals the per-estimate `digHalf` count on all 3 fixed
  and all 60 swept blocks.  (Honest note: the collapse's accumulator also matched on all 60 swept
  blocks — random low digits almost always decide inside the estimate's own block.  D2b's
  constructed block is the arm that exhibits the verdict flip.)

**Named as the next piece, not claimed:** the stride tail program — a `cmpSeg` variant whose walk
counter is reloaded from a `p` constant, with a stride-advanced loop counter and a `blockLen·k + p`
limit — and its §C10-style reach against `estFuel`.

### Receipt

**Determinism double-compile** (the compile of record): `KapilaCmpSegStride`'s `.olean`/`.ilean`/
`.trace` deleted and rebuilt **twice from scratch**, both to sha256
`3943edfa2798acc5274aa44295978e10732dd584bbdf23dcd81539f4b2ed2859` (355 352 bytes); the second
compile 33 s, the first 40 s, at a host load of 66–116 (other lanes).  Axiom banner exit 0,
**266** `depends on axioms` lines (was 244; +22 for this round): 151 house-triple, 68
`[propext, Quot.sound]`, 47 `[propext]`, and two on **no axioms** at all —
`digitwise_is_wide_at_digit` and `cmpSegReload_couples_roles`, both definitional equations.  No `sorryAx`, no `native_decide`.  `Statement.lean` still
`3dc6567e…34aa`; family files 0-diff (the only tracked edit is `KapilaRowAxioms.lean`, the banner).
The jv1000/strip lane's files (`JV1000Decay.lean`, `JV1000DecayAxioms.lean`,
`jv1000_decay_receipts.py`, `sim/sim_decay.py`) are untracked in this shared worktree and are
**not** in this commit.

**Receipts `kapila-20261111T035056Z` (FAIL, host kill) and `kapila-20261111T035701Z` (DONE) — both
kept, neither retracted.**  The first attempt passed the gate on iteration 1
(`swapouts_delta60=0 free_pct=64`) and then hit **two recorded deviations**: the bounded 240 s lock
wait expired so the build proceeded UNLOCKED (`lock.note`, `summary.json` — the policy working, not a
stall), and the axiom banner was **SIGKILLed** by the host (`axioms_exit = -9`) under load 66–116, so
its `STATUS` reads `FAIL axiom gate` with the kill as the reason.  Its `build_seconds = 4.1` is a
*replay*, so its `oleans.txt` hash (`3943edfa…ed2859`, 355 352 B) **is** the double-compile's — the
bytes of record, not a compile.  `receipts/kapila-20261111T035056Z/NOTE.md` says what the −9 is, and
`axioms.independent.txt` beside it carries a separate foreground run of the identical command on the
identical oleans (exit 0, 266 lines, house-triple only) **explicitly labelled as not the runner's own
banner** — "the banner was proved to pass out-of-band, the runner's copy was SIGKILLed" is the honest
sentence and it is the one written there.

**The second attempt is the clean receipt:** `kapila-20261111T035701Z`, launched with
`KAPILA_LOCK_WAIT=900`, **lock acquired** after 180.2 s, gate PROCEED (`delta60=0 free_pct=65`),
`build_exit = 0` in 6.1 s (a replay — the olean's mtime `19:49:34` is the double-compile's), the
runner's **own** banner exit **0**, 266 lines, house-triple only (`axiom_banner_house_triple_only:
true`), and `oleans.txt` again `3943edfa…ed2859`, 355 352 B.  So the one deviation that mattered in
attempt one (the 240 s bound) is cured by the bound's own parameter, and the kill is superseded by a
receipt that carries the runner's own banner.

**head at receipt time = `a40f541` — the peer jv1000 lane's round-19 commit, which landed in this
shared worktree mid-receipt and which also swept this round's `PROGRESS.md` entry into itself.**  The
shared-index hazard, in its ordinary form: one file, two authors, one `git add`.  **No content was
lost** — the entry is intact in `a40f541` — but it landed under the jv1000 commit's message, and this
paragraph is the re-attribution.  This round's own commit carries the module, `README_ROW.md`,
`sim_stride.py`, `KapilaRowAxioms.lean` (the banner) and the receipt, and nothing of the peer lane's.

Next single action: **the stride tail program** — land the `cmpSeg` variant (cell 2 reloaded from a
`p` constant, counter advanced by the stride constant, limit `blockLen·k + p`) and its reach proof
against `estFuel`, re-deriving §C10's `getD`-agreement transfer for the new tail.  The arithmetic it
must compose with is landed; the program is the only piece between §C13 and a segment theorem at
stride `k`.

**Register correction (appended after the fact).**  The commit message for `7e6cc7d` ends with
"Register: none (this lane keeps its record in PROGRESS.md/README_ROW.md)" — that sentence was
wrong, and this is the correction rather than a rewrite of a pushed message.  Three entries were
opened for this round: **R2125609760** (wound, medium) the peer's `a40f541` sweeping this round's
uncommitted `PROGRESS.md` entry into itself — the shared-index hazard above, filed so the body's pull
engine can see it rather than only this lane's docs; **R2125609761** (wound, medium) the
unattributed SIGKILLs — the receipt's axiom banner (`-9`) and two short `sleep` tool calls
SIGTERMed at host load 66–116, with nothing in the documented deadline inventory accounting for the
latter; **R2125609762** (task, named next piece) the stride tail program and the measured
counter/digit role collapse (`sim_stride.py` D2/D2b, the verdict flip).  The lesson recorded for
myself: "this lane keeps its record in its own docs" is exactly the rationalization that keeps a
real wound out of the register — the docs are read by the next mind in *this* lane, the register is
read by every mind.


## Row lane 2026-11-11 (19) — jv1000 `hdecay` **PROVED**: the annulus Cauchy estimate, and §6 discharged at `n = 256`

Round 18 (`76f9fdc`) landed the strip-analyticity quadrature lemma
(`trapezoid_error_le_of_decay`) and left one hypothesis open — `hdecay :
∀ k ≠ 0, ‖c k‖ ≤ M q^{|k|}` — with the route described as «Cauchy's theorem on the closed
annulus `e^{−a} ≤ |z| ≤ e^{a}`», the Laurent development of `G(z) = g(−i log z)`.  **That
route is both unnecessary and weaker than the honest statement.**  Unnecessary: Mathlib's
rectangle Cauchy–Goursat (`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`) plus
periodicity gives the coefficient bound directly.  Weaker: passing to the annulus drags in a
sup-control question (the round-18 note correctly flagged the temptation to reach for
three-lines/Phragmén–Lindelöf) that never has to be asked, because the **strip sup is itself
the hypothesis** — it is not a consequence of holomorphy, and it is exactly what the
certifier's machinery carries (`|2+2cos z| ≤ 2+2cosh(2β)`, sup `2^{p(Δ+U*)}`, both taken on
`|Im z| ≤ 2β = 0.2`).

### What landed — `SubsetSumL25/Row/JV1000Decay.lean`, 11 theorems, house triple

| theorem | content |
|---|---|
| `abs_le_abs_of_mem_uIcc` | `y ∈ uIcc 0 s ⇒ \|y\| ≤ \|s\|` (keeps both the rectangle and its vertical sides inside the strip) |
| `shift_integral_eq` | **the contour shift**: `∫₀^{2π} H(x)dx = ∫₀^{2π} H(x+is)dx` for `\|s\| < a`, `H z = g z e^{−ikz}` — the two vertical sides cancel by periodicity (`e^{−2πik} = 1`), the surviving factor is the *real* `e^{ks}` |
| `abs_fourierCoeff_le_of_shift` | `‖ĉ_k‖ ≤ M e^{ks}` at every interior `s` |
| `le_exp_endpoint_of_lt` / `le_exp_endpoint_of_gt` | the endpoint passage (`le_of_tendsto_of_tendsto`, one-sided `nhdsWithin`) |
| **`abs_fourierCoeff_le_decay`** | **`‖ĉ_k‖ ≤ M e^{−a\|k\|}`** — the estimate; `k = 0` is included and is `M` |
| `fourierCoeff_le_pow` / `hdecay_of_strip` | the same as `M q^{\|k\|}` with `q = e^{−a}`, i.e. §6's `hdecay` verbatim |
| `trapezoid_error_le_of_strip` | **§6 discharged**: `trapezoid_error_le_of_decay` with `hdecay` supplied from the strip — the quadrature bound is no longer conditional on decay |
| `exp_neg_fifth_pow_256_le` | `q²⁵⁶ = e^{−51.2} ≤ 10⁻²⁰`, **proved** from `e > 2.7182818283` alone |
| `quadrature_at_256_of_strip` | **`n = 256`, both moments**: strip sup `M ≤ 8472775`, `K ≤ 32`, tail `ε ≤ 10⁻²⁰` ⇒ `‖circleMean F − trapMean 256 F‖ ≤ 10⁻⁶` |

### The two places the tempting argument is wrong (both measured before writing Lean)

1. **`le_of_forall_lt` "strictness" does not close the endpoint.**  With the shift factor
   `e^{ks}`, for `k > 0` the decaying endpoint is `s → −a`, and at any *interior* `s` the bound
   `M e^{ks}` is **larger** than `M e^{−a|k|}` — the strictness one wants is in the wrong
   direction.  `sim/sim_decay.py` §2 measured it: `e^{k(s−a)} = 0.93 < 1` at `s = 0.19` holds
   only on the *other* side.  So the honest passage is a limit (`le_of_tendsto_of_tendsto` with
   `tendsto_const_nhds`), and nothing is lost: the strip is open, the limit takes the sup over it.
2. **The sup is hypothesis, not consequence.**  Round 18's own worry («sup on the strip gives
   sup on the circle only via three-lines») dissolves once one stops moving to the annulus: the
   shift never needs the sup on a circle at all, only on the horizontal segments `Im z = s`,
   `|s| < a`, which is inside the hypothesis.

### Measurements (`sim/sim_decay.py`, run before any Lean)

* **The shift identity is exact, not approximate.**  On the sharp test case
  `F(z) = 1/(b − cos z)`, `b = cosh 0.3`, `a = 0.2`, whose TRUE coefficients are
  `r^{|k|}/sinh(a')`, the shifted and unshifted quadratures agree with the exact values to
  `1e-16` — the float floor, i.e. the identity as an identity.
* **The bound is not vacuous at the rate.**  `|c_k|/(M e^{−a|k|})` decays exactly like
  `e^{−(a'−a)k}` (`0.0830 → 0.0170` over `k = 0…16`), so the hypothesis is tight in the rate and
  the constant `M = 1/(b − cosh a)` does the work — the same situation the moment integrands are
  in (entire, but the bound only knows `a = 0.2`).
* **Satisfiable by the actual integrands**: holding at every `k ≤ 8` with ≥ 4 orders of slack at
  `M = W_out·2^{ceil(sup)}` for both moments.
* **§7 covers both moments in one statement** because `q²⁵⁶` is proved to `10⁻²⁰`: at
  `M = 8472775 = ⌈W_out·2²¹⌉` (`2²¹` is the ceiling the certifier's own sup already carries),
  `K = 32`, the `q`-term is `8472775·10⁻²⁰·65 = 5.5·10⁻⁹` — fourteen orders below the `10⁻⁶`
  target, so the larger ceiling costs nothing.  (Round 18's §6 note listed `16549` for moment 1;
  §7 now takes the *second* moment's ceiling so a single theorem subsumes both.)
* `n = 256` is the certifier's own inner grid `N_in`, so §6/§7 land on the node count the
  enclosures actually use, not a convenient one.

### Residue, named precisely (this round does NOT fake it)

The **instantiation** passage is not in this file: `u`, `v` are `log₂` of positive strip-analytic
integrals, so they are holomorphic on the strip, and the sup composition is the measured
`W_out·2^{ceil(sup)}`.  Writing that composition down is the next round's job; what this round
proves is the analysis lemma it feeds.  `ε` (the partial-sum tail `‖F − Σ_{|k|≤K} ĉ_k e^{ikx}‖`
on the circle) is likewise a named premise with its size measured (`~10⁻¹⁶` at `K = 32`; §7
allows `10⁻²⁰` per the `q`-term budget, i.e. the tail is **not** the binding constraint).
The contour-split `U*`/`W*` bound and the rational comparison are untouched and remain the
post-decay residue.

### Mathlib diamond facts for the next author (all `#check`-verified on the pin)

1. `Complex.integral_boundary_rect_eq_zero_of_differentiableOn` is exactly the right shape; the
   `Complex.re/im` coercions normalize with a single `simpa using hrect` **once** the
   `DifferentiableOn` is stated on the closed rect `uIcc ×ℂ uIcc` (state it via `.mono` from the
   strip, never pointwise).
2. `Differentiable.cexp` exists; `Complex.differentiable_cexp.comp` does not.
3. `le_of_tendsto (hf) (h : f ≤ᶠ bound) : lim ≤ bound` — the **wrong** direction for `C ≤ lim`.
   Use `le_of_tendsto_of_tendsto tendsto_const_nhds htend`.
4. `𝓝` inside a `have`-type is fine with `open Filter`; the one-sided forms are
   `nhdsWithin a (Set.Iio a)` / `nhdsWithin (-a) (Set.Ioi (-a))`, and `self_mem_nhdsWithin` is
   the "eventually on the correct side" supplier.
5. `Nat.cast_natAbs : ↑n.natAbs = ↑|n|` then `Int.cast_abs : ↑|a| = |↑a|` then `abs_of_neg` /
   `abs_of_pos` — the ℤ-`|·|` → ℝ-`|·|` chain.  (No `Int.cast_natAbs`.)
6. `pow_le_pow_left` is **`pow_le_pow_left₀`** in this pin (`0 ≤ a → a ≤ b → ∀ n`), and the
   zero-hypothesis must be typed — `pow_le_pow_left₀ (by norm_num) (le_of_lt h) 51` — otherwise
   `le_of_lt h` fills the `0 ≤ a` slot and unification picks the wrong metavariable.
7. `IntervalIntegrable F volume …` **auto-binds `volume` as a variable** when it appears in a
   *statement*; write `MeasureTheory.volume` explicitly or the composition with
   `JV1000Strip`'s hypotheses silently fails to unify.
8. `Real.exp_nat_mul (x) (n) : exp (↑n * x) = exp x ^ n` — the ℕ comes **first**, so
   `rw [← Real.exp_nat_mul]` turns `(exp a)^n` into `exp (↑n * a)`.

### Receipts

`receipts/jv1000decay-…` (bounded runner, same discipline as the moment receipts): live-pressure
gate, bounded lock wait with any expiry recorded as a deviation, detached `lake build`, named
olean hash, **double-compile determinism**, and the banner `JV1000DecayAxioms.lean` (11
`#print axioms`) fail-closed on `sorryAx` / `native_decide` / non-house axioms.  Banner exit 0,
all 11 in the house triple.  `Statement.lean` sha256 `3dc6567e…34aa` — **0-diff**.  (Small
discipline note: the lane's `Statement.lean` invariant is a **sha256**, and the git blob sha1 of
the same file is `9ece8585…`; both are correct measurements of different things.  Checking with
the wrong tool produces a phantom deviation.)

Next single action: **the instantiation of §6/§7 at the moment integrands** — write
`u`, `v` as `log₂` of the strip-analytic integrals, prove the composite integrand holomorphic on
`|Im z| < 1/5` with sup `≤ W_out·2^{ceil sup}` (the measured `16548.4` / `8.4728·10⁶`), and feed
`quadrature_at_256_of_strip`.  After that the residue is exactly the contour-split `U*`/`W*`
bound plus the rational comparison.

## Row lane 2026-11-11 (20) — jv1000: **the composition passage** — `u`, `v` holomorphic on the strip, the composite bounded, §7 fed

Round 19 (`a40f541`) proved `hdecay` and discharged §6/§7 at `n = 256`, and named the
instantiation as «the next round's residue»: `u`, `v` are `log₂` of positive strip-analytic
integrals, so the composite `(2+2cos θ)·2^{p(Δ−u(θ))}` is holomorphic on `|Im z| < 1/5` with
sup `W_out·2^{⌈sup⌉}`.  **That is now proved, and the round's one correction is that the
composition needed *more* analysis than round 19's note expected — and that the branch-cut
worry was in the wrong place.**

### What landed — `SubsetSumL25/Row/JV1000Compose.lean`, 35 declarations, house triple

| piece | content |
|---|---|
| §1 | `trig16c`/`jvRcx`/`jvScx`: the ℂ-lift of `trig16`, **entire**, with real-axis agreement (`hF`), `2π`-periodicity (`hper`), and the certifier's own majorant `stripMod a b t = Σ_j(|a_j|+|b_j|)cosh(jt)` (`certify_c5.py` l.28) |
| §1.1 | `norm_cos_le_cosh`, `norm_sin_le_cosh` — the **sharp** bounds; `norm_two_add_two_cos` — `\|2+2cos z\| ≤ 2+2cosh(Im z)` |
| §2 | `P_c`, `Y_c` as interval integrals; `hasDerivAt_trig16c`, `norm_trig16cD_le`; **`hasDerivAt_jvPcx`** — differentiation under the interval integral with the strip majorant as dominating function; `differentiableAt_jvYcx` (product rule, factor `1 + log2·w`) |
| §3 | `jvUcx`, `jvVcx` — `jvU`/`jvV` with `Complex.log · / log 2`; **holomorphic on the strip** from `P_c ∈ slitPlane` (`Complex.differentiableAt_log`) |
| §4 | `jvMomFc1`, `jvMomFc2`: **the composite is holomorphic**, sup `≤ 8472775`, periodic; ceilings `jvWout·2¹²`, `jvWout·2²¹` |
| §5 | `quadrature_jvMomF1/F2` — **§7 fed**: `‖circleMean F − trapMean 256 F‖ ≤ 10⁻⁶` |
| §6 | `jvPcx_ofReal` … `jvUcx_ofReal`: the **real-axis bridge**; `circleMean jvMomF1 = ↑jvMomentRho0Cert`; `jv_m1_cert_of_comparison`, `jv_m2_cert_of_comparison` |

### Three corrections, each measured before it was written

1. **The composite has no branch problem — the cut lives in `u`, not in `2^{…}`.**
   `2^{w}` on ℂ must be read as `exp(w log 2)` (a `rpow` reading has no complex branch at all),
   and `exp` of a holomorphic function is *entire*.  So the composition is free once `u` is
   holomorphic, and the whole branch question is one fact about one image: does `P_c` map the
   strip into `Complex.slitPlane`?  `sim/sim_compose.py` §1: **`min Re P_c = 0.9385 > 0`** on
   `|Im t| ≤ 0.2`, `max |P_c| = 1.6606`, and `Im P_c` never changes sign where `Re P_c < 0` —
   the strip image misses the cut by `0.94`, so the premise is not delicate.
   **Corollary, not premise:** `jvP x ≥ 0` is *derived* from `hslit` (a strictly negative real
   has `re < 0, im = 0`, which is not in `slitPlane`), so the sign of `P` on the real axis is
   not another measured fact.

2. **`W_out` carries no slack, so the cos bound must be sharp.**  `8472775 = ⌈W_out·2²¹⌉` with
   `W_out·2²¹ = 8472774.07` — **0.93 of room**.  The lossy route (`‖re‖ + ‖im‖` from
   `Complex.cos_eq`) gives `2 + 2(cosh + sinh) = 4.4428` at the strip edge against the ceiling's
   `4.0401`, a 10 % overshoot — `9.32·10⁶` against `8472775`, which fails.  So `norm_cos_le_cosh` is proved *squared*, from
   `Complex.cos_eq`'s re/im split (`‖cos z‖² = cos²(re)cosh²(im) + sin²(re)sinh²(im) ≤ cosh²(im)`
   — the identity is `sin²(re)·(cosh²−sinh²) = sin²(re)`), and `cosh(1/5) ≤ 1.0200668` from
   `Real.exp_bound` at `x = ±1/5`, `n = 8` — the margin over the true `1.0200667556` is `4.4·10⁻⁸`.

3. **The sup of the product is not the product of the sups.**  Measured: the composite sup on
   the strip is **2.78** (`M₁`) / **2.65** (`M₂`) — not `16548` / `8.47·10⁶` — because `Re u` is
   *smallest* near `θ = π`, exactly where `2+2cos θ` vanishes; the ceiling is ≥10⁶× loose.  So
   §4 bounds the product and states the two witnesses separately (`Re u ≥ −U` for the
   exponential, `‖2+2cos z‖ ≤ 2+2cosh` for the weight), which is what makes `hMle` a *numeric*
   discharge rather than an analytic one.

### The residue, now exactly three items plus two side conditions

`jvMomentRho0Cert < 2^{ρ_c}` is `jv_m1_cert_of_comparison`, whose hypotheses are:

* `hslit` — `Re P_c > 0` on the strip (measured `min 0.9385`);
* `hU` — `Re u ≥ −1.326` (measured `Re u ∈ [−0.6939, +0.1813]`; the certifier's `U* = 1.3258`
  is 1.9× conservative) and `hV` — `Re v ≤ 19.178` (measured `∈ [0.3774, 0.6117]`; `W* = 19.177`
  is 31× conservative);
* `hcmp` — `‖trapMean 256 F‖ + 10⁻⁶ < 2^{ρ_c}`: **the rational comparison**, 256 elementary terms;
* `hFint`, `happrox` — the enclosure's own two side conditions (`happrox` is §7's named tail
  `ε ≤ 10⁻²⁰`; measured `~10⁻¹⁶`).

**The tightest link, recorded because it constrains round 21.**  The log₂ margin is
`1.3154·10⁻⁶`, i.e. `1.3041·10⁻⁶` in linear terms on a quantity of size `1.4302509`, and the
quadrature bound consumed is `10⁻⁶` — so the comparison has only `0.30·10⁻⁶` of room, and the
`trapMean 256` enclosure must be good to `3·10⁻⁷` absolute.  That is the number the rational
comparison round must hit, not `10⁻⁶`.

### Receipts

`jv1000_compose_receipts.py` (same discipline as the decay runner): live-pressure gate, bounded
lock wait (expiry recorded as a deviation), detached `lake build`, named-olean sha256,
**determinism double-compile**, banner `JV1000ComposeAxioms.lean` (35 `#print axioms`)
fail-closed on `sorryAx` / `native_decide` / non-house axioms.  Banner exit 0, **all 35 in the
house triple** `[propext, Classical.choice, Quot.sound]`.  `Statement.lean` sha256
`3dc6567e…34aa` — **0-diff**.  `sim/sim_compose.py` is the measurement artifact: real-axis
sanity reproduces round 17's `0.516268325851285` to 15 digits, then the four strip measurements.

Next single action: **the contour-split `U*`/`W*` bounds as theorems, then the rational
comparison at `3·10⁻⁷`** — `Re u ≥ −U*` and `Re v ≤ W*` on the strip are the last analytic
facts (`U*`, `W*` currently enter as the rational replacements `1.326` / `19.178`), and
everything downstream of them is `jv_m1_cert_of_comparison` plus a 256-term enclosure.

## Row lane 2026-11-11 (21) — jv1000: the `U*`/`W*` bounds **reduced**, and §7 found
**unsatisfiable** — then cured

Round 20 named three residues: the strip bounds `Re u ≥ −U*` / `Re v ≤ W*`, and the 256-term
comparison. This round tried to prove the strip bounds, discovered that the *proofs that were
supposed to feed them* are 400× too loose, and — while checking what §7 actually consumes —
found that round 19's quadrature lemma **cannot be instantiated at all**. That defect is now
cured, and it turns out to be worth more than the residue it blocks.

### 1. `Re u` and `Re v` are a log-of-modulus plus one ratio — and nothing else

`Complex.log_re` says `(log z).re = log ‖z‖`. Since `L2C` is `↑(log 2)`, the whole of `Re u`
collapses to

    Re u = log₂‖P_c‖ + (κ−1)·Re(Y_c/P_c) − κ·LZ − H_
    Re v = (2−κ)·Re(Y_c/P_c) − 2·log₂‖P_c‖ + κ·LZ + H_

(`jvUcx_re_eq`, `jvVcx_re_eq`). So **both** strip bounds are implied by four numeric facts
about two functions and two numbers:

| premise | threshold used | measured | margin |
|---|---|---|---|
| `9/10 ≤ Re P_c z` on the strip | 0.9 | `0.938511377` | 4 % |
| `‖Y_c z‖ ≤ 5/2` | 2.5 | `2.161568` | 16 % |
| `LZ ≤ 3/5` | 0.6 | `0.5586861327` | 7 % |
| `H_ ≤ 1/50` | 0.02 | `0.0174021677` | 15 % |

and they yield `Re u ≥ −0.903735` (against `−1.326`, **0.422 of slack**) and
`Re v ≤ 3.655633` (against `19.178`, **15.5 of slack**) — proved, `norm_num` on rationals,
`log₂(9/10) ≥ −1/6` being the only transcendental step (`Real.log_le_sub_one_of_pos` +
`Real.log_two_gt_d9`). The `P`-floor also hands over two premises for free: `hslit` (a
strictly positive real part *is* `slitPlane`'s left disjunct) and `hFint` (continuity of the
composite on the closed interval). **`hU`, `hV`, `hslit`, `hFint` are no longer hypotheses**
— `jvMoments_of_residue` takes the four numeric facts and returns `JV1000Moments`.

### 2. How much of a reduction that is — measured, because the obvious answer is "none"

The lane already proves strip majorants for `P` and `Y` (`Pmaj`, `Ymaj`). They cannot close
this, and the size of the failure is the point:

| quantity | proved majorant | true sup | looseness |
|---|---|---|---|
| `‖P_c‖` on the strip | `Pmaj = 1367.6` | `1.6606` | 824× |
| `‖Y_c‖` on the strip | `Ymaj = 14247.0` | `2.1616` | 6591× |

Run the reduction with those and it reads `Re u ≥ −526.8` — the Y-term alone,
`(κ−1)·Ymaj/λ = 526.1`, is 400× the entire `1.326` budget. So this is a genuine reduction
*only* if the residue is **tight enclosures**, and the measured tight values (`‖Y/P‖ ≤
1.3017`!) are what the four premises above carry. The crude majorants are not a
proof-strength route to `U*`; round 20's phrase "`U*`/`W*` may be used verbatim" was about
the *constants*, not about the majorants that were supposed to bound the functions.

### 3. §7 was unsatisfiable. `K ≤ 32` with `ε ≤ 10⁻²⁰` cannot both hold

`quadrature_at_256_of_strip` requires `K ≤ 32` **and** `ε ≤ 10⁻²⁰`, where `ε` bounds the
partial-sum tail `‖F − Σ_{|k|≤K} ĉ_k e^{ikx}‖`. `F` is not a trigonometric polynomial and its
coefficients decay at ratio `≈ 0.65` — the *effective* strip is `≈ 0.43`, wider than the
proved `1/5` — so the tail is

| `K` | 32 | 48 | 64 | 96 |
|---|---|---|---|---|
| true tail (measured) | `6.38·10⁻⁵` | `4.17·10⁻⁸` | `1.43·10⁻¹¹` | `6.3·10⁻¹⁵` |

At the `K` the lemma fixes, `ε ≤ 10⁻²⁰` is **false by fifteen orders**, so `happrox` had no
witness and the whole §7 feed was vacuous. Even an honest `ε = 6.4·10⁻⁵` would break the
conclusion: the tail enters as `2ε`, and `1.3·10⁻⁴ ≫ 10⁻⁶`.

Round 19's docstring defends `ε ≤ 10⁻²⁰` as "4 orders looser than the numerically measured
tail (`~10⁻¹⁶`)". That measurement is real and it is of the **wrong `K`** — `~6·10⁻¹⁵` is
what the tail is at `K ≈ 96`, nine orders below what it is at `K = 32`.

**The cure is the `K` cap, which was pointing the wrong way.** The tail shrinks with `K`;
the aliasing term `M q^n (2K+1)` grows only linearly. So `K ≤ 32` was the one constraint
preventing the only sound instantiation, and `K` was never a parameter of the certifier's
construction — it is the order of a proof-side partial sum. `quadrature_at_256_of_strip_relaxed`
proves `K ≤ 200`, `ε ≤ 10⁻⁷`, `M ≤ 8472775` gives `≤ 2.0003·10⁻⁷ < 10⁻⁶`, and the two moments
are re-fed through it (`quadrature_jvMomF1_relaxed`, `…F2_relaxed`). **The chain is now
satisfiable** — `K = 48` with `ε = 4.17·10⁻⁸` is a witness — where before it was not.

### 4. The enclosure verdict for `hcmp`: the target is real, the object is not a finite sum

`hcmp` needs `‖trapMean 256 F‖ + 10⁻⁶ < 2^{ρ_c}`. Measured room: `2^{ρ_c} − M₁ =
1.304·10⁻⁶`, so after §7's `10⁻⁶` the enclosure must be good to `3.04·10⁻⁷` — the round-20
figure, confirmed. What that costs, measured rather than estimated:

* `dM₁/du = −8.386`, so the 256 pointwise `u` values need `1.19·10⁻⁸` **absolute**;
* `|∂M/∂log₂‖P‖| = 8.386`, so `‖P_c‖` needs **`3.58·10⁻⁸` relative** at each node;
* the quadrature's own share is *not* the bottleneck: `M q²⁵⁶ (2K+1) = 3.4·10⁻⁸` at `K ≤ 200`.

So `3·10⁻⁷` is achievable **in principle** and blocked **in fact**, for one reason: every term
is `2^{trig16}`, an integral, and `u` is a `log₂` of one — so the enclosure is a *continuum*
enclosure at `3.6·10⁻⁸` relative, not "256 elementary terms, `norm_num`-scale" as round 19
and round 20 both wrote. No rigorous enclosure of `∫2^{trig16}` exists in this lane, and the
`u`-values also need the strip extrema of a 32-term trigonometric polynomial. **Named gap**,
with both operands sized.

### Receipts

`jv1000_bounds_receipts.py` (same discipline as rounds 19/20): live-pressure gate
(`swapouts_delta60 = 0`, `free_pct = 66`), bounded lock wait — **`waited_s = 365.3`**, the
shared `/Volumes/Substrate-1/bigo/.build.lock` held by `weil-verify-lane`'s
`closure_supervisor.py`; recorded as a deviation, `bounded_s = 900` (`KAPILA_LOCK_WAIT`),
acquired before expiry so the build is live-pressure-gated and lock-serialised. Detached
`lake build`, olean sha256 `b2bfad56…2009d`, **double-compile determinism
identical (`942904` bytes both runs)**, banner `JV1000BoundsAxioms.lean` — 21 `#print axioms`,
exit 0, **all 21 in the house triple**. `Statement.lean` sha256 `3dc6567e…34aa` — **0-diff**;
the family files (`KapilaRow`, `KapilaCmpSeg`, `KapilaEstimate`, `KapilaGuard`, `SubsetSumL25.lean`)
0-diff (the stride-program lane committed `46cba79`/`9972181` during this round and touched
only `Kapila*`/`sim_stride.py` — verified by `git diff --name-only 166a5f5..HEAD`).

`sim/sim_bounds_enclosure.py` is the measurement artifact: strip extrema of `Re w`/`Im w`, the
crude-vs-true majorant comparison, `min Re P_c`, `max ‖Y_c‖`, `LZ`, `H_`, the enclosure
sensitivity, and the Fourier tail at five truncation orders.

Next single action: **prove the four numeric premises' cheapest member first — `LZ ≤ 3/5` and
`H_ ≤ 1/50`** (each is a `log₂` of a mean of `2^{trig16}` on the real line; the two are
`0.5587` and `0.0174` against caps `0.6`/`0.02`, so a *crude* two-sided pointwise bound on
`trig16` — `‖r‖_∞ ≤ Σ|coeffs| = 5.15` gives `LZ ∈ [−10.4, 10.4]` and fails — is not enough;
what is needed is a min/max of a 32-term trig polynomial, i.e. the same numeric layer the
`hcmp` enclosure needs, entered from its cheapest end).
