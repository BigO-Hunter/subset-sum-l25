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
