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
| `L2_3_halfVariance` | Proofs/RandomRestrictions.lean | Var d(V_q) ≤ q — one-step conditional-mean recursion, no measure theory |
| `martingale_var` / `var_step` / `total_variance_finset` / `stepMean*` / `sum_erase_pair` | Proofs/RandomRestrictions.lean | private support lemmas of the above |

## Sorries (2, exactly) — after M4d (2026-11-08)

| Theorem | File:line | Missing obligation |
|---|---|---|
| `L2_1_isolation_prob` | Statements/Isolation.lean:43 | MVV minimum-tie argument: per-index tie prob ≤ 1/N₀, union bound ≤ n/N₀ ≤ 1/12 |
| `L5_2_sparse_distinctions` | Statements/SparseDistinctions.lean:47 | union bound of L2.5 over sparseCount n m vectors + count bound |

M4d (L2_3_halfVariance) is COMPLETE: proof in Proofs/RandomRestrictions.lean,
statement of record = the proved declaration there (the sorry placeholder was
removed from Statements/, same convention as L2_3_expectation_mono).

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

## Next actions (in order) — after M4d (2026-11-08)

1. **M3b** `L2_1_isolation_prob`: min-tie argument. Slice the space
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
