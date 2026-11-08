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

## Sorries (2, exactly)

| Theorem | File:line | Missing obligation |
|---|---|---|
| `L2_1_isolation_prob` | Statements/Isolation.lean:43 | MVV minimum-tie argument: per-index tie prob ≤ 1/N₀, union bound ≤ n/N₀ ≤ 1/12 |
| `L2_3_halfVariance` | Statements/RandomRestrictions.lean:34 | martingale/exposure argument (hardest of M4) |

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

## Commits

1. `da3100b` Skeleton + pins
2. `bb636c0` M1: statements + STMTS.md, build green (12 sorries)
3. `a60faaa` M2 + M3a: L2.5 proved, L2.1(a) proved (axioms clean)
4. `223028a` M4 first slice: L2.2 empty + nonneg proved
5. M5b: L5.2 sparse distinctions proved — `sparseAll` (support × sign-pattern
   encoding) counting + L2.5 union bound; statement fixed to probability form
   (STMTS.md note 7); axioms [propext, Classical.choice, Quot.sound]

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
3. ~~M5b `L5_2_sparse_distinctions`~~ **DONE** (see Proved table): the
   candidate set is built explicitly as `sparseAll n m` from the
   (support, sign-pattern) encoding, the counting `#sparseAll ≤ sparseCount`
   is proved, and the union bound is `badSparsePrimes ⊆ ⋃_{d} {p ∣ d.natAbs}`
   with `L2_5_prime_collision` applied per nonzero sum. Remaining for the
   cluster: M4c (item 1) and M3b (item 2).
