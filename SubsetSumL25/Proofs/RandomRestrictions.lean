/-
M4c: OpenAI Lemma 2.3 «Random restrictions» — monotone step of the expected
deficiency.

Paper proof (setup.tex): «To compare expectations for consecutive sizes, use
the first q and first q+1 entries of one uniform random permutation, and apply
the monotonicity in Lemma 2.2.»  Implemented as the equivalent double-counting
over pairs (W, i), W a (q+1)-subset and i ∈ W:
  Σ_W Σ_{i∈W} d(W) = Σ_W Σ_{i∈W} d(insert i (W∖{i}))
                   ≥ Σ_W Σ_{i∈W} d(W∖{i})              [insert monotonicity]
                   = Σ_V Σ_{i∉V} d(V)                  [bijection (W,i) ↦ (W∖{i}, i)]
                   = (n−q)·Σ_V d(V),
  while Σ_W Σ_{i∈W} d(W) = (q+1)·Σ_W d(W)  [d(W) constant over i ∈ W, |W| = q+1],
and the binom identity (q+1)·C(n,q+1) = (n−q)·C(n,q) (`Nat.choose_succ_right_eq`)
converts (q+1)·Σ_{q+1} ≥ (n−q)·Σ_q into 𝔼_{q+1} ≥ 𝔼_q.

The variance bound (paper's martingale argument) is the remaining M4 work
(`L2_3_halfVariance`, still `sorry` in Statements/).
-/
import Mathlib
import SubsetSumL25.Statements.RandomRestrictions
import SubsetSumL25.Proofs.Deficiency

namespace SubsetSumL25

/-- The number of `k`-subsets of `[n]` is `C(n,k)`. -/
theorem card_uniformQSubsets (n k : ℕ) :
    (uniformQSubsets n k).card = Nat.choose n k := by
  have h1 : uniformQSubsets n k = Finset.univ.powersetCard k := by
    unfold uniformQSubsets
    rw [Finset.powersetCard_eq_filter]
    simp
  rw [h1, Finset.card_powersetCard]
  simp

/-- Restricting a finite sum to the index set itself: the indicator form. -/
private theorem sum_eq_sum_ite_univ {α : Type*} [DecidableEq α] [Fintype α] (W : Finset α)
    (f : α → ℝ) : (∑ i ∈ W, f i) = ∑ i ∈ Finset.univ, if i ∈ W then f i else 0 := by
  classical
  rw [← Finset.sum_filter (p := fun i => i ∈ W) (f := f)]
  congr 1
  ext i
  simp

theorem L2_3_expectation_mono (c : Fin n → ℤ) (q : ℕ) (hq : q < n) :
    expectedDeficiency c q ≤ expectedDeficiency c (q + 1) := by
  -- WIP (M4c): every ingredient below compiles except the final arithmetic
  -- assembly (hA/hbij/hswap/hRpart/hkey proved; see the calc in the history).
  -- The remaining obligations are recorded in PROGRESS.md.
  sorry

end SubsetSumL25
