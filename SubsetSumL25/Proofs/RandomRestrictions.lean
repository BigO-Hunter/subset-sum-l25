/-
M4c: OpenAI Lemma 2.3 — monotone step. STATUS: clean build with sorry for
sum_erase_bij and the assembly. The proved helpers compile.
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

/-- The pair-sum bijection, via `Finset.sum_comm'`. -/
private theorem sum_erase_bij (c : Fin n → ℤ) (q : ℕ) :
    ∑ W ∈ uniformQSubsets n (q + 1), ∑ i ∈ W, deficiency c (W.erase i)
      = ∑ V ∈ uniformQSubsets n q, ∑ i ∈ Finset.univ \ V, deficiency c V := by
  sorry

theorem L2_3_expectation_mono (c : Fin n → ℤ) (q : ℕ) (hq : q < n) :
    expectedDeficiency c q ≤ expectedDeficiency c (q + 1) := by
  sorry

end SubsetSumL25
