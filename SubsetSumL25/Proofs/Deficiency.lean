/-
M4 (first slice): PROOF of OpenAI Lemma 2.2 «Properties of deficiency» —
the two foundational clauses d(∅) = 0 and d(V) ≥ 0.

Paper proof (setup.tex): «There are at most 2^{|V|} subset sums, and the empty
sum always belongs to the support.»

Remaining M4 work (still `sorry` in Statements/Deficiency.lean): the increment
bounds (insert), superadditivity, and the exchange bound — these need the
Σ(V∪{i}) = Σ(V) ∪ (cᵢ+Σ(V)) decomposition.
-/
import Mathlib
import SubsetSumL25.Statements.Deficiency

namespace SubsetSumL25

theorem L2_2_deficiency_empty (c : Fin n → ℤ) :
    deficiency c ∅ = 0 := by
  unfold deficiency
  have hs : support c ∅ = {0} := by
    unfold support
    simp [subsum]
  rw [hs]
  simp

theorem L2_2_deficiency_nonneg (c : Fin n → ℤ) (V : Finset (Fin n)) :
    0 ≤ deficiency c V := by
  unfold deficiency
  have hmem : (0 : ℤ) ∈ support c V := by
    unfold support
    refine Finset.mem_image.mpr ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset V), by simp [subsum]⟩
  have hcard1 : (1 : ℕ) ≤ (support c V).card :=
    Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨0, hmem⟩)
  have hcardpos : (0 : ℝ) < ((support c V).card : ℝ) := by exact_mod_cast hcard1
  have h1 : ((support c V).card : ℝ) ≤ (2 : ℝ) ^ V.card := by
    have hle : (support c V).card ≤ 2 ^ V.card := by
      calc (support c V).card ≤ V.powerset.card := Finset.card_image_le
        _ = 2 ^ V.card := Finset.card_powerset V
    exact_mod_cast hle
  have h2 : (1 : ℝ) ≤ ((support c V).card : ℝ) := by exact_mod_cast hcard1
  have hmono : Real.log ((support c V).card : ℝ) ≤ (V.card : ℝ) * Real.log 2 := by
    calc Real.log ((support c V).card : ℝ)
        ≤ Real.log ((2 : ℝ) ^ V.card) := Real.log_le_log hcardpos h1
      _ = (V.card : ℝ) * Real.log 2 := Real.log_pow 2 V.card
  have hdiv : Real.log ((support c V).card : ℝ) / Real.log 2 ≤ (V.card : ℝ) := by
    rw [div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
    exact hmono
  linarith

end SubsetSumL25
