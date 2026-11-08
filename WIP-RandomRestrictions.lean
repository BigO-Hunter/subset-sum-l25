/-
M4c+M4d: OpenAI Lemma 2.3 «Random restrictions».

Monotone step (proved): the double-counting over pairs (W, i), W a (q+1)-subset
and i ∈ W:
  Σ_W Σ_{i∈W} d(W) = Σ_W Σ_{i∈W} d(insert i (W∖{i}))
                   ≥ Σ_W Σ_{i∈W} d(W∖{i})              [insert monotonicity]
                   = Σ_V Σ_{i∉V} d(V)                  [bijection (W,i) ↦ (W∖{i}, i)]
                   = (n−q)·Σ_V d(V),
  while Σ_W Σ_{i∈W} d(W) = (q+1)·Σ_W d(W)  [d(W) constant over i ∈ W, |W| = q+1],
and the binom identity (q+1)·C(n,q+1) = (n−q)·C(n,q) (`Nat.choose_succ_right_eq`)
converts (q+1)·Σ_{q+1} ≥ (n−q)·Σ_q into 𝔼_{q+1} ≥ 𝔼_q.

The variance bound (paper's martingale argument) is the remaining M4 work
(`L2_3_halfVariance`, still `sorry`).
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
  have hQS1 : ∀ W ∈ uniformQSubsets n (q + 1), W.card = q + 1 := fun W hW =>
    (Finset.mem_filter.mp hW).2
  have hQS2 : ∀ V ∈ uniformQSubsets n q, V.card = q := fun V hV =>
    (Finset.mem_filter.mp hV).2
  -- insert monotonicity, pointwise over pairs (W, i ∈ W)
  have hmono : ∀ W ∈ uniformQSubsets n (q + 1), ∀ i ∈ W,
      deficiency c (insert i (W.erase i)) ≥ deficiency c (W.erase i) := by
    intro W hW i hi
    have hin : i ∉ W.erase i := Finset.notMem_erase i W
    have hmono := (L2_2_deficiency_insert c (W.erase i) i hin).1
    rw [Finset.insert_erase hi] at hmono
    linarith
  -- the pair-sum bijection (W, i) ↦ (W ∖ {i}, i)
  have h4 : ∑ W ∈ uniformQSubsets n (q + 1), ∑ i ∈ W, deficiency c (W.erase i)
      = ∑ V ∈ uniformQSubsets n q, ∑ i ∈ Finset.univ \ V, deficiency c V := by
    rw [Finset.sum_congr rfl fun W hW => sum_eq_sum_ite_univ W (fun i => deficiency c (W.erase i)),
      ← Finset.sum_product, ← Finset.sum_filter,
      Finset.sum_congr rfl fun V hV => sum_eq_sum_ite_univ V (fun i => deficiency c V),
      ← Finset.sum_product, ← Finset.sum_filter]
    refine Finset.sum_bij (fun p _ => (p.1.erase p.2, p.2)) ?_ ?_ ?_ ?_
    · rintro ⟨W, i⟩ hpair
      have hmem : W ∈ uniformQSubsets n (q + 1) ∧ i ∈ W := by simpa using hpair
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, Finset.mem_univ i⟩,
        Finset.notMem_erase i W⟩
      rw [hQS1 W hmem.1, Finset.card_erase_of_mem hmem.2]
    · rintro ⟨W₁, i₁⟩ hpair ⟨W₂, i₂⟩ _ heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨hE, hi⟩ := heq
      subst hi
      have hin : i₁ ∈ W₁ := by
        have hmem : W₁ ∈ uniformQSubsets n (q + 1) ∧ i₁ ∈ W₁ := by simpa using hpair
        exact hmem.2
      rw [← Finset.insert_erase hin, hE, Finset.insert_erase] at hpair
      exact hpair.1
    · rintro ⟨V, j⟩ hpair
      have hjV : j ∉ V := by simpa using hpair
      refine ⟨insert j V, j, ⟨?_, Finset.mem_univ j⟩, ?_, rfl⟩
      · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
        rw [Finset.card_insert_of_notMem hjV, hQS2 V (Finset.mem_filter.mp hpair).1.1]
      · rw [Finset.insert_erase hjV]
    · intro p _
      rfl
  -- the double-sum chain
  have hchain : ∑ W ∈ uniformQSubsets n (q + 1), ∑ i ∈ W, deficiency c W
      ≥ ∑ V ∈ uniformQSubsets n q, ∑ i ∈ Finset.univ \ V, deficiency c V := by
    calc ∑ W ∈ uniformQSubsets n (q + 1), ∑ i ∈ W, deficiency c W
        = ∑ W ∈ uniformQSubsets n (q + 1), ∑ i ∈ W,
            deficiency c (insert i (W.erase i)) := by
          refine Finset.sum_congr rfl fun W hW => ?_
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [Finset.insert_erase hi]
      _ ≥ ∑ W ∈ uniformQSubsets n (q + 1), ∑ i ∈ W, deficiency c (W.erase i) :=
          Finset.sum_le_sum (hmono)
      _ = ∑ V ∈ uniformQSubsets n q, ∑ i ∈ Finset.univ \ V, deficiency c V := h4
  -- constant-in-i evaluations of the two double sums
  have h1 : ∑ W ∈ uniformQSubsets n (q + 1), ∑ i ∈ W, deficiency c W
      = ((q + 1 : ℕ) : ℝ) * ∑ W ∈ uniformQSubsets n (q + 1), deficiency c W := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun W hW => by
      rw [Finset.sum_const, hQS1 W hW]
      simp
  have h5 : ∑ V ∈ uniformQSubsets n q, ∑ i ∈ Finset.univ \ V, deficiency c V
      = ((n - q : ℕ) : ℝ) * ∑ V ∈ uniformQSubsets n q, deficiency c V := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun V hV => by
      rw [Finset.sum_const]
      have hVq := hQS2 V hV
      rw [Finset.card_sdiff (Finset.subset_univ V), hVq, Nat.cast_sub (Nat.le_of_lt hq)]
      simp
  rw [← h1, ← h5] at hchain
  -- the binom identity turns the coefficient ratio into the cardinality ratio
  have hcardQ1 : (0 : ℝ) < ((uniformQSubsets n (q + 1)).card : ℝ) := by
    rw [card_uniformQSubsets]
    exact_mod_cast Nat.choose_pos (le_of_lt hq)
  have hcardQ0 : (0 : ℝ) < ((uniformQSubsets n q).card : ℝ) := by
    rw [card_uniformQSubsets]
    exact_mod_cast Nat.choose_pos (le_of_lt hq)
  have hco : (((q + 1 : ℕ) : ℝ)) * (((uniformQSubsets n (q + 1)).card : ℕ) : ℝ)
      = (((n - q : ℕ) : ℝ)) * (((uniformQSubsets n q).card : ℕ) : ℝ) := by
    rw [card_uniformQSubsets, card_uniformQSubsets, Nat.cast_mul, Nat.cast_mul,
      Nat.cast_mul, Nat.cast_mul,
      mul_comm ((q + 1 : ℕ) : ℝ) ((Nat.choose n (q + 1) : ℕ) : ℝ),
      mul_comm ((n - q : ℕ) : ℝ) ((Nat.choose n q : ℕ) : ℝ)]
    exact_mod_cast Nat.choose_succ_right_eq n q
  rw [div_le_div_iff₀ hcardQ1 hcardQ0]
  -- goal: Σ_{q+1} * card_q ≥ Σ_q * card_{q+1}
  have hpos1 : (0 : ℝ) < ((q + 1 : ℕ) : ℝ) := by positivity
  have hnm : (1 : ℝ) ≤ ((n - q : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
  have hstep : ((n - q : ℕ) : ℝ) * ∑ V ∈ uniformQSubsets n q, deficiency c V
      / ((q + 1 : ℕ) : ℝ) ≤ ∑ W ∈ uniformQSubsets n (q + 1), deficiency c W :=
    div_le_iff₀ hpos1 |>.mpr (by linarith [hchain, hnm])
  rw [hco] at hstep
  rw [mul_comm, div_le_iff₀ hcardQ0] at hstep
  linarith

end SubsetSumL25
