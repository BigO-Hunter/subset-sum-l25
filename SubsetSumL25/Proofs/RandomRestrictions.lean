/-
M4c: OpenAI Lemma 2.3 — monotone step. STATUS: clean build; card_uniformQSubsets
and sum_eq_sum_ite_univ PROVED; sum_erase_bij and L2_3_expectation_mono have
`sorry` (the remaining work). The sum_erase_bij is the pair-bijection lemma —
the `rw [Finset.sdiff_eq_filter]` fails inside the file context (works in
standalone tests); use `Finset.sum_comm'` directly on the univ∖V inner.
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

/-- (A): the erase-sum is bounded by (q+1)·Σ_{q+1} d. Pointwise per-(i ∈ W):
d(W.erase i) ≤ d W (insert monotonicity), then sum_const with W.card = q+1. -/
theorem erase_sum_le (c : Fin n → ℤ) (q : ℕ) :
    ∑ W ∈ uniformQSubsets n (q + 1), ∑ i ∈ W, deficiency c (W.erase i)
      ≤ ((q + 1 : ℕ) : ℝ) * ∑ W ∈ uniformQSubsets n (q + 1), deficiency c W := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun W hW => ?_
  have hWq : W.card = q + 1 := (Finset.mem_filter.mp hW).2
  calc ∑ i ∈ W, deficiency c (W.erase i)
      ≤ ∑ i ∈ W, deficiency c W :=
      Finset.sum_le_sum fun i hi => by
        have hm := (L2_2_deficiency_insert c (W.erase i) i (Finset.notMem_erase i W)).1
        rw [Finset.insert_erase hi] at hm
        linarith
    _ = ((W.card : ℕ) : ℝ) * deficiency c W := by rw [Finset.sum_const]; simp
    _ = ((q + 1 : ℕ) : ℝ) * deficiency c W := by rw [hWq]

/-- (B): per-fixed-i bijection: (W ∋ i, |W| = q+1) ↔ (V ∌ i, |V| = q), W ↦ W ∖ {i}.
The mem_filter And-extraction via `obtain` + `mem_filter.mp` (the `.left`/
`.right` projection chains break on the Quot/List-Mem display). -/
theorem hbij (c : Fin n → ℤ) (q : ℕ) : ∀ i : Fin n,
    ∑ W ∈ (uniformQSubsets n (q + 1)).filter (fun W => i ∈ W), deficiency c (W.erase i)
      = ∑ V ∈ (uniformQSubsets n q).filter (fun V => i ∉ V), deficiency c V := by
  intro i
  refine Finset.sum_bij (fun W _ => W.erase i) ?_ ?_ ?_ ?_
  · intro W hW
    obtain ⟨hW1, hin⟩ : W ∈ uniformQSubsets n (q + 1) ∧ i ∈ W := by simpa using hW
    obtain ⟨_, hWq⟩ : W ∈ Finset.univ ∧ W.card = q + 1 :=
      Finset.mem_filter.mp hW1
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [Finset.card_erase_of_mem hin, hWq]; omega⟩,
       Finset.notMem_erase i W⟩
  · intro W₁ hW₁ W₂ hW₂ heq
    have hin : i ∈ W₁ := (Finset.mem_filter.mp hW₁).2
    have hin2 : i ∈ W₂ := (Finset.mem_filter.mp hW₂).2
    have h5 : insert i (W₁.erase i) = insert i (W₂.erase i) := by rw [heq]
    rwa [Finset.insert_erase hin, Finset.insert_erase hin2] at h5
  · intro V hV
    obtain ⟨hV1, hjV⟩ := Finset.mem_filter.mp hV
    obtain ⟨_, hVq⟩ := Finset.mem_filter.mp hV1
    refine ⟨insert i V, ?_, ?_⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          by rw [Finset.card_insert_of_notMem hjV, hVq]⟩,
         Finset.mem_insert_self i V⟩
    · exact Finset.erase_insert hjV
  · intro W _
    rfl

/-- (C): the pair-sum bijection, via `Finset.sum_comm'` on the `univ ∖ V` inner
(the `rw [Finset.sdiff_eq_filter]` fails inside the file context; works in
standalone — see /tmp/test_sdiff.lean for the standalone version). -/
private theorem sum_erase_bij (c : Fin n → ℤ) (q : ℕ) :
    ∑ W ∈ uniformQSubsets n (q + 1), ∑ i ∈ W, deficiency c (W.erase i)
      = ∑ V ∈ uniformQSubsets n q, ∑ i ∈ Finset.univ \ V, deficiency c V := by
  sorry

/-- (D): monotone step of the expected deficiency. Uses erase_sum_le (A),
hbij (B), sum_erase_bij (C), the per-V compl-card, and the binom identity
(Nat.choose_succ_right_eq). -/
theorem L2_3_expectation_mono (c : Fin n → ℤ) (q : ℕ) (hq : q < n) :
    expectedDeficiency c q ≤ expectedDeficiency c (q + 1) := by
  sorry

end SubsetSumL25
