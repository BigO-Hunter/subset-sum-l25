/-
M4c: OpenAI Lemma 2.3 «Random restrictions» — monotone step of the expected
deficiency. STATUS: hbij (the key per-i bijection) PROVED as a module-level
lemma; the assembly calc drafted but with ~5 mechanical rewrite errors left
(the div_le_iff₀/hco-ratio plumbing). RESUMED next session.

Paper proof (setup.tex): «To compare expectations for consecutive sizes, use
the first q and first q+1 entries of one uniform random permutation, and apply
the monotonicity in Lemma 2.2.»  Implemented as the equivalent double-counting
over pairs (W, i), W a (q+1)-subset and i ∈ W:
  (q+1)·Σ_{q+1} dW = Σ_W Σ_{i∈W} dW
                   ≥ Σ_W Σ_{i∈W} d(insert i (W∖{i}))
                   ≥ Σ_W Σ_{i∈W} d(W∖{i})              [insert monotonicity]
                   = Σ_i Σ_{W∋i} d(W∖{i})
                   = Σ_i Σ_{V∌i} d(insert i V)
                   ≥ Σ_i Σ_{V∌i} dV                    [insert monotonicity]
                   = Σ_V Σ_{i∉V} dV                    [re-partitioned]
                   = (n−q)·Σ_V d(V),
and the binom identity (q+1)·C(n,q+1) = (n−q)·C(n,q) (`Nat.choose_succ_right_eq`)
converts (q+1)·Σ_{q+1} ≥ (n−q)·Σ_q into 𝔼_{q+1} ≥ 𝔼_q.
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

/-- (B): per-fixed-i bijection: (W ∋ i, |W| = q+1) ↔ (V ∌ i, |V| = q), W ↦ W ∖ {i}.
The mem_filter And-extraction via obtain+mp (the .left-projection chains break
on the Quot/List-Mem display of the filter-membership — the key fork-gotcha). -/
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

theorem L2_3_expectation_mono (c : Fin n → ℤ) (q : ℕ) (hq : q < n) :
    expectedDeficiency c q ≤ expectedDeficiency c (q + 1) := by
  -- WIP (M4c assembly, ~30 lines remaining):
  -- Step 1: (q+1)·Σ_{q+1} dW ≥ ∑_W ∑_{i∈W} d(W.erase i)   [erase_sum_le, needs restoration]
  -- Step 2: ≥ ∑_i ∑_{W∋i} d(W∖{i})                        [Finset.sum_comm']
  -- Step 3: = ∑_i ∑_{V∌i} d(insert i V)                    [hbij]
  -- Step 4: ≥ ∑_i ∑_{V∌i} dV                              [insert mono, sum_le_sum]
  -- Step 5: = ∑_V ∑_{i∉V} dV                              [Finset.sum_comm', the reverse]
  -- Step 6: = (n−q)·Σ_q dV                                [per-V compl+card_compl+sum_const]
  -- Step 7: (q+1)·C(n,q+1) = (n−q)·C(n,q) → ratio → div_le  [hco + Nat.choose_succ_right_eq]
  -- ALL INGREDIENTS PROVED; the calc plumbing had ~5 rewrite errors.
  -- The erased draft with the full calc is in the git history at 8049cef.
  sorry

end SubsetSumL25
