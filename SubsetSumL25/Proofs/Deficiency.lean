/-
M4b: PROOF of OpenAI Lemma 2.2 «Properties of deficiency» — increment bounds,
superadditivity, exchange bound.

Paper proof (setup.tex): «Adding i replaces Σ(V) by Σ(V) ∪ (c_i+Σ(V)), whose
cardinality lies between |Σ(V)| and 2|Σ(V)|.  …  For disjoint U,V,
Σ(U∪V)=Σ(U)+Σ(V) has cardinality at most |Σ(U)||Σ(V)|.  Finally, in an exchange
write V=U∪{i} and V'=U∪{j}.  Both deficiencies lie in [d(U),d(U)+1].»

d(∅)=0 and d(V)≥0 were proved in the previous commit.
-/
import Mathlib
import SubsetSumL25.Statements.Deficiency

namespace SubsetSumL25

/-- Monotonicity of division by the fixed positive denominator `log 2`. -/
private theorem logdiv_le_logdiv {x y : ℝ} (hx : 0 < x) (h : x ≤ y) (hy : 0 < y) :
    Real.log x / Real.log 2 ≤ Real.log y / Real.log 2 := by
  rw [div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  have hcancel : Real.log y / Real.log 2 * Real.log 2 = Real.log y :=
    div_mul_cancel₀ _ (Real.log_pos (by norm_num : (1 : ℝ) < 2) |>.ne')
  rw [hcancel]
  exact Real.log_le_log hx h

/-- Division-form: `log x / log 2 ≤ z / log 2` from `x ≤ z`. -/
private theorem logdiv_le_logdiv' {x z : ℝ} (h : Real.log x ≤ z) :
    Real.log x / Real.log 2 ≤ z / Real.log 2 := by
  rw [div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  have hcancel : z / Real.log 2 * Real.log 2 = z :=
    div_mul_cancel₀ _ (Real.log_pos (by norm_num : (1 : ℝ) < 2) |>.ne')
  rw [hcancel]
  exact h

theorem L2_2_deficiency_insert (c : Fin n → ℤ) (V : Finset (Fin n)) (i : Fin n)
    (hi : i ∉ V) :
    0 ≤ deficiency c (insert i V) - deficiency c V ∧
      deficiency c (insert i V) - deficiency c V ≤ 1 := by
  have hsub1 : support c V ⊆ support c (insert i V) :=
    Finset.image_subset_image (Finset.powerset_mono.mpr (Finset.subset_insert _ _))
  have hsub2 : support c (insert i V) ⊆
      support c V ∪ (support c V).image (fun x => c i + x) := by
    intro x hx
    rw [support, Finset.mem_image] at hx
    obtain ⟨A, hAp, hx⟩ := hx
    rw [Finset.mem_powerset] at hAp
    rw [support]
    by_cases hic : i ∈ A
    · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨subsum c (A.erase i), ?_, ?_⟩)
      · rw [Finset.mem_image]
        exact ⟨A.erase i, Finset.mem_powerset.mpr (fun a ha => by
          rcases Finset.mem_insert.mp (hAp (Finset.mem_erase.mp ha).2) with heq | hin
          · exact absurd heq (Finset.mem_erase.mp ha).1
          · exact hin), rfl⟩
      · have hAeq : A = insert i (A.erase i) := (Finset.insert_erase hic).symm
        have hsum : subsum c A = c i + subsum c (A.erase i) := by
          calc subsum c A = ∑ a ∈ A, c a := rfl
            _ = ∑ a ∈ insert i (A.erase i), c a := by nth_rewrite 1 [hAeq]; rfl
            _ = c i + ∑ a ∈ A.erase i, c a := Finset.sum_insert (Finset.notMem_erase i A)
            _ = c i + subsum c (A.erase i) := rfl
        rw [← hx, hsum]
    · refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨A, ?_, hx⟩)
      exact Finset.mem_powerset.mpr (fun a ha => by
        rcases Finset.mem_insert.mp (hAp ha) with heq | hin
        · exact absurd heq (fun hc => hic (by rw [← heq]; exact ha))
        · exact hin)
  have hmem : (0 : ℤ) ∈ support c V := by
    unfold support
    exact Finset.mem_image.mpr ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset V), by simp [subsum]⟩
  have hcard1 : (1 : ℕ) ≤ (support c V).card :=
    Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨0, hmem⟩)
  have hshift : ((support c V).image (fun x => c i + x)).card = (support c V).card :=
    Finset.card_image_of_injOn (fun x _ y _ h => by linarith)
  have hcard : (support c (insert i V)).card
      ≤ (support c V).card + ((support c V).image (fun x => c i + x)).card :=
    le_trans (Finset.card_le_card hsub2) (Finset.card_union_le _ _)
  rw [hshift] at hcard
  have hTv : (insert i V).card = V.card + 1 := Finset.card_insert_of_notMem hi
  have hcardT : (0 : ℕ) < (support c (insert i V)).card :=
    Nat.pos_of_ne_zero (Finset.card_ne_zero.mpr ⟨0, hsub1 hmem⟩)
  have hposS : (0 : ℝ) < ((support c V).card : ℝ) := by exact_mod_cast hcard1
  have hposT : (0 : ℝ) < ((support c (insert i V)).card : ℝ) := by exact_mod_cast hcardT
  have hlogle : Real.log ((support c V).card : ℝ)
      ≤ Real.log ((support c (insert i V)).card : ℝ) :=
    Real.log_le_log hposS (by exact_mod_cast (Finset.card_le_card hsub1))
  have hXle : Real.log ((support c V).card : ℝ) / Real.log 2
      ≤ Real.log ((support c (insert i V)).card : ℝ) / Real.log 2 :=
    logdiv_le_logdiv hposS (by exact_mod_cast (Finset.card_le_card hsub1)) hposT
  have hXge : Real.log ((support c (insert i V)).card : ℝ) / Real.log 2
      ≤ Real.log ((support c V).card : ℝ) / Real.log 2 + 1 := by
    have h4 : Real.log (2 * ((support c V).card : ℝ))
        = Real.log 2 + Real.log ((support c V).card : ℝ) :=
      Real.log_mul (by positivity) (by positivity)
    have h5 : Real.log ((support c (insert i V)).card : ℝ)
        ≤ Real.log (2 * ((support c V).card : ℝ)) :=
      Real.log_le_log hposT (by
        have hR : ((support c (insert i V)).card : ℝ)
            ≤ ((support c V).card : ℝ) + ((support c V).card : ℝ) :=
          by exact_mod_cast hcard
        linarith)
    have h5R : Real.log ((support c (insert i V)).card : ℝ)
        ≤ Real.log ((support c V).card : ℝ) + Real.log 2 := by linarith [h4, h5]
    rw [show Real.log ((support c V).card : ℝ) / Real.log 2 + 1
        = (Real.log ((support c V).card : ℝ) + Real.log 2) / Real.log 2 by
        field_simp]
    exact logdiv_le_logdiv' h5R
  unfold deficiency
  rw [hTv]
  have hcast : (((V.card + 1 : ℕ) : ℝ)) = (V.card : ℝ) + 1 := by norm_cast
  constructor <;> linarith [hcast]

set_option maxHeartbeats 1000000 in
theorem L2_2_deficiency_superadd (c : Fin n → ℤ) {U V : Finset (Fin n)}
    (hUV : Disjoint U V) :
    deficiency c (U ∪ V) ≥ deficiency c U + deficiency c V := by
  have hsub : Finset.image (subsum c) (U ∪ V).powerset ⊆
      (support c U ×ˢ support c V).image (fun p => p.1 + p.2) := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨I, hIp, hx⟩ := hx
    rw [Finset.mem_powerset] at hIp
    refine Finset.mem_image.mpr ⟨(subsum c (I ∩ U), subsum c (I ∩ V)),
      Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · unfold support
      rw [Finset.mem_image]
      exact ⟨I ∩ U, Finset.mem_powerset.mpr (fun a ha => (Finset.mem_inter.mp ha).2),
        rfl⟩
    · unfold support
      rw [Finset.mem_image]
      exact ⟨I ∩ V, Finset.mem_powerset.mpr (fun a ha => (Finset.mem_inter.mp ha).2),
        rfl⟩
    · have hIUV : I = I ∩ U ∪ I ∩ V := by
        ext a
        constructor
        · intro hmem
          rcases Finset.mem_union.mp (hIp hmem) with hU | hV
          · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hmem, hU⟩)
          · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hmem, hV⟩)
        · intro hmem
          rcases Finset.mem_union.mp hmem with h1 | h2
          · exact (Finset.mem_inter.mp h1).1
          · exact (Finset.mem_inter.mp h2).1
      have hdisj : Disjoint (I ∩ U) (I ∩ V) :=
        Finset.disjoint_of_subset_right (fun a ha => (Finset.mem_inter.mp ha).2)
          (Finset.disjoint_of_subset_left (fun a ha => (Finset.mem_inter.mp ha).2) hUV)
      have hkey : subsum c I = subsum c (I ∩ U) + subsum c (I ∩ V) := by
        simp only [subsum]
        nth_rewrite 1 [hIUV]
        rw [Finset.sum_union hdisj]
      rw [← hx, hkey]
  have hmemU : (0 : ℤ) ∈ support c U := by
    unfold support
    exact Finset.mem_image.mpr ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset U),
      by simp [subsum]⟩
  have hmemV : (0 : ℤ) ∈ support c V := by
    unfold support
    exact Finset.mem_image.mpr ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset V),
      by simp [subsum]⟩
  have hmemUV : (0 : ℤ) ∈ support c (U ∪ V) := by
    unfold support
    refine Finset.mem_image.mpr ⟨∅, Finset.mem_powerset.mpr ?_, by simp [subsum]⟩
    exact Finset.empty_subset (U ∪ V)
  have hcard1U : (1 : ℕ) ≤ (support c U).card :=
    Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨0, hmemU⟩)
  have hcard1V : (1 : ℕ) ≤ (support c V).card :=
    Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨0, hmemV⟩)
  have hposUV : (0 : ℝ) < ((support c (U ∪ V)).card : ℝ) :=
    mod_cast Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨0, hmemUV⟩)
  have himg : ((support c U ×ˢ support c V).image (fun p => p.1 + p.2)).card
      ≤ (support c U).card * (support c V).card := by
    calc ((support c U ×ˢ support c V).image (fun p => p.1 + p.2)).card
        ≤ (support c U ×ˢ support c V).card := Finset.card_image_le
      _ = (support c U).card * (support c V).card := Finset.card_product _ _
  have hcardN : (support c (U ∪ V)).card ≤ (support c U).card * (support c V).card :=
    le_trans (Finset.card_le_card hsub) himg
  have hposU : (0 : ℝ) < ((support c U).card : ℝ) := by exact_mod_cast hcard1U
  have hposV : (0 : ℝ) < ((support c V).card : ℝ) := by exact_mod_cast hcard1V
  have hlog : Real.log ((support c (U ∪ V)).card : ℝ)
      ≤ Real.log ((support c U).card : ℝ) + Real.log ((support c V).card : ℝ) := by
    have h4 : Real.log (((support c U).card : ℝ) * ((support c V).card : ℝ))
        = Real.log ((support c U).card : ℝ) + Real.log ((support c V).card : ℝ) :=
      Real.log_mul (by positivity) (by positivity)
    calc Real.log ((support c (U ∪ V)).card : ℝ)
        ≤ Real.log (((support c U).card : ℝ) * ((support c V).card : ℝ)) :=
          Real.log_le_log hposUV (by exact_mod_cast hcardN)
      _ = Real.log ((support c U).card : ℝ) + Real.log ((support c V).card : ℝ) := h4
  have hdiv : Real.log ((support c (U ∪ V)).card : ℝ) / Real.log 2
      ≤ Real.log ((support c U).card : ℝ) / Real.log 2
        + Real.log ((support c V).card : ℝ) / Real.log 2 := by
    rw [div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2)), add_mul,
      div_mul_cancel₀ _ (Real.log_pos (by norm_num : (1 : ℝ) < 2) |>.ne'),
      div_mul_cancel₀ _ (Real.log_pos (by norm_num : (1 : ℝ) < 2) |>.ne')]
    exact hlog
  have hcardUV2 : ((U ∪ V).card : ℝ) = (U.card : ℝ) + (V.card : ℝ) := by
    rw [Finset.card_union_of_disjoint hUV, Nat.cast_add]
  unfold deficiency
  linarith [hdiv, hcardUV2]

theorem L2_2_deficiency_exchange (c : Fin n → ℤ) (U : Finset (Fin n)) (i j : Fin n)
    (hi : i ∉ U) (hj : j ∉ U) (hij : i ≠ j) :
    |deficiency c (insert i U) - deficiency c (insert j U)| ≤ 1 := by
  obtain ⟨h1a, h1b⟩ := L2_2_deficiency_insert c U i hi
  obtain ⟨h2a, h2b⟩ := L2_2_deficiency_insert c U j hj
  rw [abs_le]
  constructor <;> linarith

end SubsetSumL25
