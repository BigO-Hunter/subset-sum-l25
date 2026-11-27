/-
M2+M3 (B4): the region-partition proofs (Bills' trio, re-derived for Base's
predicate) and Lemma B2's domination chain (row-guard → display → region
dispatch).  Primary-source quotes: `Statements/ThmB.lean`.
-/
import Mathlib
import SubsetSumL25.Statements.ThmB

namespace SubsetSumL25

/-- `bandUpper` is strictly increasing across the nine finite bands
(§6.1: 1 < 1.25 < 1.6 < 2 < 2.6 < 3.5 < 5 < 8 < 15). -/
theorem bandUpper_step (i : ℕ) (hi : i < 8) : bandUpper i < bandUpper (i + 1) := by
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _
  · norm_num [bandUpper]
  · norm_num [bandUpper]
  · norm_num [bandUpper]
  · norm_num [bandUpper]
  · norm_num [bandUpper]
  · norm_num [bandUpper]
  · norm_num [bandUpper]
  · norm_num [bandUpper]
  · exact absurd hi (by omega)
  · exact absurd hi (by omega)

theorem bandUpper_mono (i j : ℕ) (hij : i ≤ j) (hj : j ≤ 8) :
    bandUpper i ≤ bandUpper j := by
  have key : ∀ (d : ℕ) (i : ℕ), i + d ≤ j → bandUpper i ≤ bandUpper (i + d) := by
    intro d
    induction d with
    | zero => intro i _; simp
    | succ d ih =>
      intro i hd
      have h1 : i + d ≤ j := by omega
      have h2 : i + d < 8 := by omega
      calc bandUpper i ≤ bandUpper (i + d) := ih i h1
        _ ≤ bandUpper (i + (d + 1)) := le_of_lt (bandUpper_step (i + d) h2)
  have hkey := key (j - i) i (by omega)
  rw [show j = i + (j - i) from by omega]
  exact hkey

/-- Region existence: the `by_cases` ladder of §6.1 (Bills' `region_existence`
pattern, re-derived for Base's predicate). -/
theorem region_existence (hΓ : 0 < Γ) (W : ℝ) : ∃ i, i ≤ 9 ∧ inRegion Γ W i := by
  by_cases h0 : W ≤ Γ
  · exact ⟨0, by omega, h0⟩
  by_cases h1 : W ≤ Γ * bandUpper 1
  · refine ⟨1, by omega, ⟨?_, Or.inr h1⟩⟩
    simp only [bandUpper] at h0 ⊢
    linarith
  by_cases h2 : W ≤ Γ * bandUpper 2
  · refine ⟨2, by omega, ⟨?_, Or.inr h2⟩⟩
    simp only [bandUpper] at h1 ⊢
    linarith
  by_cases h3 : W ≤ Γ * bandUpper 3
  · refine ⟨3, by omega, ⟨?_, Or.inr h3⟩⟩
    simp only [bandUpper] at h2 ⊢
    linarith
  by_cases h4 : W ≤ Γ * bandUpper 4
  · refine ⟨4, by omega, ⟨?_, Or.inr h4⟩⟩
    simp only [bandUpper] at h3 ⊢
    linarith
  by_cases h5 : W ≤ Γ * bandUpper 5
  · refine ⟨5, by omega, ⟨?_, Or.inr h5⟩⟩
    simp only [bandUpper] at h4 ⊢
    linarith
  by_cases h6 : W ≤ Γ * bandUpper 6
  · refine ⟨6, by omega, ⟨?_, Or.inr h6⟩⟩
    simp only [bandUpper] at h5 ⊢
    linarith
  by_cases h7 : W ≤ Γ * bandUpper 7
  · refine ⟨7, by omega, ⟨?_, Or.inr h7⟩⟩
    simp only [bandUpper] at h6 ⊢
    linarith
  by_cases h8 : W ≤ Γ * bandUpper 8
  · refine ⟨8, by omega, ⟨?_, Or.inr h8⟩⟩
    simp only [bandUpper] at h7 ⊢
    linarith
  refine ⟨9, by omega, ⟨?_, Or.inl rfl⟩⟩
  simp only [bandUpper] at h8 ⊢
  linarith

/-- Upper bound: a region `i ≤ 8` puts `W ≤ Γ·bandUpper i` (region 9 has none —
`bandUpper 9 = 0` is junk). -/
theorem region_upper {Γ W : ℝ} {i : ℕ} (hi : i ≤ 8) (hI : inRegion Γ W i) :
    W ≤ Γ * bandUpper i := by
  cases i with
  | zero =>
    have h := hI
    simpa [inRegion, bandUpper] using h
  | succ k =>
    obtain ⟨-, h2⟩ := hI
    have hk : k + 1 ≠ 9 := by omega
    rcases h2 with h | h
    · omega
    · exact h

theorem region_lower {Γ W : ℝ} {i : ℕ} (hi : 1 ≤ i) (hI : inRegion Γ W i) :
    Γ * bandUpper (i - 1) < W := by
  cases i with
  | zero => omega
  | succ k => exact hI.1

/-- Region disjointness (Bills' `region_disjoint`, re-derived): the bands are
ordered and `Γ > 0` scales the order. -/
theorem region_disjoint (hΓ : 0 < Γ) (W : ℝ) (i j : ℕ) (hi : i ≤ 9) (hj : j ≤ 9)
    (hI : inRegion Γ W i) (hJ : inRegion Γ W j) : i = j := by
  rcases lt_trichotomy i j with hlt | heq | hgt
  · have hj1 : 1 ≤ j := by omega
    have hlow := region_lower hj1 hJ
    have hiU : W ≤ Γ * bandUpper i := region_upper (by omega) hI
    have hmono : Γ * bandUpper i ≤ Γ * bandUpper (j - 1) := by
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hΓ)
      exact bandUpper_mono i (j - 1) (by omega) (by have := hj; omega)
    linarith
  · exact heq
  · have hi1 : 1 ≤ i := by omega
    have hlow := region_lower hi1 hI
    have hjU : W ≤ Γ * bandUpper j := region_upper (by omega) hJ
    have hmono : Γ * bandUpper j ≤ Γ * bandUpper (i - 1) := by
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hΓ)
      exact bandUpper_mono j (i - 1) (by omega) (by have := hi; omega)
    linarith

/-- The regions are unique (Bills' `full_region_partition`). -/
theorem region_unique (hΓ : 0 < Γ) (W : ℝ) :
    ∃! i, i ≤ 9 ∧ inRegion Γ W i := by
  obtain ⟨i, hi, hI⟩ := region_existence hΓ W
  exact ExistsUnique.intro i ⟨hi, hI⟩
    (fun y (hy : y ≤ 9 ∧ inRegion Γ W y) =>
      (region_disjoint hΓ W i y hi hy.1 hI hy.2).symm)


/-- The referee-extracted per-row guard (rung B4): `a_Γ ≤ 3/4` makes the
fourth row's error `(4a_Γ+3)ε` at most `6ε`, so **all six** rows of the
certificate vector have error at most `6ε` (§6.3: «the rows have errors at most
3ε, 4ε, 6ε, (4a_Γ+3)ε, 4ε and 4ε»). -/
theorem row_errors_le_six_eps {ε aΓ : ℝ} (hε : 0 ≤ ε) (haΓ : aΓ ≤ 3 / 4)
    {e₁ e₂ e₃ e₄ e₅ e₆ : ℝ}
    (h₁ : e₁ ≤ 3 * ε) (h₂ : e₂ ≤ 4 * ε) (h₃ : e₃ ≤ 6 * ε)
    (h₄ : e₄ ≤ (4 * aΓ + 3) * ε) (h₅ : e₅ ≤ 4 * ε) (h₆ : e₆ ≤ 4 * ε) :
    e₁ ≤ 6 * ε ∧ e₂ ≤ 6 * ε ∧ e₃ ≤ 6 * ε ∧ e₄ ≤ 6 * ε ∧ e₅ ≤ 6 * ε ∧ e₆ ≤ 6 * ε := by
  have h6 : (4 * aΓ + 3) * ε ≤ 6 * ε :=
    mul_le_mul_of_nonneg_right (by linarith) hε
  exact ⟨by linarith, by linarith, h₃, by linarith, by linarith, by linarith⟩


/-- Lemma B2's display: `z·Ḡ ≥ z₀G^π₀ − 6ε Σ_t z_t`. -/
theorem z_dot_Gbar_ge {ι : Type*} [Fintype ι] {ε : ℝ} (hε : 0 ≤ ε)
    {Gbar Gpi z : ι → ℝ} {t₀ : ι}
    (hrowerr : ∀ t, |Gbar t - Gpi t| ≤ 6 * ε)
    (hz : ∀ t, 0 ≤ z t) (hGpi : ∀ t ≠ t₀, 0 ≤ Gpi t) :
    z t₀ * Gpi t₀ - 6 * ε * ∑ t, z t ≤ ∑ t, z t * Gbar t := by
  classical
  have hlow : ∀ t, Gpi t - 6 * ε ≤ Gbar t := by
    intro t
    have h := hrowerr t
    rw [abs_le] at h
    linarith
  have hsumz : ∑ t, z t = z t₀ + ∑ t ∈ Finset.univ.erase t₀, z t := by
    have h := Finset.sum_erase_add (s := Finset.univ) (f := z) (Finset.mem_univ t₀)
    linarith
  have hsplit : ∑ t, z t * Gbar t
      = z t₀ * Gbar t₀ + ∑ t ∈ Finset.univ.erase t₀, z t * Gbar t := by
    have h := Finset.sum_erase_add
      (s := Finset.univ) (f := fun t => z t * Gbar t) (Finset.mem_univ t₀)
    linarith
  have h0 : z t₀ * (Gpi t₀ - 6 * ε) ≤ z t₀ * Gbar t₀ :=
    mul_le_mul_of_nonneg_left (hlow t₀) (hz t₀)
  have hrest : ∑ t ∈ Finset.univ.erase t₀, (-6 * ε * z t)
      ≤ ∑ t ∈ Finset.univ.erase t₀, z t * Gbar t := by
    refine Finset.sum_le_sum fun t ht => ?_
    have hne : t ≠ t₀ := Finset.ne_of_mem_erase ht
    have hGt : 0 ≤ Gpi t := hGpi t hne
    have h2 : -6 * ε * z t ≤ z t * (Gpi t - 6 * ε) := by
      rw [mul_sub]
      have h3 : 0 ≤ z t * Gpi t := mul_nonneg (hz t) hGt
      have h4 : z t * (6 * ε) = 6 * ε * z t := by ring
      linarith [h3, h4]
    have h5 : z t * (Gpi t - 6 * ε) ≤ z t * Gbar t :=
      mul_le_mul_of_nonneg_left (hlow t) (hz t)
    linarith
  have h0' : z t₀ * (Gpi t₀ - 6 * ε) = z t₀ * Gpi t₀ - 6 * ε * z t₀ := by ring
  have hgoal : z t₀ * Gpi t₀ - 6 * ε * (z t₀ + ∑ t ∈ Finset.univ.erase t₀, z t)
      = z t₀ * (Gpi t₀ - 6 * ε) + ∑ t ∈ Finset.univ.erase t₀, (-6 * ε * z t) := by
    rw [mul_add, h0', ← Finset.mul_sum]
    ring
  rw [hsumz, hsplit, hgoal]
  exact add_le_add h0 hrest

/-- Lemma B2, region ρ₀ (verbatim: «Here W_{v,π} ≤ Γ, so α_π = 1.  Sampling
means U_{v,π} < Δ.  Then G^π₀ = Δ − U_{v,π} > 0 and z₀ ≥ 1 give
−U_{v,π} = −Δ + G^π₀ ≤ −Δ + z₀G^π₀»). -/
theorem lem_B2_region_zero {Δ α U G₀ z₀ : ℝ} (hα : α = 1) (hU : U < Δ)
    (hG₀def : G₀ = Δ - U) (hz₀ : 1 ≤ z₀) : -α * U ≤ -Δ + z₀ * G₀ := by
  have hnonneg : 0 ≤ Δ - U := by linarith
  have h1 : (1 : ℝ) * (Δ - U) ≤ z₀ * (Δ - U) :=
    mul_le_mul_of_nonneg_right hz₀ hnonneg
  rw [hα, hG₀def]
  nlinarith [h1, hnonneg]

/-- Lemma B2, regions ρ₁..ρ₉ (verbatim: «Here W_{v,π} > Γb_{i−1} ≥ Γ.  So
α_π = Γ/W_{v,π} < 1/b_{i−1} ≤ z₀, and α_π a_Γ W_{v,π} = Δ.  Sampling means
α_π U_{v,π} < Δ, that is, G^π₀ = a_Γ W_{v,π} − U_{v,π} > 0.  Then
−α_π U_{v,π} = −Δ + α_π G^π₀ ≤ −Δ + z₀ G^π₀»).  `b` is `b_{i−1}` (and `15` for
ρ₉). -/
theorem lem_B2_region_band {Δ α U aΓ W G₀ z₀ b : ℝ} (hΓ : 0 < Γ) (hb : 0 < b)
    (hα : α = Γ / W) (hW : Γ * b < W) (haΓΔ : α * aΓ * W = Δ) (hU : α * U < Δ)
    (hG₀def : G₀ = aΓ * W - U) (hz₀ : 1 ≤ z₀ * b) :
    -α * U ≤ -Δ + z₀ * G₀ := by
  have hWpos : 0 < W := by
    have hΓb : (0 : ℝ) < Γ * b := by positivity
    linarith
  have hαpos : 0 < α := by rw [hα]; exact div_pos hΓ hWpos
  have hαb : α * b ≤ 1 := by
    rw [hα, div_mul_eq_mul_div, div_le_one hWpos]
    exact le_of_lt hW
  have hz₀' : 1 / b ≤ z₀ := (div_le_iff₀ hb).mpr hz₀
  have hαle : α ≤ z₀ := by
    -- α = Γ/W, Γb < W ⟹ Γ/W ≤ 1/b; and 1/b ≤ z₀
    have h1 : Γ / W ≤ 1 / b :=
      (div_le_div_iff₀ hWpos hb).mpr (by show Γ * b ≤ 1 * W; rw [one_mul]; exact le_of_lt hW)
    linarith [h1, hz₀']
  have hG₀pos : 0 < G₀ := by
    rw [hG₀def]
    have h1 : α * U < α * aΓ * W := by rw [haΓΔ]; exact hU
    have h2 : U < aΓ * W := by
      by_contra hc
      push_neg at hc
      have h3 : α * aΓ * W ≤ α * U := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hc (le_of_lt hαpos)
      rw [haΓΔ] at h3
      linarith
    linarith
  have hzG : α * G₀ ≤ z₀ * G₀ := mul_le_mul_of_nonneg_right hαle (le_of_lt hG₀pos)
  have hkey : α * G₀ = Δ - α * U := by
    rw [hG₀def, mul_sub, ← mul_assoc, haΓΔ]
  linarith [hkey, hzG]

/-- Lemma B2 (domination), verbatim conclusion: the dispatch of the two region
cases against Lemma B2's display.  `zGbar` is the paper's `z·Ḡ =
(1/n)Σ_{i=1}^n z·G(x_i)`; `t₀` is row `0` of the certificate vector. -/
theorem lem_B2_domination {ι : Type*} [Fintype ι] {ε Δ α U G₀ zGbar : ℝ}
    {Gbar Gpi z : ι → ℝ} {t₀ : ι}
    (hzdot : z t₀ * Gpi t₀ - 6 * ε * ∑ t, z t ≤ zGbar)
    (hcase : -α * U ≤ -Δ + z t₀ * Gpi t₀) :
    -α * U ≤ -Δ + zGbar + 6 * ε * ∑ t, z t := by
  linarith [hcase, hzdot]

end SubsetSumL25
