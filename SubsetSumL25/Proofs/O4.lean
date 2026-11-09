/-
M2 (O4): proofs of the L3.2 finite-circle core.  Primary-source quotes live
in `Statements/O4.lean`; this file is the statement-of-record for everything
proved here.

Two statement corrections vs M1 (caught while proving, the hn07 pattern —
disclosed in STMTS.md §O4): the quotient-boundedness pair as originally
stated was false.  The corrected pair is exactly the paper's use of
`K_x = f·g/Q`: with the denominator bounded BELOW, an upper quotient bound
`num/den ≤ N/d` needs `d ≤ den` (o4_div_le); with the denominator bounded
ABOVE, a lower quotient bound `m/D ≤ num/den` needs `den ≤ D` (o4_le_div).
-/
import Mathlib
import SubsetSumL25.Statements.O4

namespace SubsetSumL25

/-- The normalized P-point average on the circle grid `2πj/P`. -/
noncomputable def o4Avg (P : ℕ) (H : ℝ → ℝ) : ℝ :=
  (∑ j ∈ Finset.range P, H (2 * Real.pi * j / P)) / P

/-- The paper's P₀ for the integrand bound `B`, continuous bound `C`, target
`T`. -/
noncomputable def o4P₀ (B C T : ℝ) : ℕ := (⌈2 * Real.pi * B / (T - C)⌉ : ℤ).toNat + 1

/-- The Riemann-sum estimate, Lipschitz form. -/
theorem o4_avg_err_le {H : ℝ → ℝ} {B : ℝ}
    (hLip : ∀ t s : ℝ, |H t - H s| ≤ B * |t - s|)
    {P : ℕ} (hP : 0 < P) :
    |o4Avg P H - (∫ x in (0:ℝ)..(2 * Real.pi), H x) / (2 * Real.pi)|
      ≤ 2 * Real.pi * B / P := by
  classical
  have hPc : (0:ℝ) < (P:ℝ) := by exact_mod_cast hP
  set len : ℝ := 2 * Real.pi / P with hlen
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  have hlenpos : 0 < len := by rw [hlen]; positivity
  have hB0 : 0 ≤ B := by
    by_cases hb : 0 ≤ B
    · exact hb
    · push_neg at hb
      have h1 := hLip 0 1
      have hneg : (0:ℝ) - 1 = -1 := by norm_num
      rw [hneg, abs_neg, abs_one, mul_one] at h1
      linarith [abs_nonneg (H 0 - H 1)]
  have hcont : Continuous H := by
    refine continuous_iff_continuousAt.mpr ?_
    intro t
    refine Metric.continuousAt_iff.mpr ?_
    intro ε hε
    refine ⟨ε / (B + 1), by positivity, fun u hu => ?_⟩
    rw [Real.dist_eq] at hu ⊢
    have h2 : B * |u - t| < ε := by
      have hu' := le_of_lt hu
      calc B * |u - t| ≤ B * (ε / (B + 1)) := mul_le_mul_of_nonneg_left hu' hB0
        _ = (B / (B + 1)) * ε := by ring
        _ < ε := by
            have hstep : B / (B + 1) < 1 := by
              rw [div_lt_iff₀ (by positivity : (0:ℝ) < B + 1)]
              nlinarith
            have hlt := mul_lt_mul_of_pos_right hstep hε
            rwa [one_mul] at hlt
    exact lt_of_le_of_lt (hLip u t) h2
  have hterm : ∀ j : ℕ, (2 * Real.pi * j / P : ℝ) = len * j := by
    intro j; rw [hlen]; field_simp
  -- per-slice bound: (∫ slice H) − len·H(aj) = ∫ slice (H x − H(aj)), bounded by B·len²
  have hslice : ∀ j : ℕ,
      |(∫ x in len * j..len * (j + 1), H x) - len * H (len * j)| ≤ B * len * len := by
    intro j
    have hab : len * j ≤ len * (j + 1) := by nlinarith
    have hcI : IntervalIntegrable H MeasureTheory.volume (len * j) (len * (j + 1)) :=
      hcont.intervalIntegrable _ _
    have hcC : IntervalIntegrable (fun _ => H (len * j)) MeasureTheory.volume
        (len * j) (len * (j + 1)) := continuous_const.intervalIntegrable _ _
    have hv : (len * (j + 1) - len * j : ℝ) = len := by push_cast; ring
    have hstep1 : (∫ x in len * j..len * (j + 1), H x) - len * H (len * j)
        = ∫ x in len * j..len * (j + 1), (H x - H (len * j)) := by
      rw [intervalIntegral.integral_sub hcI hcC, intervalIntegral.integral_const,
        smul_eq_mul, hv]
    have hbound : ∀ x ∈ Set.uIoc (len * j) (len * (j + 1)),
        ‖H x - H (len * j)‖ ≤ B * len := by
      intro x hx
      rw [Set.uIoc_of_le hab] at hx
      rw [Real.norm_eq_abs]
      have h1 : |H x - H (len * j)| ≤ B * |x - len * j| := hLip x (len * j)
      have h2 : |x - len * j| ≤ len := by
        rw [abs_le]
        constructor <;> linarith [hx.1, hx.2]
      exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hB0)
    rw [hstep1, ← Real.norm_eq_abs]
    refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const hbound) ?_
    rw [hv, abs_of_pos hlenpos]
  -- integral split over the P grid slices
  have hP2 : len * (P:ℝ) = 2 * Real.pi := by rw [hlen]; field_simp
  have hsplit : ∫ x in (0:ℝ)..(2 * Real.pi), H x
      = ∑ j ∈ Finset.range P, ∫ x in len * j..len * (j + 1), H x := by
    have hs := intervalIntegral.sum_integral_adjacent_intervals
      (f := H) (μ := MeasureTheory.volume) (a := fun j => len * j) (n := P)
      (fun _ _ => hcont.intervalIntegrable _ _)
    push_cast at hs
    rw [mul_zero, hP2] at hs
    exact hs.symm
  -- the key algebra
  have hkey : (2 * Real.pi) * (o4Avg P H
        - (∫ x in (0:ℝ)..(2 * Real.pi), H x) / (2 * Real.pi))
      = ∑ j ∈ Finset.range P, (len * H (len * j)
          - ∫ x in len * j..len * (j + 1), H x) := by
    rw [hsplit]
    have hunfold : o4Avg P H = (∑ j ∈ Finset.range P, H (2 * Real.pi * j / P)) / P := rfl
    have hsumterm : (∑ j ∈ Finset.range P, H (2 * Real.pi * j / P))
        = ∑ j ∈ Finset.range P, H (len * j) := by
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [hterm j]
    rw [hunfold, hsumterm, mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum]
    field_simp [hlen]
    have hlen2 : len * (P:ℝ) = 2 * Real.pi := by
      rw [hlen]
      field_simp
    rw [← hlen2]
    ring
  -- bound the sum of differences
  have hsum : |∑ j ∈ Finset.range P, (len * H (len * j)
      - ∫ x in len * j..len * (j + 1), H x)| ≤ (P:ℝ) * (B * len * len) := by
    have h1 : ∀ j ∈ Finset.range P, |len * H (len * j)
        - ∫ x in len * j..len * (j + 1), H x| ≤ B * len * len := by
      intro j _
      rw [abs_sub_comm]
      exact hslice j
    have h2 : ∑ j ∈ Finset.range P, (B * len * len) ≤ (P:ℝ) * (B * len * len) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
    exact le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum h1) h2)
  -- assemble
  have hx : o4Avg P H - (∫ x in (0:ℝ)..(2 * Real.pi), H x) / (2 * Real.pi)
      = (∑ j ∈ Finset.range P, (len * H (len * j)
          - ∫ x in len * j..len * (j + 1), H x)) / (2 * Real.pi) := by
    rw [eq_div_iff hpi.ne', mul_comm]
    exact hkey
  rw [hx, abs_div, abs_of_pos hpi]
  calc |∑ j ∈ Finset.range P, (len * H (len * j)
        - ∫ x in len * j..len * (j + 1), H x)| / (2 * Real.pi)
      ≤ ((P:ℝ) * (B * len * len)) / (2 * Real.pi) := by
        refine (div_le_div_iff₀ hpi hpi).mpr ?_
        exact mul_le_mul_of_nonneg_right hsum (by linarith)
    _ ≤ 2 * Real.pi * B / P := by
        rw [hlen]
        field_simp
        exact le_refl B

/-- The finite relative-entropy order (3.3): Gibbs's inequality for finite
probability vectors. -/
theorem o4_gibbs {P : ℕ} (w q : ℕ → ℝ)
    (hwpos : ∀ i ∈ Finset.range P, 0 < w i) (hwsum : ∑ i ∈ Finset.range P, w i = 1)
    (hqpos : ∀ i ∈ Finset.range P, 0 < q i) (hqsum : ∑ i ∈ Finset.range P, q i = 1) :
    ∑ i ∈ Finset.range P, w i * Real.log (q i / w i) ≤ 0
      ∧ 0 ≤ ∑ i ∈ Finset.range P, w i * Real.log (w i / q i) := by
  have hc : ConcaveOn ℝ (Set.Ioi 0) Real.log := strictConcaveOn_log_Ioi.concaveOn
  have hj : ∑ i ∈ Finset.range P, w i * Real.log (q i / w i)
      ≤ Real.log (∑ i ∈ Finset.range P, q i) := by
    have hstep := hc.le_map_sum (w := w) (t := Finset.range P)
      (p := fun i => q i / w i)
      (fun i hi => le_of_lt (hwpos i hi)) hwsum
      (fun i hi => Set.mem_Ioi.mpr (div_pos (hqpos i hi) (hwpos i hi)))
    simp only [smul_eq_mul] at hstep
    have hinside : ∑ i ∈ Finset.range P, w i * (q i / w i)
        = ∑ i ∈ Finset.range P, q i := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hw := ne_of_gt (hwpos i hi)
      field_simp
    rw [hinside] at hstep
    exact hstep
  rw [hqsum, Real.log_one] at hj
  have hflip : ∀ i ∈ Finset.range P, Real.log (w i / q i) = -Real.log (q i / w i) := by
    intro i hi
    rw [Real.log_div (ne_of_gt (hwpos i hi)) (ne_of_gt (hqpos i hi)),
      Real.log_div (ne_of_gt (hqpos i hi)) (ne_of_gt (hwpos i hi))]
    ring
  have hsum2 : ∑ i ∈ Finset.range P, w i * Real.log (w i / q i)
      = -(∑ i ∈ Finset.range P, w i * Real.log (q i / w i)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [hflip i hi]
    ring
  refine ⟨hj, ?_⟩
  rw [hsum2]
  linarith

/-- The P₀ assembly: finite average below the target for all `P ≥ o4P₀`. -/
theorem o4_finite_from_continuous {H : ℝ → ℝ} {B C T : ℝ}
    (hLip : ∀ t s : ℝ, |H t - H s| ≤ B * |t - s|)
    (hC : (∫ x in (0:ℝ)..(2 * Real.pi), H x) / (2 * Real.pi) < C)
    (hCT : C < T) :
    ∀ P ≥ o4P₀ B C T, 0 < P → o4Avg P H < T := by
  intro P hP₀ hP
  have hPc : (0:ℝ) < (P:ℝ) := by exact_mod_cast hP
  have hTC : 0 < T - C := by linarith
  have hP1 := o4_avg_err_le hLip hP
  have hb : (2:ℝ) * Real.pi * B / P < T - C := by
    by_cases hB0 : 0 ≤ B
    · set x : ℝ := 2 * Real.pi * B / (T - C) with hx
      have hx0 : 0 ≤ x := div_nonneg (by positivity) hTC.le
      have hceil : ((⌈x⌉ : ℤ) : ℝ) + 1 ≤ (o4P₀ B C T : ℝ) := by
        have hto : ((⌈x⌉ : ℤ).toNat : ℤ) = ⌈x⌉ :=
          Int.toNat_of_nonneg (Int.ceil_nonneg hx0)
        have hdef : o4P₀ B C T = (⌈x⌉ : ℤ).toNat + 1 := rfl
        rw [hdef]
        push_cast
        have h2 : ((⌈x⌉ : ℤ).toNat : ℝ) = ((⌈x⌉ : ℤ) : ℝ) := by exact_mod_cast hto
        rw [h2]
      have hPcast : ((o4P₀ B C T : ℕ) : ℝ) ≤ (P:ℝ) := by exact_mod_cast hP₀
      have hPx : x ≤ (P:ℝ) - 1 := by
        have h1 : x ≤ ((⌈x⌉ : ℤ) : ℝ) := Int.le_ceil x
        linarith
      have hexpr : (2:ℝ) * Real.pi * B / P = x * (T - C) / P := by
        rw [hx]; field_simp
      rw [hexpr, div_lt_iff₀ hPc]
      nlinarith [hTC, hPx]
    · push_neg at hB0
      have habs : 0 ≤ |H 0 - H 1| := abs_nonneg _
      have h1 := hLip 0 1
      have hneg : (0:ℝ) - 1 = -1 := by norm_num
      rw [hneg, abs_neg, abs_one, mul_one] at h1
      linarith
  have habs := abs_le.mp hP1
  linarith

/-- Uniform log-boundedness. -/
theorem o4_log_abs_le {W m M : ℝ} (hm : 0 < m) (h1 : m ≤ W) (h2 : W ≤ M) :
    |Real.log W| ≤ max |Real.log m| |Real.log M| := by
  have hWpos : 0 < W := lt_of_lt_of_le hm h1
  have hlow : Real.log m ≤ Real.log W := Real.log_le_log hm h1
  have hhigh : Real.log W ≤ Real.log M := Real.log_le_log hWpos h2
  have ham : |Real.log m| ≤ max |Real.log m| |Real.log M| := le_max_left _ _
  have haM : |Real.log M| ≤ max |Real.log m| |Real.log M| := le_max_right _ _
  have hs1 : -|Real.log m| ≤ Real.log m := by
    have h := le_abs_self (-Real.log m)
    rw [abs_neg] at h
    linarith
  have hs2 : Real.log M ≤ |Real.log M| := le_abs_self _
  refine abs_le.mpr ⟨?_, ?_⟩
  · linarith
  · linarith

/-- Quotient boundedness, upper half (the paper's `K_x ≤ AB/q`: numerator
bounded above, denominator bounded below). -/
theorem o4_div_le {num den N d : ℝ} (hden : 0 < den) (hd : 0 < d) (hle : d ≤ den)
    (hN : 0 ≤ N) (hnum : num ≤ N) :
    num / den ≤ N / d := by
  have h1 : num * d ≤ N * d := mul_le_mul_of_nonneg_right hnum (le_of_lt hd)
  have h2 : N * d ≤ N * den := mul_le_mul_of_nonneg_left hle hN
  exact (div_le_div_iff₀ hden hd).mpr (le_trans h1 h2)

/-- Quotient boundedness, lower half (the paper's `ab/Q̄ ≤ K_x`: numerator
bounded below, denominator bounded above). -/
theorem o4_le_div {num den m D : ℝ} (hden : 0 < den) (hD : den ≤ D)
    (_hm : 0 < m) (hnum : m ≤ num) (hnum0 : 0 ≤ num) :
    m / D ≤ num / den := by
  have hD0 : 0 < D := by linarith
  have h1 : m * den ≤ num * den := mul_le_mul_of_nonneg_right hnum (le_of_lt hden)
  have h2 : num * den ≤ num * D := mul_le_mul_of_nonneg_left hD hnum0
  exact (div_le_div_iff₀ hD0 hden).mpr (le_trans h1 h2)

end SubsetSumL25
