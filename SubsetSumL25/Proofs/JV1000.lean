/-
M2 (V1): jv1000's sine extension — the statement-of-record.  Sources and
the proved-vs-named ledger live in `Statements/JV1000.lean`; verbatim quotes
are reproduced there.  The O4 hooks (Proofs/O4.lean: o4_avg_err_le,
o4_finite_from_continuous, o4_log_abs_le, o4_gibbs) carry NO parity
hypothesis — this file instantiates them at the sine-inclusive trig-polynomial
family, which is exactly jv1000's item 3 («without an evenness assumption»).

Cast-discipline note (M2c lesson carried): everything below stays in natural
ℝ/ℕ forms; no ℕ→ℝ cast injection, no Nat.factorization.
-/
import Mathlib
import SubsetSumL25.Proofs.O4

namespace SubsetSumL25

/-! ### The jv1000 log-density polynomials -/

/-- The jv1000 log-density polynomial (rev8g §8, verbatim shape): `r(x) =
Σ_{j=1}^{16} (a_j cos jx + b_j sin jx)` — 16 cosine + 16 sine terms per
density (64 coefficients across r and s; Base's filters are 8-term
cosine-only).  Coefficients are arbitrary reals; the certified point
instantiates them. -/
noncomputable def trig16 (a b : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc (1:ℕ) 16, (a j * Real.cos (j * x) + b j * Real.sin (j * x))

/-- The harmonic-amplitude weight `Σ_j (|a_j| + |b_j|)` — jv1000's «summing
harmonic amplitudes», evaluated to 3.21 at the certified point. -/
noncomputable def amp16 (a b : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc (1:ℕ) 16, (|a j| + |b j|)

/-- The harmonic-power weight `Σ_j j·(|a_j| + |b_j|)` — the Lipschitz
constant of r, the first rung of «coefficient sum with harmonic powers». -/
noncomputable def lip16 (a b : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc (1:ℕ) 16, (j:ℝ) * (|a j| + |b j|)

/-! ### V1 item 1 — positivity, smoothness, well-defined densities -/

/-- Positivity is parity-free: `2^r > 0` for ANY coefficient choice. -/
theorem v1_pos (a b : ℕ → ℝ) (x : ℝ) : 0 < (2:ℝ) ^ (trig16 a b x) :=
  Real.rpow_pos_of_pos (by norm_num) _

/-- C^∞ on 𝕋: finite sums of cos/sin at linear phases are analytic. -/
theorem v1_smooth (a b : ℕ → ℝ) : ContDiff ℝ ⊤ (trig16 a b) := by
  refine ContDiff.sum fun j _ => ?_
  have hc2 : ContDiff ℝ ⊤ (fun x : ℝ => (j:ℝ) * x) :=
    contDiff_const.mul contDiff_id
  exact (contDiff_const.mul hc2.cos).add (contDiff_const.mul hc2.sin)

/-- The densities f = 2^r/∫2^r are well-defined: the normalizing integral is
strictly positive for any coefficient choice (the integrand is continuous and
strictly positive on an interval of positive length). -/
theorem v1_density_pos (a b : ℕ → ℝ) :
    0 < ∫ x in (0:ℝ)..(2 * Real.pi), (2:ℝ) ^ (trig16 a b x) := by
  have hcont : Continuous fun x : ℝ => (2:ℝ) ^ (trig16 a b x) := by
    have hfun : (fun x : ℝ => (2:ℝ) ^ (trig16 a b x))
        = fun x : ℝ => Real.exp (Real.log 2 * trig16 a b x) := by
      funext x
      rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
    rw [hfun]
    exact Real.continuous_exp.comp
      (continuous_const.mul (v1_smooth a b).continuous)
  have hne0 : ∀ x : ℝ, ((2:ℝ) ^ (trig16 a b x)) ≠ 0 := fun x => ne_of_gt (v1_pos a b x)
  have hnonneg : ∀ x : ℝ, 0 ≤ (2:ℝ) ^ (trig16 a b x) := fun x => le_of_lt (v1_pos a b x)
  have hsub : Set.Ioo (0:ℝ) (2 * Real.pi)
      ⊆ Function.support (fun x : ℝ => (2:ℝ) ^ (trig16 a b x)) ∩ Set.Ioc (0:ℝ) (2 * Real.pi) :=
    fun x hx => ⟨hne0 x, Set.mem_Ioc.2 ⟨hx.1, hx.2.le⟩⟩
  have hv : (0:ENNReal) < MeasureTheory.volume (Set.Ioo (0:ℝ) (2 * Real.pi)) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.2 (by linarith [Real.pi_pos])
  have hfinal : (0:ℝ) < 2 * Real.pi ∧ 0 < MeasureTheory.volume
      (Function.support (fun x : ℝ => (2:ℝ) ^ (trig16 a b x)) ∩ Set.Ioc (0:ℝ) (2 * Real.pi)) :=
    And.intro (by positivity) (lt_of_lt_of_le hv (MeasureTheory.measure_mono hsub))
  exact (intervalIntegral.integral_pos_iff_support_of_nonneg_ae
    (MeasureTheory.ae_of_all MeasureTheory.volume hnonneg)
    (hcont.intervalIntegrable 0 (2 * Real.pi))).2 hfinal

/-! ### V1 item 3 — uniform boundedness, parity-free -/

/-- The harmonic-amplitude bound: every value of r is at most the amplitude
weight. -/
theorem v1_amp_bound (a b : ℕ → ℝ) (x : ℝ) : |trig16 a b x| ≤ amp16 a b := by
  have hterm : ∀ j ∈ Finset.Icc (1:ℕ) 16,
      |a j * Real.cos (j * x) + b j * Real.sin (j * x)| ≤ |a j| + |b j| := by
    intro j _
    calc |a j * Real.cos (j * x) + b j * Real.sin (j * x)|
        ≤ |a j * Real.cos (j * x)| + |b j * Real.sin (j * x)| := abs_add_le _ _
      _ ≤ |a j| + |b j| := by
          rw [abs_mul, abs_mul]
          refine add_le_add ?_ ?_
          · simpa using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (j * x)) (abs_nonneg _)
          · simpa using mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (j * x)) (abs_nonneg _)
  show |∑ j ∈ Finset.Icc (1:ℕ) 16, (a j * Real.cos (j * x) + b j * Real.sin (j * x))|
      ≤ ∑ j ∈ Finset.Icc (1:ℕ) 16, (|a j| + |b j|)
  refine le_trans (Finset.abs_sum_le_sum_abs
    (fun j => a j * Real.cos (j * x) + b j * Real.sin (j * x)) _) (Finset.sum_le_sum hterm)

/-- The certified-point corollary (rev8g: «|r(x)|, |s(x)| < 3.21 by summing
harmonic amplitudes»). -/
theorem v1_cert_amp {a b : ℕ → ℝ} (hcert : amp16 a b ≤ 3.21) (x : ℝ) :
    |trig16 a b x| ≤ 3.21 :=
  le_trans (v1_amp_bound a b x) hcert

/-! ### The Lipschitz hook for (F7) — no evenness -/

/-- `|cos t − cos s| ≤ |t − s|` — the trig-identity form. -/
theorem v1_cos_lip (t s : ℝ) : |Real.cos t - Real.cos s| ≤ |t - s| := by
  have h1 : |Real.sin ((t + s) / 2)| ≤ 1 := Real.abs_sin_le_one ((t + s) / 2)
  have h2 : |Real.sin ((t - s) / 2)| ≤ |(t - s) / 2| := Real.abs_sin_le_abs
  calc |Real.cos t - Real.cos s|
      = 2 * |Real.sin ((t + s) / 2)| * |Real.sin ((t - s) / 2)| := by
        rw [Real.cos_sub_cos, abs_mul, abs_mul, abs_neg]; norm_num
    _ ≤ (2 * 1) * |Real.sin ((t - s) / 2)| :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 2))
          (abs_nonneg (Real.sin ((t - s) / 2)))
    _ = 2 * |Real.sin ((t - s) / 2)| := by norm_num
    _ ≤ 2 * |(t - s) / 2| :=
        mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ) ≤ 2)
    _ = |t - s| := by rw [abs_div, abs_of_pos (show (0:ℝ) < 2 by norm_num)]; field_simp

/-- `|sin t − sin s| ≤ |t − s|` — from the cos bound by the half-period
shift. -/
theorem v1_sin_lip (t s : ℝ) : |Real.sin t - Real.sin s| ≤ |t - s| := by
  have h := v1_cos_lip (Real.pi / 2 - t) (Real.pi / 2 - s)
  rw [Real.cos_pi_div_two_sub, Real.cos_pi_div_two_sub] at h
  have hrw : ((Real.pi / 2 - t) - (Real.pi / 2 - s)) = -(t - s) := by ring
  rw [hrw, abs_neg] at h
  exact h

/-- V1 item 3: r is Lipschitz with the explicit constant
`Σ j·(|a_j| + |b_j|)` — the (F7) hook with NO evenness hypothesis. -/
theorem v1_lipschitz (a b : ℕ → ℝ) :
    ∀ t s : ℝ, |trig16 a b t - trig16 a b s| ≤ lip16 a b * |t - s| := by
  intro t s
  simp only [trig16, lip16]
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ j ∈ Finset.Icc (1:ℕ) 16,
      |a j * Real.cos ((j:ℝ) * t) + b j * Real.sin ((j:ℝ) * t)
        - (a j * Real.cos ((j:ℝ) * s) + b j * Real.sin ((j:ℝ) * s))|
      ≤ ((j:ℝ) * (|a j| + |b j|)) * |t - s| := by
    intro j hj
    have hrw : a j * Real.cos ((j:ℝ) * t) + b j * Real.sin ((j:ℝ) * t)
        - (a j * Real.cos ((j:ℝ) * s) + b j * Real.sin ((j:ℝ) * s))
        = a j * (Real.cos ((j:ℝ) * t) - Real.cos ((j:ℝ) * s))
          + b j * (Real.sin ((j:ℝ) * t) - Real.sin ((j:ℝ) * s)) := by ring
    rw [hrw]
    have hjc : |(j:ℝ) * t - (j:ℝ) * s| = (j:ℝ) * |t - s| := by
      have h1 : (j:ℝ) * t - (j:ℝ) * s = (j:ℝ) * (t - s) := by ring
      rw [h1, abs_mul, Nat.abs_cast]
    have hstep1 : |a j * (Real.cos ((j:ℝ) * t) - Real.cos ((j:ℝ) * s))
        + b j * (Real.sin ((j:ℝ) * t) - Real.sin ((j:ℝ) * s))|
        ≤ |a j| * |Real.cos ((j:ℝ) * t) - Real.cos ((j:ℝ) * s)|
          + |b j| * |Real.sin ((j:ℝ) * t) - Real.sin ((j:ℝ) * s)| := by
      have h := abs_add_le (a j * (Real.cos ((j:ℝ) * t) - Real.cos ((j:ℝ) * s)))
        (b j * (Real.sin ((j:ℝ) * t) - Real.sin ((j:ℝ) * s)))
      rw [abs_mul, abs_mul] at h
      exact h
    have hstep2 : |a j| * |Real.cos ((j:ℝ) * t) - Real.cos ((j:ℝ) * s)|
        + |b j| * |Real.sin ((j:ℝ) * t) - Real.sin ((j:ℝ) * s)|
        ≤ |a j| * |(j:ℝ) * t - (j:ℝ) * s|
          + |b j| * |(j:ℝ) * t - (j:ℝ) * s| :=
      add_le_add
        (mul_le_mul_of_nonneg_left (v1_cos_lip _ _) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (v1_sin_lip _ _) (abs_nonneg _))
    have hstep3 : |a j| * |(j:ℝ) * t - (j:ℝ) * s|
        + |b j| * |(j:ℝ) * t - (j:ℝ) * s|
        = (|a j| + |b j|) * ((j:ℝ) * |t - s|) := by
      rw [hjc, add_mul]
    have hstep4 : (|a j| + |b j|) * ((j:ℝ) * |t - s|)
        ≤ ((j:ℝ) * (|a j| + |b j|)) * |t - s| := by
      rw [mul_comm (j:ℝ) (|a j| + |b j|), ← mul_assoc]
    calc |a j * (Real.cos ((j:ℝ) * t) - Real.cos ((j:ℝ) * s))
          + b j * (Real.sin ((j:ℝ) * t) - Real.sin ((j:ℝ) * s))|
        ≤ |a j| * |Real.cos ((j:ℝ) * t) - Real.cos ((j:ℝ) * s)|
          + |b j| * |Real.sin ((j:ℝ) * t) - Real.sin ((j:ℝ) * s)| := hstep1
      _ ≤ |a j| * |(j:ℝ) * t - (j:ℝ) * s|
          + |b j| * |(j:ℝ) * t - (j:ℝ) * s| := hstep2
      _ = (|a j| + |b j|) * ((j:ℝ) * |t - s|) := hstep3
      _ ≤ ((j:ℝ) * (|a j| + |b j|)) * |t - s| := hstep4
  show |∑ j ∈ Finset.Icc (1:ℕ) 16, (a j * Real.cos ((j:ℝ) * t)
      + b j * Real.sin ((j:ℝ) * t) - (a j * Real.cos ((j:ℝ) * s)
      + b j * Real.sin ((j:ℝ) * s)))|
      ≤ (∑ j ∈ Finset.Icc (1:ℕ) 16, (j:ℝ) * (|a j| + |b j|)) * |t - s|
  rw [Finset.sum_mul]
  exact le_trans (Finset.abs_sum_le_sum_abs
    (fun j => a j * Real.cos ((j:ℝ) * t) + b j * Real.sin ((j:ℝ) * t)
      - (a j * Real.cos ((j:ℝ) * s) + b j * Real.sin ((j:ℝ) * s)))
    (Finset.Icc (1:ℕ) 16)) (Finset.sum_le_sum hterm)

/-- The O4 transfer (rev8g item 3): the P₀ assembly (Lemma 3.2's Riemann
step, `o4_finite_from_continuous`) applies to the sine-inclusive
trig-polynomial integrands with the explicit Lipschitz constant
`lip16 a b` — no evenness hypothesis anywhere. -/
theorem v1_o4_transfer (a b : ℕ → ℝ) (H : ℝ → ℝ) (hH : ∀ x, H x = trig16 a b x)
    (C T : ℝ) (hC : (∫ x in (0:ℝ)..(2 * Real.pi), H x) / (2 * Real.pi) < C)
    (hCT : C < T) :
    ∀ P ≥ o4P₀ (lip16 a b) C T, 0 < P → o4Avg P H < T := by
  refine o4_finite_from_continuous (B := lip16 a b) ?_ hC hCT
  intro t s
  rw [hH t, hH s]
  exact v1_lipschitz a b t s

/-- The L3.2 uniform-boundedness conclusion for the sine family: with the
certified amplitude bound the density weights 2^{r(x)} sit in the fixed
positive range `[2^{-3.21}, 2^{3.21}]`, so their logs are uniformly bounded
(`o4_log_abs_le`) by `3.21·log 2` — no evenness. -/
theorem v1_log_bounded (a b : ℕ → ℝ) (hcert : amp16 a b ≤ 3.21) (x : ℝ) :
    |Real.log ((2:ℝ) ^ (trig16 a b x))| ≤ 3.21 * Real.log 2 := by
  have hamp := v1_cert_amp hcert x
  rw [abs_le] at hamp
  have hlo : ((2:ℝ) ^ (-(3.21:ℝ))) ≤ (2:ℝ) ^ (trig16 a b x) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hamp.1
  have hhi : (2:ℝ) ^ (trig16 a b x) ≤ ((2:ℝ) ^ (3.21:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hamp.2
  refine le_trans (o4_log_abs_le (W := (2:ℝ) ^ (trig16 a b x))
    (m := (2:ℝ) ^ (-(3.21:ℝ))) (M := (2:ℝ) ^ (3.21:ℝ))
    (by positivity) hlo hhi) ?_
  have e1 : Real.log ((2:ℝ) ^ (-(3.21:ℝ)))
      = -((3.21:ℝ) * Real.log 2) := by
    rw [Real.log_rpow (by norm_num) (-(3.21:ℝ)), neg_mul]
  have e2 : Real.log ((2:ℝ) ^ (3.21:ℝ)) = (3.21:ℝ) * Real.log 2 :=
    Real.log_rpow (by norm_num) (3.21:ℝ)
  rw [e1, e2, abs_neg,
    abs_of_nonneg (by linarith [Real.log_pos (by norm_num : (1:ℝ) < 2)] :
      (0:ℝ) ≤ (3.21:ℝ) * Real.log 2), max_self]

/-! ### V1 item 2 — the entropy identities at the discrete hook -/

/-- The relative-entropy inequalities (Base (3.3): «D ≥ 0, D−A ≥ 0,
D−E ≥ 0») for the sine-inclusive densities at the P-point weights —
`o4_gibbs` carries no parity hypothesis, so the identities hold unchanged
for ANY coefficient choice (rev8g item 2: «regardless of the filters'
parity»). -/
theorem v1_entropy_discrete (a b c d : ℕ → ℝ) (P : ℕ) (hP : 0 < P)
    (w q : ℕ → ℝ)
    (hw : ∀ i ∈ Finset.range P, w i = (2:ℝ) ^ (trig16 a b (2 * Real.pi * i / P))
      / (∑ i ∈ Finset.range P, (2:ℝ) ^ (trig16 a b (2 * Real.pi * i / P))))
    (hq : ∀ i ∈ Finset.range P, q i = (2:ℝ) ^ (trig16 c d (2 * Real.pi * i / P))
      / (∑ i ∈ Finset.range P, (2:ℝ) ^ (trig16 c d (2 * Real.pi * i / P)))) :
    ∑ i ∈ Finset.range P, w i * Real.log (q i / w i) ≤ 0
      ∧ 0 ≤ ∑ i ∈ Finset.range P, w i * Real.log (w i / q i) := by
  classical
  have hSpos : 0 < ∑ i ∈ Finset.range P, (2:ℝ) ^ (trig16 a b (2 * Real.pi * i / P)) :=
    Finset.sum_pos' (fun i _ => le_of_lt (v1_pos a b _))
      ⟨0, Finset.mem_range.2 hP, v1_pos a b _⟩
  have hTpos : 0 < ∑ i ∈ Finset.range P, (2:ℝ) ^ (trig16 c d (2 * Real.pi * i / P)) :=
    Finset.sum_pos' (fun i _ => le_of_lt (v1_pos c d _))
      ⟨0, Finset.mem_range.2 hP, v1_pos c d _⟩
  have hwsum : ∑ i ∈ Finset.range P, w i = 1 := by
    rw [Finset.sum_congr rfl fun i hi => hw i hi, ← Finset.sum_div]
    exact div_self (ne_of_gt hSpos)
  have hqsum : ∑ i ∈ Finset.range P, q i = 1 := by
    rw [Finset.sum_congr rfl fun i hi => hq i hi, ← Finset.sum_div]
    exact div_self (ne_of_gt hTpos)
  refine o4_gibbs w q ?_ hwsum ?_ hqsum
  · intro i hi
    rw [hw i hi]
    exact div_pos (v1_pos a b _) hSpos
  · intro i hi
    rw [hq i hi]
    exact div_pos (v1_pos c d _) hTpos

end SubsetSumL25
