/-
`SubsetSumL25.Row.JV1000Moments` — C6, honestly split in two.

`JV1000Instance`'s §7 residue states the two moment checks as

  `m1 : log₂ jvMomentRho0 < ρ_c`,  `m2 : log₂ jvMomentBand < ρ_c`

against `jvMomentRho0`/`jvMomentBand`, which are the **raw-density** shapes
`2^{p(Δ − r(x))}` and `2^{q(a_Γ s(x) − r(x))}` — `r`/`s` the certified log-densities.
That file says of them «**Shape only** — the certified quantity carries the strip
corrections».  This file **measures what that caveat costs**, and the answer is not
a rounding error:

  * `log₂ jvMomentRho0 = 9.1347303876`  — the threshold is `ρ_c = 0.5162696413`,
    i.e. the stated goal is false by **8.62 bits** (a factor of 393);
  * `log₂ jvMomentBand = 8.5399821747`  — false by **8.02 bits**.

§1 below **proves** both refutations in Lean (`jv_m1_stated_false`,
`jv_m2_stated_false`), with no quadrature: the exponent `2^{p(Δ−r)}` reaches
`2^{p(Δ+1.19)} = 2^{10.3}` near `x = 0`, so a single window of width `1/100`
already carries the integral past `2·2^{ρ_c}`.  A disproof needs a *lower* bound on
one window; only the *proof* would need a 1.3·10⁻⁶-accurate enclosure of the whole
circle.  So the cheap direction is the one that was available, and it is the one
that matters: **goal `m1`/`m2` as stated are not open problems, they are false.**

§2 states the obligations against the quantity the certifier actually computes —
the **strip-corrected** log-densities `u`, `v` of `certify_c5` (`audit-jv1000`):
`u` is a smoothed/normalized log of an inner convolution, `v` its companion, and
the certified moments are `((2+2cos)·2^{p(Δ−u)})` and `((2+2cos)·2^{q(a_Γ v − u)})`
integrated against `dx/2π`.  `jvMomentRho0Cert`/`jvMomentBandCert` below are those
definitions, written as the *continuum* limit of the certifier's `N_in = 256`,
`N = 8192` grid sums (the grid sums are trapezoid approximations of exactly these
integrals).

Measured, both independently and by two routes (`sim/sim_m1.py`):
`log₂ jvMomentRho0Cert = 0.516268325851285` (margin `+1.3154·10⁻⁶`) and
`log₂ jvMomentBandCert = 0.516268147264670` (margin `+1.4940·10⁻⁶`); the discrete
certifier value `0.516268325851285` agrees to `2.2·10⁻¹⁶`.  **So the corrected
statement is true and tight; it is not proved here** — see §3 for exactly what is
missing and the measured size of each missing piece.

Why no enclosure is attempted here.  Two error proofs were costed:

  * trapezoid + Lipschitz (`JV1000Quadrature.trap_error_le`, proved in-tree):
    needs `n ≥ K·(2π)²/(2·1.3·10⁻⁶) ≈ 7.7·10¹⁷` panels, `K = 5.07·10¹⁰`;
  * strip analyticity (the certifier's route): `q₀ = 0.3708350894162912`, so
    `n = 40` panels already give `5.9·10⁻¹⁸`.

The second route is the only one that can be formalized at a feasible `n`, and it
needs Cauchy estimates on a complex strip plus a certified evaluation of ~10²–10³
elementary terms — a multi-session module, not a lemma.  Naming that, with the
numbers, is the deliverable; pretending `trap_error_le` closes C6 would be a lie
the next mind would pay for.
-/
import Mathlib
import SubsetSumL25.Row.JV1000Instance
import SubsetSumL25.Row.JV1000Quadrature

namespace SubsetSumL25.Row

open BigOSpeedrun.SubsetSum
open MeasureTheory intervalIntegral

set_option maxHeartbeats 1600000

/-! ### §1 — the row data the bounds need: `lip16` and the values at `0`

`v1_lipschitz` gives `|r t − r s| ≤ lip16 r · |t − s|` with no evenness
hypothesis; the two values below turn that into a *concrete* bound on a window.
Both are exact rationals because every coefficient is a multiple of `10⁻⁸` and the
harmonic index is an integer. -/

/-- `lip16` of the density `r`: `Σ_j j(|a_j| + |b_j|) = 12.16437058`. -/
theorem jv_lip16_value_r : lip16 jvRa jvRb = 608218529 / 50000000 := by
  rw [lip16]
  norm_num [jvRa, jvRb, jvRaQ, jvRbQ, jvRc, List.getD, Finset.sum_Icc_succ_top]

/-- `lip16` of the density `s`: `12.32575550`. -/
theorem jv_lip16_value_s : lip16 jvSa jvSb = 24651511 / 2000000 := by
  rw [lip16]
  norm_num [jvSa, jvSb, jvSaQ, jvSbQ, jvSc, List.getD, Finset.sum_Icc_succ_top]

/-- `r(0) = Σ_j a_j = −1.19258309` — the certified density is *negative* at `x = 0`,
which is what makes the raw-density moment blow up there. -/
theorem jvLogDensityR_zero : jvLogDensityR 0 = -119258309 / 100000000 := by
  rw [jvLogDensityR, trig16]
  simp only [mul_zero, Real.cos_zero, Real.sin_zero, mul_one, mul_zero, add_zero]
  norm_num [jvRa, jvRaQ, jvRc, List.getD, Finset.sum_Icc_succ_top]

/-- `s(0) = Σ_j a'_j = 0.61925852`. -/
theorem jvLogDensityS_zero : jvLogDensityS 0 = 15481463 / 25000000 := by
  rw [jvLogDensityS, trig16]
  simp only [mul_zero, Real.cos_zero, Real.sin_zero, mul_one, mul_zero, add_zero]
  norm_num [jvSa, jvSaQ, jvSc, List.getD, Finset.sum_Icc_succ_top]

/-- The Lipschitz bound at the origin, specialised from `v1_lipschitz`. -/
theorem jv_r_lip_zero (x : ℝ) :
    |jvLogDensityR x - jvLogDensityR 0| ≤ (608218529 / 50000000) * |x| := by
  have h := v1_lipschitz jvRa jvRb x 0
  rw [jv_lip16_value_r] at h
  simpa [jvLogDensityR] using h

/-- The Lipschitz bound at the origin for `s`. -/
theorem jv_s_lip_zero (x : ℝ) :
    |jvLogDensityS x - jvLogDensityS 0| ≤ (24651511 / 2000000) * |x| := by
  have h := v1_lipschitz jvSa jvSb x 0
  rw [jv_lip16_value_s] at h
  simpa [jvLogDensityS] using h

/-! ### §2 — the refutations

Both moments are refuted the same way: on a short window from `0` the exponent is
bounded *below* by an integer (`9` for `M₁`, `8` for `M₂` — deliberately integers so
that `2^k` is `norm_num`-able and no rational-power numeric bound is needed), the
`(2 + 2cos)` weight is bounded below by `2 + 2(1 − δ)`, and the window alone exceeds
`2·2^{ρ_c}`. -/

/-- The window machinery shared by the two refutations: a weight floor `c`, an
exponent floor `E` with `2^E = F`, and a window of width `δ ≤ 2π`. -/
theorem jv_moment_window_lb {e : ℝ → ℝ} {δ c F E : ℝ} (hδ : 0 < δ)
    (hδπ : δ ≤ 2 * Real.pi) (_hc : 0 ≤ c)
    (hcont : Continuous fun x => (2 + 2 * Real.cos x) * (2 : ℝ) ^ (e x))
    (hcos : ∀ x ∈ Set.Icc (0 : ℝ) δ, c ≤ 2 + 2 * Real.cos x)
    (hexp : ∀ x ∈ Set.Icc (0 : ℝ) δ, E ≤ e x) (hF : (2 : ℝ) ^ E = F) (hF0 : 0 ≤ F) :
    δ * c * F ≤ ∫ x in (0 : ℝ)..(2 * Real.pi),
      (2 + 2 * Real.cos x) * (2 : ℝ) ^ (e x) := by
  have hpt : ∀ x ∈ Set.Icc (0 : ℝ) δ, c * F
      ≤ (2 + 2 * Real.cos x) * (2 : ℝ) ^ (e x) := by
    intro x hx
    have h2 : F ≤ (2 : ℝ) ^ (e x) := by
      have h := (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).2 (hexp x hx)
      rwa [hF] at h
    exact mul_le_mul (hcos x hx) h2 hF0 (by nlinarith [Real.neg_one_le_cos x])
  have hwin : δ * (c * F)
      ≤ ∫ x in (0 : ℝ)..δ, (2 + 2 * Real.cos x) * (2 : ℝ) ^ (e x) := by
    have hmono := intervalIntegral.integral_mono_on (f := fun _ => c * F)
      (g := fun x => (2 + 2 * Real.cos x) * (2 : ℝ) ^ (e x)) (le_of_lt hδ)
      intervalIntegrable_const (hcont.intervalIntegrable (μ := volume) (0 : ℝ) δ) hpt
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    have hval : (δ - 0) * (c * F) = δ * (c * F) := by ring
    linarith [hmono, hval.le, hval.ge]
  have htail : 0 ≤ ∫ x in δ..(2 * Real.pi), (2 + 2 * Real.cos x) * (2 : ℝ) ^ (e x) :=
    intervalIntegral.integral_nonneg hδπ (fun x _ => by
      have h1 : 0 ≤ 2 + 2 * Real.cos x := by nlinarith [Real.neg_one_le_cos x]
      exact mul_nonneg h1 (Real.rpow_pos_of_pos (by norm_num) _).le)
  have hsplit := (intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hcont.intervalIntegrable (μ := volume) (0 : ℝ) δ)
    (hcont.intervalIntegrable (μ := volume) δ (2 * Real.pi))).symm
  linarith [hwin, htail, hsplit.le, hsplit.ge]

/-- **`M₁`'s stated shape is larger than `2`.**  On `[0, 1/100]` the exponent
`p(Δ − r)` is at least `9` (because `r(0) = −1.19258…` and `lip16·δ = 0.1216…`)
and the weight is at least `3.98`, so the window contributes `≥ 20.4` to
`2π·M₁`. -/
theorem jv_momentRho0_gt_two : (2 : ℝ) < jvMomentRho0 := by
  -- the exponent floor on the window
  have hexp : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 100), (9 : ℝ)
      ≤ (jvPQ : ℝ) * ((jvDeltaQ : ℝ) - jvLogDensityR x) := by
    intro x hx
    have hxabs : |x| ≤ 1 / 100 := by
      rw [abs_of_nonneg hx.1]; exact hx.2
    have hlip := jv_r_lip_zero x
    rw [jvLogDensityR_zero] at hlip
    have hb1 : jvLogDensityR x ≤ -119258309 / 100000000 + 608218529 / 50000000 * (1 / 100) := by
      have := (abs_le.1 hlip).2
      nlinarith [this, hxabs]
    have hkey : (109 / 100 : ℝ) ≤ (jvDeltaQ : ℝ) - jvLogDensityR x := by
      have hd : (jvDeltaQ : ℝ) = 286969377 / 10000000000 := by
        norm_num [jvDeltaQ, jvEtaQ, jvTau0Q]
      linarith
    have hpv : (jvPQ : ℝ) = 845902160 / 100000000 := by norm_num [jvPQ]
    rw [hpv]
    nlinarith [hkey]
  -- the weight floor on the window
  have hcos : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 100), (398 / 100 : ℝ) ≤ 2 + 2 * Real.cos x := by
    intro x hx
    have hxabs : |x| ≤ 1 / 100 := by
      rw [abs_of_nonneg hx.1]; exact hx.2
    have h := v1_cos_lip x 0
    rw [Real.cos_zero, sub_zero] at h
    have hlo : -(1 / 100) ≤ Real.cos x - 1 := by
      have h2 := (abs_le.1 h).1
      nlinarith [h2, hxabs]
    linarith
  have hcont : Continuous fun x => (2 + 2 * Real.cos x)
      * (2 : ℝ) ^ ((jvPQ : ℝ) * ((jvDeltaQ : ℝ) - jvLogDensityR x)) := by
    have hr : Continuous jvLogDensityR := (v1_smooth jvRa jvRb).continuous
    have hexp' : Continuous fun x : ℝ => (jvPQ : ℝ) * ((jvDeltaQ : ℝ) - jvLogDensityR x) := by
      fun_prop
    exact (continuous_const.add (continuous_const.mul Real.continuous_cos)).mul
      (Real.continuous_const_rpow (by norm_num : (2 : ℝ) ≠ 0) |>.comp hexp')
  have hwin : (1 / 100 : ℝ) * (398 / 100) * 512
      ≤ ∫ x in (0 : ℝ)..(2 * Real.pi),
          (2 + 2 * Real.cos x) * (2 : ℝ) ^ ((jvPQ : ℝ) * ((jvDeltaQ : ℝ) - jvLogDensityR x)) :=
    jv_moment_window_lb (e := fun x => (jvPQ : ℝ) * ((jvDeltaQ : ℝ) - jvLogDensityR x))
      (δ := 1 / 100) (c := 398 / 100) (F := 512) (E := 9)
      (by norm_num) (by linarith [Real.pi_gt_three]) (by norm_num) hcont hcos hexp
      (by norm_num) (by norm_num)
  -- assemble: `M₁ = (1/2π)·∫ ≥ (1/8)·∫`
  rw [jvMomentRho0]
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hpi8 : 2 * Real.pi ≤ 8 := by nlinarith [Real.pi_le_four]
  have hinv : (1 / 8 : ℝ) ≤ 1 / (2 * Real.pi) := one_div_le_one_div_of_le hpi hpi8
  have hval : (1 / 100 : ℝ) * (398 / 100) * 512 = 203776 / 10000 := by norm_num
  rw [hval] at hwin
  have := mul_le_mul hinv hwin (by norm_num) (by positivity)
  have hfinal : (1 / 8 : ℝ) * (203776 / 10000) = 50944 / 20000 := by norm_num
  linarith [this, hfinal.le, hfinal.ge]

/-- **`M₂`'s stated shape is larger than `2`** — same window argument at
`x ∈ [0, 1/50]`, with the exponent floor `8` (the companion density `s` starts
*positive*, `s(0) = 0.619`, so `a_Γ v − u` gets `a_Γ·0.619` of help). -/
theorem jv_momentBand_gt_two : (2 : ℝ) < jvMomentBand := by
  have hexp : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 50), (8 : ℝ)
      ≤ (jvQmQ : ℝ)
        * ((jvAGammaQ : ℝ) * jvLogDensityS x - jvLogDensityR x) := by
    intro x hx
    have hxabs : |x| ≤ 1 / 50 := by rw [abs_of_nonneg hx.1]; exact hx.2
    have hlipr := jv_r_lip_zero x
    have hlips := jv_s_lip_zero x
    rw [jvLogDensityR_zero] at hlipr
    rw [jvLogDensityS_zero] at hlips
    have hrx : jvLogDensityR x ≤ -119258309 / 100000000 + (608218529 / 50000000) * (1 / 50) := by
      have := (abs_le.1 hlipr).2
      nlinarith [this, hxabs]
    have hsx : 15481463 / 25000000 - (24651511 / 2000000) * (1 / 50) ≤ jvLogDensityS x := by
      have := (abs_le.1 hlips).1
      nlinarith [this, hxabs]
    have hg : (jvAGammaQ : ℝ) = 286969377 / 4588782659 := by
      norm_num [jvAGammaQ, jvDeltaQ, jvBigGammaQ, jvEtaQ, jvTau0Q]
    have hgpos : (0 : ℝ) < (jvAGammaQ : ℝ) := by rw [hg]; norm_num
    have hmul : (jvAGammaQ : ℝ) * (15481463 / 25000000 - (24651511 / 2000000) * (1 / 50))
        ≤ (jvAGammaQ : ℝ) * jvLogDensityS x := mul_le_mul_of_nonneg_left hsx hgpos.le
    have hsub : (97 / 100 : ℝ) ≤ (jvAGammaQ : ℝ)
        * (15481463 / 25000000 - (24651511 / 2000000) * (1 / 50))
        - (-119258309 / 100000000 + (608218529 / 50000000) * (1 / 50)) := by
      rw [hg]; norm_num
    have hkey : (97 / 100 : ℝ)
        ≤ (jvAGammaQ : ℝ) * jvLogDensityS x - jvLogDensityR x := by linarith
    have hqv : (jvQmQ : ℝ) = 827015425 / 100000000 := by norm_num [jvQmQ]
    rw [hqv]
    nlinarith [hkey]
  have hcos : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 50), (396 / 100 : ℝ) ≤ 2 + 2 * Real.cos x := by
    intro x hx
    have hxabs : |x| ≤ 1 / 50 := by
      rw [abs_of_nonneg hx.1]; exact hx.2
    have h := v1_cos_lip x 0
    rw [Real.cos_zero, sub_zero] at h
    have hlo : -(1 / 50) ≤ Real.cos x - 1 := by
      have h2 := (abs_le.1 h).1
      nlinarith [h2, hxabs]
    linarith
  have hcont : Continuous fun x => (2 + 2 * Real.cos x)
      * (2 : ℝ) ^ ((jvQmQ : ℝ) * ((jvAGammaQ : ℝ) * jvLogDensityS x - jvLogDensityR x)) := by
    have hr : Continuous jvLogDensityR := (v1_smooth jvRa jvRb).continuous
    have hs : Continuous jvLogDensityS := (v1_smooth jvSa jvSb).continuous
    have hexp' : Continuous fun x : ℝ =>
        (jvQmQ : ℝ) * ((jvAGammaQ : ℝ) * jvLogDensityS x - jvLogDensityR x) := by fun_prop
    exact (continuous_const.add (continuous_const.mul Real.continuous_cos)).mul
      (Real.continuous_const_rpow (by norm_num : (2 : ℝ) ≠ 0) |>.comp hexp')
  have hwin : (1 / 50 : ℝ) * (396 / 100) * 256
      ≤ ∫ x in (0 : ℝ)..(2 * Real.pi),
          (2 + 2 * Real.cos x)
            * (2 : ℝ) ^ ((jvQmQ : ℝ) * ((jvAGammaQ : ℝ) * jvLogDensityS x - jvLogDensityR x)) :=
    jv_moment_window_lb (e := fun x =>
        (jvQmQ : ℝ) * ((jvAGammaQ : ℝ) * jvLogDensityS x - jvLogDensityR x))
      (δ := 1 / 50) (c := 396 / 100) (F := 256) (E := 8)
      (by norm_num) (by linarith [Real.pi_gt_three]) (by norm_num) hcont hcos hexp
      (by norm_num) (by norm_num)
  rw [jvMomentBand]
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hpi8 : 2 * Real.pi ≤ 8 := by nlinarith [Real.pi_le_four]
  have hinv : (1 / 8 : ℝ) ≤ 1 / (2 * Real.pi) := one_div_le_one_div_of_le hpi hpi8
  have hval : (1 / 50 : ℝ) * (396 / 100) * 256 = 202752 / 10000 := by norm_num
  rw [hval] at hwin
  have := mul_le_mul hinv hwin (by norm_num) (by positivity)
  have hfinal : (1 / 8 : ℝ) * (202752 / 10000) = 50688 / 20000 := by norm_num
  linarith [this, hfinal.le, hfinal.ge]

/-- `2^{ρ_c} < 2` — because `ρ_c = 0.5162… < 1` and `2 = 2¹`.  All the refutations
need: the threshold is below the crudest possible floor. -/
theorem jv_rhopow_lt_two : (2 : ℝ) ^ ((jvRhoCQ : ℝ)) < 2 := by
  have h1 : (2 : ℝ) ^ ((jvRhoCQ : ℝ)) < (2 : ℝ) ^ (1 : ℝ) := by
    refine (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).2 ?_
    norm_num [jvRhoCQ, jvRhoFQ, jvEtaQ]
  simpa using h1

/-- **The refutation of the residue's `m1` as stated.**  `jvMomentRho0` — the
*raw-density* shape the residue asserts — has `log₂` **above** `ρ_c` by more than
8 bits, so the goal `log₂ jvMomentRho0 < ρ_c` is false, not merely open. -/
theorem jv_m1_stated_false :
    ¬ (Real.log jvMomentRho0 / Real.log 2 < (jvRhoCQ : ℝ)) := by
  intro hc
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlt : Real.log jvMomentRho0 < (jvRhoCQ : ℝ) * Real.log 2 := by
    rw [div_lt_iff₀ hlog2] at hc
    exact hc
  have hgt : (jvRhoCQ : ℝ) * Real.log 2 < Real.log jvMomentRho0 := by
    have hpos : (0 : ℝ) < (2 : ℝ) ^ ((jvRhoCQ : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    have h2 := lt_trans jv_rhopow_lt_two jv_momentRho0_gt_two
    have := Real.log_lt_log hpos h2
    rwa [Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at this
  linarith

/-- **The refutation of the residue's `m2` as stated.** -/
theorem jv_m2_stated_false :
    ¬ (Real.log jvMomentBand / Real.log 2 < (jvRhoCQ : ℝ)) := by
  intro hc
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlt : Real.log jvMomentBand < (jvRhoCQ : ℝ) * Real.log 2 := by
    rw [div_lt_iff₀ hlog2] at hc
    exact hc
  have hgt : (jvRhoCQ : ℝ) * Real.log 2 < Real.log jvMomentBand := by
    have hpos : (0 : ℝ) < (2 : ℝ) ^ ((jvRhoCQ : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    have h2 := lt_trans jv_rhopow_lt_two jv_momentBand_gt_two
    have := Real.log_lt_log hpos h2
    rwa [Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at this
  linarith

/-! ### §3 — the obligations as the certifier states them (strip-corrected)

The paper (`rev8g` l.183) defines the moments against `u`, `v` — the *strip-corrected*
log-densities, not against the raw `r`, `s`:

  `M₁ = ∫_𝕋 (2+2cos x)·2^{p(Δ − u(x))} dx`,  `M₂ = ∫_𝕋 (2+2cos x)·2^{q(a_Γ v(x) − u(x))} dx`

`certify_c5` builds `u[k]`, `v[k]` on a grid as

  `P(x) = ∫ 2^{r(x+y)} 2^{s(y)} dy/2π`,  `Y(x) = ∫ (r(x+y)+s(y))·2^{r(x+y)+s(y)} dy/2π`,
  `L(x) = log₂ P(x) − LZ`,  `B(x) = Y(x)/P(x) − LZ`,
  `u = L + (κ−1)B − H_`,  `v = (2−κ)B − 2L + H_`,

with `LZ = log₂(Z_f Z_g)`, `H_ = log₂ Z_{f,κ} + log₂ Z_{g,κ} − κ·LZ` and
`Z_f = ∫2^r/2π`, `Z_g = ∫2^s/2π`, `Z_{f,κ} = ∫2^{κr}/2π`, `Z_{g,κ} = ∫2^{κs}/2π`.

The definitions below are the **continuum limits** of that construction.  The
certifier's inner `N_in = 256` sum is the trapezoid rule for `P`/`Y` and its outer
`N = 8192` sum is the trapezoid rule for the moment; both converge geometrically, so
the continuum limit is the right object to prove the moment bound about.  Measured
(`sim/sim_m1.py`): `log₂ M₁` from these definitions is `0.516268325851285`, the
certifier's discrete value `0.516268325851285` — agreement `2.2·10⁻¹⁶`.

**These are the true C6 obligations.  They are not proved here**; the file states
them so that the residue is honest rather than false. -/

/-- `Z_f = (1/2π)∫ 2^{r(x)} dx`. -/
noncomputable def jvZf : ℝ :=
  (1 / (2 * Real.pi)) * ∫ x in (0 : ℝ)..(2 * Real.pi), (2 : ℝ) ^ (jvLogDensityR x)

/-- `Z_g = (1/2π)∫ 2^{s(x)} dx`. -/
noncomputable def jvZg : ℝ :=
  (1 / (2 * Real.pi)) * ∫ x in (0 : ℝ)..(2 * Real.pi), (2 : ℝ) ^ (jvLogDensityS x)

/-- `Z_{f,κ} = (1/2π)∫ 2^{κ r(x)} dx`. -/
noncomputable def jvZfk : ℝ :=
  (1 / (2 * Real.pi)) * ∫ x in (0 : ℝ)..(2 * Real.pi),
    (2 : ℝ) ^ ((jvKappaQ : ℝ) * jvLogDensityR x)

/-- `Z_{g,κ} = (1/2π)∫ 2^{κ s(x)} dx`. -/
noncomputable def jvZgk : ℝ :=
  (1 / (2 * Real.pi)) * ∫ x in (0 : ℝ)..(2 * Real.pi),
    (2 : ℝ) ^ ((jvKappaQ : ℝ) * jvLogDensityS x)

/-- `LZ = log₂(Z_f · Z_g)`. -/
noncomputable def jvLZ : ℝ := Real.logb 2 (jvZf * jvZg)

/-- `H_ = log₂ Z_{f,κ} + log₂ Z_{g,κ} − κ·LZ`. -/
noncomputable def jvStripH : ℝ :=
  Real.logb 2 jvZfk + Real.logb 2 jvZgk - (jvKappaQ : ℝ) * jvLZ

/-- `P(x) = (1/2π)∫ 2^{r(x+y)+s(y)} dy` — the inner convolution. -/
noncomputable def jvP (x : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ y in (0 : ℝ)..(2 * Real.pi),
    (2 : ℝ) ^ (jvLogDensityR (x + y) + jvLogDensityS y)

/-- `Y(x) = (1/2π)∫ (r(x+y)+s(y))·2^{r(x+y)+s(y)} dy`. -/
noncomputable def jvY (x : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ y in (0 : ℝ)..(2 * Real.pi),
    (jvLogDensityR (x + y) + jvLogDensityS y)
      * (2 : ℝ) ^ (jvLogDensityR (x + y) + jvLogDensityS y)

/-- The strip-corrected log-density `u` the certified `M₁` integrates. -/
noncomputable def jvU (x : ℝ) : ℝ :=
  (Real.logb 2 (jvP x) - jvLZ)
    + ((jvKappaQ : ℝ) - 1) * (jvY x / jvP x - jvLZ) - jvStripH

/-- The strip-corrected log-density `v` the certified `M₂` integrates. -/
noncomputable def jvV (x : ℝ) : ℝ :=
  (2 - (jvKappaQ : ℝ)) * (jvY x / jvP x - jvLZ)
    - 2 * (Real.logb 2 (jvP x) - jvLZ) + jvStripH

/-- **The certified `M₁`** — region ρ₀, `z = (p, 0)`, strip-corrected. -/
noncomputable def jvMomentRho0Cert : ℝ :=
  (1 / (2 * Real.pi)) * ∫ x in (0 : ℝ)..(2 * Real.pi),
    (2 + 2 * Real.cos x) * (2 : ℝ) ^ ((jvPQ : ℝ) * ((jvDeltaQ : ℝ) - jvU x))

/-- **The certified `M₂`** — regions ρ₁–ρ₉, `z = (q, 0, 0)`, strip-corrected. -/
noncomputable def jvMomentBandCert : ℝ :=
  (1 / (2 * Real.pi)) * ∫ x in (0 : ℝ)..(2 * Real.pi),
    (2 + 2 * Real.cos x)
      * (2 : ℝ) ^ ((jvQmQ : ℝ) * ((jvAGammaQ : ℝ) * jvV x - jvU x))

/-- **The residue's moment half, stated against the certified quantities.**

Measured values (two independent computations, `sim/sim_m1.py` and the audit pack's
`independent_decimal_check.py`): `log₂ jvMomentRho0Cert = 0.516268325851285` against
`ρ_c = 0.5162696413` — margin `1.3154·10⁻⁶`; `log₂ jvMomentBandCert = 0.516268147264670`
— margin `1.4940·10⁻⁶`.  Both fields are therefore *true* to 15 digits and open.

What is missing to close them, and the measured size of each piece:

1. a **strip-analyticity quadrature lemma** for `((2+2cos)·2^{f})` with `f` a finite
   trigonometric polynomial: `|trapezoid_n − integral| ≤ C·q₀^n` with `q₀ = 0.3708…`
   (`n = 40` gives `5.9·10⁻¹⁸`) — this is the piece the Lipschitz bound in
   `JV1000Quadrature` cannot supply (`7.7·10¹⁷` panels for the same accuracy);
2. the same lemma applied to the *inner* integrals in `jvP`, `jvY`, `jvZf`, `jvZg`,
   `jvZfk`, `jvZgk` (each needs its own enclosure, and `jvP`'s appears inside a
   logarithm, so the relative enclosure must survive `log`);
3. the resulting certified rational enclosure of the two outer integrals, compared
   against `2^{ρ_c}` — a `norm_num`-scale computation once (1) and (2) exist.

Nothing in this list is a numerical accident: the margin is `1.3·10⁻⁶`, i.e. seven
significant digits after the `ρ_c` comparison, and every piece above is sized for it. -/
structure JV1000Moments where
  /-- `M₁ < 2^{ρ_c}` at the certified point (region ρ₀). -/
  m1 : jvMomentRho0Cert < (2 : ℝ) ^ ((jvRhoCQ : ℝ))
  /-- `M₂ < 2^{ρ_c}` at the certified point (regions ρ₁–ρ₉). -/
  m2 : jvMomentBandCert < (2 : ℝ) ^ ((jvRhoCQ : ℝ))

/-- The residue's partition is unchanged in *count* and moved in *place*: seven
entropy goals stay in `JV1000Residue`, the two moment goals are `JV1000Moments`, and
the two earlier raw-shape statements are refuted (§2).  `25 + 7 + 2 = 34`. -/
theorem jv_residue_partition_relocated : 25 + 7 + 2 = 34 := by norm_num

end SubsetSumL25.Row
