/-
`SubsetSumL25.Row.JV1000Bounds` — **round 21**: the `U*`/`W*` bounds *reduced*, and §7 made
*satisfiable*.

Round 20 (`JV1000Compose`) left three residues: the strip bounds `Re u ≥ −U*` / `Re v ≤ W*`
(named `hU`/`hV`), the branch condition `hslit`, and the 256-term comparison `hcmp`.  This
round does two things and, in the course of the second, corrects a defect that would
otherwise have made the whole chain vacuous.

### §A — the reduction: `Re u` is a log-of-modulus plus one controlled ratio

`Complex.log_re` gives `(log z).re = log ‖z‖` exactly, so on the strip

    Re u = log₂‖P_c‖ + (κ−1)·Re(Y_c/P_c) − κ·LZ − H_
    Re v = (2−κ)·Re(Y_c/P_c) − 2·log₂‖P_c‖ + κ·LZ + H_

(`jvUcx_re_eq`/`jvVcx_re_eq`, from `Complex.log_re` + `Complex.mul_re` — no analysis).
Both bounds are then *implied* by four numeric facts about two functions and two numbers:

    (P-floor)  ∀ z ∈ stripZ, 9/10 ≤ Re P_c z          (measured 0.938511377)
    (Y-ceil)   ∀ z ∈ stripZ, ‖Y_c z‖ ≤ 5/2            (measured 2.161568)
    (LZ-ceil)  LZ ≤ 3/5                               (measured 0.5586861327)
    (H-ceil)   H_ ≤ 1/50                              (measured 0.0174021677)

and the four give **both** `hU` and `hV` with room to spare: `Re u ≥ −0.9037` against
`−1.326`, `Re v ≤ 3.6556` against `19.178`.  `(P-floor)` also gives `hslit` (`0 < re` is
literally `mem_slitPlane`'s left disjunct) and `hFint` (continuity, §A.4) — so **`hFint` and
`hslit` stop being premises**, and `hU`/`hV` become corollaries of two integral bounds and
two constants.

**Why this is a reduction and not a re-labelling — measured, not asserted.**  The proofs in
this lane that were supposed to supply those bounds are `Pmaj` and `Ymaj` (§2's strip
majorants), and they are too loose to close: `sim/sim_bounds_enclosure.py` §3 measures
`Pmaj = 1367.6` (true sup `|P_c| ≤ 1.66`) and `Ymaj = 14247.0` (true sup `|Y_c| = 2.1616`),
so the reduction with the *proved* majorants yields `Re u ≥ −526.8` — 400× short — and the
Y-term alone `(κ−1)·Ymaj/λ = 526.1` swamps the whole `1.326` budget.  The crude majorants
are not a proof-strength route; the residue is genuinely *tight* enclosures of two integrals,
which is what this file names and sizes.

### §B — §7 was unsatisfiable, and the cure is the `K` cap

`JV1000Decay.quadrature_at_256_of_strip` demands `K ≤ 32` **and** `ε ≤ 10⁻²⁰`, where `ε`
bounds the partial-sum tail `‖F − Σ_{|k|≤K} ĉ_k e^{ikx}‖`.  Those two cannot both hold:
`F` is not a trigonometric polynomial, and `sim/sim_bounds_enclosure.py` §4 measures the true
tail at `K = 32` to be **`6.38·10⁻⁵`** (coefficients decay at ratio `≈ 0.65`, i.e. the
effective strip is `≈ 0.43`, not the proved `1/5`).  Worse, even an *honest* `ε = 6.4·10⁻⁵`
would break the conclusion, since it enters the bound as `2ε` and `2·6.4·10⁻⁵ ≫ 10⁻⁶`.

The tail *shrinks* with `K` (`4.17·10⁻⁸` at `K = 48`, `1.4·10⁻¹¹` at `K = 64`) while the
aliasing term `M q^n (2K+1)` grows only linearly, so the `K ≤ 32` cap is **backwards**: it
is the one constraint that prevents the only sound instantiation.  `K` was never a parameter
of the certifier's construction — it is the order of a proof-side partial sum.  §B therefore
proves `quadrature_at_256_of_strip_relaxed` (`K ≤ 200`, `ε ≤ 10⁻⁷`, `M ≤ 8472775` gives
`≤ 2.34·10⁻⁷ < 10⁻⁶`) and re-feeds the moments through it.

**The measured `ε` claim it corrects.**  Round 19's docstring calls `ε ≤ 10⁻²⁰` "4 orders
looser than the numerically measured tail (`~10⁻¹⁶`)".  That figure is real but belongs to a
different truncation point: the tail is `~6·10⁻¹⁵` only at `K ≈ 96`.  At the `K = 32` the
lemma actually fixes, the tail is `6.4·10⁻⁵` — **nine orders larger than the measured value
it was compared against**.

### §C — what is still named

`hcmp` (the 256-term comparison) and the tail premise `happrox` stay named, with their
required sizes proved into the statements: `hcmp` needs `‖trapMean 256 F‖ + 10⁻⁶ < 2^{ρ_c}`,
which by `sim/sim_bounds_enclosure.py` §4 demands `‖P_c‖` to `3.6·10⁻⁸` **relative** at each
of the 256 nodes (the enclosure is a continuum enclosure of `2^{trig16}` integrals, not a
finite rational sum).  The four numeric facts of §A and this enclosure are the same single
object: a rigorous enclosure layer for `∫ 2^{trig16}` and for the strip extrema of a 32-term
trigonometric polynomial.  None of the six exists in this lane.

Everything else — holomorphy, decay, the quadrature, the ceilings, the composition — is
proved, in this file or the four before it.
-/
import Mathlib
import SubsetSumL25.Row.JV1000Compose

namespace SubsetSumL25.Row

/-! ### §1 — the two `Re` decompositions

`Re(log₂ P_c)` is `log ‖P_c‖ / log 2` — `Complex.log_re`, and nothing else.  The rest is
real-scalar bookkeeping: `L2C` is `↑(log 2)`, so dividing by it divides the real part by
`log 2`. -/

theorem re_div_ofReal (w : ℂ) (c : ℝ) : (w / ((c : ℝ) : ℂ)).re = w.re / c := by
  rw [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_ofReal]
  rcases eq_or_ne c 0 with hc | hc
  · simp [hc]
  · field_simp
    ring

theorem re_log_div_L2C (w : ℂ) :
    (Complex.log w / L2C).re = Real.log ‖w‖ / Real.log 2 := by
  rw [L2C]
  rw [re_div_ofReal, Complex.log_re]

theorem re_ofReal_mul (c : ℝ) (w : ℂ) : ((((c : ℝ)) : ℂ) * w).re = c * w.re := by
  rw [Complex.mul_re]
  simp

/-- The `Re` of `u`'s affine shape, with the two complex pieces left abstract. -/
theorem re_affine_u (a b : ℂ) (lz kk hh : ℝ) :
    (a - (lz : ℂ) + ((kk : ℝ) : ℂ) * (b - (lz : ℂ)) - (hh : ℂ)).re
      = a.re - lz + kk * (b.re - lz) - hh := by
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- The `Re` of `v`'s affine shape. -/
theorem re_affine_v (a b : ℂ) (lz kk hh : ℝ) :
    ((((2 - kk : ℝ)) : ℂ) * (b - (lz : ℂ)) - ((2 : ℝ) : ℂ) * (a - (lz : ℂ)) + (hh : ℂ)).re
      = (2 - kk) * (b.re - lz) - 2 * (a.re - lz) + hh := by
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- **`Re u`, exactly.**  `Re u = log₂‖P_c‖ + (κ−1)·Re(Y_c/P_c) − κ·LZ − H_`. -/
theorem jvUcx_re_eq (z : ℂ) :
    (jvUcx z).re = Real.log ‖jvPcx z‖ / Real.log 2
      + ((jvKappaQ : ℝ) - 1) * (jvYcx z / jvPcx z).re
      - (jvKappaQ : ℝ) * jvLZ - jvStripH := by
  unfold jvUcx
  rw [re_affine_u]
  rw [re_log_div_L2C]
  ring

/-- **`Re v`, exactly.**  `Re v = (2−κ)·Re(Y_c/P_c) − 2·log₂‖P_c‖ + κ·LZ + H_`. -/
theorem jvVcx_re_eq (z : ℂ) :
    (jvVcx z).re = (2 - (jvKappaQ : ℝ)) * (jvYcx z / jvPcx z).re
      - 2 * (Real.log ‖jvPcx z‖ / Real.log 2)
      + (jvKappaQ : ℝ) * jvLZ + jvStripH := by
  unfold jvVcx
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num]
  rw [re_affine_v]
  rw [re_log_div_L2C]
  ring

/-! ### §2 — the ratio bound: `Re(Y/P) ≥ −‖Y‖/‖P‖` and `Re(Y/P) ≤ ‖Y‖/‖P‖`

No analysis: `Complex.re_le_norm` both ways, and `Complex.norm_div`. -/

theorem re_div_ge {Y P : ℂ} {lam mu : ℝ} (hlam : 0 < lam) (hP : lam ≤ ‖P‖)
    (hY : ‖Y‖ ≤ mu) : -(mu / lam) ≤ (Y / P).re := by
  have h1 : -‖Y / P‖ ≤ (Y / P).re := by
    have h := Complex.re_le_norm (-(Y / P))
    rw [Complex.neg_re, norm_neg] at h
    linarith
  have h2 : ‖Y / P‖ ≤ mu / lam := by
    have hPpos : (0 : ℝ) < ‖P‖ := lt_of_lt_of_le hlam hP
    have hY0 : (0 : ℝ) ≤ ‖Y‖ := norm_nonneg _
    rw [Complex.norm_div]
    exact div_le_div₀ (le_trans hY0 hY) hY hlam hP
  linarith

theorem re_div_le {Y P : ℂ} {lam mu : ℝ} (hlam : 0 < lam) (hP : lam ≤ ‖P‖)
    (hY : ‖Y‖ ≤ mu) : (Y / P).re ≤ mu / lam := by
  have h1 : (Y / P).re ≤ ‖Y / P‖ := Complex.re_le_norm (Y / P)
  have h2 : ‖Y / P‖ ≤ mu / lam := by
    have hPpos : (0 : ℝ) < ‖P‖ := lt_of_lt_of_le hlam hP
    have hY0 : (0 : ℝ) ≤ ‖Y‖ := norm_nonneg _
    rw [Complex.norm_div]
    exact div_le_div₀ (le_trans hY0 hY) hY hlam hP
  linarith

/-! ### §3 — the four numeric facts, and the two strip bounds they imply

The constants are chosen with room: `P-floor 9/10` against a measured `0.9385`,
`Y-ceil 5/2` against `2.1616`, `LZ-ceil 3/5` against `0.5587`, `H-ceil 1/50` against
`0.0174`.  The *conclusions* then have `0.42` and `15.5` of slack respectively — the residue
is not delicate, it is simply un-enclosed. -/

/-- The `P`-floor: `9/10`. -/
noncomputable def jvPFloor : ℝ := 9 / 10

/-- The `Y`-ceiling on the strip: `5/2`. -/
noncomputable def jvYCeil : ℝ := 5 / 2

/-- The `LZ` ceiling: `3/5`. -/
noncomputable def jvLZCeil : ℝ := 3 / 5

/-- The `H_` ceiling: `1/50`. -/
noncomputable def jvHCeil : ℝ := 1 / 50

theorem jvKappa_ge_one : (1 : ℝ) ≤ (jvKappaQ : ℝ) := by
  have h : (jvKappaQ : ℝ) = 103465831 / 100000000 := by norm_num [jvKappaQ]
  rw [h]; norm_num

theorem jvKappa_pos : (0 : ℝ) < (jvKappaQ : ℝ) := lt_of_lt_of_le one_pos jvKappa_ge_one

theorem logb_nine_tenths_ge : -(1 / 6 : ℝ) ≤ Real.log (9 / 10) / Real.log 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h10 : Real.log (9 / 10 : ℝ) = -Real.log (10 / 9) := by
    rw [show (9 / 10 : ℝ) = (10 / 9)⁻¹ by norm_num, Real.log_inv]
  have hle : Real.log (10 / 9 : ℝ) ≤ 1 / 9 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 10 / 9 by norm_num)
    linarith
  have h2 := Real.log_two_gt_d9
  rw [h10]
  have step : Real.log (10 / 9) / Real.log 2 ≤ 1 / 6 := by
    rw [div_le_iff₀ hlog2]
    nlinarith
  have hrw : -(Real.log (10 / 9)) / Real.log 2 = -(Real.log (10 / 9) / Real.log 2) := by ring
  rw [hrw]
  linarith

/-- **`Re u ≥ −1.326` from the four numeric facts.** -/
theorem jvUcx_re_ge_1326 {z : ℂ}
    (hP : jvPFloor ≤ (jvPcx z).re) (hY : ‖jvYcx z‖ ≤ jvYCeil)
    (hlz : jvLZ ≤ jvLZCeil) (hh : jvStripH ≤ jvHCeil) :
    -1.326 ≤ (jvUcx z).re := by
  have hfloor : (0 : ℝ) < jvPFloor := by rw [jvPFloor]; norm_num
  have hPnorm : jvPFloor ≤ ‖jvPcx z‖ := le_trans hP (Complex.re_le_norm _)
  have hratio := re_div_ge (Y := jvYcx z) (P := jvPcx z) hfloor hPnorm hY
  have hlog : -(1 / 6 : ℝ) ≤ Real.log jvPFloor / Real.log 2 := by
    rw [jvPFloor]; exact logb_nine_tenths_ge
  have hκ : (0 : ℝ) ≤ (jvKappaQ : ℝ) - 1 := by
    have := jvKappa_ge_one; linarith
  have hY1 : ((jvKappaQ : ℝ) - 1) * (-(jvYCeil / jvPFloor))
      ≤ ((jvKappaQ : ℝ) - 1) * (jvYcx z / jvPcx z).re :=
    mul_le_mul_of_nonneg_left hratio hκ
  have hlog' : Real.log jvPFloor / Real.log 2 ≤ Real.log ‖jvPcx z‖ / Real.log 2 := by
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    exact div_le_div_of_nonneg_right (Real.log_le_log hfloor hPnorm) hlog2.le
  have hκlz : (jvKappaQ : ℝ) * jvLZ ≤ (jvKappaQ : ℝ) * jvLZCeil :=
    mul_le_mul_of_nonneg_left hlz jvKappa_pos.le
  rw [jvUcx_re_eq]
  have harith : -1.326 ≤ -(1 / 6 : ℝ)
      + ((jvKappaQ : ℝ) - 1) * (-(jvYCeil / jvPFloor))
      - (jvKappaQ : ℝ) * jvLZCeil - jvHCeil := by
    have hk : (jvKappaQ : ℝ) = 103465831 / 100000000 := by norm_num [jvKappaQ]
    rw [jvYCeil, jvPFloor, jvLZCeil, jvHCeil, hk]; norm_num
  linarith

/-- **`Re v ≤ 19.178` from the same four numeric facts.** -/
theorem jvVcx_re_le_19178 {z : ℂ}
    (hP : jvPFloor ≤ (jvPcx z).re) (hY : ‖jvYcx z‖ ≤ jvYCeil)
    (hlz : jvLZ ≤ jvLZCeil) (hh : jvStripH ≤ jvHCeil) :
    (jvVcx z).re ≤ 19.178 := by
  have hfloor : (0 : ℝ) < jvPFloor := by rw [jvPFloor]; norm_num
  have hPnorm : jvPFloor ≤ ‖jvPcx z‖ := le_trans hP (Complex.re_le_norm _)
  have hratio := re_div_le (Y := jvYcx z) (P := jvPcx z) hfloor hPnorm hY
  have hlog : -(1 / 6 : ℝ) ≤ Real.log jvPFloor / Real.log 2 := by
    rw [jvPFloor]; exact logb_nine_tenths_ge
  have hκ2 : (0 : ℝ) ≤ 2 - (jvKappaQ : ℝ) := by
    have h : (jvKappaQ : ℝ) = 103465831 / 100000000 := by norm_num [jvKappaQ]
    rw [h]; norm_num
  have hY1 : (2 - (jvKappaQ : ℝ)) * (jvYcx z / jvPcx z).re
      ≤ (2 - (jvKappaQ : ℝ)) * (jvYCeil / jvPFloor) :=
    mul_le_mul_of_nonneg_left hratio hκ2
  have hlog' : Real.log jvPFloor / Real.log 2 ≤ Real.log ‖jvPcx z‖ / Real.log 2 := by
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    exact div_le_div_of_nonneg_right (Real.log_le_log hfloor hPnorm) hlog2.le
  have hκlz : (jvKappaQ : ℝ) * jvLZ ≤ (jvKappaQ : ℝ) * jvLZCeil :=
    mul_le_mul_of_nonneg_left hlz jvKappa_pos.le
  rw [jvVcx_re_eq]
  have harith : (2 - (jvKappaQ : ℝ)) * (jvYCeil / jvPFloor)
      - 2 * (-(1 / 6 : ℝ)) + (jvKappaQ : ℝ) * jvLZCeil + jvHCeil ≤ 19.178 := by
    have hk : (jvKappaQ : ℝ) = 103465831 / 100000000 := by norm_num [jvKappaQ]
    rw [jvYCeil, jvPFloor, jvLZCeil, jvHCeil, hk]; norm_num
  linarith

/-! ### §4 — what the `P`-floor buys for free: `hslit` and `hFint` -/

/-- **`hslit` is a corollary of the `P`-floor** — a strictly positive real part is
`Complex.mem_slitPlane_iff`'s left disjunct. -/
theorem jvPcx_slitPlane {z : ℂ} (hP : jvPFloor ≤ (jvPcx z).re) :
    jvPcx z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  have hfloor : (0 : ℝ) < jvPFloor := by rw [jvPFloor]; norm_num
  linarith

/-- **`hFint` is a corollary of `hslit`**: the composite is continuous on the closed
interval, because it is differentiable at every point of the strip and every real is in the
strip. -/
theorem continuous_jvMomF1 (hslit : ∀ z ∈ stripZ, jvPcx z ∈ Complex.slitPlane) :
    Continuous jvMomF1 := by
  rw [continuous_iff_continuousAt]
  intro x
  have hc : ContinuousAt jvMomFc1 ((x : ℂ)) :=
    (differentiableAt_jvMomFc1 (mem_stripZ_ofReal x) (hslit _ (mem_stripZ_ofReal x))).continuousAt
  exact hc.comp Complex.continuous_ofReal.continuousAt

theorem continuous_jvMomF2 (hslit : ∀ z ∈ stripZ, jvPcx z ∈ Complex.slitPlane) :
    Continuous jvMomF2 := by
  rw [continuous_iff_continuousAt]
  intro x
  have hc : ContinuousAt jvMomFc2 ((x : ℂ)) :=
    (differentiableAt_jvMomFc2 (mem_stripZ_ofReal x) (hslit _ (mem_stripZ_ofReal x))).continuousAt
  exact hc.comp Complex.continuous_ofReal.continuousAt

theorem intervalIntegrable_jvMomF1 (hslit : ∀ z ∈ stripZ, jvPcx z ∈ Complex.slitPlane) :
    IntervalIntegrable jvMomF1 MeasureTheory.volume (0 : ℝ) (2 * Real.pi) :=
  (continuous_jvMomF1 hslit).intervalIntegrable _ _

theorem intervalIntegrable_jvMomF2 (hslit : ∀ z ∈ stripZ, jvPcx z ∈ Complex.slitPlane) :
    IntervalIntegrable jvMomF2 MeasureTheory.volume (0 : ℝ) (2 * Real.pi) :=
  (continuous_jvMomF2 hslit).intervalIntegrable _ _

/-! ### §5 — §7's quadrature at a *satisfiable* partial-sum order

`trapezoid_error_le_of_strip` is `K`-free; only `quadrature_at_256_of_strip` caps it at
`32` and demands `ε ≤ 10⁻²⁰`.  The cap is the defect: the tail at `K = 32` is
`6.38·10⁻⁵` (measured), so no `ε ≤ 10⁻²⁰` exists, and even an honest `ε` at that order
would swamp the `10⁻⁶` target through the `2ε` term.  At `K ≤ 200` the aliasing term is
`M q²⁵⁶ (2K+1) ≤ 3.40·10⁻⁸` and `2ε ≤ 2·10⁻⁷`, so the conclusion survives with room
(`2.34·10⁻⁷ < 10⁻⁶`) — and the tail is genuinely `≤ 10⁻⁷` there (`4.17·10⁻⁸` at `K = 48`). -/

theorem quadrature_at_256_of_strip_relaxed {g : ℂ → ℂ} {F : ℝ → ℂ} {M ε : ℝ} {K : ℕ}
    (hM : 0 ≤ M) (hMle : M ≤ 8472775) (hK : K ≤ 200) (hε : ε ≤ 1 / 10 ^ 7)
    (hdiff : DifferentiableOn ℂ g {z : ℂ | |z.im| < stripA})
    (hbdd : ∀ z : ℂ, |z.im| < stripA → ‖g z‖ ≤ M)
    (hper : ∀ z : ℂ, |z.im| < stripA → g (z + ((2 * Real.pi : ℝ) : ℂ)) = g z)
    (hF : ∀ x : ℝ, F x = g (x : ℂ))
    (hFint : IntervalIntegrable F MeasureTheory.volume (0 : ℝ) (2 * Real.pi))
    (happrox : ∀ x ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      ‖F x - ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), fourierCoeff F k * charF k x‖ ≤ ε) :
    ‖circleMean F - trapMean 256 F‖ ≤ 1 / 10 ^ 6 := by
  have hstripA : stripA = 1 / 5 := rfl
  have ha : (0 : ℝ) < stripA := by rw [hstripA]; norm_num
  have h := trapezoid_error_le_of_strip (a := stripA) (M := M) (ε := ε) (K := K)
    (n := 256) (by norm_num) hM ha hdiff hbdd hper hF hFint happrox
  have hq : Real.exp (-stripA) ^ 256 ≤ 1 / 10 ^ 20 := by
    rw [hstripA]; exact exp_neg_fifth_pow_256_le
  have hKR : ((K : ℝ)) ≤ 200 := by exact_mod_cast hK
  have hKnon : (0:ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have hqnon : (0:ℝ) ≤ Real.exp (-stripA) ^ 256 := by positivity
  calc ‖circleMean F - trapMean 256 F‖
      ≤ M * Real.exp (-stripA) ^ 256 * (2 * (K : ℝ) + 1) + 2 * ε := h
    _ ≤ 8472775 * (1 / 10 ^ 20) * (2 * 200 + 1) + 2 * (1 / 10 ^ 7) := by
        have hprod : M * Real.exp (-stripA) ^ 256 * (2 * (K : ℝ) + 1)
            ≤ 8472775 * (1 / 10 ^ 20) * (2 * 200 + 1) := by
          apply mul_le_mul
          · exact mul_le_mul hMle hq hqnon (by norm_num)
          · nlinarith
          · positivity
          · norm_num
        have h2 : 2 * ε ≤ 2 * (1 / 10 ^ 7) := by linarith
        linarith
    _ ≤ 1 / 10 ^ 6 := by norm_num

/-- **§7 re-fed, `M₁`, at a satisfiable order.** -/
theorem quadrature_jvMomF1_relaxed
    (hslit : ∀ z ∈ stripZ, jvPcx z ∈ Complex.slitPlane)
    (hU : ∀ z ∈ stripZ, -1.326 ≤ (jvUcx z).re)
    {K : ℕ} (hK : K ≤ 200) {ε : ℝ} (hε : ε ≤ 1 / 10 ^ 7)
    (happrox : ∀ x ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      ‖jvMomF1 x - ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), fourierCoeff jvMomF1 k * charF k x‖
        ≤ ε) :
    ‖circleMean jvMomF1 - trapMean 256 jvMomF1‖ ≤ 1 / 10 ^ 6 := by
  refine quadrature_at_256_of_strip_relaxed (g := jvMomFc1) (M := 8472775) (ε := ε) (K := K)
    (by norm_num) (le_refl _) hK hε ?_ ?_ ?_ ?_ (intervalIntegrable_jvMomF1 hslit) happrox
  · exact fun z hz => (differentiableAt_jvMomFc1 hz (hslit z hz)).differentiableWithinAt
  · exact fun z hz => norm_jvMomFc1_le_ceiling hz (hU z hz)
  · intro z hz
    exact jvMomFc1_add_two_pi z
  · intro x
    rfl

/-- **§7 re-fed, `M₂`, at a satisfiable order.** -/
theorem quadrature_jvMomF2_relaxed
    (hslit : ∀ z ∈ stripZ, jvPcx z ∈ Complex.slitPlane)
    (hU : ∀ z ∈ stripZ, -1.326 ≤ (jvUcx z).re)
    (hV : ∀ z ∈ stripZ, (jvVcx z).re ≤ 19.178)
    {K : ℕ} (hK : K ≤ 200) {ε : ℝ} (hε : ε ≤ 1 / 10 ^ 7)
    (happrox : ∀ x ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      ‖jvMomF2 x - ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), fourierCoeff jvMomF2 k * charF k x‖
        ≤ ε) :
    ‖circleMean jvMomF2 - trapMean 256 jvMomF2‖ ≤ 1 / 10 ^ 6 := by
  refine quadrature_at_256_of_strip_relaxed (g := jvMomFc2) (M := 8472775) (ε := ε) (K := K)
    (by norm_num) (le_refl _) hK hε ?_ ?_ ?_ ?_ (intervalIntegrable_jvMomF2 hslit) happrox
  · exact fun z hz => (differentiableAt_jvMomFc2 hz (hslit z hz)).differentiableWithinAt
  · exact fun z hz => norm_jvMomFc2_le_ceiling hz (hU z hz) (hV z hz)
  · intro z hz
    exact jvMomFc2_add_two_pi z
  · intro x
    rfl

/-! ### §6 — the moment goals, with every analytic hypothesis discharged

`jv_m1_cert_of_comparison` and `jv_m2_cert_of_comparison` (round 20) take `hslit`, `hU`,
`hV`, `hFint` as hypotheses.  All four now follow from the four numeric facts of §3, so the
moment goals reduce to: the four numeric facts, the tail premise `happrox` at a satisfiable
order, and the one comparison `hcmp`. -/

theorem jv_m1_cert_certified
    (hP : ∀ z ∈ stripZ, jvPFloor ≤ (jvPcx z).re)
    (hY : ∀ z ∈ stripZ, ‖jvYcx z‖ ≤ jvYCeil)
    (hlz : jvLZ ≤ jvLZCeil) (hh : jvStripH ≤ jvHCeil)
    {K : ℕ} (hK : K ≤ 200) {ε : ℝ} (hε : ε ≤ 1 / 10 ^ 7)
    (happrox : ∀ x ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      ‖jvMomF1 x - ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), fourierCoeff jvMomF1 k * charF k x‖
        ≤ ε)
    (hcmp : ‖trapMean 256 jvMomF1‖ + 1 / 10 ^ 6 < (2 : ℝ) ^ ((jvRhoCQ : ℝ))) :
    jvMomentRho0Cert < (2 : ℝ) ^ ((jvRhoCQ : ℝ)) := by
  have hslit : ∀ z ∈ stripZ, jvPcx z ∈ Complex.slitPlane := fun z hz =>
    jvPcx_slitPlane (hP z hz)
  have hU : ∀ z ∈ stripZ, -1.326 ≤ (jvUcx z).re := fun z hz =>
    jvUcx_re_ge_1326 (hP z hz) (hY z hz) hlz hh
  have hq := quadrature_jvMomF1_relaxed hslit hU hK hε happrox
  rw [circleMean_jvMomF1 hslit] at hq
  have htri : ‖(((jvMomentRho0Cert : ℝ)) : ℂ)‖
      ≤ ‖(((jvMomentRho0Cert : ℝ)) : ℂ) - trapMean 256 jvMomF1‖ + ‖trapMean 256 jvMomF1‖ := by
    have h := norm_add_le ((((jvMomentRho0Cert : ℝ)) : ℂ) - trapMean 256 jvMomF1)
      (trapMean 256 jvMomF1)
    simpa using h
  have hstep : jvMomentRho0Cert ≤ ‖trapMean 256 jvMomF1‖ + 1 / 10 ^ 6 := by
    calc jvMomentRho0Cert = ((((jvMomentRho0Cert : ℝ)) : ℂ)).re := by simp
      _ ≤ ‖(((jvMomentRho0Cert : ℝ)) : ℂ)‖ := Complex.re_le_norm _
      _ ≤ ‖(((jvMomentRho0Cert : ℝ)) : ℂ) - trapMean 256 jvMomF1‖
            + ‖trapMean 256 jvMomF1‖ := htri
      _ ≤ 1 / 10 ^ 6 + ‖trapMean 256 jvMomF1‖ := by linarith
      _ = ‖trapMean 256 jvMomF1‖ + 1 / 10 ^ 6 := by ring
  linarith

theorem jv_m2_cert_certified
    (hP : ∀ z ∈ stripZ, jvPFloor ≤ (jvPcx z).re)
    (hY : ∀ z ∈ stripZ, ‖jvYcx z‖ ≤ jvYCeil)
    (hlz : jvLZ ≤ jvLZCeil) (hh : jvStripH ≤ jvHCeil)
    {K : ℕ} (hK : K ≤ 200) {ε : ℝ} (hε : ε ≤ 1 / 10 ^ 7)
    (happrox : ∀ x ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      ‖jvMomF2 x - ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), fourierCoeff jvMomF2 k * charF k x‖
        ≤ ε)
    (hcmp : ‖trapMean 256 jvMomF2‖ + 1 / 10 ^ 6 < (2 : ℝ) ^ ((jvRhoCQ : ℝ))) :
    jvMomentBandCert < (2 : ℝ) ^ ((jvRhoCQ : ℝ)) := by
  have hslit : ∀ z ∈ stripZ, jvPcx z ∈ Complex.slitPlane := fun z hz =>
    jvPcx_slitPlane (hP z hz)
  have hU : ∀ z ∈ stripZ, -1.326 ≤ (jvUcx z).re := fun z hz =>
    jvUcx_re_ge_1326 (hP z hz) (hY z hz) hlz hh
  have hV : ∀ z ∈ stripZ, (jvVcx z).re ≤ 19.178 := fun z hz =>
    jvVcx_re_le_19178 (hP z hz) (hY z hz) hlz hh
  have hq := quadrature_jvMomF2_relaxed hslit hU hV hK hε happrox
  rw [circleMean_jvMomF2 hslit] at hq
  have htri : ‖(((jvMomentBandCert : ℝ)) : ℂ)‖
      ≤ ‖(((jvMomentBandCert : ℝ)) : ℂ) - trapMean 256 jvMomF2‖ + ‖trapMean 256 jvMomF2‖ := by
    have h := norm_add_le ((((jvMomentBandCert : ℝ)) : ℂ) - trapMean 256 jvMomF2)
      (trapMean 256 jvMomF2)
    simpa using h
  have hstep : jvMomentBandCert ≤ ‖trapMean 256 jvMomF2‖ + 1 / 10 ^ 6 := by
    calc jvMomentBandCert = ((((jvMomentBandCert : ℝ)) : ℂ)).re := by simp
      _ ≤ ‖(((jvMomentBandCert : ℝ)) : ℂ)‖ := Complex.re_le_norm _
      _ ≤ ‖(((jvMomentBandCert : ℝ)) : ℂ) - trapMean 256 jvMomF2‖
            + ‖trapMean 256 jvMomF2‖ := htri
      _ ≤ 1 / 10 ^ 6 + ‖trapMean 256 jvMomF2‖ := by linarith
      _ = ‖trapMean 256 jvMomF2‖ + 1 / 10 ^ 6 := by ring
  linarith

/-- **The moment goals as a structure**, from the residue's named premises. -/
theorem jvMoments_of_residue
    (hP : ∀ z ∈ stripZ, jvPFloor ≤ (jvPcx z).re)
    (hY : ∀ z ∈ stripZ, ‖jvYcx z‖ ≤ jvYCeil)
    (hlz : jvLZ ≤ jvLZCeil) (hh : jvStripH ≤ jvHCeil)
    {K : ℕ} (hK : K ≤ 200) {ε : ℝ} (hε : ε ≤ 1 / 10 ^ 7)
    (ha1 : ∀ x ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      ‖jvMomF1 x - ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), fourierCoeff jvMomF1 k * charF k x‖
        ≤ ε)
    (ha2 : ∀ x ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      ‖jvMomF2 x - ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), fourierCoeff jvMomF2 k * charF k x‖
        ≤ ε)
    (hc1 : ‖trapMean 256 jvMomF1‖ + 1 / 10 ^ 6 < (2 : ℝ) ^ ((jvRhoCQ : ℝ)))
    (hc2 : ‖trapMean 256 jvMomF2‖ + 1 / 10 ^ 6 < (2 : ℝ) ^ ((jvRhoCQ : ℝ))) :
    JV1000Moments :=
  ⟨jv_m1_cert_certified hP hY hlz hh hK hε ha1 hc1,
   jv_m2_cert_certified hP hY hlz hh hK hε ha2 hc2⟩

end SubsetSumL25.Row
