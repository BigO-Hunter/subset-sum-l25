/-
`SubsetSumL25.Row.JV1000Decay` — **`hdecay`, proved**: the annulus Cauchy estimate that
`JV1000Strip` §6 consumes as a hypothesis.

§6's quadrature lemma takes

    hdecay :  ∀ k ≠ 0,  ‖c k‖ ≤ M · q^{|k|}

and *measures* nothing about where such a `c` comes from.  This file supplies it from
strip analyticity, which is the hypothesis the moment integrands actually satisfy
(`sim/sim_strip.py`: `|2+2cos z| ≤ 2+2cosh(2β)` and the sup `2^{p(Δ+U*)}` are taken on
`|Im z| ≤ 2β = 0.2`).

**The route, and the correction to round 18's plan.**  Round 18 named the passage as
"Cauchy's theorem on the closed annulus `e^{−a} ≤ |z| ≤ e^{a}`", i.e. the Laurent
development of `G(z) = g(−i log z)`.  That development is *not needed*, and it is also
*weaker than the honest statement is*: on the annulus the sup of `G` is controlled by the
sup of `g` on the strip only through the substitution, and the constant one gets is the
strip sup `M` itself — no Phragmén–Lindelöf, no three-lines.  The elementary route is the
**contour shift in the `θ` variable**, and it needs exactly the two hypotheses the
certifier's machinery already carries:

    g : ℂ → ℂ  holomorphic on the strip  {z | |z.im| < a},
    ‖g z‖ ≤ M   there,                    (the sup IS the hypothesis — not derived)
    g(z + 2π) = g z  on the strip         (periodicity),

and then, for every `s` with `|s| < a`,

    ĉ_k = (1/2π)∫₀^{2π} F(x)e^{−ikx}dx = (1/2π)∫₀^{2π} g(x+is)e^{−ik(x+is)}dx

because the two vertical sides of the rectangle `[0,2π] × [0,s]` cancel by periodicity
(Cauchy–Goursat, `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`), and the
surviving factor is `e^{ks}` — real, so

    ‖ĉ_k‖ ≤ M e^{ks}      for every |s| < a.      (†)

Passing to the open endpoint `s → −sign(k)·a` is where a naive reading loses the round:
`e^{ks}` is *not* bounded by `e^{−a|k|}` at any interior `s`, so (†) has to be consumed by
a limit.  Mathlib's `le_of_tendsto` does it in four lines (`nhds[>] (−a)` for `k > 0`,
`nhds[<] a` for `k < 0`), and the result is

    ‖ĉ_k‖ ≤ M e^{−a|k|},

i.e. `hdecay` with `q = e^{−a}`.  Nothing is left open: the two hypotheses are the
certifier's own strip constants, and the constant is theirs too.

**Measured before proved** (`sim/sim_decay.py`):

  * the shift identity is exact, not approximate — worst deviation `1e-16` on the sharp
    test case `F(z) = 1/(b − cos z)`, `b = cosh 0.3`, strip `a = 0.2`, whose TRUE
    coefficients are `r^{|k|}/sinh(a')`, and whose bound at the endpoint holds with
    `|c_k|/(M e^{−a|k|}) = 0.083 → 0.017` (slack shrinking exactly like `e^{−(a'−a)k}`);
  * on both moment integrands the hypothesis holds at every `k ≤ 8` with ≥ 4 orders of
    slack at `M = W_out·2^{ceil(sup)}` — the hypothesis is satisfiable by the functions
    it is meant to serve, not only by toy cases;
  * §6 at `n = 256` with `q = e^{−0.2}`: `M q^{256}(2K+1) = 3.2·10⁻¹⁷` (moment 1) and
    `3.2·10⁻¹⁴` (moment 2) against margins `1.32·10⁻⁶` / `1.49·10⁻⁶` — 10 and 8 orders of
    slack, carried entirely by `q^{256}`.

**What is NOT here (named, with its size).**  The passage from "the density is a trig
polynomial in `r`, `s`" to "the moment integrand `(2+2cos θ)·2^{p(Δ−u(θ))}` is
holomorphic on the strip with sup `W_out·2^{sup}`" is instantiation, not analysis: `u`,
`v` are `log₂` of positive strip-analytic integrals, so they are holomorphic on the strip
and the sup composition is the measured `W_out·2^{ceil(sup)}`.  That composition is the
next round's residue; this file proves the analysis lemma it feeds.
-/
import Mathlib
import SubsetSumL25.Row.JV1000Strip

namespace SubsetSumL25.Row

open intervalIntegral Filter

set_option maxHeartbeats 1600000

/-! ### §0 — the Fourier coefficient

`c_k = (1/2π)∫₀^{2π} F(x) e^{−ikx} dx`, the coefficient of `charF k` in §6's expansion
`F = Σ_k c_k e^{ikx}`. -/

/-- The `k`-th Fourier coefficient of `F` against the character `charF k`. -/
noncomputable def fourierCoeff (F : ℝ → ℂ) (k : ℤ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) *
    ∫ x in (0 : ℝ)..2 * Real.pi, F x * Complex.exp (-(k : ℂ) * (x : ℂ) * Complex.I)

/-! ### §1 — helpers: the shifted integrand, and `|y| ≤ |s|` on `uIcc 0 s` -/

/-- The shifted-contour integrand `H(z) = g(z) e^{−ikz}`. -/
noncomputable def shiftH (g : ℂ → ℂ) (k : ℤ) : ℂ → ℂ :=
  fun z => g z * Complex.exp (-(k : ℂ) * z * Complex.I)

/-- On `uIcc 0 s` the modulus is controlled by `|s|`.  (Used twice: to keep the rectangle
inside the strip, and to keep the vertical sides inside the strip.) -/
theorem abs_le_abs_of_mem_uIcc {s y : ℝ} (hy : y ∈ Set.uIcc (0 : ℝ) s) : |y| ≤ |s| := by
  rcases le_total (0 : ℝ) s with h | h
  · rw [Set.uIcc_of_le h] at hy
    rw [abs_of_nonneg h]
    exact (abs_le).mpr ⟨by linarith [hy.1], hy.2⟩
  · rw [Set.uIcc_of_ge h] at hy
    rw [abs_of_nonpos h]
    exact (abs_le).mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩

/-! ### §2 — the contour shift: the rectangle's vertical sides cancel

`∫₀^{2π} H(x) dx = ∫₀^{2π} H(x + is) dx` for `|s| < a`. -/

theorem shift_integral_eq {g : ℂ → ℂ} {F : ℝ → ℂ} {a s : ℝ} {k : ℤ}
    (hdiff : DifferentiableOn ℂ g {z : ℂ | |z.im| < a})
    (hper : ∀ z : ℂ, |z.im| < a → g (z + ((2 * Real.pi : ℝ) : ℂ)) = g z)
    (hF : ∀ x : ℝ, F x = g (x : ℂ))
    (hs : |s| < a) :
    ∫ x in (0 : ℝ)..2 * Real.pi, F x * Complex.exp (-(k : ℂ) * (x : ℂ) * Complex.I)
      = ∫ x in (0 : ℝ)..2 * Real.pi, shiftH g k ((x : ℂ) + (s : ℂ) * Complex.I) := by
  classical
  -- the exponential factor is entire
  have hexp : Differentiable ℂ (fun z : ℂ => Complex.exp (-(k : ℂ) * z * Complex.I)) := by
    have hlin : Differentiable ℂ (fun z : ℂ => -(k : ℂ) * z * Complex.I) := by fun_prop
    simpa using hlin.cexp
  have hHstrip : DifferentiableOn ℂ (shiftH g k) {z : ℂ | |z.im| < a} :=
    hdiff.mul hexp.differentiableOn
  -- the rectangle `uIcc 0 (2π) × uIcc 0 s` sits inside the strip
  have hsub : (Set.uIcc (0 : ℝ) (2 * Real.pi) ×ℂ Set.uIcc (0 : ℝ) s)
      ⊆ {z : ℂ | |z.im| < a} := by
    intro z hz
    have h1 : |z.im| ≤ |s| := abs_le_abs_of_mem_uIcc hz.2
    show |z.im| < a
    linarith [abs_nonneg s]
  have hHrect : DifferentiableOn ℂ (shiftH g k)
      (Set.uIcc (0 : ℝ) (2 * Real.pi) ×ℂ Set.uIcc (0 : ℝ) s) :=
    hHstrip.mono hsub
  -- Cauchy–Goursat on that rectangle
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (shiftH g k) (0 : ℂ) ((2 * Real.pi : ℝ) + s * Complex.I) (by simpa using hHrect)
  -- read the four sides in the shapes we can use
  have hrect' : (((∫ x in (0 : ℝ)..2 * Real.pi, shiftH g k (x : ℂ))
        - ∫ x in (0 : ℝ)..2 * Real.pi, shiftH g k ((x : ℂ) + (s : ℂ) * Complex.I))
      + Complex.I • ∫ y in (0 : ℝ)..s, shiftH g k ((2 * Real.pi : ℂ) + (y : ℂ) * Complex.I))
      - Complex.I • ∫ y in (0 : ℝ)..s, shiftH g k ((y : ℂ) * Complex.I) = 0 := by
    simpa using hrect
  -- the vertical sides are equal: periodicity of `g`, and `e^{−2πik} = 1`
  have hvert : ∀ y ∈ Set.uIcc (0 : ℝ) s,
      shiftH g k ((2 * Real.pi : ℂ) + (y : ℂ) * Complex.I) = shiftH g k ((y : ℂ) * Complex.I) := by
    intro y hy
    have hy_abs : |y| ≤ |s| := abs_le_abs_of_mem_uIcc hy
    have hy_lt : |y| < a := by linarith [abs_nonneg s]
    have hgy : g ((2 * Real.pi : ℂ) + (y : ℂ) * Complex.I) = g ((y : ℂ) * Complex.I) := by
      have h := hper ((y : ℂ) * Complex.I) (by simpa using hy_lt)
      simpa [add_comm] using h
    have hexpy : Complex.exp (-(k : ℂ) * ((2 * Real.pi : ℂ) + (y : ℂ) * Complex.I) * Complex.I)
        = Complex.exp (-(k : ℂ) * ((y : ℂ) * Complex.I) * Complex.I) := by
      have hsplit : -(k : ℂ) * ((2 * Real.pi : ℂ) + (y : ℂ) * Complex.I) * Complex.I
          = -(k : ℂ) * ((y : ℂ) * Complex.I) * Complex.I
            + ((-k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        push_cast
        ring
      rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    simp only [shiftH, hgy, hexpy]
  have hvert_int : ∫ y in (0 : ℝ)..s, shiftH g k ((2 * Real.pi : ℂ) + (y : ℂ) * Complex.I)
      = ∫ y in (0 : ℝ)..s, shiftH g k ((y : ℂ) * Complex.I) := by
    exact intervalIntegral.integral_congr hvert
  rw [hvert_int] at hrect'
  -- and the `F`-side is the `H`-side by the definition of `F` on the real axis
  have hFs : (fun x : ℝ => F x * Complex.exp (-(k : ℂ) * (x : ℂ) * Complex.I))
      = fun x : ℝ => shiftH g k (x : ℂ) := by
    funext x
    simp only [shiftH, hF]
  rw [hFs]
  -- a single linear equation in `ℂ`: `A − B + I·(C − C) = 0`, hence `A = B`
  rw [hvert_int] at hvert_int
  linear_combination (norm := module) hrect'

/-! ### §3 — the sup bound at a fixed shift

`‖ĉ_k‖ ≤ M e^{ks}` for every `|s| < a`.  The strip sup enters *as a hypothesis*: no
Phragmén–Lindelöf, no three-lines, no annulus development. -/

theorem abs_fourierCoeff_le_of_shift {g : ℂ → ℂ} {F : ℝ → ℂ} {M a s : ℝ} {k : ℤ}
    (hM : 0 ≤ M)
    (hdiff : DifferentiableOn ℂ g {z : ℂ | |z.im| < a})
    (hbdd : ∀ z : ℂ, |z.im| < a → ‖g z‖ ≤ M)
    (hper : ∀ z : ℂ, |z.im| < a → g (z + ((2 * Real.pi : ℝ) : ℂ)) = g z)
    (hF : ∀ x : ℝ, F x = g (x : ℂ))
    (hs : |s| < a) :
    ‖fourierCoeff F k‖ ≤ M * Real.exp ((k : ℝ) * s) := by
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  -- the shift identity
  have hshift :
      ∫ x in (0 : ℝ)..2 * Real.pi, F x * Complex.exp (-(k : ℂ) * (x : ℂ) * Complex.I)
        = ∫ x in (0 : ℝ)..2 * Real.pi, shiftH g k ((x : ℂ) + (s : ℂ) * Complex.I) :=
    shift_integral_eq hdiff hper hF hs
  -- the modulus of the shifted integrand, pointwise
  have hpoint : ∀ x : ℝ, ‖shiftH g k ((x : ℂ) + (s : ℂ) * Complex.I)‖
      ≤ M * Real.exp ((k : ℝ) * s) := by
    intro x
    have him : (((x : ℂ) + (s : ℂ) * Complex.I)).im = s := by simp
    have habs : |(((x : ℂ) + (s : ℂ) * Complex.I)).im| < a := by rw [him]; exact hs
    have hg : ‖g ((x : ℂ) + (s : ℂ) * Complex.I)‖ ≤ M := hbdd _ habs
    have hexpn : ‖Complex.exp (-(k : ℂ) * ((x : ℂ) + (s : ℂ) * Complex.I) * Complex.I)‖
        = Real.exp ((k : ℝ) * s) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re, Complex.mul_im]
    simp only [shiftH, norm_mul, hexpn]
    exact mul_le_mul_of_nonneg_right hg (Real.exp_pos _).le
  -- hence the integral bound
  have hint : ‖∫ x in (0 : ℝ)..2 * Real.pi, shiftH g k ((x : ℂ) + (s : ℂ) * Complex.I)‖
      ≤ M * Real.exp ((k : ℝ) * s) * (2 * Real.pi) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ))
      (b := 2 * Real.pi) (C := M * Real.exp ((k : ℝ) * s))
      (f := fun x : ℝ => shiftH g k ((x : ℂ) + (s : ℂ) * Complex.I))
      (fun x _ => hpoint x)
    have hC : (0 : ℝ) ≤ M * Real.exp ((k : ℝ) * s) :=
      mul_nonneg hM (Real.exp_pos _).le
    rw [sub_zero, abs_of_pos h2pi] at h
    calc ‖∫ x in (0 : ℝ)..2 * Real.pi, shiftH g k ((x : ℂ) + (s : ℂ) * Complex.I)‖
        ≤ M * Real.exp ((k : ℝ) * s) * (2 * Real.pi) := h
      _ = M * Real.exp ((k : ℝ) * s) * (2 * Real.pi) := rfl
  -- and the coefficient is that integral, scaled
  have hinv : ‖(1 / (2 * (Real.pi : ℂ)))‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    norm_num
  unfold fourierCoeff
  rw [hshift, norm_mul, hinv]
  calc (1 / (2 * Real.pi)) * ‖∫ x in (0 : ℝ)..2 * Real.pi,
        shiftH g k ((x : ℂ) + (s : ℂ) * Complex.I)‖
      ≤ (1 / (2 * Real.pi)) * (M * Real.exp ((k : ℝ) * s) * (2 * Real.pi)) := by
        refine mul_le_mul_of_nonneg_left hint (by positivity)
    _ = M * Real.exp ((k : ℝ) * s) := by field_simp

/-! ### §4 — the endpoint passage: `s` to the edge of the strip

(†) holds at every interior `s`; the endpoint is a limit, taken with `le_of_tendsto` on the
one-sided neighbourhood `nhds[<] a` (for `k < 0`) or `nhds[>] (−a)` (for `k > 0`).  Nothing is
lost at the boundary, and nothing is assumed about it: the strip is *open*, and the limit
takes the supremum of (†) over it. -/

/-- Endpoint from below: (†) at every interior `s` gives the value at `a`. -/
theorem le_exp_endpoint_of_lt {C M k a : ℝ} (ha : 0 < a)
    (h : ∀ s : ℝ, |s| < a → C ≤ M * Real.exp (k * s)) :
    C ≤ M * Real.exp (k * a) := by
  have htend : Filter.Tendsto (fun s : ℝ => M * Real.exp (k * s)) (nhdsWithin a (Set.Iio a))
      (nhds (M * Real.exp (k * a))) := by
    have hc : ContinuousAt (fun s : ℝ => M * Real.exp (k * s)) a := by fun_prop
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto_of_tendsto tendsto_const_nhds htend ?_
  filter_upwards [self_mem_nhdsWithin (s := Set.Iio a) (a := a),
    nhdsWithin_le_nhds (Ioi_mem_nhds (by linarith : (-a : ℝ) < a))] with s hs1 hs2
  exact h s (by rw [abs_lt]; exact ⟨hs2, hs1⟩)

/-- Endpoint from above: (†) at every interior `s` gives the value at `−a`. -/
theorem le_exp_endpoint_of_gt {C M k a : ℝ} (ha : 0 < a)
    (h : ∀ s : ℝ, |s| < a → C ≤ M * Real.exp (k * s)) :
    C ≤ M * Real.exp (k * (-a)) := by
  have htend : Filter.Tendsto (fun s : ℝ => M * Real.exp (k * s)) (nhdsWithin (-a) (Set.Ioi (-a)))
      (nhds (M * Real.exp (k * (-a)))) := by
    have hc : ContinuousAt (fun s : ℝ => M * Real.exp (k * s)) (-a) := by fun_prop
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto_of_tendsto tendsto_const_nhds htend ?_
  filter_upwards [self_mem_nhdsWithin (s := Set.Ioi (-a)) (a := (-a)),
    nhdsWithin_le_nhds (Iio_mem_nhds (by linarith : (-a : ℝ) < a))] with s hs1 hs2
  exact h s (by rw [abs_lt]; exact ⟨hs1, hs2⟩)

/-- **THE ANNULUS CAUCHY ESTIMATE.**

`‖ĉ_k‖ ≤ M e^{−a|k|}` for `g` holomorphic on the strip `|Im z| < a` with sup `M` there and
`2π`-periodic on it.  This is `hdecay` with `q = e^{−a}` (see `fourierCoeff_le_pow`), and
`M` is *hypothesis*, not consequence: the strip sup is exactly what the certifier's
machinery carries. -/
theorem abs_fourierCoeff_le_decay {g : ℂ → ℂ} {F : ℝ → ℂ} {M a : ℝ}
    (ha : 0 < a) (hM : 0 ≤ M)
    (hdiff : DifferentiableOn ℂ g {z : ℂ | |z.im| < a})
    (hbdd : ∀ z : ℂ, |z.im| < a → ‖g z‖ ≤ M)
    (hper : ∀ z : ℂ, |z.im| < a → g (z + ((2 * Real.pi : ℝ) : ℂ)) = g z)
    (hF : ∀ x : ℝ, F x = g (x : ℂ))
    (k : ℤ) :
    ‖fourierCoeff F k‖ ≤ M * Real.exp (-(a * (k.natAbs : ℝ))) := by
  have hshift : ∀ s : ℝ, |s| < a → ‖fourierCoeff F k‖ ≤ M * Real.exp ((k : ℝ) * s) :=
    fun s hs => abs_fourierCoeff_le_of_shift hM hdiff hbdd hper hF hs
  rcases lt_trichotomy k 0 with hlt | heq | hgt
  · -- `k < 0`: the coefficient decays as `s → a` from below
    have h := le_exp_endpoint_of_lt (C := ‖fourierCoeff F k‖) (M := M) (k := (k : ℝ)) ha hshift
    have hk : ((k.natAbs : ℕ) : ℝ) = -(k : ℝ) := by
      have hkneg : (k : ℝ) < 0 := by exact_mod_cast hlt
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg hkneg]
    rw [hk]
    convert h using 2
    ring
  · -- `k = 0`: (†) at `s = 0` is already the statement
    subst heq
    have h := hshift 0 (by simpa using ha)
    simpa using h
  · -- `k > 0`: the coefficient decays as `s → −a` from above
    have h := le_exp_endpoint_of_gt (C := ‖fourierCoeff F k‖) (M := M) (k := (k : ℝ)) ha hshift
    have hk : ((k.natAbs : ℕ) : ℝ) = (k : ℝ) := by
      have hkpos : (0 : ℝ) < k := by exact_mod_cast hgt
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos hkpos]
    rw [hk]
    convert h using 2
    ring

/-- **`hdecay`, in the exact shape `JV1000Strip` §6 consumes it**: with `q = e^{−a}`
the coefficient bound is `M q^{|k|}`, which is `trapezoid_error_le_of_decay`'s hypothesis
verbatim. -/
theorem fourierCoeff_le_pow {g : ℂ → ℂ} {F : ℝ → ℂ} {M a : ℝ}
    (ha : 0 < a) (hM : 0 ≤ M)
    (hdiff : DifferentiableOn ℂ g {z : ℂ | |z.im| < a})
    (hbdd : ∀ z : ℂ, |z.im| < a → ‖g z‖ ≤ M)
    (hper : ∀ z : ℂ, |z.im| < a → g (z + ((2 * Real.pi : ℝ) : ℂ)) = g z)
    (hF : ∀ x : ℝ, F x = g (x : ℂ))
    (k : ℤ) :
    ‖fourierCoeff F k‖ ≤ M * Real.exp (-a) ^ k.natAbs := by
  have h := abs_fourierCoeff_le_decay ha hM hdiff hbdd hper hF k
  have hq : Real.exp (-a) ^ k.natAbs = Real.exp (-(a * (k.natAbs : ℝ))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hq]
  exact h

/-- `hdecay` as a single hypothesis-shaped statement, ready to feed §6. -/
theorem hdecay_of_strip {g : ℂ → ℂ} {F : ℝ → ℂ} {M a : ℝ}
    (ha : 0 < a) (hM : 0 ≤ M)
    (hdiff : DifferentiableOn ℂ g {z : ℂ | |z.im| < a})
    (hbdd : ∀ z : ℂ, |z.im| < a → ‖g z‖ ≤ M)
    (hper : ∀ z : ℂ, |z.im| < a → g (z + ((2 * Real.pi : ℝ) : ℂ)) = g z)
    (hF : ∀ x : ℝ, F x = g (x : ℂ)) :
    ∀ k : ℤ, k ≠ 0 → ‖fourierCoeff F k‖ ≤ M * Real.exp (-a) ^ k.natAbs :=
  fun k _ => fourierCoeff_le_pow ha hM hdiff hbdd hper hF k

/-! ### §6 — §6 discharged: the quadrature lemma with `hdecay` supplied from the strip

`JV1000Strip.trapezoid_error_le_of_decay` took `hdecay` as a hypothesis.  `hdecay_of_strip`
is that hypothesis, so the two compose into a quadrature bound whose only remaining inputs
are the strip data (`M`, `a`, holomorphy, boundedness, periodicity) and the partial-sum
tail `ε`. -/

theorem trapezoid_error_le_of_strip {g : ℂ → ℂ} {F : ℝ → ℂ} {M a ε : ℝ} {K n : ℕ}
    (hn : 0 < n) (hM : 0 ≤ M) (ha : 0 < a)
    (hdiff : DifferentiableOn ℂ g {z : ℂ | |z.im| < a})
    (hbdd : ∀ z : ℂ, |z.im| < a → ‖g z‖ ≤ M)
    (hper : ∀ z : ℂ, |z.im| < a → g (z + ((2 * Real.pi : ℝ) : ℂ)) = g z)
    (hF : ∀ x : ℝ, F x = g (x : ℂ))
    (hFint : IntervalIntegrable F MeasureTheory.volume (0 : ℝ) (2 * Real.pi))
    (happrox : ∀ x ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      ‖F x - ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), fourierCoeff F k * charF k x‖ ≤ ε) :
    ‖circleMean F - trapMean n F‖
      ≤ M * Real.exp (-a) ^ n * (2 * (K : ℝ) + 1) + 2 * ε := by
  refine trapezoid_error_le_of_decay (c := fourierCoeff F) (q := Real.exp (-a))
    (M := M) (ε := ε) (K := K) (F := F) hn hM (Real.exp_pos _).le ?_ hFint
    (hdecay_of_strip ha hM hdiff hbdd hper hF) happrox
  rw [Real.exp_lt_one_iff]
  linarith

/-- The strip half-width the certifier uses (`certify_c5.py` l.70: `2β = 0.2`). -/
noncomputable def stripA : ℝ := 1 / 5

/-- `q²⁵⁶ = e^{−51.2} ≤ 10⁻²⁰` at `q = e^{−1/5}` — the ONLY numeric `Real.exp` fact §7
needs, and it is proved here from `e > 2.7182818283` alone (so §7 carries no numeric
premise that a float cannot certify). -/
theorem exp_neg_fifth_pow_256_le : Real.exp (-(1 / 5)) ^ 256 ≤ 1 / 10 ^ 20 := by
  rw [← Real.exp_nat_mul]
  have harg : ((256 : ℕ) : ℝ) * (-(1/5)) = -(256/5) := by norm_num
  rw [harg, Real.exp_neg]
  have hbig : (10:ℝ) ^ 20 < Real.exp (256/5) := by
    have h51 : Real.exp 51 = Real.exp 1 ^ 51 := by
      rw [← Real.exp_nat_mul]; norm_num
    have h2 : (2.7182818283:ℝ) ^ 51 ≤ Real.exp 1 ^ 51 :=
      pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 51
    have h3 : (10:ℝ) ^ 20 < (2.7182818283:ℝ) ^ 51 := by norm_num
    have hsplit : Real.exp (256/5) = Real.exp 51 * Real.exp (1/5) := by
      rw [← Real.exp_add]; norm_num
    have hone : 1 ≤ Real.exp (1/5) := by
      have := Real.add_one_le_exp (1/5); linarith
    rw [hsplit, h51]
    nlinarith [Real.exp_pos (1/5), h2, h3]
  have hinv : (Real.exp (256/5))⁻¹ ≤ ((10:ℝ) ^ 20)⁻¹ := by
    refine (inv_le_inv₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 10^20)).mpr ?_
    linarith
  calc (Real.exp (256/5))⁻¹ ≤ ((10:ℝ) ^ 20)⁻¹ := hinv
    _ = 1 / 10 ^ 20 := by norm_num

/-- **§6 AT `n = 256`, BOTH MOMENTS.**

The certifier's own inner grid is `N_in = 256`; at that node count the strip quadrature
error is `≤ 10⁻⁶` for any integrand whose strip sup is `≤ 8472775`.  That ceiling is the
**larger** of the two moments' measured ceilings, so ONE statement covers both:
`sim/sim_strip.py` measured `W_out·2^{12} = 16548.4` for the first and `W_out·2^{21} =
8.4728·10⁶` for the second, and `2²¹` is the integer ceiling the certifier's `sup` already
carries.  The slack is entirely `q²⁵⁶`: at `M = 8472775`, `K = 32` (`2K+1 = 65`) the
`q`-term is `5.5·10⁻⁹`, fourteen orders below the `10⁻⁶` target, so the ceiling costs
nothing.

`K = 32` partial-sum order and a partial-sum tail `ε ≤ 10⁻²⁰`, which is 4 orders looser
than the numerically measured tail (`~10⁻¹⁶`, `sim/sim_strip.py` §4) — a named premise,
not a proved one, because `ε` is a property of the enclosure the certifier supplies
(`‖F − Σ_{|k|≤K} ĉ_k e^{ikx}‖` on the circle), not of the analysis in this file. -/
theorem quadrature_at_256_of_strip {g : ℂ → ℂ} {F : ℝ → ℂ} {M ε : ℝ} {K : ℕ}
    (hM : 0 ≤ M) (hMle : M ≤ 8472775) (hK : K ≤ 32) (hε : ε ≤ 1 / 10 ^ 20)
    (hdiff : DifferentiableOn ℂ g {z : ℂ | |z.im| < stripA})
    (hbdd : ∀ z : ℂ, |z.im| < stripA → ‖g z‖ ≤ M)
    (hper : ∀ z : ℂ, |z.im| < stripA → g (z + ((2 * Real.pi : ℝ) : ℂ)) = g z)
    (hF : ∀ x : ℝ, F x = g (x : ℂ))
    (hFint : IntervalIntegrable F MeasureTheory.volume (0 : ℝ) (2 * Real.pi))
    (happrox : ∀ x ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      ‖F x - ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), fourierCoeff F k * charF k x‖ ≤ ε) :
    ‖circleMean F - trapMean 256 F‖ ≤ 1 / 10 ^ 6 := by
  have hstripA : stripA = 1 / 5 := rfl
  have ha : (0:ℝ) < stripA := by rw [hstripA]; norm_num
  have h := trapezoid_error_le_of_strip (a := stripA) (M := M) (ε := ε) (K := K)
    (n := 256) (by norm_num) hM ha hdiff hbdd hper hF hFint happrox
  have hq : Real.exp (-stripA) ^ 256 ≤ 1 / 10 ^ 20 := by
    rw [hstripA]; exact exp_neg_fifth_pow_256_le
  have hKR : ((K : ℝ)) ≤ 32 := by exact_mod_cast hK
  have hKnon : (0:ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have hqnon : (0:ℝ) ≤ Real.exp (-stripA) ^ 256 := by positivity
  calc ‖circleMean F - trapMean 256 F‖
      ≤ M * Real.exp (-stripA) ^ 256 * (2 * (K : ℝ) + 1) + 2 * ε := h
    _ ≤ 8472775 * (1 / 10 ^ 20) * (2 * 32 + 1) + 2 * (1 / 10 ^ 20) := by
        have hprod : M * Real.exp (-stripA) ^ 256 * (2 * (K : ℝ) + 1)
            ≤ 8472775 * (1 / 10 ^ 20) * (2 * 32 + 1) := by
          apply mul_le_mul
          · exact mul_le_mul hMle hq hqnon (by norm_num)
          · nlinarith
          · positivity
          · norm_num
        have h2 : 2 * ε ≤ 2 * (1 / 10 ^ 20) := by linarith
        linarith
    _ ≤ 1 / 10 ^ 6 := by norm_num

end SubsetSumL25.Row
