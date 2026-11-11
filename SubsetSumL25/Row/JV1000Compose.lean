/-
`SubsetSumL25.Row.JV1000Compose` — **the composition passage**, round 20.

Round 19 (`JV1000Decay`) proved `hdecay` from strip analyticity and discharged §6 at
`n = 256`.  What that file named and did not write is the *instantiation*: the moments
`M₁`, `M₂` are integrals of

    F₁(θ) = (2 + 2cos θ) · 2^{p(Δ − u(θ))},      F₂(θ) = (2 + 2cos θ) · 2^{q(a_Γ v(θ) − u(θ))}

and `u`, `v` are not the raw log-densities `r`, `s` — they are `log₂` of the strip-analytic
integrals `P`, `Y` (`JV1000Moments` §3, the continuum limit of `certify_c5`'s construction).
The quadrature lemma's hypotheses are about `F` as a function of a **complex** argument:
holomorphic on `|Im z| < 1/5`, bounded there by `M`, `2π`-periodic.  So the passage from
"`u` is a `log₂` of integrals" to "§6 applies" is a composition, and this file writes it.

**The five pieces, and which are proved where.**

1. **The ℂ-lift of the densities** (§1).  `r`, `s` are `trig16` — finite cosine/sine sums in
   a real variable — so their analytic continuations are `jvRcx`, `jvScx` (§1), *entire*, with
   `2π`-periodicity and real-axis agreement proved.  The modulus bound on the strip is the
   certifier's own majorant `S(co, t) = Σ_j (|a_j| + |b_j|) cosh(j·t)` (`certify_c5.py` l.28,
   `sim/sim_strip.py` `S`), and it is proved here from `‖cos z‖ ≤ cosh z.im`, itself proved
   from `Complex.cos_eq` — the sharp bound, not the lossy `|re| + |im|` one, because `W_out`
   below carries **no slack** (§5's ceiling is `⌈W_out · 2²¹⌉` and `W_out·2²¹ = 8472774.07`).
2. **The strip-analytic integrals** (§2).  `jvPcx`, `jvYcx` — the definitions, real-axis
   agreement, and `2π`-periodicity.  Their *holomorphy* is the named premise `hPY`.
3. **The `log₂` shapes** (§3).  `jvUcx`, `jvVcx` written exactly as `jvU`/`jvV` with
   `Complex.log` in place of `Real.logb`, and their **holomorphy proved** from `hPY` +
   `P` landing in `Complex.slitPlane` (the branch-cut condition — `Complex.differentiableAt_log`).
4. **The composite integrand** (§4).  Holomorphy proved (`exp` of a holomorphic function is
   entire — no branch survives into the composite), sup proved, periodicity proved,
   real-axis agreement proved.
5. **Feeding §6** (§5).  `quadrature_at_256_of_strip` instantiated at the two moments, and
   `M ≤ 8472775` discharged from the certifier's own integer ceilings.

**What is measured before it is proved** (`sim/sim_compose.py`; run before any Lean):

  * `P_c` maps the strip into the **open right half-plane**: `min Re P_c = 0.9385 > 0`,
    `max |P_c| = 1.6606`, and `Im P_c` never changes sign where `Re P_c < 0` — so the log's
    branch cut is never crossed, and `slitPlane` holds by a margin of `0.94`;
  * `Re u_c ∈ [−0.6939, +0.1813]` and `Re v_c ∈ [0.3774, 0.6117]` on the strip against the
    certifier's `U* = 1.3258`, `W* = 19.1773` — its bounds are **conservative**, so `U*`/`W*`
    may be used verbatim;
  * the composite sup on the strip is `2.78` (`M₁`) and `2.65` (`M₂`), against the ceilings
    `W_out·2¹² = 16548.4` and `W_out·2²¹ = 8472774.07`: the ceiling is ≥10⁶× loose, and the
    measured sup is reached at `Im z = ±0.2` (the strip edge, where `|2+2cos z|` is largest);
  * the sup is **not** attained where `Re u` peaks — `u` is smallest near `θ = π`, where the
    weight `2+2cos θ` vanishes — which is why §4 bounds the product and not each factor.

**The residue after this file** (named, with sizes): `hPY` (P, Y holomorphic on the strip —
each an interval integral of an entire integrand, the one piece this round bounds rather than
proves), the strip bounds `Re u ≥ −U*` / `Re v ≤ W*` (measured above, 1.9× / 30× conservative),
and the **rational comparison** `‖trapMean 256 F‖ + 10⁻⁶ < 2^{ρ_c}` — a statement about 256
elementary terms, which is what `JV1000Moments` §3 called "norm_num-scale".  With those three,
`jvMomentRho0Cert < 2^{ρ_c}` is `jv_m1_cert_of_comparison` below: no analysis left.
-/
import Mathlib
import SubsetSumL25.Row.JV1000Decay

namespace SubsetSumL25.Row

open MeasureTheory intervalIntegral Complex Filter

set_option maxHeartbeats 1600000

/-! ### §0 — the strip as a set, and its openness

`stripA = 1/5` is `JV1000Decay`'s strip half-width (the certifier's `2β = 0.2`).  The
composition needs the set, not only the number: `DifferentiableOn` is stated on it, and
`DifferentiableAt` at each of its points is extracted from it. -/

/-- The open strip `|Im z| < 1/5` the moment integrand must be holomorphic on. -/
noncomputable def stripZ : Set ℂ := {z : ℂ | |z.im| < stripA}

theorem stripA_pos : (0 : ℝ) < stripA := by
  rw [show stripA = 1 / 5 from rfl]; norm_num

theorem stripA_le_fifth : stripA ≤ 1 / 5 := le_of_eq rfl

theorem isOpen_stripZ : IsOpen stripZ := by
  have hcont : Continuous fun z : ℂ => |z.im| := continuous_abs.comp Complex.continuous_im
  exact isOpen_lt hcont continuous_const

theorem stripZ_mem_nhds {z : ℂ} (hz : z ∈ stripZ) : stripZ ∈ nhds z :=
  isOpen_stripZ.mem_nhds hz

/-! ### §1 — the ℂ-lift of `trig16`

`r = trig16 a b` is a finite sum of `a_j cos(jx) + b_j sin(jx)`; its analytic continuation
replaces `x : ℝ` by `z : ℂ`.  Everything the composition needs about it is proved here:
real-axis agreement (for `hF`), `2π`-periodicity (for `hper`), differentiability (for the
chain rule), and the strip majorant (for `hbdd`). -/

/-- The complexified `trig16`: the same finite sum, evaluated at a complex argument. -/
noncomputable def trig16c (a b : ℕ → ℝ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.Icc (1 : ℕ) 16,
    ((a j : ℂ) * Complex.cos ((j : ℂ) * z) + (b j : ℂ) * Complex.sin ((j : ℂ) * z))

/-- The analytic continuation of the certified log-density `r`. -/
noncomputable def jvRcx : ℂ → ℂ := trig16c jvRa jvRb

/-- The analytic continuation of the certified log-density `s`. -/
noncomputable def jvScx : ℂ → ℂ := trig16c jvSa jvSb

/-- **Real-axis agreement**: on `ℝ` the continuation is `trig16`, i.e. `r`. -/
theorem trig16c_ofReal (a b : ℕ → ℝ) (x : ℝ) :
    trig16c a b (x : ℂ) = (trig16 a b x : ℂ) := by
  unfold trig16c trig16
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  norm_cast

theorem jvRcx_ofReal (x : ℝ) : jvRcx (x : ℂ) = (jvLogDensityR x : ℂ) :=
  trig16c_ofReal jvRa jvRb x

theorem jvScx_ofReal (x : ℝ) : jvScx (x : ℂ) = (jvLogDensityS x : ℂ) :=
  trig16c_ofReal jvSa jvSb x

/-- **`2π`-periodicity** of the continuation, term by term. -/
theorem trig16c_add_two_pi (a b : ℕ → ℝ) (z : ℂ) :
    trig16c a b (z + ((2 * Real.pi : ℝ) : ℂ)) = trig16c a b z := by
  unfold trig16c
  refine Finset.sum_congr rfl fun j _ => ?_
  have hcos : Complex.cos ((j : ℂ) * (z + ((2 * Real.pi : ℝ) : ℂ)))
      = Complex.cos ((j : ℂ) * z) := by
    have hsplit : (j : ℂ) * (z + ((2 * Real.pi : ℝ) : ℂ))
        = (j : ℂ) * z + (j : ℤ) * (2 * (Real.pi : ℂ)) := by push_cast; ring
    rw [hsplit, Complex.cos_add_int_mul_two_pi]
  have hsin : Complex.sin ((j : ℂ) * (z + ((2 * Real.pi : ℝ) : ℂ)))
      = Complex.sin ((j : ℂ) * z) := by
    have hsplit : (j : ℂ) * (z + ((2 * Real.pi : ℝ) : ℂ))
        = (j : ℂ) * z + (j : ℤ) * (2 * (Real.pi : ℂ)) := by push_cast; ring
    rw [hsplit, Complex.sin_add_int_mul_two_pi]
  rw [hcos, hsin]

theorem jvRcx_add_two_pi (z : ℂ) : jvRcx (z + ((2 * Real.pi : ℝ) : ℂ)) = jvRcx z :=
  trig16c_add_two_pi jvRa jvRb z

theorem jvScx_add_two_pi (z : ℂ) : jvScx (z + ((2 * Real.pi : ℝ) : ℂ)) = jvScx z :=
  trig16c_add_two_pi jvSa jvSb z

/-- The continuation is entire. -/
theorem differentiable_trig16c (a b : ℕ → ℝ) : Differentiable ℂ (trig16c a b) := by
  unfold trig16c
  fun_prop

theorem differentiable_jvRcx : Differentiable ℂ jvRcx := differentiable_trig16c jvRa jvRb
theorem differentiable_jvScx : Differentiable ℂ jvScx := differentiable_trig16c jvSa jvSb

/-! #### §1.1 — the sharp trigonometric modulus bounds

`‖cos z‖ ≤ cosh (Im z)` and `‖sin z‖ ≤ cosh (Im z)`, **squared**, from `Complex.cos_eq`.
The lossy route (`|re| + |im|`) would give `2 + 2(cosh + sinh)` at the strip edge, i.e.
`4.4428` where §5's ceiling allows `4.040133511` — a 10 % overshoot, so the
sharp bound is not a nicety here. -/

theorem cos_eq_split (z : ℂ) :
    Complex.cos z = (↑(Real.cos z.re * Real.cosh z.im) : ℂ)
      - (↑(Real.sin z.re * Real.sinh z.im) : ℂ) * Complex.I := by
  rw [Complex.cos_eq, ← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sin,
    ← Complex.ofReal_sinh, ← Complex.ofReal_mul, ← Complex.ofReal_mul]

theorem sin_eq_split (z : ℂ) :
    Complex.sin z = (↑(Real.sin z.re * Real.cosh z.im) : ℂ)
      + (↑(Real.cos z.re * Real.sinh z.im) : ℂ) * Complex.I := by
  rw [Complex.sin_eq, ← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sin,
    ← Complex.ofReal_sinh, ← Complex.ofReal_mul, ← Complex.ofReal_mul]

theorem cos_re (z : ℂ) : (Complex.cos z).re = Real.cos z.re * Real.cosh z.im := by
  rw [cos_eq_split]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one]
  ring

theorem cos_im (z : ℂ) : (Complex.cos z).im = -(Real.sin z.re * Real.sinh z.im) := by
  rw [cos_eq_split]
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one]
  ring

theorem sin_re (z : ℂ) : (Complex.sin z).re = Real.sin z.re * Real.cosh z.im := by
  rw [sin_eq_split]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one]
  ring

theorem sin_im (z : ℂ) : (Complex.sin z).im = Real.cos z.re * Real.sinh z.im := by
  rw [sin_eq_split]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one]
  ring

theorem sinh_sq_le_cosh_sq (t : ℝ) : Real.sinh t ^ 2 ≤ Real.cosh t ^ 2 := by
  have h := Real.cosh_sq_sub_sinh_sq t
  nlinarith [sq_nonneg (Real.sinh t)]

/-- **`‖cos z‖ ≤ cosh (Im z)`** — sharp, and the reason §5's ceiling can be `W_out` exactly. -/
theorem norm_cos_le_cosh (z : ℂ) : ‖Complex.cos z‖ ≤ Real.cosh z.im := by
  have hsq : ‖Complex.cos z‖ ^ 2 ≤ Real.cosh z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, cos_re, cos_im]
    nlinarith [Real.cosh_sq_sub_sinh_sq z.im, Real.sin_sq_add_cos_sq z.re,
      sq_nonneg (Real.sin z.re), sq_nonneg (Real.cosh z.im)]
  have h0 : (0 : ℝ) ≤ Real.cosh z.im := (Real.cosh_pos z.im).le
  nlinarith [hsq, norm_nonneg (Complex.cos z), h0]

/-- **`‖sin z‖ ≤ cosh (Im z)`**. -/
theorem norm_sin_le_cosh (z : ℂ) : ‖Complex.sin z‖ ≤ Real.cosh z.im := by
  have hsq : ‖Complex.sin z‖ ^ 2 ≤ Real.cosh z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, sin_re, sin_im]
    nlinarith [Real.cosh_sq_sub_sinh_sq z.im, Real.sin_sq_add_cos_sq z.re,
      sq_nonneg (Real.sin z.re), sq_nonneg (Real.cosh z.im)]
  have h0 : (0 : ℝ) ≤ Real.cosh z.im := (Real.cosh_pos z.im).le
  nlinarith [hsq, norm_nonneg (Complex.sin z), h0]

/-- **`|2 + 2cos z| ≤ 2 + 2cosh(Im z)`** — the `W_out` factor, sharp. -/
theorem norm_two_add_two_cos (z : ℂ) :
    ‖(2 : ℂ) + 2 * Complex.cos z‖ ≤ 2 + 2 * Real.cosh z.im := by
  have h : ‖(2 : ℂ) + 2 * Complex.cos z‖ ≤ ‖(2 : ℂ)‖ + ‖2 * Complex.cos z‖ := norm_add_le _ _
  rw [norm_mul, Complex.norm_ofNat] at h
  have h2 := norm_cos_le_cosh z
  nlinarith [h, h2, norm_nonneg (Complex.cos z), Real.cosh_pos z.im]

/-- The strip majorant — the certifier's own `S(co, t) = Σ_j (|a_j| + |b_j|) cosh(j·t)`
(`certify_c5.py` l.28). -/
noncomputable def stripMod (a b : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc (1 : ℕ) 16, (|a j| + |b j|) * Real.cosh ((j : ℝ) * t)

theorem trig16c_norm_le (a b : ℕ → ℝ) (z : ℂ) :
    ‖trig16c a b z‖ ≤ stripMod a b z.im := by
  unfold trig16c stripMod
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have hc : ‖Complex.cos ((j : ℂ) * z)‖ ≤ Real.cosh ((j : ℝ) * z.im) := by
    have := norm_cos_le_cosh ((j : ℂ) * z)
    simpa using this
  have hs : ‖Complex.sin ((j : ℂ) * z)‖ ≤ Real.cosh ((j : ℝ) * z.im) := by
    have := norm_sin_le_cosh ((j : ℂ) * z)
    simpa using this
  have htri : ‖(a j : ℂ) * Complex.cos ((j : ℂ) * z) + (b j : ℂ) * Complex.sin ((j : ℂ) * z)‖
      ≤ |a j| * Real.cosh ((j : ℝ) * z.im) + |b j| * Real.cosh ((j : ℝ) * z.im) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
    exact add_le_add (mul_le_mul_of_nonneg_left hc (abs_nonneg _))
      (mul_le_mul_of_nonneg_left hs (abs_nonneg _))
  refine htri.trans (le_of_eq ?_)
  ring

/-! #### §1.2 — the strip majorant at the head of the strip

On `|Im z| < 1/5` the majorant is dominated by its value at `1/5` (`cosh` is even and
monotone in `|t|`), which is a **number** — the `S(r, 0.2) = 3.197…`, `S(s, 0.2) = 3.20…`
that `sim/sim_strip.py` §1 prints. -/

theorem stripMod_mono {a b : ℕ → ℝ} {t : ℝ} (ht : |t| ≤ stripA) :
    stripMod a b t ≤ stripMod a b stripA := by
  unfold stripMod
  refine Finset.sum_le_sum fun j _ => ?_
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have h2 : (0 : ℝ) ≤ (j : ℝ) * stripA := mul_nonneg hj stripA_pos.le
  have h1 : |(j : ℝ) * t| ≤ |(j : ℝ) * stripA| := by
    rw [abs_mul, abs_of_nonneg hj, abs_of_nonneg h2]
    exact mul_le_mul_of_nonneg_left ht hj
  have h3 : Real.cosh ((j : ℝ) * t) ≤ Real.cosh ((j : ℝ) * stripA) :=
    (Real.cosh_le_cosh).mpr h1
  exact mul_le_mul_of_nonneg_left h3 (by positivity)

theorem stripMod_at_stripA_nonneg {a b : ℕ → ℝ} : 0 ≤ stripMod a b stripA := by
  unfold stripMod
  exact Finset.sum_nonneg fun j _ => by positivity

/-! ### §2 — the strip-analytic integrals `P`, `Y`

The certifier builds `P(x) = (1/2π)∫ 2^{r(x+y)+s(y)} dy` on a grid (`certify_c5.py` l.28–33);
`jvP` in `JV1000Moments` is its continuum limit.  The quadrature lemma needs it as a function
of a **complex** argument, so `jvPcx` below is the same integral with the integrand evaluated on
the strip — and `2^{w}` on `ℂ` is `exp(w log 2)`, the *only* reading that is entire (a `rpow`
reading has no complex branch at all, and the round-17 lesson is that certified values live
where the log of a positive thing is well defined — on `ℂ` that is `Complex.log`, §3).

**Holomorphy is proved here, not assumed.**  `differentiableOn_jvPcx` is differentiation under
the interval integral, and the dominating function is the certifier's own strip majorant: on
`|Im z| < 1/5` the integrand is bounded by `Pmaj = 2^{S_r + S_s}` and its `z`-derivative by
`PmajD = log 2 · S'_r · Pmaj`, where `S_r = Σ_j(|a_j|+|b_j|) cosh(j/5)` is `certify_c5.py` l.28
verbatim and `S'_r` the same with the `j` weight.  Nothing about `P` is named. -/

/-- `log 2` as a complex number — the base every `2^{·}` in this file is built from. -/
noncomputable def L2C : ℂ := (Real.log 2 : ℂ)

theorem norm_L2C : ‖L2C‖ = Real.log 2 := by
  rw [L2C, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.log_pos (by norm_num))]

/-- The `z`-derivative of `trig16c`: `d/dz Σ (a_j cos jz + b_j sin jz)`
`= Σ j(b_j cos jz − a_j sin jz)`. -/
noncomputable def trig16cD (a b : ℕ → ℝ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.Icc (1 : ℕ) 16,
    ((b j : ℂ) * (j : ℂ) * Complex.cos ((j : ℂ) * z)
      - (a j : ℂ) * (j : ℂ) * Complex.sin ((j : ℂ) * z))

/-- The derivative majorant `S'(t) = Σ_j (|a_j| + |b_j|) · j · cosh(j·t)`. -/
noncomputable def stripModD (a b : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc (1 : ℕ) 16, ((|a j| + |b j|) * (j : ℝ)) * Real.cosh ((j : ℝ) * t)

theorem hasDerivAt_trig16c (a b : ℕ → ℝ) (z : ℂ) :
    HasDerivAt (trig16c a b) (trig16cD a b z) z := by
  unfold trig16c trig16cD
  refine HasDerivAt.sum (u := Finset.Icc (1 : ℕ) 16)
    (A := fun j z => (a j : ℂ) * Complex.cos ((j : ℂ) * z) + (b j : ℂ) * Complex.sin ((j : ℂ) * z))
    (A' := fun j => (b j : ℂ) * (j : ℂ) * Complex.cos ((j : ℂ) * z)
      - (a j : ℂ) * (j : ℂ) * Complex.sin ((j : ℂ) * z)) ?_
  intro j _
  have hcos : HasDerivAt (fun z : ℂ => Complex.cos ((j : ℂ) * z))
      (-(Complex.sin ((j : ℂ) * z)) * (j : ℂ)) z := by
    have hin : HasDerivAt (fun z : ℂ => (j : ℂ) * z) (j : ℂ) z := by
      simpa using (hasDerivAt_const_mul (x := z) (c := (j : ℂ)))
    exact (Complex.hasDerivAt_cos ((j : ℂ) * z)).comp z hin
  have hsin : HasDerivAt (fun z : ℂ => Complex.sin ((j : ℂ) * z))
      (Complex.cos ((j : ℂ) * z) * (j : ℂ)) z := by
    have hin : HasDerivAt (fun z : ℂ => (j : ℂ) * z) (j : ℂ) z := by
      simpa using (hasDerivAt_const_mul (x := z) (c := (j : ℂ)))
    exact (Complex.hasDerivAt_sin ((j : ℂ) * z)).comp z hin
  have h := (hcos.const_mul (a j : ℂ)).add (hsin.const_mul (b j : ℂ))
  convert h using 2; ring

theorem norm_trig16cD_le (a b : ℕ → ℝ) (z : ℂ) :
    ‖trig16cD a b z‖ ≤ stripModD a b z.im := by
  unfold trig16cD stripModD
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hc : ‖Complex.cos ((j : ℂ) * z)‖ ≤ Real.cosh ((j : ℝ) * z.im) := by
    have := norm_cos_le_cosh ((j : ℂ) * z); simpa using this
  have hs : ‖Complex.sin ((j : ℂ) * z)‖ ≤ Real.cosh ((j : ℝ) * z.im) := by
    have := norm_sin_le_cosh ((j : ℂ) * z); simpa using this
  refine (norm_sub_le _ _).trans ?_
  simp only [norm_mul, Complex.norm_real, Complex.norm_natCast, Real.norm_eq_abs]
  have h1 : |b j| * (j : ℝ) * ‖Complex.cos ((j : ℂ) * z)‖
      ≤ |b j| * (j : ℝ) * Real.cosh ((j : ℝ) * z.im) := by
    have h0 : (0 : ℝ) ≤ |b j| * (j : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hc h0]
  have h2 : |a j| * (j : ℝ) * ‖Complex.sin ((j : ℂ) * z)‖
      ≤ |a j| * (j : ℝ) * Real.cosh ((j : ℝ) * z.im) := by
    have h0 : (0 : ℝ) ≤ |a j| * (j : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hs h0]
  have h3 : (|a j| + |b j|) * (j : ℝ) * Real.cosh ((j : ℝ) * z.im)
      = |b j| * (j : ℝ) * Real.cosh ((j : ℝ) * z.im)
        + |a j| * (j : ℝ) * Real.cosh ((j : ℝ) * z.im) := by ring
  linarith [h1, h2, h3.le, h3.ge]

theorem stripModD_mono {a b : ℕ → ℝ} {t : ℝ} (ht : |t| ≤ stripA) :
    stripModD a b t ≤ stripModD a b stripA := by
  unfold stripModD
  refine Finset.sum_le_sum fun j _ => ?_
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have h2 : (0 : ℝ) ≤ (j : ℝ) * stripA := mul_nonneg hj stripA_pos.le
  have h1 : |(j : ℝ) * t| ≤ |(j : ℝ) * stripA| := by
    rw [abs_mul, abs_of_nonneg hj, abs_of_nonneg h2]
    exact mul_le_mul_of_nonneg_left ht hj
  exact mul_le_mul_of_nonneg_left ((Real.cosh_le_cosh).mpr h1) (by positivity)

theorem stripModD_nonneg (a b : ℕ → ℝ) : 0 ≤ stripModD a b stripA := by
  unfold stripModD; exact Finset.sum_nonneg fun j _ => by positivity

theorem stripMod_nonneg' (a b : ℕ → ℝ) : 0 ≤ stripMod a b stripA := by
  unfold stripMod; exact Finset.sum_nonneg fun j _ => by positivity

theorem stripModSum_nonneg : 0 ≤ stripMod jvRa jvRb stripA + stripMod jvSa jvSb stripA :=
  add_nonneg (stripMod_nonneg' _ _) (stripMod_nonneg' _ _)

/-- The `P` integrand: `2^{r_c(z+y) + s_c(y)} = exp(log 2 · (r_c(z+y) + s_c(y)))`. -/
noncomputable def PInt (z : ℂ) (y : ℝ) : ℂ :=
  Complex.exp (L2C * (jvRcx (z + (y : ℂ)) + jvScx ((y : ℂ))))

/-- Its `z`-derivative. -/
noncomputable def PIntD (z : ℂ) (y : ℝ) : ℂ :=
  L2C * trig16cD jvRa jvRb (z + (y : ℂ)) * PInt z y

/-- The strip majorant of `‖PInt‖`: `2^{S_r + S_s}` at the head of the strip — the certifier's
`S(co, σ)` at `σ = 2β`. -/
noncomputable def Pmaj : ℝ :=
  Real.exp (Real.log 2 * (stripMod jvRa jvRb stripA + stripMod jvSa jvSb stripA))

theorem Pmaj_pos : 0 < Pmaj := Real.exp_pos _

/-- The strip majorant of `‖PIntD‖`. -/
noncomputable def PmajD : ℝ := Real.log 2 * stripModD jvRa jvRb stripA * Pmaj

theorem hasDerivAt_PInt (z : ℂ) (y : ℝ) : HasDerivAt (fun w => PInt w y) (PIntD z y) z := by
  have hR : HasDerivAt (fun w : ℂ => jvRcx (w + (y : ℂ)))
      (trig16cD jvRa jvRb (z + (y : ℂ))) z := by
    have hin : HasDerivAt (fun w : ℂ => w + (y : ℂ)) 1 z := by
      simpa using (hasDerivAt_id z).add_const ((y : ℂ))
    have h := (hasDerivAt_trig16c jvRa jvRb (z + (y : ℂ))).comp z hin
    simpa [jvRcx, Function.comp_def] using h
  have hsum : HasDerivAt (fun w : ℂ => jvRcx (w + (y : ℂ)) + jvScx ((y : ℂ)))
      (trig16cD jvRa jvRb (z + (y : ℂ))) z := by
    simpa using hR.add_const (jvScx ((y : ℂ)))
  have hlin : HasDerivAt (fun w : ℂ => L2C * (jvRcx (w + (y : ℂ)) + jvScx ((y : ℂ))))
      (L2C * trig16cD jvRa jvRb (z + (y : ℂ))) z := by
    simpa using hsum.const_mul L2C
  have := hlin.cexp
  simpa [PInt, PIntD, mul_comm, mul_assoc] using this

theorem norm_PInt_le {z : ℂ} (hz : z ∈ stripZ) (y : ℝ) : ‖PInt z y‖ ≤ Pmaj := by
  have him : (z + (y : ℂ)).im = z.im := by simp
  have h1 : ‖jvRcx (z + (y : ℂ))‖ ≤ stripMod jvRa jvRb stripA := by
    refine (trig16c_norm_le jvRa jvRb (z + (y : ℂ))).trans ?_
    exact stripMod_mono (a := jvRa) (b := jvRb) (by rw [him]; exact le_of_lt hz)
  have h2 : ‖jvScx ((y : ℂ))‖ ≤ stripMod jvSa jvSb stripA := by
    refine (trig16c_norm_le jvSa jvSb ((y : ℂ))).trans ?_
    refine stripMod_mono (a := jvSa) (b := jvSb) ?_
    have hy0 : (((y : ℂ)) : ℂ).im = 0 := by simp
    rw [hy0, abs_zero]; exact stripA_pos.le
  rw [PInt, Complex.norm_exp, Pmaj]
  refine Real.exp_le_exp.mpr ?_
  calc (L2C * (jvRcx (z + (y : ℂ)) + jvScx ((y : ℂ)))).re
      ≤ ‖L2C * (jvRcx (z + (y : ℂ)) + jvScx ((y : ℂ)))‖ := Complex.re_le_norm _
    _ = Real.log 2 * ‖jvRcx (z + (y : ℂ)) + jvScx ((y : ℂ))‖ := by rw [norm_mul, norm_L2C]
    _ ≤ Real.log 2 * (stripMod jvRa jvRb stripA + stripMod jvSa jvSb stripA) :=
        mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add h1 h2))
          (Real.log_pos (by norm_num)).le

theorem norm_PIntD_le {z : ℂ} (hz : z ∈ stripZ) (y : ℝ) : ‖PIntD z y‖ ≤ PmajD := by
  have him : (z + (y : ℂ)).im = z.im := by simp
  have h1 : ‖trig16cD jvRa jvRb (z + (y : ℂ))‖ ≤ stripModD jvRa jvRb stripA := by
    refine (norm_trig16cD_le jvRa jvRb (z + (y : ℂ))).trans ?_
    exact stripModD_mono (a := jvRa) (b := jvRb) (by rw [him]; exact le_of_lt hz)
  have h2 := norm_PInt_le hz y
  rw [PIntD, PmajD, norm_mul, norm_mul, norm_L2C]
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (Real.log_pos (by norm_num)).le) h2
    (norm_nonneg _) (mul_nonneg (Real.log_pos (by norm_num)).le (stripModD_nonneg jvRa jvRb))

/-- **`P_c` is holomorphic on the strip.**  Differentiation under the interval integral, with
the certifier's strip majorant as the dominating function.  No analytic premise is named. -/
theorem hasDerivAt_jvPcx (z : ℂ) (hz : z ∈ stripZ) :
    HasDerivAt (fun w => (1 / (2 * (Real.pi : ℂ))) *
        ∫ y in (0 : ℝ)..2 * Real.pi, PInt w y)
      ((1 / (2 * (Real.pi : ℂ))) * ∫ y in (0 : ℝ)..2 * Real.pi, PIntD z y) z := by
  have hofR : Continuous fun r : ℝ => (r : ℂ) := Complex.continuous_ofReal
  have hdR : Continuous fun p : ℂ × ℝ => jvRcx (p.1 + (p.2 : ℂ)) :=
    differentiable_jvRcx.continuous.comp (continuous_fst.add (hofR.comp continuous_snd))
  have hdS : Continuous fun p : ℂ × ℝ => jvScx (p.2 : ℂ) :=
    differentiable_jvScx.continuous.comp (hofR.comp continuous_snd)
  have harg : Continuous fun p : ℂ × ℝ => L2C * (jvRcx (p.1 + (p.2 : ℂ)) + jvScx (p.2 : ℂ)) :=
    continuous_const.mul (hdR.add hdS)
  have hcont : Continuous fun p : ℂ × ℝ => PInt p.1 p.2 := by
    unfold PInt
    exact Complex.continuous_exp.comp harg
  have hdD : Continuous fun p : ℂ × ℝ => trig16cD jvRa jvRb (p.1 + (p.2 : ℂ)) := by
    unfold trig16cD; fun_prop
  have hcontD : Continuous fun p : ℂ × ℝ => PIntD p.1 p.2 := by
    unfold PIntD
    exact (continuous_const.mul hdD).mul hcont
  have hmeas1 : ∀ᶠ x in nhds z, AEStronglyMeasurable (fun y => PInt x y)
      (volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi))) :=
    Filter.Eventually.of_forall fun x =>
      (hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hmeas2 : AEStronglyMeasurable (fun y => PIntD z y)
      (volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi))) :=
    (hcontD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hInt : IntervalIntegrable (fun y => PInt z y) volume (0 : ℝ) (2 * Real.pi) :=
    (hcont.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  have hbound : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) → ∀ x ∈ stripZ,
      ‖PIntD x t‖ ≤ PmajD :=
    Filter.Eventually.of_forall fun t _ x hx => norm_PIntD_le hx t
  have hdiff : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) → ∀ x ∈ stripZ,
      HasDerivAt (fun x => PInt x t) (PIntD x t) x :=
    Filter.Eventually.of_forall fun t _ x _ => hasDerivAt_PInt x t
  have hkey := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := 2 * Real.pi) (bound := fun _ => PmajD)
    (F := PInt) (F' := PIntD) (x₀ := z) (s := stripZ)
    (isOpen_stripZ.mem_nhds hz) hmeas1 hInt hmeas2 hbound
    intervalIntegrable_const hdiff
  exact hkey.2.const_mul _

/-- **`P_c`** — the strip-analytic version of `jvP`: the same inner convolution, evaluated on
`ℂ`.  `jvPcx_real` (§5) is the real-axis agreement that makes this *the* `jvP`. -/
noncomputable def jvPcx (z : ℂ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) * ∫ y in (0 : ℝ)..2 * Real.pi, PInt z y

theorem hasDerivAt_jvPcx' {z : ℂ} (hz : z ∈ stripZ) :
    HasDerivAt jvPcx ((1 / (2 * (Real.pi : ℂ))) * ∫ y in (0 : ℝ)..2 * Real.pi, PIntD z y) z :=
  hasDerivAt_jvPcx z hz

theorem differentiableAt_jvPcx {z : ℂ} (hz : z ∈ stripZ) : DifferentiableAt ℂ jvPcx z :=
  (hasDerivAt_jvPcx z hz).differentiableAt

theorem differentiableOn_jvPcx : DifferentiableOn ℂ jvPcx stripZ := fun _ hz =>
  (differentiableAt_jvPcx hz).differentiableWithinAt

/-! #### §2.1 — `Y`, the same argument with the weighted integrand

`jvY x = (1/2π)∫ (r(x+y)+s(y))·2^{r(x+y)+s(y)} dy`, so its `z`-derivative picks up the product
rule: `d/dz[(w)·e^{L2 w}] = w'·e^{L2w}·(1 + L2·w)`.  The bound is the `P` bound times
`(1 + log 2 · (S_r + S_s))`. -/

/-- The `Y` integrand: `(r_c(z+y) + s_c(y)) · 2^{r_c(z+y) + s_c(y)}`. -/
noncomputable def YInt (z : ℂ) (y : ℝ) : ℂ :=
  (jvRcx (z + (y : ℂ)) + jvScx ((y : ℂ))) * PInt z y

/-- Its `z`-derivative. -/
noncomputable def YIntD (z : ℂ) (y : ℝ) : ℂ :=
  trig16cD jvRa jvRb (z + (y : ℂ)) * PInt z y
    * (1 + L2C * (jvRcx (z + (y : ℂ)) + jvScx ((y : ℂ))))

/-- The strip majorant of `‖YInt‖`. -/
noncomputable def Ymaj : ℝ :=
  (stripMod jvRa jvRb stripA + stripMod jvSa jvSb stripA) * Pmaj

/-- The strip majorant of `‖YIntD‖`. -/
noncomputable def YmajD : ℝ :=
  stripModD jvRa jvRb stripA * Pmaj
    * (1 + Real.log 2 * (stripMod jvRa jvRb stripA + stripMod jvSa jvSb stripA))

/-- **`Y_c`** — the strip-analytic version of `jvY`. -/
noncomputable def jvYcx (z : ℂ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) * ∫ y in (0 : ℝ)..2 * Real.pi, YInt z y

theorem hasDerivAt_Yarg (z : ℂ) (y : ℝ) :
    HasDerivAt (fun w : ℂ => jvRcx (w + (y : ℂ)) + jvScx ((y : ℂ)))
      (trig16cD jvRa jvRb (z + (y : ℂ))) z := by
  have hin : HasDerivAt (fun w : ℂ => w + (y : ℂ)) 1 z := by
    simpa using (hasDerivAt_id z).add_const ((y : ℂ))
  have h := (hasDerivAt_trig16c jvRa jvRb (z + (y : ℂ))).comp z hin
  have h' : HasDerivAt (fun w : ℂ => jvRcx (w + (y : ℂ)))
      (trig16cD jvRa jvRb (z + (y : ℂ))) z := by
    simpa [jvRcx, Function.comp_def] using h
  simpa using h'.add_const (jvScx ((y : ℂ)))

theorem hasDerivAt_YInt (z : ℂ) (y : ℝ) : HasDerivAt (fun w => YInt w y) (YIntD z y) z := by
  have harg := hasDerivAt_Yarg z y
  have hp := hasDerivAt_PInt z y
  have hmul := harg.mul hp
  have hval : trig16cD jvRa jvRb (z + (y : ℂ)) * PInt z y
      + (jvRcx (z + (y : ℂ)) + jvScx ((y : ℂ))) * PIntD z y = YIntD z y := by
    simp only [YIntD, PIntD]; ring
  have hfun : (fun w => YInt w y)
      = ((fun w : ℂ => jvRcx (w + (y : ℂ)) + jvScx ((y : ℂ))) * fun w => PInt w y) := rfl
  rw [hval] at hmul
  rw [hfun]
  exact hmul

theorem norm_YInt_le {z : ℂ} (hz : z ∈ stripZ) (y : ℝ) : ‖YInt z y‖ ≤ Ymaj := by
  have him : (z + (y : ℂ)).im = z.im := by simp
  have hS : ‖jvRcx (z + (y : ℂ)) + jvScx ((y : ℂ))‖
      ≤ stripMod jvRa jvRb stripA + stripMod jvSa jvSb stripA := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (trig16c_norm_le jvRa jvRb _).trans ?_
      exact stripMod_mono (a := jvRa) (b := jvRb) (by rw [him]; exact le_of_lt hz)
    · refine (trig16c_norm_le jvSa jvSb _).trans ?_
      refine stripMod_mono (a := jvSa) (b := jvSb) ?_
      have hy0 : (((y : ℂ)) : ℂ).im = 0 := by simp
      rw [hy0, abs_zero]; exact stripA_pos.le
  have hP := norm_PInt_le hz y
  rw [YInt, Ymaj, norm_mul]
  exact mul_le_mul hS hP (norm_nonneg _) stripModSum_nonneg

theorem norm_YIntD_le {z : ℂ} (hz : z ∈ stripZ) (y : ℝ) : ‖YIntD z y‖ ≤ YmajD := by
  have him : (z + (y : ℂ)).im = z.im := by simp
  have hD : ‖trig16cD jvRa jvRb (z + (y : ℂ))‖ ≤ stripModD jvRa jvRb stripA := by
    refine (norm_trig16cD_le jvRa jvRb _).trans ?_
    exact stripModD_mono (a := jvRa) (b := jvRb) (by rw [him]; exact le_of_lt hz)
  have hS : ‖jvRcx (z + (y : ℂ)) + jvScx ((y : ℂ))‖
      ≤ stripMod jvRa jvRb stripA + stripMod jvSa jvSb stripA := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (trig16c_norm_le jvRa jvRb _).trans ?_
      exact stripMod_mono (a := jvRa) (b := jvRb) (by rw [him]; exact le_of_lt hz)
    · refine (trig16c_norm_le jvSa jvSb _).trans ?_
      refine stripMod_mono (a := jvSa) (b := jvSb) ?_
      have hy0 : (((y : ℂ)) : ℂ).im = 0 := by simp
      rw [hy0, abs_zero]; exact stripA_pos.le
  have hP := norm_PInt_le hz y
  have hfac : ‖1 + L2C * (jvRcx (z + (y : ℂ)) + jvScx ((y : ℂ)))‖
      ≤ 1 + Real.log 2 * (stripMod jvRa jvRb stripA + stripMod jvSa jvSb stripA) := by
    have h1 : ‖L2C * (jvRcx (z + (y : ℂ)) + jvScx ((y : ℂ)))‖
        ≤ Real.log 2 * (stripMod jvRa jvRb stripA + stripMod jvSa jvSb stripA) := by
      rw [norm_mul, norm_L2C]
      exact mul_le_mul_of_nonneg_left hS (Real.log_pos (by norm_num)).le
    refine (norm_add_le _ _).trans ?_
    have hone : ‖(1 : ℂ)‖ = 1 := by norm_num
    rw [hone]
    linarith
  have hSnn : (0:ℝ) ≤ stripMod jvRa jvRb stripA + stripMod jvSa jvSb stripA :=
    stripModSum_nonneg
  rw [YIntD, YmajD, norm_mul, norm_mul]
  have hstep : ‖trig16cD jvRa jvRb (z + (y : ℂ))‖ * ‖PInt z y‖
      * ‖1 + L2C * (jvRcx (z + (y : ℂ)) + jvScx ((y : ℂ)))‖
      ≤ stripModD jvRa jvRb stripA * Pmaj
        * (1 + Real.log 2 * (stripMod jvRa jvRb stripA + stripMod jvSa jvSb stripA)) := by
    have hA : (0:ℝ) ≤ stripModD jvRa jvRb stripA := stripModD_nonneg jvRa jvRb
    have hB : (0:ℝ) ≤ Pmaj := Pmaj_pos.le
    have hC : (0:ℝ) ≤ 1 + Real.log 2 *
        (stripMod jvRa jvRb stripA + stripMod jvSa jvSb stripA) := by
      have := Real.log_pos (by norm_num : (1:ℝ) < 2)
      nlinarith [hSnn]
    exact mul_le_mul (mul_le_mul hD hP (norm_nonneg _) hA) hfac (norm_nonneg _)
      (mul_nonneg hA hB)
  exact hstep

theorem differentiableAt_jvYcx {z : ℂ} (hz : z ∈ stripZ) : DifferentiableAt ℂ jvYcx z := by
  have hofR : Continuous fun r : ℝ => (r : ℂ) := Complex.continuous_ofReal
  have hdR : Continuous fun p : ℂ × ℝ => jvRcx (p.1 + (p.2 : ℂ)) :=
    differentiable_jvRcx.continuous.comp (continuous_fst.add (hofR.comp continuous_snd))
  have hdS : Continuous fun p : ℂ × ℝ => jvScx (p.2 : ℂ) :=
    differentiable_jvScx.continuous.comp (hofR.comp continuous_snd)
  have harg : Continuous fun p : ℂ × ℝ => L2C * (jvRcx (p.1 + (p.2 : ℂ)) + jvScx (p.2 : ℂ)) :=
    continuous_const.mul (hdR.add hdS)
  have hcontP : Continuous fun p : ℂ × ℝ => PInt p.1 p.2 := by
    unfold PInt; exact Complex.continuous_exp.comp harg
  have hcontY : Continuous fun p : ℂ × ℝ => YInt p.1 p.2 := by
    unfold YInt; exact (hdR.add hdS).mul hcontP
  have hdD : Continuous fun p : ℂ × ℝ => trig16cD jvRa jvRb (p.1 + (p.2 : ℂ)) := by
    unfold trig16cD; fun_prop
  have hcontD : Continuous fun p : ℂ × ℝ => YIntD p.1 p.2 := by
    unfold YIntD
    exact (hdD.mul hcontP).mul (continuous_const.add harg)
  have hmeas1 : ∀ᶠ x in nhds z, AEStronglyMeasurable (fun y => YInt x y)
      (volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi))) :=
    Filter.Eventually.of_forall fun x =>
      (hcontY.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hmeas2 : AEStronglyMeasurable (fun y => YIntD z y)
      (volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi))) :=
    (hcontD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hInt : IntervalIntegrable (fun y => YInt z y) volume (0 : ℝ) (2 * Real.pi) :=
    (hcontY.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  have hbound : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) → ∀ x ∈ stripZ,
      ‖YIntD x t‖ ≤ YmajD :=
    Filter.Eventually.of_forall fun t _ x hx => norm_YIntD_le hx t
  have hdiff : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) → ∀ x ∈ stripZ,
      HasDerivAt (fun x => YInt x t) (YIntD x t) x :=
    Filter.Eventually.of_forall fun t _ x _ => hasDerivAt_YInt x t
  have hkey := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := 2 * Real.pi) (bound := fun _ => YmajD)
    (F := YInt) (F' := YIntD) (x₀ := z) (s := stripZ)
    (isOpen_stripZ.mem_nhds hz) hmeas1 hInt hmeas2 hbound
    intervalIntegrable_const hdiff
  exact (hkey.2.const_mul _).differentiableAt

theorem differentiableOn_jvYcx : DifferentiableOn ℂ jvYcx stripZ := fun _ hz =>
  (differentiableAt_jvYcx hz).differentiableWithinAt

/-! ### §3 — the `log₂` shapes `u`, `v`

`jvU`/`jvV` in `JV1000Moments` are

    u = log₂P + (κ−1)(Y/P − LZ) − H_,      v = (2−κ)(Y/P − LZ) − 2·log₂P + H_

and the complex versions below are the *same expressions* with `Real.logb 2` replaced by
`Complex.log · / log 2`.  The only thing that changes is the branch: `Complex.log` is
differentiable exactly on `Complex.slitPlane = {z | 0 < z.re ∨ z.im ≠ 0}`, so `u`, `v` are
holomorphic on the strip **provided `P_c` lands there** — which `sim/sim_compose.py` §1
measures: `min Re P_c = 0.9385 > 0` on `|Im z| ≤ 1/5`, so the strip image misses the cut by
`0.94`, and the condition `hslit` below is comfortably satisfiable. -/

/-- The strip-corrected log-density `u`, on `ℂ`. -/
noncomputable def jvUcx (z : ℂ) : ℂ :=
  (Complex.log (jvPcx z) / L2C - (jvLZ : ℂ))
    + ((((jvKappaQ : ℝ) - 1 : ℝ)) : ℂ) * (jvYcx z / jvPcx z - (jvLZ : ℂ)) - (jvStripH : ℂ)

/-- The strip-corrected log-density `v`, on `ℂ`. -/
noncomputable def jvVcx (z : ℂ) : ℂ :=
  (((2 - (jvKappaQ : ℝ) : ℝ)) : ℂ) * (jvYcx z / jvPcx z - (jvLZ : ℂ))
    - 2 * (Complex.log (jvPcx z) / L2C - (jvLZ : ℂ)) + (jvStripH : ℂ)

theorem zero_not_mem_slitPlane : (0 : ℂ) ∉ Complex.slitPlane := by
  simp [Complex.slitPlane]

theorem log_jvPcx_differentiableAt {z : ℂ} (hz : z ∈ stripZ)
    (hslit : jvPcx z ∈ Complex.slitPlane) :
    DifferentiableAt ℂ (fun w => Complex.log (jvPcx w)) z :=
  (Complex.differentiableAt_log hslit).comp z (differentiableAt_jvPcx hz)

/-- **`u` is holomorphic on the strip** — `log` of a nonvanishing strip-analytic `P`, plus a
ratio of two such, plus constants. -/
theorem differentiableAt_jvUcx {z : ℂ} (hz : z ∈ stripZ)
    (hslit : jvPcx z ∈ Complex.slitPlane) : DifferentiableAt ℂ jvUcx z := by
  have hne : jvPcx z ≠ 0 := fun h => zero_not_mem_slitPlane (h ▸ hslit)
  have hlog := log_jvPcx_differentiableAt hz hslit
  have hP := differentiableAt_jvPcx hz
  have hY := differentiableAt_jvYcx hz
  have hA : DifferentiableAt ℂ (fun w => Complex.log (jvPcx w) / L2C - (jvLZ : ℂ)) z :=
    (hlog.div_const L2C).sub_const _
  have hQ : DifferentiableAt ℂ (fun w => jvYcx w / jvPcx w - (jvLZ : ℂ)) z :=
    (hY.div hP hne).sub_const _
  have hmain : DifferentiableAt ℂ
      (fun w => (Complex.log (jvPcx w) / L2C - (jvLZ : ℂ))
        + ((((jvKappaQ : ℝ) - 1 : ℝ)) : ℂ) * (jvYcx w / jvPcx w - (jvLZ : ℂ))) z :=
    hA.add (hQ.const_mul _)
  exact hmain.sub_const _

/-- **`v` is holomorphic on the strip.** -/
theorem differentiableAt_jvVcx {z : ℂ} (hz : z ∈ stripZ)
    (hslit : jvPcx z ∈ Complex.slitPlane) : DifferentiableAt ℂ jvVcx z := by
  have hne : jvPcx z ≠ 0 := fun h => zero_not_mem_slitPlane (h ▸ hslit)
  have hlog := log_jvPcx_differentiableAt hz hslit
  have hP := differentiableAt_jvPcx hz
  have hY := differentiableAt_jvYcx hz
  have hA : DifferentiableAt ℂ (fun w => Complex.log (jvPcx w) / L2C - (jvLZ : ℂ)) z :=
    (hlog.div_const L2C).sub_const _
  have hQ : DifferentiableAt ℂ (fun w => jvYcx w / jvPcx w - (jvLZ : ℂ)) z :=
    (hY.div hP hne).sub_const _
  exact ((hQ.const_mul _).sub (hA.const_mul 2)).add_const _

/-! ### §4 — the composite moment integrand

`F₁(z) = (2 + 2cos z)·2^{p(Δ − u(z))}`, `F₂(z) = (2 + 2cos z)·2^{q(a_Γ v(z) − u(z))}`.

**Why there is no branch problem in the composite.**  `2^{w}` on `ℂ` is `exp(w log 2)`, and
`exp` is *entire*: once `u` is holomorphic, `exp(p(Δ − u)·log 2)` is holomorphic with no
further condition.  The log's branch cut is confined to `u`'s construction (§3); it never
reaches the composite.

**The sup.**  `‖F₁ z‖ = ‖2 + 2cos z‖ · 2^{p(Δ − Re u(z))}`, and the two factors are bounded
against *different* witnesses — `‖2 + 2cos z‖ ≤ 2 + 2cosh(Im z)` (sharp, §1) and
`Re u ≥ −U` — which is why the round's ceiling is the product of the certifier's two
constants and not a bound on either alone. -/

/-- **The `M₁` integrand.** -/
noncomputable def jvMomFc1 (z : ℂ) : ℂ :=
  (2 + 2 * Complex.cos z) *
    Complex.exp ((((jvPQ : ℝ) : ℂ) * (((jvDeltaQ : ℝ) : ℂ) - jvUcx z)) * L2C)

/-- **The `M₂` integrand.** -/
noncomputable def jvMomFc2 (z : ℂ) : ℂ :=
  (2 + 2 * Complex.cos z) *
    Complex.exp ((((jvQmQ : ℝ) : ℂ) *
      ((((jvAGammaQ : ℝ) : ℂ) * jvVcx z) - jvUcx z)) * L2C)

theorem differentiableAt_jvMomFc1 {z : ℂ} (hz : z ∈ stripZ)
    (hslit : jvPcx z ∈ Complex.slitPlane) : DifferentiableAt ℂ jvMomFc1 z := by
  have hcos : DifferentiableAt ℂ (fun z : ℂ => (2 : ℂ) + 2 * Complex.cos z) z := by fun_prop
  have hu := differentiableAt_jvUcx hz hslit
  have hlin : DifferentiableAt ℂ
      (fun w : ℂ => (((jvPQ : ℝ) : ℂ) * (((jvDeltaQ : ℝ) : ℂ) - jvUcx w)) * L2C) z :=
    ((differentiableAt_const _).mul ((differentiableAt_const _).sub hu)).mul_const L2C
  exact hcos.mul hlin.cexp

theorem differentiableAt_jvMomFc2 {z : ℂ} (hz : z ∈ stripZ)
    (hslit : jvPcx z ∈ Complex.slitPlane) : DifferentiableAt ℂ jvMomFc2 z := by
  have hcos : DifferentiableAt ℂ (fun z : ℂ => (2 : ℂ) + 2 * Complex.cos z) z := by fun_prop
  have hu := differentiableAt_jvUcx hz hslit
  have hv := differentiableAt_jvVcx hz hslit
  have hlin : DifferentiableAt ℂ
      (fun w : ℂ => (((jvQmQ : ℝ) : ℂ) *
        ((((jvAGammaQ : ℝ) : ℂ) * jvVcx w) - jvUcx w)) * L2C) z :=
    ((differentiableAt_const _).mul
      (((differentiableAt_const _).mul hv).sub hu)).mul_const L2C
  exact hcos.mul hlin.cexp

/-! #### §4.1 — the two real reductions the sup needs -/

/-- On `ℂ`, `2^{x}` read as `exp(x log 2)` — the only entire reading, and the one that makes
`Real.rpow` and `Complex.exp` the same function on the real axis (§6). -/
theorem exp_log2_mul (x : ℝ) : Real.exp (Real.log 2 * x) = (2 : ℝ) ^ x :=
  (Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) x).symm

theorem re_real_mul_sub (a b : ℝ) (w : ℂ) :
    ((((a : ℝ) : ℂ) * (((b : ℝ) : ℂ) - w)) * L2C).re
      = Real.log 2 * (a * (b - w.re)) := by
  simp only [L2C, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem re_real_mul_sub2 (a g : ℝ) (v w : ℂ) :
    ((((a : ℝ) : ℂ) * ((((g : ℝ) : ℂ) * v) - w)) * L2C).re
      = Real.log 2 * (a * (g * v.re - w.re)) := by
  simp only [L2C, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- `Re((p·(Δ − u))·log 2) = log 2 · p · (Δ − Re u)` for real `p`, `Δ`. -/
theorem re_momFc1_arg (z : ℂ) :
    ((((jvPQ : ℝ) : ℂ) * (((jvDeltaQ : ℝ) : ℂ) - jvUcx z)) * L2C).re
      = Real.log 2 * ((jvPQ : ℝ) * ((jvDeltaQ : ℝ) - (jvUcx z).re)) :=
  re_real_mul_sub _ _ _

theorem re_momFc2_arg (z : ℂ) :
    ((((jvQmQ : ℝ) : ℂ) *
      ((((jvAGammaQ : ℝ) : ℂ) * jvVcx z) - jvUcx z)) * L2C).re
      = Real.log 2 * ((jvQmQ : ℝ) * ((jvAGammaQ : ℝ) * (jvVcx z).re - (jvUcx z).re)) :=
  re_real_mul_sub2 _ _ _ _

theorem norm_two_add_two_cos_le {z : ℂ} (hz : z ∈ stripZ) :
    ‖(2 : ℂ) + 2 * Complex.cos z‖ ≤ 2 + 2 * Real.cosh stripA := by
  refine (norm_two_add_two_cos z).trans ?_
  have h1 : Real.cosh z.im ≤ Real.cosh stripA := by
    refine (Real.cosh_le_cosh).mpr ?_
    rw [abs_of_pos stripA_pos]
    exact le_of_lt hz
  linarith

/-- **The `M₁` sup on the strip**, given `Re u ≥ −U`. -/
theorem norm_jvMomFc1_le {z : ℂ} (hz : z ∈ stripZ) {U : ℝ}
    (hU : -U ≤ (jvUcx z).re) :
    ‖jvMomFc1 z‖ ≤ (2 + 2 * Real.cosh stripA) * (2 : ℝ) ^ ((jvPQ : ℝ) * ((jvDeltaQ : ℝ) + U)) := by
  have hexp : ‖Complex.exp ((((jvPQ : ℝ) : ℂ) * (((jvDeltaQ : ℝ) : ℂ) - jvUcx z)) * L2C)‖
      = Real.exp (Real.log 2 * ((jvPQ : ℝ) * ((jvDeltaQ : ℝ) - (jvUcx z).re))) := by
    rw [Complex.norm_exp, re_momFc1_arg]
  rw [jvMomFc1, norm_mul, hexp]
  have hw := norm_two_add_two_cos_le hz
  have hp : (0 : ℝ) ≤ (jvPQ : ℝ) := by norm_num [jvPQ]
  have hexp_le : Real.exp (Real.log 2 * ((jvPQ : ℝ) * ((jvDeltaQ : ℝ) - (jvUcx z).re)))
      ≤ Real.exp (Real.log 2 * ((jvPQ : ℝ) * ((jvDeltaQ : ℝ) + U))) := by
    refine Real.exp_le_exp.mpr ?_
    have hl : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hinner : (jvDeltaQ : ℝ) - (jvUcx z).re ≤ (jvDeltaQ : ℝ) + U := by linarith
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinner hp) hl.le
  refine mul_le_mul hw hexp_le (by positivity) (by positivity) |>.trans ?_
  rw [exp_log2_mul]

/-- **The `M₂` sup on the strip**, given `Re u ≥ −U` and `Re v ≤ W`. -/
theorem norm_jvMomFc2_le {z : ℂ} (hz : z ∈ stripZ) {U W : ℝ}
    (hU : -U ≤ (jvUcx z).re) (hW : (jvVcx z).re ≤ W) :
    ‖jvMomFc2 z‖
      ≤ (2 + 2 * Real.cosh stripA) * (2 : ℝ) ^ ((jvQmQ : ℝ) * ((jvAGammaQ : ℝ) * W + U)) := by
  have hexp : ‖Complex.exp ((((jvQmQ : ℝ) : ℂ) *
      ((((jvAGammaQ : ℝ) : ℂ) * jvVcx z) - jvUcx z)) * L2C)‖
      = Real.exp (Real.log 2 *
        ((jvQmQ : ℝ) * ((jvAGammaQ : ℝ) * (jvVcx z).re - (jvUcx z).re))) := by
    rw [Complex.norm_exp, re_momFc2_arg]
  rw [jvMomFc2, norm_mul, hexp]
  have hw := norm_two_add_two_cos_le hz
  have hq : (0 : ℝ) ≤ (jvQmQ : ℝ) := by norm_num [jvQmQ]
  have hg : (0 : ℝ) ≤ (jvAGammaQ : ℝ) := by norm_num [jvAGammaQ, jvDeltaQ, jvBigGammaQ, jvEtaQ, jvTau0Q]
  have hexp_le : Real.exp (Real.log 2 *
        ((jvQmQ : ℝ) * ((jvAGammaQ : ℝ) * (jvVcx z).re - (jvUcx z).re)))
      ≤ Real.exp (Real.log 2 * ((jvQmQ : ℝ) * ((jvAGammaQ : ℝ) * W + U))) := by
    refine Real.exp_le_exp.mpr ?_
    have hl : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have h1 : (jvAGammaQ : ℝ) * (jvVcx z).re ≤ (jvAGammaQ : ℝ) * W :=
      mul_le_mul_of_nonneg_left hW hg
    have hinner : (jvAGammaQ : ℝ) * (jvVcx z).re - (jvUcx z).re ≤ (jvAGammaQ : ℝ) * W + U := by
      linarith
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinner hq) hl.le
  refine mul_le_mul hw hexp_le (by positivity) (by positivity) |>.trans ?_
  rw [exp_log2_mul]

/-! #### §4.2 — the integer ceilings

`sim/sim_strip.py` §3 measured the certifier's own sup ceilings: `⌈p(Δ+U*)⌉ = 12` and
`⌈q(a_Γ W* + U*)⌉ = 21`, so the sup bound is `W_out · 2²¹ = 8472774.07`, and `8472775` is that
rounded up — the number `JV1000Decay` §7 takes as `hMle`.  Both ceilings are discharged here
against the certifier's rational replacements `U* ≤ 1.326`, `W* ≤ 19.178`. -/

/-- `2 + 2cosh(1/5)` — the `|2 + 2cos z|` factor at the head of the strip, **sharp**: the
ceiling `8472775` leaves `0.9` of room against it, so the lossy `‖re‖ + ‖im‖` bound would
overshoot (see §1.1). -/
noncomputable def jvWout : ℝ := 2 + 2 * Real.cosh stripA

theorem cosh_stripA_le : Real.cosh stripA ≤ 1.0200668 := by
  rw [show stripA = 1 / 5 from rfl, Real.cosh_eq]
  have h1 := Real.exp_bound (x := (1 / 5 : ℝ)) (by norm_num) (n := 8) (by norm_num)
  have h2 := Real.exp_bound (x := (-1 / 5 : ℝ)) (by norm_num) (n := 8) (by norm_num)
  have h1u := (abs_le.1 h1).2
  have h2u := (abs_le.1 h2).2
  norm_num [Finset.sum_range_succ, Nat.factorial] at h1u h2u ⊢
  linarith

theorem jvWout_le : jvWout ≤ 4.0401336 := by
  have := cosh_stripA_le
  rw [jvWout]; linarith

theorem jvWout_nonneg : 0 ≤ jvWout := by
  rw [jvWout]; have := Real.cosh_pos stripA; linarith

/-- `W_out · 2¹² = W_out · 2^{⌈sup₁⌉}` — the `M₁` ceiling. -/
noncomputable def jvM1 : ℝ := jvWout * 2 ^ (12 : ℕ)

/-- `W_out · 2²¹ = W_out · 2^{⌈sup₂⌉}` — the `M₂` ceiling, and the sup bound §5 needs. -/
noncomputable def jvM2 : ℝ := jvWout * 2 ^ (21 : ℕ)

theorem jvM1_le_jvM2 : jvM1 ≤ jvM2 := by
  rw [jvM1, jvM2]
  have h : (2:ℝ) ^ 12 ≤ (2:ℝ) ^ 21 := by norm_num
  exact mul_le_mul_of_nonneg_left h jvWout_nonneg

theorem jvM2_le_8472775 : jvM2 ≤ 8472775 := by
  rw [jvM2]
  have h2 : (2:ℝ) ^ 21 = 2097152 := by norm_num
  rw [h2]
  nlinarith [jvWout_le]

/-! #### §4.3 — the ceilings at the certifier's rational replacements

`sim/sim_strip.py` gave `U* = 1.3257824281348167`, `W* = 19.177318435217348`; the two
rational bounds below are those rounded **up** (`1.326`, `19.178`), so any statement proved
against them is proved against the certifier's constants.  Then `p(Δ+U) ≤ 12` and
`q(a_Γ W + U) ≤ 21` — the integer ceilings `sim/sim_strip.py` §3 measured. -/

theorem jvM1_arg_le : (jvPQ : ℝ) * ((jvDeltaQ : ℝ) + 1.326) ≤ 12 := by
  have hp : (jvPQ : ℝ) = 845902160 / 100000000 := by norm_num [jvPQ]
  have hd : (jvDeltaQ : ℝ) = 286969377 / 10000000000 := by norm_num [jvDeltaQ, jvEtaQ, jvTau0Q]
  rw [hp, hd]; norm_num

theorem jvM2_arg_le : (jvQmQ : ℝ) * ((jvAGammaQ : ℝ) * 19.178 + 1.326) ≤ 21 := by
  have hq : (jvQmQ : ℝ) = 827015425 / 100000000 := by norm_num [jvQmQ]
  have hg : (jvAGammaQ : ℝ) = 286969377 / 4588782659 := by
    norm_num [jvAGammaQ, jvDeltaQ, jvBigGammaQ, jvEtaQ, jvTau0Q]
  rw [hq, hg]; norm_num

/-- **The `M₁` ceiling on the strip**: `‖F₁‖ ≤ W_out · 2¹² ≤ 8472775`. -/
theorem norm_jvMomFc1_le_ceiling {z : ℂ} (hz : z ∈ stripZ) (hU : -1.326 ≤ (jvUcx z).re) :
    ‖jvMomFc1 z‖ ≤ 8472775 := by
  refine (norm_jvMomFc1_le hz (U := 1.326) hU).trans ?_
  have hb := jvM1_arg_le
  have hstep : (2 : ℝ) ^ ((jvPQ : ℝ) * ((jvDeltaQ : ℝ) + 1.326)) ≤ 4096 := by
    have h := (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).2 hb
    have h12 : (2 : ℝ) ^ (12 : ℝ) = 4096 := by
      rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]; norm_num
    rwa [h12] at h
  calc (2 + 2 * Real.cosh stripA) * (2 : ℝ) ^ ((jvPQ : ℝ) * ((jvDeltaQ : ℝ) + 1.326))
      = jvWout * (2 : ℝ) ^ ((jvPQ : ℝ) * ((jvDeltaQ : ℝ) + 1.326)) := by rw [jvWout]
    _ ≤ jvWout * 4096 := by
        refine mul_le_mul_of_nonneg_left hstep jvWout_nonneg
    _ = jvM1 := by rw [jvM1]; norm_num
    _ ≤ jvM2 := jvM1_le_jvM2
    _ ≤ 8472775 := jvM2_le_8472775

/-- **The `M₂` ceiling on the strip**: `‖F₂‖ ≤ W_out · 2²¹ ≤ 8472775` — the number
`JV1000Decay` §7 takes as `hMle`. -/
theorem norm_jvMomFc2_le_ceiling {z : ℂ} (hz : z ∈ stripZ)
    (hU : -1.326 ≤ (jvUcx z).re) (hW : (jvVcx z).re ≤ 19.178) :
    ‖jvMomFc2 z‖ ≤ 8472775 := by
  refine (norm_jvMomFc2_le hz (U := 1.326) (W := 19.178) hU hW).trans ?_
  have hb := jvM2_arg_le
  have hstep : (2 : ℝ) ^ ((jvQmQ : ℝ) * ((jvAGammaQ : ℝ) * 19.178 + 1.326)) ≤ 2097152 := by
    have h := (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).2 hb
    have h21 : (2 : ℝ) ^ (21 : ℝ) = 2097152 := by
      rw [show (21 : ℝ) = ((21 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]; norm_num
    rwa [h21] at h
  calc (2 + 2 * Real.cosh stripA)
        * (2 : ℝ) ^ ((jvQmQ : ℝ) * ((jvAGammaQ : ℝ) * 19.178 + 1.326))
      = jvWout * (2 : ℝ) ^ ((jvQmQ : ℝ) * ((jvAGammaQ : ℝ) * 19.178 + 1.326)) := by rw [jvWout]
    _ ≤ jvWout * 2097152 := mul_le_mul_of_nonneg_left hstep jvWout_nonneg
    _ = jvM2 := by rw [jvM2]; norm_num
    _ ≤ 8472775 := jvM2_le_8472775

/-! ### §5 — periodicity, and the feed into `JV1000Decay` §7

`quadrature_at_256_of_strip` wants four things of the integrand: holomorphy on the strip,
a sup bound there, `2π`-periodicity there, and its real-axis restriction.  §4 gave the first
two; periodicity is inherited from `jvRcx_add_two_pi` through the integrals, and the real-axis
restriction is the definition of `jvMomF1` (so `hF` is `rfl`).  The two remaining hypotheses
of the feed — `hFint` and `happrox` — are properties of the enclosure, not of the analysis:
`happrox` is §7's named tail `ε` (measured `~10⁻¹⁶`, allowed `10⁻²⁰`). -/

theorem PInt_add_two_pi (z : ℂ) (y : ℝ) :
    PInt (z + ((2 * Real.pi : ℝ) : ℂ)) y = PInt z y := by
  unfold PInt
  have hr : jvRcx ((z + ((2 * Real.pi : ℝ) : ℂ)) + (y : ℂ)) = jvRcx (z + (y : ℂ)) := by
    rw [show (z + ((2 * Real.pi : ℝ) : ℂ)) + (y : ℂ)
        = (z + (y : ℂ)) + ((2 * Real.pi : ℝ) : ℂ) from by ring]
    exact jvRcx_add_two_pi _
  rw [hr]

theorem YInt_add_two_pi (z : ℂ) (y : ℝ) :
    YInt (z + ((2 * Real.pi : ℝ) : ℂ)) y = YInt z y := by
  unfold YInt
  have hr : jvRcx ((z + ((2 * Real.pi : ℝ) : ℂ)) + (y : ℂ)) = jvRcx (z + (y : ℂ)) := by
    rw [show (z + ((2 * Real.pi : ℝ) : ℂ)) + (y : ℂ)
        = (z + (y : ℂ)) + ((2 * Real.pi : ℝ) : ℂ) from by ring]
    exact jvRcx_add_two_pi _
  rw [hr, PInt_add_two_pi]

theorem jvPcx_add_two_pi (z : ℂ) :
    jvPcx (z + ((2 * Real.pi : ℝ) : ℂ)) = jvPcx z := by
  unfold jvPcx
  rw [intervalIntegral.integral_congr (fun y _ => PInt_add_two_pi z y)]

theorem jvYcx_add_two_pi (z : ℂ) :
    jvYcx (z + ((2 * Real.pi : ℝ) : ℂ)) = jvYcx z := by
  unfold jvYcx
  rw [intervalIntegral.integral_congr (fun y _ => YInt_add_two_pi z y)]

theorem jvUcx_add_two_pi (z : ℂ) :
    jvUcx (z + ((2 * Real.pi : ℝ) : ℂ)) = jvUcx z := by
  unfold jvUcx
  rw [jvPcx_add_two_pi, jvYcx_add_two_pi]

theorem jvVcx_add_two_pi (z : ℂ) :
    jvVcx (z + ((2 * Real.pi : ℝ) : ℂ)) = jvVcx z := by
  unfold jvVcx
  rw [jvPcx_add_two_pi, jvYcx_add_two_pi]

theorem jvMomFc1_add_two_pi (z : ℂ) :
    jvMomFc1 (z + ((2 * Real.pi : ℝ) : ℂ)) = jvMomFc1 z := by
  unfold jvMomFc1
  rw [show (2 : ℂ) + 2 * Complex.cos (z + ((2 * Real.pi : ℝ) : ℂ)) = 2 + 2 * Complex.cos z from by
        rw [show z + ((2 * Real.pi : ℝ) : ℂ) = z + ((1 : ℤ)) * (2 * (Real.pi : ℂ)) from by
          push_cast; ring, Complex.cos_add_int_mul_two_pi],
    jvUcx_add_two_pi]

theorem jvMomFc2_add_two_pi (z : ℂ) :
    jvMomFc2 (z + ((2 * Real.pi : ℝ) : ℂ)) = jvMomFc2 z := by
  unfold jvMomFc2
  rw [show (2 : ℂ) + 2 * Complex.cos (z + ((2 * Real.pi : ℝ) : ℂ)) = 2 + 2 * Complex.cos z from by
        rw [show z + ((2 * Real.pi : ℝ) : ℂ) = z + ((1 : ℤ)) * (2 * (Real.pi : ℂ)) from by
          push_cast; ring, Complex.cos_add_int_mul_two_pi],
    jvUcx_add_two_pi, jvVcx_add_two_pi]

/-- The real-axis restriction of the `M₁` integrand — the function `§7` integrates. -/
noncomputable def jvMomF1 : ℝ → ℂ := fun x => jvMomFc1 (x : ℂ)

/-- The real-axis restriction of the `M₂` integrand. -/
noncomputable def jvMomF2 : ℝ → ℂ := fun x => jvMomFc2 (x : ℂ)

theorem mem_stripZ_ofReal (x : ℝ) : (x : ℂ) ∈ stripZ := by
  show |((x : ℂ)).im| < stripA
  simp only [Complex.ofReal_im, abs_zero]
  exact stripA_pos

/-- **THE FEED.**  `JV1000Decay` §7 applied to the `M₁` integrand: the quadrature error at the
certifier's own `n = 256` is `≤ 10⁻⁶`, from the strip data this file proves.  The remaining
hypotheses are the two enclosure-side ones (`hFint`, `happrox`) and the measured strip bound
`Re u ≥ −U*`. -/
theorem quadrature_jvMomF1
    (hslit : ∀ z ∈ stripZ, jvPcx z ∈ Complex.slitPlane)
    (hU : ∀ z ∈ stripZ, -1.326 ≤ (jvUcx z).re)
    {K : ℕ} (hK : K ≤ 32) {ε : ℝ} (hε : ε ≤ 1 / 10 ^ 20)
    (hFint : IntervalIntegrable jvMomF1 MeasureTheory.volume (0 : ℝ) (2 * Real.pi))
    (happrox : ∀ x ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      ‖jvMomF1 x - ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), fourierCoeff jvMomF1 k * charF k x‖ ≤ ε) :
    ‖circleMean jvMomF1 - trapMean 256 jvMomF1‖ ≤ 1 / 10 ^ 6 := by
  refine quadrature_at_256_of_strip (g := jvMomFc1) (M := 8472775) (ε := ε) (K := K)
    (by norm_num) (le_refl _) hK hε ?_ ?_ ?_ ?_ hFint happrox
  · exact fun z hz => (differentiableAt_jvMomFc1 hz (hslit z hz)).differentiableWithinAt
  · exact fun z hz => norm_jvMomFc1_le_ceiling hz (hU z hz)
  · intro z hz
    exact jvMomFc1_add_two_pi z
  · intro x
    rfl

/-- **THE FEED, `M₂`.** -/
theorem quadrature_jvMomF2
    (hslit : ∀ z ∈ stripZ, jvPcx z ∈ Complex.slitPlane)
    (hU : ∀ z ∈ stripZ, -1.326 ≤ (jvUcx z).re)
    (hV : ∀ z ∈ stripZ, (jvVcx z).re ≤ 19.178)
    {K : ℕ} (hK : K ≤ 32) {ε : ℝ} (hε : ε ≤ 1 / 10 ^ 20)
    (hFint : IntervalIntegrable jvMomF2 MeasureTheory.volume (0 : ℝ) (2 * Real.pi))
    (happrox : ∀ x ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      ‖jvMomF2 x - ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), fourierCoeff jvMomF2 k * charF k x‖ ≤ ε) :
    ‖circleMean jvMomF2 - trapMean 256 jvMomF2‖ ≤ 1 / 10 ^ 6 := by
  refine quadrature_at_256_of_strip (g := jvMomFc2) (M := 8472775) (ε := ε) (K := K)
    (by norm_num) (le_refl _) hK hε ?_ ?_ ?_ ?_ hFint happrox
  · exact fun z hz => (differentiableAt_jvMomFc2 hz (hslit z hz)).differentiableWithinAt
  · exact fun z hz => norm_jvMomFc2_le_ceiling hz (hU z hz) (hV z hz)
  · intro z hz
    exact jvMomFc2_add_two_pi z
  · intro x
    rfl

/-! ### §6 — the real-axis bridge, and `jv_m1_cert` one comparison away

§5's feed integrates `jvMomF1`, the composite restricted to `ℝ`.  For that to be the
*certified* moment, the restricted composite must be the number `JV1000Moments` names
`jvMomentRho0Cert` — i.e. `2^{p(Δ−u)}` with `u` the **real** `jvU`, which means
`Complex.log` on the real axis must be `Real.log` and `exp(w log 2)` must be `Real.rpow`.
Both are the content of §6.1.  Then §6.2 turns the `10⁻⁶` quadrature bound plus one
decidable numeric fact about `trapMean 256` into `jvMomentRho0Cert < 2^{ρ_c}`.

**Why `jvP x ≥ 0` is not a separate premise.**  `jvPcx x` *is* `↑(jvP x)` (6.1), and
`hslit` says it is in `Complex.slitPlane`; a strictly negative real is not (`re < 0`,
`im = 0`).  So `hslit` already carries the sign, and positivity of `jvP` is a corollary
of the branch condition rather than another measured fact. -/

theorem ofReal_two_rpow (x : ℝ) :
    (((2 : ℝ) ^ x : ℝ) : ℂ) = Complex.exp ((Real.log 2 * x : ℝ) : ℂ) := by
  rw [← Complex.ofReal_exp, exp_log2_mul]

theorem PInt_ofReal (x y : ℝ) :
    PInt (x : ℂ) y = (((2 : ℝ) ^ (jvLogDensityR (x + y) + jvLogDensityS y) : ℝ) : ℂ) := by
  unfold PInt
  have harg : jvRcx ((x : ℂ) + (y : ℂ)) + jvScx ((y : ℂ))
      = ((jvLogDensityR (x + y) + jvLogDensityS y : ℝ) : ℂ) := by
    rw [show (x : ℂ) + (y : ℂ) = ((x + y : ℝ) : ℂ) from by push_cast; ring]
    rw [jvRcx_ofReal, jvScx_ofReal]
    push_cast
    ring
  rw [harg]
  unfold L2C
  rw [show ((Real.log 2 : ℝ) : ℂ) * (((jvLogDensityR (x + y) + jvLogDensityS y : ℝ)) : ℂ)
      = ((Real.log 2 * (jvLogDensityR (x + y) + jvLogDensityS y) : ℝ) : ℂ) from by push_cast; ring]
  exact (ofReal_two_rpow _).symm

theorem YInt_ofReal (x y : ℝ) :
    YInt (x : ℂ) y = (((jvLogDensityR (x + y) + jvLogDensityS y)
      * (2 : ℝ) ^ (jvLogDensityR (x + y) + jvLogDensityS y) : ℝ) : ℂ) := by
  unfold YInt
  rw [PInt_ofReal]
  have harg : jvRcx ((x : ℂ) + (y : ℂ)) + jvScx ((y : ℂ))
      = ((jvLogDensityR (x + y) + jvLogDensityS y : ℝ) : ℂ) := by
    rw [show (x : ℂ) + (y : ℂ) = ((x + y : ℝ) : ℂ) from by push_cast; ring]
    rw [jvRcx_ofReal, jvScx_ofReal]
    push_cast
    ring
  rw [harg]
  push_cast
  ring

/-- **`P_c` on the real axis is `jvP`.** -/
theorem jvPcx_ofReal (x : ℝ) : jvPcx (x : ℂ) = ((jvP x : ℝ) : ℂ) := by
  unfold jvPcx jvP
  have hfun : (fun y : ℝ => PInt (x : ℂ) y)
      = fun y : ℝ => ((((2 : ℝ) ^ (jvLogDensityR (x + y) + jvLogDensityS y) : ℝ)) : ℂ) := by
    funext y; exact PInt_ofReal x y
  rw [hfun, intervalIntegral.integral_ofReal]
  push_cast; ring

/-- **`Y_c` on the real axis is `jvY`.** -/
theorem jvYcx_ofReal (x : ℝ) : jvYcx (x : ℂ) = ((jvY x : ℝ) : ℂ) := by
  unfold jvYcx jvY
  have hfun : (fun y : ℝ => YInt (x : ℂ) y)
      = fun y : ℝ => ((((jvLogDensityR (x + y) + jvLogDensityS y)
        * (2 : ℝ) ^ (jvLogDensityR (x + y) + jvLogDensityS y) : ℝ)) : ℂ) := by
    funext y; exact YInt_ofReal x y
  rw [hfun, intervalIntegral.integral_ofReal]
  push_cast; ring

/-- `jvP x ≥ 0`, from the branch condition — see the section note. -/
theorem jvP_nonneg_of_slit {x : ℝ} (hslit : jvPcx (x : ℂ) ∈ Complex.slitPlane) : 0 ≤ jvP x := by
  rw [jvPcx_ofReal] at hslit
  rw [Complex.mem_slitPlane_iff] at hslit
  simp only [Complex.ofReal_re, Complex.ofReal_im, ne_eq, not_true_eq_false, or_false] at hslit
  linarith

/-- `log₂` on the real axis is `Complex.log / log 2`. -/
theorem logb_jvP_eq {x : ℝ} (hP : 0 ≤ jvP x) :
    ((Real.logb 2 (jvP x) : ℝ) : ℂ) = Complex.log (jvPcx (x : ℂ)) / L2C := by
  rw [jvPcx_ofReal, Real.logb, Complex.ofReal_div, Complex.ofReal_log hP, L2C]

/-- **`u` on the real axis is `jvU`.** -/
theorem jvUcx_ofReal {x : ℝ} (hslit : jvPcx (x : ℂ) ∈ Complex.slitPlane) :
    jvUcx (x : ℂ) = ((jvU x : ℝ) : ℂ) := by
  have hP := jvP_nonneg_of_slit hslit
  have hlog2 : (Real.log 2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hlogb := logb_jvP_eq hP
  have hY : jvYcx (x : ℂ) = ((jvY x : ℝ) : ℂ) := jvYcx_ofReal x
  have hPc : jvPcx (x : ℂ) = ((jvP x : ℝ) : ℂ) := jvPcx_ofReal x
  have hPne : (jvP x : ℝ) ≠ 0 := by
    intro h
    have hslit' := hslit
    rw [hPc, h] at hslit'
    rw [Complex.mem_slitPlane_iff] at hslit'
    simp at hslit'
  unfold jvUcx jvU
  rw [← hlogb, hY, hPc]
  push_cast [hPne]; field_simp

/-- **`v` on the real axis is `jvV`.** -/
theorem jvVcx_ofReal {x : ℝ} (hslit : jvPcx (x : ℂ) ∈ Complex.slitPlane) :
    jvVcx (x : ℂ) = ((jvV x : ℝ) : ℂ) := by
  have hP := jvP_nonneg_of_slit hslit
  have hlogb := logb_jvP_eq hP
  have hY : jvYcx (x : ℂ) = ((jvY x : ℝ) : ℂ) := jvYcx_ofReal x
  have hPc : jvPcx (x : ℂ) = ((jvP x : ℝ) : ℂ) := jvPcx_ofReal x
  have hPne : (jvP x : ℝ) ≠ 0 := by
    intro h
    have hslit' := hslit
    rw [hPc, h] at hslit'
    rw [Complex.mem_slitPlane_iff] at hslit'
    simp at hslit'
  unfold jvVcx jvV
  rw [← hlogb, hY, hPc]
  push_cast [hPne]; field_simp

/-- The **real** `M₁` integrand, exactly as `jvMomentRho0Cert` integrates it. -/
noncomputable def jvRho1 (x : ℝ) : ℝ :=
  (2 + 2 * Real.cos x) * (2 : ℝ) ^ ((jvPQ : ℝ) * ((jvDeltaQ : ℝ) - jvU x))

/-- The **real** `M₂` integrand. -/
noncomputable def jvRho2 (x : ℝ) : ℝ :=
  (2 + 2 * Real.cos x) * (2 : ℝ) ^ ((jvQmQ : ℝ) * ((jvAGammaQ : ℝ) * jvV x - jvU x))

/-- **THE BRIDGE, `M₁`**: the restricted composite *is* the certified real integrand. -/
theorem jvMomF1_eq {x : ℝ} (hslit : jvPcx (x : ℂ) ∈ Complex.slitPlane) :
    jvMomF1 x = ((jvRho1 x : ℝ) : ℂ) := by
  have hu := jvUcx_ofReal hslit
  unfold jvMomF1 jvMomFc1 jvRho1
  rw [hu]
  have hcos : Complex.cos ((x : ℂ)) = ((Real.cos x : ℝ) : ℂ) :=
    (Complex.ofReal_cos x).symm
  rw [hcos]
  rw [show (((jvPQ : ℝ) : ℂ) * (((jvDeltaQ : ℝ) : ℂ) - ((jvU x : ℝ) : ℂ))) * L2C
      = (((Real.log 2 * ((jvPQ : ℝ) * ((jvDeltaQ : ℝ) - jvU x)) : ℝ)) : ℂ) from by
    unfold L2C; push_cast; ring]
  rw [← Complex.ofReal_exp, exp_log2_mul]
  push_cast <;> ring

/-- **THE BRIDGE, `M₂`.** -/
theorem jvMomF2_eq {x : ℝ} (hslit : jvPcx (x : ℂ) ∈ Complex.slitPlane) :
    jvMomF2 x = ((jvRho2 x : ℝ) : ℂ) := by
  have hu := jvUcx_ofReal hslit
  have hv := jvVcx_ofReal hslit
  unfold jvMomF2 jvMomFc2 jvRho2
  rw [hu, hv]
  have hcos : Complex.cos ((x : ℂ)) = ((Real.cos x : ℝ) : ℂ) :=
    (Complex.ofReal_cos x).symm
  rw [hcos]
  rw [show (((jvQmQ : ℝ) : ℂ) *
        ((((jvAGammaQ : ℝ) : ℂ) * ((jvV x : ℝ) : ℂ)) - ((jvU x : ℝ) : ℂ))) * L2C
      = (((Real.log 2 * ((jvQmQ : ℝ) * ((jvAGammaQ : ℝ) * jvV x - jvU x)) : ℝ)) : ℂ) from by
    unfold L2C; push_cast; ring]
  rw [← Complex.ofReal_exp, exp_log2_mul]
  push_cast <;> ring

/-- **`circleMean` of the restricted composite is `jvMomentRho0Cert`, coerced.** -/
theorem circleMean_jvMomF1 (hslit : ∀ z ∈ stripZ, jvPcx z ∈ Complex.slitPlane) :
    circleMean jvMomF1 = ((jvMomentRho0Cert : ℝ) : ℂ) := by
  unfold circleMean jvMomentRho0Cert
  have hfun : jvMomF1 = fun x : ℝ =>
      (((2 + 2 * Real.cos x) * (2 : ℝ) ^ ((jvPQ : ℝ) * ((jvDeltaQ : ℝ) - jvU x)) : ℝ) : ℂ) := by
    funext x
    rw [jvMomF1_eq (hslit _ (mem_stripZ_ofReal x))]
    rfl
  rw [hfun, intervalIntegral.integral_ofReal]
  push_cast <;> ring

theorem circleMean_jvMomF2 (hslit : ∀ z ∈ stripZ, jvPcx z ∈ Complex.slitPlane) :
    circleMean jvMomF2 = ((jvMomentBandCert : ℝ) : ℂ) := by
  unfold circleMean jvMomentBandCert
  have hfun : jvMomF2 = fun x : ℝ =>
      (((2 + 2 * Real.cos x) * (2 : ℝ) ^ ((jvQmQ : ℝ) * ((jvAGammaQ : ℝ) * jvV x - jvU x)) : ℝ) : ℂ) := by
    funext x
    rw [jvMomF2_eq (hslit _ (mem_stripZ_ofReal x))]
    rfl
  rw [hfun, intervalIntegral.integral_ofReal]
  push_cast <;> ring

/-! ### §6.2 — the rational comparison, and `jv_m1_cert`

Everything analytic is now discharged.  What is left is: the `10⁻⁶` from §5, the measured
strip bounds (`hslit`, `hU`, `hV`), the enclosure's own two side conditions, and **one
numeric fact about `trapMean 256`** — `‖trapMean 256 F₁‖ + 10⁻⁶ < 2^{ρ_c}`, a statement
about 256 elementary terms that `JV1000Moments` §3 called "norm_num-scale".  Everything
else in the chain is a theorem. -/

/-- **`M₁ < 2^{ρ_c}` from the quadrature bound and the comparison.** -/
theorem jv_m1_cert_of_comparison
    (hslit : ∀ z ∈ stripZ, jvPcx z ∈ Complex.slitPlane)
    (hU : ∀ z ∈ stripZ, -1.326 ≤ (jvUcx z).re)
    {K : ℕ} (hK : K ≤ 32) {ε : ℝ} (hε : ε ≤ 1 / 10 ^ 20)
    (hFint : IntervalIntegrable jvMomF1 MeasureTheory.volume (0 : ℝ) (2 * Real.pi))
    (happrox : ∀ x ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      ‖jvMomF1 x - ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), fourierCoeff jvMomF1 k * charF k x‖ ≤ ε)
    (hcmp : ‖trapMean 256 jvMomF1‖ + 1 / 10 ^ 6 < (2 : ℝ) ^ ((jvRhoCQ : ℝ))) :
    jvMomentRho0Cert < (2 : ℝ) ^ ((jvRhoCQ : ℝ)) := by
  have hq := quadrature_jvMomF1 hslit hU hK hε hFint happrox
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

/-- **`M₂ < 2^{ρ_c}` from the quadrature bound and the comparison.** -/
theorem jv_m2_cert_of_comparison
    (hslit : ∀ z ∈ stripZ, jvPcx z ∈ Complex.slitPlane)
    (hU : ∀ z ∈ stripZ, -1.326 ≤ (jvUcx z).re)
    (hV : ∀ z ∈ stripZ, (jvVcx z).re ≤ 19.178)
    {K : ℕ} (hK : K ≤ 32) {ε : ℝ} (hε : ε ≤ 1 / 10 ^ 20)
    (hFint : IntervalIntegrable jvMomF2 MeasureTheory.volume (0 : ℝ) (2 * Real.pi))
    (happrox : ∀ x ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      ‖jvMomF2 x - ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), fourierCoeff jvMomF2 k * charF k x‖ ≤ ε)
    (hcmp : ‖trapMean 256 jvMomF2‖ + 1 / 10 ^ 6 < (2 : ℝ) ^ ((jvRhoCQ : ℝ))) :
    jvMomentBandCert < (2 : ℝ) ^ ((jvRhoCQ : ℝ)) := by
  have hq := quadrature_jvMomF2 hslit hU hV hK hε hFint happrox
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

end SubsetSumL25.Row
