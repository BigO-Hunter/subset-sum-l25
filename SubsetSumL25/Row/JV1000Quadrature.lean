/-
`SubsetSumL25.Row.JV1000Quadrature` — the interval-quadrature error bound the
jv1000 moments need, in the only form an *elementary* interval proof can use:
the trapezoid rule against a **Lipschitz** constant, with no derivative and no
analyticity hypothesis.

Why this file exists, and what it is worth — measured, not asserted.

C6 (`M₁`, `M₂`) has to be evaluated to better than `1.3·10⁻⁶` in absolute terms
(`ρ_c = 0.5162696413`, the moments sit at `2^{0.5162683} ≈ 1.4302509`, so the
margin is `1.3·10⁻⁶` on a quantity of size `1.43`).  Three candidate error
proofs, with the numbers this lane actually measured (`sim/sim_m1.py`):

1. **Trapezoid + Lipschitz error** (this file).  For a Lipschitz function with
   constant `L`, the trapezoid error over `n` equal panels is at most
   `L·(b−a)²/(2n)`.  The ρ₀ integrand's Lipschitz constant is
   `K = 2^{p(Δ+3.21)}·(2 + 4·log 2·p·lip16) = 5.07·10¹⁰`
   (from `|r| ≤ 3.21` and `lip16 = 12.16437058`, both in-tree — `jv_abs_density_r`,
   `jv_lip16_value_r`).  Reaching `1.3·10⁻⁶` therefore needs
   `n ≥ K·(2π)²/(2·1.3·10⁻⁶) ≈ 1.2·10¹⁷` panels.  **The bound is correct and
   useless**: the true trapezoid error at `n = 256` is of order `10⁻¹²`, i.e. the
   Lipschitz bound is ~20 orders of magnitude pessimistic here.
2. **Higher-order (C²) Taylor error.**  Buys a factor `n`, not the 10¹⁷ needed.
3. **Strip analyticity (the certifier's own route).**  The integrand is a finite
   trigonometric polynomial, hence entire; the periodic trapezoid rule on a
   function analytic in a strip converges *geometrically*.  The audit pack's strip
   bound is `q₀ = 0.3708350894162912`, so `q₀^n < 10⁻¹⁷` already at `n = 40`.
   **This is the architecture a Lean proof of C6 must use**, and it needs Cauchy
   estimates on a complex strip rather than anything in this file.

So this module is the *cheap half*: the error theorem is proved, reusable, and
honest, and it is what let the lane **measure** that the Lipschitz route is
closed.  It is not, and is not offered as, the route to C6.

Constant discipline, stated rather than hidden: the sharp constant for the
trapezoid rule on a Lipschitz function is `1/4` (attained by the tent
`L|x − (a+b)/2|`); the chord-deviation argument below gives `1/3` if one
integrates the pointwise majorant `2L(x−a)(b−x)/(b−a)` exactly, and `1/2` if one
uses the cruder pointwise majorant `L(b−a)/2`, which needs **no polynomial
quadrature at all**.  This file takes `1/2`: the factor 2 against the sharp `1/4`
is irrelevant next to the 10¹⁷ above, and refusing to compute `∫ x²` costs
nothing.  Stated so the next author does not mistake `1/2` for sharp.
-/
import Mathlib

namespace SubsetSumL25.Row

open MeasureTheory intervalIntegral

/-! ### §0 — the two elementary integrals -/

/-- `∫ x in a..b, x = (b² − a²)/2`. -/
theorem integral_self (a b : ℝ) : ∫ x in a..b, x = (b ^ 2 - a ^ 2) / 2 := by
  have h := integral_pow (a := a) (b := b) 1
  simpa using h

/-! ### §1 — the chord deviation

Everything reduces to one pointwise estimate: a Lipschitz function deviates from
its chord by at most `2L(x−a)(b−x)/(b−a)`, which is at most `L(b−a)/2`.  The two
halves of the deviation are bounded separately by the Lipschitz hypothesis,
which is why no derivative and no mean-value theorem appears. -/

/-- Pointwise chord deviation. -/
theorem chord_dev_le {f : ℝ → ℝ} {a b L : ℝ} (hab : a < b)
    (hlip : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |f x - f y| ≤ L * |x - y|)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    |f x - ((b - x) * f a + (x - a) * f b) / (b - a)|
      ≤ 2 * L * (x - a) * (b - x) / (b - a) := by
  have hba : (0 : ℝ) < b - a := by linarith
  have hxa : 0 ≤ x - a := by linarith [hx.1]
  have hbx : 0 ≤ b - x := by linarith [hx.2]
  have hxa' : |x - a| = x - a := abs_of_nonneg hxa
  have hbx' : |b - x| = b - x := abs_of_nonneg hbx
  have h1 : |f x - f a| ≤ L * (x - a) := by
    have := hlip x hx a ⟨le_refl a, le_of_lt hab⟩
    rwa [hxa'] at this
  have h2 : |f x - f b| ≤ L * (b - x) := by
    have := hlip x hx b ⟨le_of_lt hab, le_refl b⟩
    rw [show |x - b| = b - x from by rw [← abs_neg, neg_sub]; exact hbx'] at this
    exact this
  have hkey : f x - ((b - x) * f a + (x - a) * f b) / (b - a)
      = ((b - x) * (f x - f a) + (x - a) * (f x - f b)) / (b - a) := by
    field_simp
    ring
  rw [hkey, abs_div, abs_of_pos hba]
  apply div_le_div_of_nonneg_right _ (le_of_lt hba)
  calc |(b - x) * (f x - f a) + (x - a) * (f x - f b)|
      ≤ |(b - x) * (f x - f a)| + |(x - a) * (f x - f b)| := abs_add_le _ _
    _ = (b - x) * |f x - f a| + (x - a) * |f x - f b| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hbx, abs_of_nonneg hxa]
    _ ≤ (b - x) * (L * (x - a)) + (x - a) * (L * (b - x)) := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_left h1 hbx
        · exact mul_le_mul_of_nonneg_left h2 hxa
    _ = 2 * L * (x - a) * (b - x) := by ring

/-- The pointwise majorant, flattened to the panel-width bound
`2L(x−a)(b−x)/(b−a) ≤ L(b−a)/2` — the product `(x−a)(b−x)` peaks at `(b−a)²/4`
in the middle of the panel. -/
theorem chord_dev_le_const {f : ℝ → ℝ} {a b L : ℝ} (hab : a < b) (hL : 0 ≤ L)
    (hlip : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |f x - f y| ≤ L * |x - y|)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    |f x - ((b - x) * f a + (x - a) * f b) / (b - a)| ≤ L * (b - a) / 2 := by
  have hba : (0 : ℝ) < b - a := by linarith
  have h1 := chord_dev_le hab hlip hx
  have hxa : 0 ≤ x - a := by linarith [hx.1]
  have hbx : 0 ≤ b - x := by linarith [hx.2]
  -- (x−a)(b−x) ≤ ((b−a)/2)²  (AM–GM, with the sum forced by the panel)
  have hsum : (x - a) + (b - x) = b - a := by ring
  have hsq : 0 ≤ ((x - a) - (b - x)) ^ 2 := sq_nonneg _
  have hprod : (x - a) * (b - x) ≤ ((b - a) / 2) ^ 2 := by nlinarith [hsum, hsq]
  have hstep : 2 * L * (x - a) * (b - x) / (b - a) ≤ L * (b - a) / 2 := by
    rw [div_le_iff₀ hba]
    nlinarith
  linarith

/-! ### §2 — the trapezoid rule on one panel -/

/-- The chord's integral is the trapezoid area: `∫ lerp = (b−a)(f a + f b)/2`. -/
theorem integral_lerp {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) :
    ∫ x in a..b, ((b - x) * f a + (x - a) * f b) / (b - a)
      = (b - a) * (f a + f b) / 2 := by
  have hba : (0 : ℝ) < b - a := by linarith
  have hlin : ∀ x : ℝ, ((b - x) * f a + (x - a) * f b) / (b - a)
      = ((f b - f a) / (b - a)) * x + ((b * f a - a * f b) / (b - a)) := by
    intro x
    field_simp
    ring
  have hfun : (fun x : ℝ => ((b - x) * f a + (x - a) * f b) / (b - a))
      = fun x => ((f b - f a) / (b - a)) * x + ((b * f a - a * f b) / (b - a)) :=
    funext hlin
  rw [hfun, intervalIntegral.integral_add
      (f := fun x : ℝ => ((f b - f a) / (b - a)) * x)
      (g := fun _ => ((b * f a - a * f b) / (b - a)))
      ((continuous_const.mul continuous_id).intervalIntegrable _ _)
      intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    integral_self]
  simp only [smul_eq_mul]
  field_simp
  ring

/-- **The trapezoid error for a Lipschitz function on one panel**:
`|∫_a^b f − (b−a)(f a + f b)/2| ≤ L(b−a)²/2`. -/
theorem trap_error_le {f : ℝ → ℝ} {a b L : ℝ} (hab : a ≤ b) (hL : 0 ≤ L)
    (hint : IntervalIntegrable f volume a b)
    (hlip : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |f x - f y| ≤ L * |x - y|) :
    |(∫ x in a..b, f x) - (b - a) * (f a + f b) / 2| ≤ L * (b - a) ^ 2 / 2 := by
  rcases eq_or_lt_of_le hab with hab' | hab'
  · subst hab'
    simp
  have hba : (0 : ℝ) < b - a := by linarith
  set g : ℝ → ℝ := fun x => ((b - x) * f a + (x - a) * f b) / (b - a) with hg
  have hgint : IntervalIntegrable g volume a b :=
    (by fun_prop : Continuous g).intervalIntegrable _ _
  have hgval : ∫ x in a..b, g x = (b - a) * (f a + f b) / 2 := integral_lerp hab'
  have hdev : |∫ x in a..b, (f x - g x)| ≤ L * (b - a) ^ 2 / 2 := by
    have hpt : ∀ x ∈ Set.Icc a b, |f x - g x| ≤ L * (b - a) / 2 :=
      fun x hx => chord_dev_le_const hab' hL hlip hx
    have hfint : IntervalIntegrable (fun x => f x - g x) volume a b := hint.sub hgint
    have hmono : ∫ x in a..b, |f x - g x| ≤ ∫ x in a..b, (L * (b - a) / 2) :=
      intervalIntegral.integral_mono_on hab hfint.abs intervalIntegrable_const hpt
    have habs : |∫ x in a..b, (f x - g x)| ≤ ∫ x in a..b, |f x - g x| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    have hc : ∫ x in a..b, (L * (b - a) / 2) = (b - a) * (L * (b - a) / 2) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
    have hval : (b - a) * (L * (b - a) / 2) = L * (b - a) ^ 2 / 2 := by ring
    calc |∫ x in a..b, (f x - g x)| ≤ ∫ x in a..b, |f x - g x| := habs
      _ ≤ ∫ x in a..b, (L * (b - a) / 2) := hmono
      _ = L * (b - a) ^ 2 / 2 := by rw [hc, hval]
  calc |(∫ x in a..b, f x) - (b - a) * (f a + f b) / 2|
      = |∫ x in a..b, (f x - g x)| := by
        rw [intervalIntegral.integral_sub hint hgint, hgval]
    _ ≤ L * (b - a) ^ 2 / 2 := hdev

/-! ### §3 — the composite rule: `n` equal panels

The composite trapezoid rule over `n` panels of width `h`, written as the sum of
*per-panel* trapezoids rather than the telescoped compact form.  The compact form
`h(f(a)/2 + f(a+h) + … + f(a+nh)/2)` is the same number by telescoping; the panel
form is what induction on `n` produces directly, and it is what an instantiation
wants anyway (`Finset.sum` over panels, `Finset.sum_range_succ`).

Error: `n` panels, `L·h²/2` each, so `L·(b−a)²/(2n)` for `h = (b−a)/n`.  With
`h = 2π/n` that is `L·(2π)²/(2n)` — the number the lane's C6 measurement uses. -/

/-- **Composite trapezoid error, `n` equal panels.** -/
theorem trap_error_panels {f : ℝ → ℝ} {a h L : ℝ} (hL : 0 ≤ L) (hh : 0 ≤ h)
    (hint : ∀ u v : ℝ, IntervalIntegrable f volume u v)
    (hlip : ∀ x y : ℝ, |f x - f y| ≤ L * |x - y|) :
    ∀ N : ℕ, |(∫ x in a..(a + (N : ℝ) * h), f x)
        - ∑ k ∈ Finset.range N,
            (h * (f (a + (k : ℝ) * h) + f (a + ((k : ℝ) + 1) * h)) / 2)|
      ≤ (N : ℝ) * (L * h ^ 2 / 2) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have hb' : a + ((N : ℝ) + 1) * h = a + (N : ℝ) * h + h := by ring
    have hle1 : a ≤ a + (N : ℝ) * h := by nlinarith
    have hle2 : a + (N : ℝ) * h ≤ a + (N : ℝ) * h + h := by nlinarith
    have hsplit : ∫ x in a..(a + ((N : ℝ) + 1) * h), f x
        = (∫ x in a..(a + (N : ℝ) * h), f x)
          + ∫ x in (a + (N : ℝ) * h)..(a + (N : ℝ) * h + h), f x := by
      rw [hb', ← intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)]
    have hsum : ∑ k ∈ Finset.range (N + 1),
          (h * (f (a + (k : ℝ) * h) + f (a + ((k : ℝ) + 1) * h)) / 2)
        = (∑ k ∈ Finset.range N,
            (h * (f (a + (k : ℝ) * h) + f (a + ((k : ℝ) + 1) * h)) / 2))
          + h * (f (a + (N : ℝ) * h) + f (a + (N : ℝ) * h + h)) / 2 := by
      rw [Finset.sum_range_succ,
        show a + ((N : ℝ) + 1) * h = a + (N : ℝ) * h + h from by ring]
    have hpanel : |(∫ x in (a + (N : ℝ) * h)..(a + (N : ℝ) * h + h), f x)
        - h * (f (a + (N : ℝ) * h) + f (a + (N : ℝ) * h + h)) / 2|
        ≤ L * h ^ 2 / 2 := by
      have hw : (a + (N : ℝ) * h + h) - (a + (N : ℝ) * h) = h := by ring
      have h := trap_error_le (f := f) (a := a + (N : ℝ) * h) (b := a + (N : ℝ) * h + h)
        (L := L) (by linarith) hL (hint _ _) (fun x _ y _ => hlip x y)
      rw [hw] at h
      exact h
    rw [hsplit, hsum, show ((N : ℝ) + 1) * (L * h ^ 2 / 2)
      = (N : ℝ) * (L * h ^ 2 / 2) + L * h ^ 2 / 2 by ring]
    have htri : |((∫ x in a..(a + (N : ℝ) * h), f x)
          + ∫ x in (a + (N : ℝ) * h)..(a + (N : ℝ) * h + h), f x)
        - ((∑ k ∈ Finset.range N,
            (h * (f (a + (k : ℝ) * h) + f (a + ((k : ℝ) + 1) * h)) / 2))
          + h * (f (a + (N : ℝ) * h) + f (a + (N : ℝ) * h + h)) / 2)|
        ≤ |(∫ x in a..(a + (N : ℝ) * h), f x)
            - ∑ k ∈ Finset.range N,
                (h * (f (a + (k : ℝ) * h) + f (a + ((k : ℝ) + 1) * h)) / 2)|
          + |(∫ x in (a + (N : ℝ) * h)..(a + (N : ℝ) * h + h), f x)
            - h * (f (a + (N : ℝ) * h) + f (a + (N : ℝ) * h + h)) / 2| := by
      have := abs_add_le ((∫ x in a..(a + (N : ℝ) * h), f x)
            - ∑ k ∈ Finset.range N,
                (h * (f (a + (k : ℝ) * h) + f (a + ((k : ℝ) + 1) * h)) / 2))
          ((∫ x in (a + (N : ℝ) * h)..(a + (N : ℝ) * h + h), f x)
            - h * (f (a + (N : ℝ) * h) + f (a + (N : ℝ) * h + h)) / 2)
      convert this using 2 <;> ring
    linarith [htri, ih, hpanel]

end SubsetSumL25.Row
