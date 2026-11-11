import SubsetSumL25.Row.JV1000Decay

/- Axiom banner for `SubsetSumL25.Row.JV1000Decay` — `#print axioms` on every theorem of
the `hdecay` module.  House triple only (propext, Classical.choice, Quot.sound);
fail-closed in `jv1000_decay_receipts.py`.

Why this banner is load-bearing: this module supplies the ONE hypothesis
`JV1000Strip.trapezoid_error_le_of_decay` leaves open — the annulus Cauchy estimate
`‖c_k‖ ≤ M e^{−a|k|}`.  A decay bound that carried `sorryAx` or `native_decide` would be
maximally deceptive: the quadrature lemma would then *look* unconditional while resting on
nothing.  Every theorem below must come back in the house triple.

The five that carry the mathematical weight:

  * `shift_integral_eq` — the rectangle's vertical sides cancel by periodicity, so the
    contour may be shifted: `∫₀^{2π} H(x)dx = ∫₀^{2π} H(x+is)dx` for `|s| < a`.
  * `abs_fourierCoeff_le_of_shift` — hence `‖ĉ_k‖ ≤ M e^{ks}` at every interior `s`.
  * `le_exp_endpoint_of_lt` / `le_exp_endpoint_of_gt` — the endpoint passage to the open
    edge of the strip (`le_of_tendsto_of_tendsto`, one-sided neighbourhoods).
  * `abs_fourierCoeff_le_decay` — `‖ĉ_k‖ ≤ M e^{−a|k|}`, the estimate itself; and
    `fourierCoeff_le_pow` / `hdecay_of_strip` restate it as `hdecay` with `q = e^{−a}`.

The two that discharge §6:

  * `trapezoid_error_le_of_strip` — `trapezoid_error_le_of_decay` with `hdecay` supplied.
  * `quadrature_at_256_of_strip` — the same at the certifier's `N_in = 256`, `≤ 10⁻⁶`,
    with the single numeric `Real.exp` fact (`exp_neg_fifth_pow_256_le`) proved from
    `e > 2.7182818283` rather than assumed. -/
open SubsetSumL25.Row

-- §1: the elementary modulus bound on `uIcc 0 s`
#print axioms SubsetSumL25.Row.abs_le_abs_of_mem_uIcc

-- §2: the contour shift (Cauchy–Goursat on the rectangle + periodicity)
#print axioms SubsetSumL25.Row.shift_integral_eq

-- §3: the sup bound at a fixed shift
#print axioms SubsetSumL25.Row.abs_fourierCoeff_le_of_shift

-- §4: the endpoint passage
#print axioms SubsetSumL25.Row.le_exp_endpoint_of_lt
#print axioms SubsetSumL25.Row.le_exp_endpoint_of_gt

-- §5: THE ANNULUS CAUCHY ESTIMATE, and `hdecay` in §6's shape
#print axioms SubsetSumL25.Row.abs_fourierCoeff_le_decay
#print axioms SubsetSumL25.Row.fourierCoeff_le_pow
#print axioms SubsetSumL25.Row.hdecay_of_strip

-- §6: §6 discharged
#print axioms SubsetSumL25.Row.trapezoid_error_le_of_strip

-- §7: the numeric `Real.exp` fact and the n = 256 instantiation
#print axioms SubsetSumL25.Row.exp_neg_fifth_pow_256_le
#print axioms SubsetSumL25.Row.quadrature_at_256_of_strip
