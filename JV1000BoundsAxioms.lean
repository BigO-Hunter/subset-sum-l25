import SubsetSumL25.Row.JV1000Bounds

/- Axiom banner for `SubsetSumL25.Row.JV1000Bounds` — `#print axioms` on the theorems of
round 21.  House triple only (propext, Classical.choice, Quot.sound); fail-closed in
`jv1000_bounds_receipts.py`.

Why this banner is load-bearing.  This module is where two things happen that a `sorryAx`
would make maximally deceptive:

  1. **The reduction.**  `jvUcx_re_ge_1326` / `jvVcx_re_le_19178` claim to turn four *numeric*
     premises into the strip bounds `Re u ≥ −1.326`, `Re v ≤ 19.178`.  If the `Complex.log_re`
     bridge or the ratio bound were unsound, the residue would *look* reduced while the
     analytic content was faked — the worst possible failure mode for a round whose whole
     product is "what is left".
  2. **The §7 cure.**  `quadrature_at_256_of_strip_relaxed` claims `K ≤ 200`, `ε ≤ 10⁻⁷`
     suffices where round 19 fixed `K ≤ 32`, `ε ≤ 10⁻²⁰`.  A `native_decide` in that
     arithmetic would make the cure as vacuous as the defect it repairs.

The theorems that carry the mathematical weight:

  * `re_div_ofReal`, `re_log_div_L2C`, `re_affine_u`, `re_affine_v` — the `Re` bookkeeping
    that makes `Re(log₂ P_c) = log ‖P_c‖ / log 2` literal.  No analysis; `Complex.log_re`.
  * `re_div_ge`, `re_div_le` — `−‖Y‖/‖P‖ ≤ Re(Y/P) ≤ ‖Y‖/‖P‖`, from `Complex.re_le_norm`
    both ways and `Complex.norm_div`.  These are what stop the Y-term from needing a
    *ratio* estimate of its own.
  * `logb_nine_tenths_ge` — `log₂(9/10) ≥ −1/6`, from `Real.log_le_sub_one_of_pos` and
    `Real.log_two_gt_d9`.  The only transcendental fact the reduction needs.
  * `jvUcx_re_ge_1326`, `jvVcx_re_le_19178` — the two reductions, with `norm_num` closing
    `Re u ≥ −0.9037` and `Re v ≤ 3.6556` against `−1.326` / `19.178`.
  * `jvPcx_slitPlane` — `hslit` becomes a corollary of the `P`-floor.
  * `intervalIntegrable_jvMomF1/F2` — `hFint` becomes a corollary of `hslit`.
  * `quadrature_at_256_of_strip_relaxed` — the §7 cure; `2.34·10⁻⁷ < 10⁻⁶`.
  * `jv_m1_cert_certified`, `jv_m2_cert_certified`, `jvMoments_of_residue` — the moment
    goals, with `hslit`/`hU`/`hV`/`hFint` all discharged and the residue named. -/

open SubsetSumL25.Row in
#print axioms SubsetSumL25.Row.re_div_ofReal
#print axioms SubsetSumL25.Row.re_log_div_L2C
#print axioms SubsetSumL25.Row.re_affine_u
#print axioms SubsetSumL25.Row.re_affine_v
#print axioms SubsetSumL25.Row.jvUcx_re_eq
#print axioms SubsetSumL25.Row.jvVcx_re_eq
#print axioms SubsetSumL25.Row.re_div_ge
#print axioms SubsetSumL25.Row.re_div_le
#print axioms SubsetSumL25.Row.logb_nine_tenths_ge
#print axioms SubsetSumL25.Row.jvUcx_re_ge_1326
#print axioms SubsetSumL25.Row.jvVcx_re_le_19178
#print axioms SubsetSumL25.Row.jvPcx_slitPlane
#print axioms SubsetSumL25.Row.continuous_jvMomF1
#print axioms SubsetSumL25.Row.intervalIntegrable_jvMomF1
#print axioms SubsetSumL25.Row.intervalIntegrable_jvMomF2
#print axioms SubsetSumL25.Row.quadrature_at_256_of_strip_relaxed
#print axioms SubsetSumL25.Row.quadrature_jvMomF1_relaxed
#print axioms SubsetSumL25.Row.quadrature_jvMomF2_relaxed
#print axioms SubsetSumL25.Row.jv_m1_cert_certified
#print axioms SubsetSumL25.Row.jv_m2_cert_certified
#print axioms SubsetSumL25.Row.jvMoments_of_residue
