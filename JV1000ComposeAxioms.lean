import SubsetSumL25.Row.JV1000Compose

/- Axiom banner for `SubsetSumL25.Row.JV1000Compose` — `#print axioms` on the theorems of
the composition passage.  House triple only (propext, Classical.choice, Quot.sound);
fail-closed in `jv1000_compose_receipts.py`.

Why this banner is load-bearing: this module is where the *instantiation* of the moments
happens — the step that turns "`u`, `v` are `log₂` of strip-analytic integrals" into "the
quadrature lemma applies to the certified moment integrand".  A holomorphy or sup bound
carrying `sorryAx`/`native_decide` would be maximally deceptive here, in exactly the way
round 19's banner guarded `hdecay`: the composite would then *look* strip-analytic while
resting on nothing.

The theorems that carry the mathematical weight:

  * `norm_cos_le_cosh` / `norm_sin_le_cosh` — the SHARP trigonometric modulus bounds from
    `Complex.cos_eq`.  Not a nicety: `8472775` is `⌈W_out · 2²¹⌉` with `W_out = 2+2cosh(1/5)`,
    and the lossy `|re| + |im|` route overshoots that ceiling by 10% (`4.4428` vs `4.0401`).
  * `trig16c_norm_le` / `stripMod_mono` — the certifier's own strip majorant `S(co, t)`.
  * `hasDerivAt_trig16c` / `norm_trig16cD_le` — the derivative of the continued density and
    its majorant, i.e. the dominating function for differentiation under the integral.
  * `hasDerivAt_jvPcx` — **`P_c` HOLOMORPHIC ON THE STRIP**, by differentiation under the
    interval integral.  No analytic premise named.
  * `differentiableAt_jvYcx` — the same for `Y`, with the product rule's `(1 + log 2 · w)`.
  * `differentiableAt_jvUcx` / `differentiableAt_jvVcx` — `u`, `v` holomorphic on the strip
    given `P_c` in `Complex.slitPlane` (the branch-cut condition, measured at margin 0.94).
  * `differentiableAt_jvMomFc1` / `differentiableAt_jvMomFc2` — **THE COMPOSITE IS
    HOLOMORPHIC**; no branch survives into it (`exp` of a holomorphic function is entire).
  * `norm_jvMomFc1_le_ceiling` / `norm_jvMomFc2_le_ceiling` — **THE COMPOSITE SUP** on the
    strip, `≤ 8472775` — fed to §7 as `hMle`.
  * `jvMomFc1_add_two_pi` / `jvMomFc2_add_two_pi` — periodicity, inherited from the densities.
  * `quadrature_jvMomF1` / `quadrature_jvMomF2` — **THE FEED**: §7 at `n = 256`, `≤ 10⁻⁶`.
  * `jvMomF1_eq` / `circleMean_jvMomF1` — the real-axis bridge: the restricted composite *is*
    the certified real integrand, so `circleMean` is `jvMomentRho0Cert` coerced.
  * `jv_m1_cert_of_comparison` / `jv_m2_cert_of_comparison` — the moment goals, with the
    quadrature half discharged and only the rational comparison named. -/
open SubsetSumL25.Row

-- §1: the sharp trigonometric modulus bounds and the strip majorant
#print axioms SubsetSumL25.Row.norm_cos_le_cosh
#print axioms SubsetSumL25.Row.norm_sin_le_cosh
#print axioms SubsetSumL25.Row.norm_two_add_two_cos
#print axioms SubsetSumL25.Row.trig16c_norm_le
#print axioms SubsetSumL25.Row.stripMod_mono
#print axioms SubsetSumL25.Row.trig16c_ofReal
#print axioms SubsetSumL25.Row.trig16c_add_two_pi

-- §2: the derivative machinery, and `P` HOLOMORPHIC ON THE STRIP
#print axioms SubsetSumL25.Row.hasDerivAt_trig16c
#print axioms SubsetSumL25.Row.norm_trig16cD_le
#print axioms SubsetSumL25.Row.hasDerivAt_jvPcx
#print axioms SubsetSumL25.Row.differentiableOn_jvPcx

-- §2.1: the same for `Y`
#print axioms SubsetSumL25.Row.differentiableAt_jvYcx

-- §3: `u`, `v` holomorphic on the strip (given the measured branch condition)
#print axioms SubsetSumL25.Row.differentiableAt_jvUcx
#print axioms SubsetSumL25.Row.differentiableAt_jvVcx

-- §4: THE COMPOSITE — holomorphic, sup-bounded
#print axioms SubsetSumL25.Row.differentiableAt_jvMomFc1
#print axioms SubsetSumL25.Row.differentiableAt_jvMomFc2
#print axioms SubsetSumL25.Row.norm_jvMomFc1_le
#print axioms SubsetSumL25.Row.norm_jvMomFc2_le
#print axioms SubsetSumL25.Row.cosh_stripA_le
#print axioms SubsetSumL25.Row.norm_jvMomFc1_le_ceiling
#print axioms SubsetSumL25.Row.norm_jvMomFc2_le_ceiling

-- §5: periodicity and THE FEED into `JV1000Decay` §7 at n = 256
#print axioms SubsetSumL25.Row.jvMomFc1_add_two_pi
#print axioms SubsetSumL25.Row.jvMomFc2_add_two_pi
#print axioms SubsetSumL25.Row.quadrature_jvMomF1
#print axioms SubsetSumL25.Row.quadrature_jvMomF2

-- §6: the real-axis bridge and the moment goals one comparison away
#print axioms SubsetSumL25.Row.jvPcx_ofReal
#print axioms SubsetSumL25.Row.jvYcx_ofReal
#print axioms SubsetSumL25.Row.jvUcx_ofReal
#print axioms SubsetSumL25.Row.jvVcx_ofReal
#print axioms SubsetSumL25.Row.jvMomF1_eq
#print axioms SubsetSumL25.Row.jvMomF2_eq
#print axioms SubsetSumL25.Row.circleMean_jvMomF1
#print axioms SubsetSumL25.Row.circleMean_jvMomF2
#print axioms SubsetSumL25.Row.jv_m1_cert_of_comparison
#print axioms SubsetSumL25.Row.jv_m2_cert_of_comparison
