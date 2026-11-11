import SubsetSumL25.Row.JV1000Strip

/- Axiom banner for `SubsetSumL25.Row.JV1000Strip` — `#print axioms` on every theorem of
the strip-analyticity quadrature module.  House triple only (propext, Classical.choice,
Quot.sound); fail-closed in `jv1000_strip_receipts.py`.

Why this banner is load-bearing: this module is the first in the jv1000 row whose
*content* is a quadrature guarantee rather than a refutation.  A quadrature bound that
carried `sorryAx` or `native_decide` would be worse than useless — it would look exactly
like the real thing.  Every theorem below must come back in the house triple.

The three that carry the mathematical weight:

  * `char_sum` / `trapMean_char` — the `n`-point trapezoid rule is EXACT on every
    character `e^{imx}` (its mean is `1` iff `n ∣ m`, `0` otherwise).  This is spectral
    accuracy itself, and it is what the Lipschitz route in `JV1000Quadrature` cannot see.
  * `trap_error_char` — hence the error functional `circleMean − trapMean n` vanishes off
    the aliased frequencies.
  * `trapezoid_error_le_of_decay` — hence `|trap_n − ∫| ≤ M qⁿ (2K+1) + 2ε`: geometric
    in `n` with the constant from the coefficient bound. -/
open SubsetSumL25.Row

-- §1–§3: the character machinery (spectral exactness of the periodic trapezoid rule)
#print axioms SubsetSumL25.Row.char_sum
#print axioms SubsetSumL25.Row.integral_char
#print axioms SubsetSumL25.Row.trapMean_char
#print axioms SubsetSumL25.Row.circleMean_char
#print axioms SubsetSumL25.Row.trap_error_char

-- §4: the two sup-norm bounds
#print axioms SubsetSumL25.Row.trapMean_norm_le
#print axioms SubsetSumL25.Row.circleMean_norm_le

-- §5: the geometric tail
#print axioms SubsetSumL25.Row.geom_tail_le

-- §6: linearity over a finite character sum
#print axioms SubsetSumL25.Row.trapMean_add
#print axioms SubsetSumL25.Row.trapMean_smul
#print axioms SubsetSumL25.Row.circleMean_add
#print axioms SubsetSumL25.Row.circleMean_smul
#print axioms SubsetSumL25.Row.trapMean_sub
#print axioms SubsetSumL25.Row.circleMean_sub
#print axioms SubsetSumL25.Row.trapMean_finset_sum
#print axioms SubsetSumL25.Row.circleMean_finset_sum

-- §6: THE QUADRATURE LEMMA
#print axioms SubsetSumL25.Row.trapezoid_error_le_of_decay
