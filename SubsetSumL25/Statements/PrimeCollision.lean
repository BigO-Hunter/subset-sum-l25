/-
OpenAI Lemma 2.5 («Random-prime collisions», setup.tex lem:prime-collision).

Verbatim statement (setup.tex):

    There are absolute constants K and L_* such that the following holds.  For
    an integer L ≥ L_*, let p be uniform among the primes in [2^L, 2^{L+1}).  If
    D is a nonzero integer with |D| < 2^B, where B ≥ 1, then
        Pr{D ≡ 0 (mod p)} ≤ K·B·L·2^{−L}.
    The same bound applies to the collision of two fixed unequal integers whose
    difference has absolute value less than 2^B.

PNT premise as explicit hypothesis: the paper's proof opens «The prime number
theorem gives at least c₀·2^L/L primes in the specified interval … Rosser and
Schoenfeld».  Mathlib d13f23b carries only Chebyshev-grade estimates
(`Chebyshev.PrimeCounting.pi_ge`, `pi_le_log4_mul_div`) whose constants
(0.69·x/ln x below, 1.39·x/ln x above) annihilate in the interval difference
π(2^{L+1}) − π(2^L), so that input is NOT derivable from this Mathlib.  It is
therefore a named hypothesis `hcount`, exactly the paper's own external input;
`K` is then explicit (`c₀⁻¹`).  Details in STMTS.md.

`sorry`: M1 placeholder — proof target Proofs/PrimeCollision.lean (M2).
-/
import SubsetSumL25.Statements.Defs

namespace SubsetSumL25

/-- The number of primes in `[2^L, 2^{L+1})` dividing the integer `D`
(for a prime `p`, `p ∣ D.natAbs` ⟺ `p ∣ D` over `ℤ`). -/
def badPrimes (L : ℕ) (D : ℤ) : ℕ :=
  ((primesInterval L).filter (fun p => p ∣ D.natAbs)).card

/-
The two collision theorems (`L2_5_prime_collision`,
`L2_5_prime_collision_two`) are PROVED in `SubsetSumL25.Proofs.PrimeCollision`;
they lived here with `sorry` placeholders at M1 and moved to Proofs/ at M2.
-/

end SubsetSumL25
