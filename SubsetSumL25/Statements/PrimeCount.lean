/-
M1 (PRIMECOUNT): the `hcount` premise — the dyadic prime-count input of the
proved collision lemmas O3 (`L2_5_prime_collision`) and O6
(`L5_2_sparse_distinctions`), named so far as the paper's own external input
(setup.tex lem:prime-collision proof: «The prime number theorem gives at
least c₀·2^L/L primes in the specified interval … Rosser and Schoenfeld»).

Why it is openable here: the pinned Mathlib (d13f23b) carries only
Chebyshev-grade estimates, and their constants ANNIHILATE in the interval
difference — `pi_ge` gives ≈0.69·x/log x below and `pi_le_log4_mul_div`
≈2.77·x/log x above, so π(2^{L+1}) − π(2^L) ≥ (2/(L+1) − 4/L)·2^L < 0
(measured, 2026-11-09).  There is no PNT asymptotic in the pin (grep of
`IsEquivalent … primeCounting`: no hits).  The count is still unconditional:
Erdős's binomial-coefficient accounting gives it elementarily, and the pin
holds the three anchors the accounting needs —
`Chebyshev.theta_le_log4_mul_x` (θ(x) ≤ log4·x, i.e. ∏_{p≤x} p ≤ 4^x),
`Chebyshev.pi_le_log4_mul_div` (the small-prime count term),
`Nat.factorization_choose'` (Legendre carries in the central binomial).

Proof plan (M2), the Erdős accounting on the central binomial coefficient,
with n = 2^L at the end:
  E1  `central_binom_big`:  4^n/(2n+1) ≤ C(2n,n)   — PROVED here.
  E2  `prime_divides_central_binom`: for prime n < p ≤ 2n, p ∣ C(2n,n)
      (one carry: p ≤ n+n < p²) — PROVED here.
  E3  `mid_prime_not_divides`: for prime 2n/3 < p ≤ n, p ∤ C(2n,n)
      (⌊2n/p⌋ = 2, ⌊n/p⌋ = 1 in every Legendre term ⇒ zero carries).
  E4  small-prime part: Σ_{p ≤ √(2n)} v_p(C(2n,n))·log p ≤ π(√(2n))·log(2n)
      (each p ≤ √(2n) has p^{v_p} ≤ 2n); count term via pi_le_log4_mul_div — O(√n).
  E5  mid-prime product: ∏_{√(2n) < p ≤ 2n/3} p ≤ 4^{2n/3} (theta_le_log4_mul_x);
      with E3 the whole (√(2n), n] strip contributes ≤ (2n/3)·log4.
  E6  assembly: n·log4 − log(2n+1) ≤ log C(2n,n)
      ≤ π(√(2n))·log(2n) + (2n/3)·log4 + k·log(2n) with k = π(2n) − π(n),
      since every k-prime contributes its own log p ≥ log(n+1).
      Hence k ≥ (n·log4/3 − O(√n·log n))/log(2n) ≥ c·n/log(2n) for n ≥ n₀.
  E7  dyadic specialization n = 2^L: k = (primesInterval L).card, so
      c₀·2^L/L ≤ card for L ≥ L₀ with explicit c₀, L₀.

Discharge shape: `L2_5_prime_collision` takes c₀, L₀ as parameters with
K = 1/c₀, L* = L₀, so the existence theorem below instantiates it (and the
L5.2 union bound, which consumes L2.5's statement) unconditionally — the
corollary `L2_5_prime_collision_unconditional` is the closed artifact.

`sorry`: E3–E7 are M1 placeholders — proof target `Proofs/PrimeCount.lean` (M2).
-/
import SubsetSumL25.Statements.Defs
import SubsetSumL25.Statements.PrimeCollision

namespace SubsetSumL25

/-- E1 (real form): the central binomial coefficient carries the geometric mass
`4^n/(2n+1)` — `Σ_k C(2n,k) = 2^{2n} = 4^n` and every row entry is ≤ the middle
one (`Nat.choose_le_middle`). -/
theorem central_binom_big (n : ℕ) :
    (4 : ℝ) ^ n / (2 * n + 1) ≤ (Nat.choose (2 * n) n : ℝ) := by
  have hsum : ∑ k ∈ Finset.range (2 * n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n) := by
    simpa using Nat.sum_range_choose (2 * n)
  have hle : ∀ k ∈ Finset.range (2 * n + 1), Nat.choose (2 * n) k ≤ Nat.choose (2 * n) n := by
    intro k _
    have h := Nat.choose_le_middle k (2 * n)
    rwa [Nat.mul_div_cancel_left _ (show (0:ℕ) < 2 by norm_num)] at h
  have hbound : (2 ^ (2 * n) : ℕ) ≤ (2 * n + 1) * Nat.choose (2 * n) n := by
    calc (2 ^ (2 * n) : ℕ) = ∑ k ∈ Finset.range (2 * n + 1), Nat.choose (2 * n) k := hsum.symm
      _ ≤ ∑ _k ∈ Finset.range (2 * n + 1), Nat.choose (2 * n) n :=
            Finset.sum_le_sum fun k hk => hle k hk
      _ = (2 * n + 1) * Nat.choose (2 * n) n := by simp
  have hcast : ((2 ^ (2 * n) : ℕ) : ℝ) = (4 : ℝ) ^ n := by
    have h1 : (2 ^ (2 * n) : ℕ) = 4 ^ n := by
      calc 2 ^ (2 * n) = 2 ^ n * 2 ^ n := by rw [show 2 * n = n + n from by ring, Nat.pow_add]
        _ = 4 ^ n := by rw [← Nat.mul_pow]
    rw [h1]
    simp
  have hreal : ((4 : ℝ) ^ n) ≤ ((2:ℝ) * (n:ℝ) + 1) * ((Nat.choose (2 * n) n : ℕ) : ℝ) := by
    have h2 : (((2 * n + 1) * Nat.choose (2 * n) n : ℕ) : ℝ)
        = ((2:ℝ) * (n:ℝ) + 1) * ((Nat.choose (2 * n) n : ℕ) : ℝ) := by
      rw [Nat.cast_mul]
      norm_num
    rw [← hcast, ← h2]
    exact Nat.cast_le.2 hbound
  rw [div_le_iff₀ (show (0:ℝ) < 2 * n + 1 by positivity), mul_comm]
  exact hreal

/-- E2: a prime strictly between `n` and `2n` divides the central binomial
coefficient — exactly one carry in base `p` (`p ≤ n + n < p²`),
`v_p(C(2n,n)) = #{i : p^i ≤ n%p^i + n%p^i} = 1`. -/
theorem prime_divides_central_binom (n p : ℕ) (hp : p.Prime) (hn : n < p)
    (hp2 : p ≤ 2 * n) : p ∣ Nat.choose (n + n) n := by
  have hp0 : 0 < p := hp.pos
  have hn1 : 0 < n := by omega
  have hpp : 2 * p ≤ p * p := by nlinarith [hp.two_le]
  have h2n : n + n < p ^ 2 := by
    have hpp : 2 * p ≤ p * p := by nlinarith [hp.two_le]
    rw [pow_two]
    omega
  have hlog : Nat.log p (n + n) < 2 := by
    rw [Nat.log_lt_iff_lt_pow hp.one_lt]
    exacts [h2n, by omega]
  have hdiv1 : (2 * n) / p = 1 := by
    have h1 : (1:ℕ) ≤ (2 * n) / p := (Nat.le_div_iff_mul_le hp0).2 (by omega)
    have h2 : (2 * n) / p < 2 := (Nat.div_lt_iff_lt_mul hp0).2 (by omega)
    omega
  have hdiv0 : n / p = 0 := Nat.div_eq_of_lt hn
  have hIco : (Finset.Ico 1 2 : Finset ℕ) = {1} := by decide
  have hfac : (Nat.choose (n + n) n).factorization p = 1 := by
    rw [Nat.factorization_choose' hp (n := n) (k := n) (b := 2) hlog, hIco]
    simp only [Finset.filter_singleton, pow_one, Nat.mod_eq_of_lt hn]
    rw [if_pos (by omega), Finset.card_singleton]
  exact Nat.dvd_of_factorization_pos (by rw [hfac]; simp)

/-- E6/E7 (the hcount premise): the dyadic interval `[2^L, 2^{L+1})` holds
≥ `c₀·2^L/L` primes for all large `L`, for some absolute `0 < c₀` and `L₀`. -/
theorem erdos_dyadic_primes :
    ∃ (c₀ : ℝ) (L₀ : ℕ), 0 < c₀ ∧ ∀ L, L₀ ≤ L →
      c₀ * (2 : ℝ) ^ L / L ≤ ((primesInterval L).card : ℝ) := by
  sorry

/-- Discharge: the collision bound O3 without the `hcount`/`hpos` hypotheses —
`erdos_dyadic_primes` supplies the witnesses (K = 1/c₀, L* = L₀), so O3 and the
L5.2 union bound become unconditional number theory. -/
theorem L2_5_prime_collision_unconditional :
    ∃ (K : ℝ) (Lstar : ℕ), 0 < K ∧ ∀ L, Lstar ≤ L → ∀ (D : ℤ) (B : ℕ),
      D ≠ 0 → 1 ≤ B → ((D.natAbs : ℝ) < (2 : ℝ) ^ B) →
      (badPrimes L D : ℝ) / (primesInterval L).card
        ≤ K * (B : ℝ) * (L : ℝ) / (2 : ℝ) ^ L := by
  sorry

end SubsetSumL25
