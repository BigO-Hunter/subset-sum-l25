/-
M2a (PRIMECOUNT): the first proof rungs of the Erdős accounting.

E3 (zero carries): a prime in `(2n/3, n]` (with `p² > 2n`, which the dyadic
assembly instantiates automatically for `n ≥ 5`) has `⌊2n/p⌋ = 2` and
`⌊n/p⌋ = 1` in every Legendre slot, so `v_p(C(2n,n)) = 0` — the whole strip
contributes nothing to the central binomial coefficient.

E4 (large range, `n < p ≤ 2n`): `v_p(C(2n,n)) = 1` exactly — E2 gives the
carry (`≥ 1`), `Nat.factorization_choose_le_one` the bound (`≤ 1`, from
`p ≥ n+1 ⟹ p² ≥ (n+1)² > 2n`).

E5-bound: the product `P_large` of the primes in `(n, 2n]` is at most
`(2n)^k` for `k` their count — the trivial direction of the accounting;
the assembly (M2b/M2c) needs it as the upper side of
`P_large ≥ 4^{n/3}/((2n+1)·A·D)`.

Credit chain: Base → Bills → us (the accounting plan follows the papers'
own proof of the collision-count input; the Lean form is ours).
-/
import SubsetSumL25.Statements.PrimeCount

namespace SubsetSumL25

/-- E3: for a prime `2n/3 < p ≤ n` with `p² > 2n`, every base-`p` carry of
`n + n` vanishes — `v_p(C(2n,n)) = 0`. -/
theorem mid_factorization_eq_zero (n p : ℕ) (hp : p.Prime) (hstrip : 2 * n / 3 < p)
    (hpn : p ≤ n) (hp2 : 2 * n < p ^ 2) :
    (Nat.choose (n + n) n).factorization p = 0 := by
  have hn2p : n < 2 * p := by omega
  have hlog : Nat.log p (n + n) < 2 := by
    rw [Nat.log_lt_iff_lt_pow hp.one_lt]
    exacts [by linarith, by omega]
  have hIco : (Finset.Ico 1 2 : Finset ℕ) = {1} := by decide
  have hmod : n % p = n - p := by
    have hp0 : 0 < p := hp.pos
    have h1 : n / p = 1 := by
      have hA : (1:ℕ) ≤ n / p := (Nat.le_div_iff_mul_le hp0).2 (by omega)
      have hB : n / p < 2 := (Nat.div_lt_iff_lt_mul hp0).2 (by omega)
      omega
    have hdm := Nat.div_add_mod n p
    rw [h1] at hdm
    omega
  have hfac : (Nat.choose (n + n) n).factorization p
      = ((Finset.Ico 1 2).filter (fun i => p ^ i ≤ n % p ^ i + n % p ^ i)).card :=
    Nat.factorization_choose' hp (n := n) (k := n) (b := 2) hlog
  rw [hfac, hIco]
  simp only [Finset.filter_singleton, pow_one, hmod]
  rw [if_neg (by omega)]
  rfl

/-- E4: for a prime `n < p ≤ 2n` (with `n ≥ 1`), `v_p(C(2n,n)) = 1` exactly —
the carry of E2 and the single-carry bound meet. -/
theorem large_factorization_eq_one (n p : ℕ) (hn1 : 0 < n) (hp : p.Prime)
    (hpn : n < p) (hp2 : p ≤ 2 * n) :
    (Nat.choose (n + n) n).factorization p = 1 := by
  have hdvd : p ∣ Nat.choose (n + n) n := prime_divides_central_binom n p hp hpn hp2
  have hcne : Nat.choose (n + n) n ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hpos : 0 < (Nat.choose (n + n) n).factorization p :=
    hp.factorization_pos_of_dvd hcne hdvd
  have hp2' : n + n < p ^ 2 := by
    have hsq : (n + 1) * (n + 1) ≤ p * p := by nlinarith
    have hpp : p ^ 2 = p * p := pow_two p
    nlinarith
  have hle : (Nat.choose (n + n) n).factorization p ≤ 1 :=
    Nat.factorization_choose_le_one hp2'
  omega

/-- E5-bound (the trivial side): the product of the primes in `(n, 2n]` is at
most `(2n)^k`, where `k` is their count. -/
theorem large_product_le (n : ℕ) :
    ∏ p ∈ Finset.filter Nat.Prime (Finset.Ioc n (2 * n)), p
      ≤ (2 * n) ^ (Finset.filter Nat.Prime (Finset.Ioc n (2 * n))).card :=
  Finset.prod_le_pow_card _ _ _ fun p hp =>
    (Finset.mem_Ioc.1 (Finset.mem_filter.1 hp).1).2

end SubsetSumL25
