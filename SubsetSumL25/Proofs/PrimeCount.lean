/-
M2a+M2b (PRIMECOUNT): the Erdős accounting foundations.

M2a:
  E3 (zero carries): a prime in `(2n/3, n]` (with `p² > 2n`, automatic for
  `n ≥ 3`) has `⌊2n/p⌋ = 2` and `⌊n/p⌋ = 1` in every Legendre slot, so
  `v_p(C(2n,n)) = 0` — the strip contributes nothing.
  E4 (large range, `n < p ≤ 2n`): `v_p(C(2n,n)) = 1` exactly.
  E5-bound: `P_large ≤ (2n)^k` for `k` the count of primes in `(n, 2n]`.

M2b: the 4-way factorization split
  `C = C(2n,n) = P_small · P_mid · P_strip · P_large` over the primes ≤ 2n:
  P_small — primes p ≤ √(2n), each p^{v_p} ≤ 2n (pow_factorization_choose_le);
  P_mid   — √(2n) < p ≤ 2n/3, each v_p ≤ 1 (factorization_choose_le_one),
            so P_mid ≤ primorial(2n/3) ≤ 4^{2n/3} (Chebyshev.theta);
  P_strip — every v_p = 0 (E3);
  P_large — n < p ≤ 2n, each v_p = 1 (E4), so P_large = ∏ primes.

Credit chain: Base → Bills → us.
-/
import SubsetSumL25.Statements.PrimeCount

namespace SubsetSumL25

/-! ### M2a — E3 and the large-range lemmas -/

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

/-! ### M2b — the four-way split -/

/-- The primes `p` with `p ≤ m`. -/
def primesUpTo (m : ℕ) : Finset ℕ := Finset.filter Nat.Prime (Finset.range (m + 1))

/-- The small-prime factor set: primes `≤ √(2n)`. -/
def smallSet (n : ℕ) : Finset ℕ :=
  (primesUpTo (2 * n)).filter fun p => p ≤ Nat.sqrt (2 * n)

/-- The mid-prime factor set: `√(2n) < p ≤ 2n/3` (nested-filter shape, as
produced by the two splits). -/
def midSet (n : ℕ) : Finset ℕ :=
  ((primesUpTo (2 * n)).filter fun p => Nat.sqrt (2 * n) < p).filter
    fun p => p ≤ 2 * n / 3

/-- The dead strip: `√(2n) < p`, `2n/3 < p ≤ n` (zero carries, E3). -/
def stripSet (n : ℕ) : Finset ℕ :=
  (((primesUpTo (2 * n)).filter fun p => Nat.sqrt (2 * n) < p).filter
    fun p => 2 * n / 3 < p).filter fun p => p ≤ n

/-- The large-prime factor set: `n < p ≤ 2n` (nested-filter shape). -/
def largeSet (n : ℕ) : Finset ℕ :=
  (((primesUpTo (2 * n)).filter fun p => Nat.sqrt (2 * n) < p).filter
    fun p => 2 * n / 3 < p).filter fun p => n < p

private theorem prod_filter_split (S : Finset ℕ) (f : ℕ → ℕ) (a : ℕ) :
    (∏ p ∈ S.filter (fun p => p ≤ a), f p) * (∏ p ∈ S.filter (fun p => a < p), f p)
      = ∏ p ∈ S, f p := by
  have hd : Disjoint (S.filter fun p => p ≤ a) (S.filter fun p => a < p) := by
    refine Finset.disjoint_right.2 fun p h1 h2 => ?_
    have h3 := Finset.mem_filter.1 h1
    have h4 := Finset.mem_filter.1 h2
    omega
  rw [← Finset.prod_union hd]
  rw [show S.filter (fun p => p ≤ a) ∪ S.filter (fun p => a < p) = S from by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases h : p ≤ a
    · simp [h, Nat.not_lt.2 h]
    · simp [h, Nat.lt_of_not_le h]]

private theorem mem_primesUpTo {m p : ℕ} (hp : p.Prime) (hle : p ≤ m) : p ∈ primesUpTo m :=
  Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hp⟩

/-- The doubly-nested filter set (as produced by the split) equals `largeSet`
— the extra guards are implied: `√(2n) < p` from `2n < p² ≤ n²`. -/
theorem largeSet_nested (n : ℕ) (hn : 0 < n) :
    (((primesUpTo (2 * n)).filter fun p => Nat.sqrt (2 * n) < p).filter
        fun p => 2 * n / 3 < p).filter (fun p => n < p) = largeSet n := by
  ext p
  constructor
  · intro hmem
    have h3 := Finset.mem_filter.1 hmem
    have h2 := Finset.mem_filter.1 h3.1
    have h1 := Finset.mem_filter.1 h2.1
    have hrange := Finset.mem_filter.1 h1.1
    have t1 : p ∈ primesUpTo (2 * n) := mem_primesUpTo hrange.2
      (Nat.le_of_lt_succ (Finset.mem_range.1 hrange.1))
    have t2 : p ∈ (primesUpTo (2 * n)).filter
        (fun q => Nat.sqrt (2 * n) < q) := Finset.mem_filter.2 ⟨t1, h1.2⟩
    have t3 : p ∈ ((primesUpTo (2 * n)).filter
        (fun q => Nat.sqrt (2 * n) < q)).filter
        (fun q => 2 * n / 3 < q) := Finset.mem_filter.2 ⟨t2, h2.2⟩
    exact Finset.mem_filter.2 ⟨t3, h3.2⟩
  · intro hmem
    have hm := Finset.mem_filter.1 hmem
    have hp : p.Prime :=
      (Finset.mem_filter.1 (Finset.mem_filter.1 (Finset.mem_filter.1 hm.1).1).1).2
    have hle : p ≤ 2 * n :=
      Nat.le_of_lt_succ (Finset.mem_range.1
        (Finset.mem_filter.1 (Finset.mem_filter.1 (Finset.mem_filter.1 hm.1).1).1).1)
    have hp2 : 2 * n < p ^ 2 := by
      have hsq : (n + 1) * (n + 1) ≤ p * p := by nlinarith
      have hpp : p ^ 2 = p * p := pow_two p
      nlinarith
    have t1 : p ∈ primesUpTo (2 * n) := mem_primesUpTo hp hle
    have t2 : p ∈ (primesUpTo (2 * n)).filter
        (fun q => Nat.sqrt (2 * n) < q) := Finset.mem_filter.2 ⟨t1, Nat.sqrt_lt'.2 hp2⟩
    have t3 : p ∈ ((primesUpTo (2 * n)).filter
        (fun q => Nat.sqrt (2 * n) < q)).filter
        (fun q => 2 * n / 3 < q) := Finset.mem_filter.2 ⟨t2, by omega⟩
    exact Finset.mem_filter.2 ⟨t3, hm.2⟩

/-- Base identity: the central binomial coefficient is the product of its
prime-power factorization over the primes `≤ 2n`. -/
theorem central_prod_factorization (n : ℕ) (hn : 0 < n) :
    Nat.choose (n + n) n
      = ∏ p ∈ primesUpTo (2 * n), p ^ (Nat.choose (n + n) n).factorization p := by
  have hc0 : Nat.choose (n + n) n ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hcpos : 0 < Nat.choose (n + n) n := Nat.choose_pos (by omega)
  have hdvd : Nat.choose (n + n) n ∣ Nat.factorial (2 * n) := by
    have h2n : n + n = 2 * n := by ring
    have hmul := Nat.choose_mul_factorial_mul_factorial (n := n + n) (k := n) (by omega)
    rw [show n + n - n = n from by omega, h2n] at hmul
    rw [h2n]
    refine ⟨Nat.factorial n * Nat.factorial n, ?_⟩
    rw [← hmul, mul_assoc]
  have hsupp : (Nat.choose (n + n) n).factorization.support ⊆ primesUpTo (2 * n) := by
    intro p hmem
    have hne := Finsupp.mem_support_iff.1 hmem
    have hp : p.Prime := by
      by_contra hnp
      exact hne (Nat.factorization_eq_zero_of_not_prime _ hnp)
    have hdvd2 : p ∣ Nat.choose (n + n) n := Nat.dvd_of_factorization_pos hne
    have hdvd3 : p ∣ Nat.factorial (2 * n) := hdvd2.trans hdvd
    have hle : p ≤ 2 * n := by
      by_contra hgt
      have hlt : 2 * n < p := Nat.lt_of_not_le hgt
      have hlog : Nat.log p (2 * n) < 2 := by
        rw [Nat.log_lt_iff_lt_pow hp.one_lt]
        exacts [by nlinarith [hp.two_le, hlt], by omega]
      have hIco : (Finset.Ico 1 2 : Finset ℕ) = {1} := by decide
      have hfz : (Nat.factorial (2 * n)).factorization p = 0 := by
        rw [Nat.factorization_factorial hp (n := 2 * n) (b := 2) hlog, hIco]
        simp [Nat.div_eq_of_lt (show (2:ℕ) * n < p from by omega), pow_one]
      have hpos := hp.factorization_pos_of_dvd (Nat.factorial_ne_zero (2 * n)) hdvd3
      rw [hfz] at hpos
      omega
    exact mem_primesUpTo hp hle
  have h1 : Nat.choose (n + n) n
      = (Nat.choose (n + n) n).factorization.prod fun p v => p ^ v :=
    (Nat.prod_factorization_pow_eq_self hc0).symm
  have h3 : (Nat.choose (n + n) n).factorization.prod (fun p v => p ^ v)
      = ∏ p ∈ primesUpTo (2 * n), p ^ (Nat.choose (n + n) n).factorization p := by
    show ∏ p ∈ (Nat.choose (n + n) n).factorization.support,
        p ^ (Nat.choose (n + n) n).factorization p
      = ∏ p ∈ primesUpTo (2 * n), p ^ (Nat.choose (n + n) n).factorization p
    exact Finset.prod_subset hsupp fun p _hS hsupp => by
      have h0 := Finsupp.notMem_support_iff.1 hsupp
      rw [h0, pow_zero]
  conv_lhs => rw [h1]
  rw [h3]

/-- The four-way split (all four factors over their prime sets). -/
theorem central_four_split (n : ℕ) (hn : 0 < n) :
    Nat.choose (n + n) n
      = (∏ p ∈ smallSet n, p ^ (Nat.choose (n + n) n).factorization p)
        * ((∏ p ∈ midSet n, p ^ (Nat.choose (n + n) n).factorization p)
          * ((∏ p ∈ stripSet n, p ^ (Nat.choose (n + n) n).factorization p)
            * (∏ p ∈ largeSet n, p ^ (Nat.choose (n + n) n).factorization p))) := by
  conv_lhs => rw [central_prod_factorization n hn]
  rw [← prod_filter_split (primesUpTo (2 * n)) _ (Nat.sqrt (2 * n)),
    ← prod_filter_split ((primesUpTo (2 * n)).filter fun p => Nat.sqrt (2 * n) < p) _
      (2 * n / 3),
    ← prod_filter_split
      (((primesUpTo (2 * n)).filter fun p => Nat.sqrt (2 * n) < p).filter
        fun p => 2 * n / 3 < p) _ n]
  rfl

/-- The strip contributes nothing (E3 on every element). -/
theorem strip_prod_eq_one (n : ℕ) (hn : 0 < n) :
    ∏ p ∈ stripSet n, p ^ (Nat.choose (n + n) n).factorization p = 1 := by
  apply Finset.prod_eq_one
  intro p hmem
  have hm := Finset.mem_filter.1 hmem
  have hmid := Finset.mem_filter.1 hm.1
  have hguard := Finset.mem_filter.1 hmid.1
  have hp : p.Prime := (Finset.mem_filter.1 hguard.1).2
  have hp2 : 2 * n < p ^ 2 := Nat.sqrt_lt'.1 hguard.2
  have := mid_factorization_eq_zero n p hp hmid.2 hm.2 hp2
  rw [this, pow_zero]

/-- The large factor is the plain product of the primes in `(n, 2n]` (E4). -/
theorem large_prod_eq (n : ℕ) (hn : 0 < n) :
    ∏ p ∈ largeSet n, p ^ (Nat.choose (n + n) n).factorization p
      = ∏ p ∈ largeSet n, p := by
  apply Finset.prod_congr rfl
  intro p hmem
  have hm := Finset.mem_filter.1 hmem
  have hguard := Finset.mem_filter.1 hm.1
  have hinner := Finset.mem_filter.1 hguard.1
  have hp : p.Prime := (Finset.mem_filter.1 hinner.1).2
  rw [large_factorization_eq_one n p hn hp hm.2
    (Nat.le_of_lt_succ (Finset.mem_range.1 (Finset.mem_filter.1 hinner.1).1)), pow_one]

/-- The small factor is at most `(2n)^{#small}` — each `p^{v_p} ≤ 2n`
(`Nat.pow_factorization_choose_le`). -/
theorem small_prod_le (n : ℕ) (hn : 0 < n) :
    ∏ p ∈ smallSet n, p ^ (Nat.choose (n + n) n).factorization p
      ≤ (2 * n) ^ (smallSet n).card :=
  Finset.prod_le_pow_card _ _ _ fun p hmem => by
    have h2n : 0 < n + n := by omega
    calc p ^ (Nat.choose (n + n) n).factorization p
        ≤ n + n := Nat.pow_factorization_choose_le h2n
      _ = 2 * n := by ring

/-- The mid factor is at most `4^{2n/3}` — single carries (`p² > 2n` from
`p > √(2n)`), subset of the primorial, Chebyshev's θ bound. -/
theorem mid_prod_le (n : ℕ) (hn : 0 < n) :
    ∏ p ∈ midSet n, p ^ (Nat.choose (n + n) n).factorization p
      ≤ (4 : ℕ) ^ (2 * n / 3) := by
  have hstep : ∏ p ∈ midSet n, p ^ (Nat.choose (n + n) n).factorization p
      ≤ ∏ p ∈ midSet n, p := by
    refine Finset.prod_le_prod (fun p hp => ?_)
    have hinner := Finset.mem_filter.1 hp
    have hprime : p.Prime := (Finset.mem_filter.1 (Finset.mem_filter.1 hinner.1).1).2
    have hp2 : 2 * n < p ^ 2 :=
      Nat.sqrt_lt'.1 (Finset.mem_filter.1 hinner.1).2
    have hv1 : (Nat.choose (n + n) n).factorization p ≤ 1 :=
      Nat.factorization_choose_le_one (show n + n < p ^ 2 from by linarith)
    have hfin : p ^ (Nat.choose (n + n) n).factorization p ≤ p ^ 1 :=
      Nat.pow_le_pow_right hprime.one_le hv1
    rwa [Nat.pow_one] at hfin
  have hsub : midSet n ⊆ primesUpTo (2 * n / 3) := fun p hmem => by
    have hm := Finset.mem_filter.1 hmem
    have hinner := Finset.mem_filter.1 hm.1
    exact mem_primesUpTo (Finset.mem_filter.1 hinner.1).2 hm.2
  have hmidchain : ∏ p ∈ midSet n, p ^ (Nat.choose (n + n) n).factorization p
      ≤ (4 : ℕ) ^ (2 * n / 3) := by
    have hmono : ∏ p ∈ midSet n, p ≤ ∏ p ∈ primesUpTo (2 * n / 3), p :=
      Finset.prod_le_prod_of_subset_of_one_le hsub fun p hp _hp' =>
        Nat.one_le_iff_ne_zero.2 (Nat.ne_of_gt (Finset.mem_filter.1 hp).2.pos)
    have hprim : ∏ p ∈ primesUpTo (2 * n / 3), p ≤ (4 : ℕ) ^ (2 * n / 3) := by
      sorry  -- M2c tail: θ x = log (∏ primes ≤ x) via theta_eq_sum_primesLE_log
             -- + Real.log_prod + Real.log_le_log_iff + the Nat.cast bridge;
             -- the hθle/hppos pieces are verified in the M2c session notes
    exact le_trans hstep (le_trans hmono hprim)
  exact hmidchain

end SubsetSumL25
