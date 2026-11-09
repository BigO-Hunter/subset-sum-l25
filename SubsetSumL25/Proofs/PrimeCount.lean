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
import SubsetSumL25.Proofs.PrimeCollision

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

/-- Step M2c-1 (odd half-exponent): `12 * (2m+1) ≤ 2^(m+1)` for `m ≥ 12`.
The induction step consumes `2^(k+1) ≥ 24`, which the conditional IH at
`k ≥ 12` supplies; `k < 12` is decided directly (the statement is false for
small `k`, so those cases close off the contradictory hypothesis). -/
theorem twelve_le_odd (m : ℕ) (hm : 12 ≤ m) :
    12 * (2 * m + 1) ≤ 2 ^ m := by
  induction m with
  | zero => exact absurd hm (by omega)
  | succ k ih =>
      rcases Nat.lt_or_ge k 12 with hk | hk
      · interval_cases k <;> first | omega | decide
      · have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ']
        have h3 : 12 * (2 * (k + 1) + 1) = 12 * (2 * k + 1) + 24 := by ring
        have h4 := ih hk
        omega

/-- Step M2c-1 (even half-exponent): `12 * (2m+2) ≤ 2^(m+1)` for `m ≥ 12`. -/
theorem twelve_le_even (m : ℕ) (hm : 12 ≤ m) :
    12 * (2 * m + 2) ≤ 2 ^ (m + 1) := by
  induction m with
  | zero => exact absurd hm (by omega)
  | succ k ih =>
      rcases Nat.lt_or_ge k 12 with hk | hk
      · interval_cases k <;> first | omega | decide
      · have h2 : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [Nat.pow_succ']
        have h3 : 12 * (2 * (k + 1) + 2) = 12 * (2 * k + 2) + 24 := by ring
        have h4 := ih hk
        omega

/-- Step M2c-1: `12 * (L + 1) ≤ 2 ^ ((L + 1) / 2)` for `L ≥ 24` (both parities,
via `Nat.mod_two_eq_zero_or_one`). -/
theorem twelve_le_half (L : ℕ) (hL : 24 ≤ L) : 12 * (L + 1) ≤ 2 ^ ((L + 1) / 2) := by
  rcases Nat.mod_two_eq_zero_or_one L with hp | hp
  · obtain ⟨m, rfl⟩ : ∃ m, L = 2 * m := ⟨L / 2, by omega⟩
    have hm : 12 ≤ m := by omega
    have hdiv : (2 * m + 1) / 2 = m := by omega
    rw [hdiv]
    exact twelve_le_odd m hm
  · obtain ⟨m, rfl⟩ : ∃ m, L = 2 * m + 1 := ⟨L / 2, by omega⟩
    have hm : 12 ≤ m := by omega
    have hdiv : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    have he := twelve_le_even m hm
    have heq : 12 * (2 * m + 1 + 1) = 12 * (2 * m + 2) := by ring
    rw [hdiv, heq]
    exact he

/-- M2c helper: `42 * (L + 2) ≤ 2 ^ L` for `L ≥ 9` — the constant slack the
final count bound consumes. -/
theorem two_pow_ge_42_add : ∀ L, 9 ≤ L → 42 * (L + 2) ≤ 2 ^ L := by
  intro L
  induction L with
  | zero => intro h; omega
  | succ k ih =>
      intro h
      rcases Nat.lt_or_ge k 9 with hk | hk
      · interval_cases k <;> first | omega | decide
      · have h2 : 2 * 2 ^ k = 2 ^ (k + 1) := by rw [Nat.pow_succ']
        have h9 := ih hk
        have hstep : 42 * (k + 1 + 2) = 42 * (k + 2) + 42 := by ring
        omega

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
  classical
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
      classical
      have hppos : 0 < ∏ p ∈ primesUpTo (2 * n / 3), p := by
        refine Finset.prod_pos ?_
        intro p hp
        exact Nat.Prime.pos (Finset.mem_filter.1 hp).2
      have hθle := Chebyshev.theta_le_log4_mul_x
        (x := ((2 * n / 3 : ℕ) : ℝ)) (by norm_num)
      rw [Chebyshev.theta_eq_sum_primesLE_log] at hθle
      have h4log : Real.log ((4:ℝ) ^ (2 * n / 3)) = ((2 * n / 3 : ℕ) : ℝ) * Real.log 4 :=
        Real.log_pow (4:ℝ) (2 * n / 3)
      have hlogprod : Real.log ((∏ p ∈ primesUpTo (2 * n / 3), p : ℕ) : ℝ)
          = ∑ p ∈ primesUpTo (2 * n / 3), Real.log (p : ℝ) := by
        rw [Nat.cast_prod]
        exact Real.log_prod (fun p hp => Nat.cast_ne_zero.2
          (Nat.ne_of_gt (Nat.Prime.pos (Finset.mem_filter.1 hp).2)))
      have hkey : Real.log ((∏ p ∈ primesUpTo (2 * n / 3), p : ℕ) : ℝ)
          ≤ Real.log (((4 : ℕ) ^ (2 * n / 3) : ℕ) : ℝ) := by
        rw [Nat.cast_pow, Nat.cast_ofNat, h4log, hlogprod,
          mul_comm ((2 * n / 3 : ℕ) : ℝ) (Real.log 4)]
        exact hθle
      have hpos2 : (0:ℝ) < ((∏ p ∈ primesUpTo (2 * n / 3), p : ℕ) : ℝ) := by
        exact_mod_cast hppos
      have hypos : (0:ℝ) < (((4 : ℕ) ^ (2 * n / 3) : ℕ) : ℝ) := by
        positivity
      have hprimr : (∏ p ∈ primesUpTo (2 * n / 3), p : ℕ)
          ≤ ((4 : ℕ) ^ (2 * n / 3) : ℕ) :=
        Nat.cast_le.1 (by
          have h := (Real.log_le_log_iff hpos2 hypos).mp hkey
          exact_mod_cast h)
      exact hprimr
    exact le_trans hstep (le_trans hmono hprim)
  exact hmidchain

/-! ### M2c — the assembly (E6/E7) -/

/-- M2c assembly (E6/E7, the `hcount` premise): Erdos's binomial accounting
specialized to the dyadic interval. Chain (n = 2^L ≥ 2^24):
`4^n/(2n+1) ≤ C(2n,n) = P_small·P_mid·P_large` (the strip is 1, E3);
`P_small ≤ (2n)^{c_small}` with `c_small ≤ 3·2^{(L+1)/2}` and `12(L+1) ≤
2^{(L+1)/2}` (`twelve_le_half`), so the small primes eat at most half the
2-exponent budget; `P_mid ≤ 4^{2n/3}` (Chebyshev's θ); `P_large = ∏_{n<p≤2n} p
≤ (2n)^k` with `k = (primesInterval L).card` (the sets differ only at the
non-prime endpoints `n = 2^L`, `2n = 2^{L+1}`). Injectivity of `2^·` turns
the product inequality into an exponent inequality; `omega` with the
`42·(L+2) ≤ 2^L` slack finishes at `c₀ = 1/12`, `L₀ = 24`. -/
theorem erdos_dyadic_primes :
    ∃ (c₀ : ℝ) (L₀ : ℕ), 0 < c₀ ∧ ∀ L, L₀ ≤ L →
      c₀ * (2 : ℝ) ^ L / L ≤ ((primesInterval L).card : ℝ) := by
  refine ⟨1 / 12, 24, by norm_num, ?_⟩
  intro L hL
  have hL1 : 0 < L := by omega
  set k := (primesInterval L).card with hk_def
  set n := 2 ^ L with hn_def
  have hn0 : 0 < n := Nat.two_pow_pos L
  have h2A : 2 ^ (L + 1) = 2 * n := by rw [hn_def, Nat.pow_succ]; ring
  -- the small-prime share: (L+1)·c_small ≤ n/2 via 12(L+1) ≤ 2^((L+1)/2)
  have hY1 : 12 * (L + 1) ≤ 2 ^ ((L + 1) / 2) := twelve_le_half L hL
  have hYsq : (2 ^ ((L + 1) / 2)) ^ 2 ≤ 2 * n := by
    have e1 : (2 ^ ((L + 1) / 2)) ^ 2 = 2 ^ (((L + 1) / 2) * 2) :=
      (Nat.pow_mul 2 ((L + 1) / 2) 2).symm
    have e2 : ((L + 1) / 2) * 2 ≤ L + 1 := by omega
    calc (2 ^ ((L + 1) / 2)) ^ 2 = 2 ^ (((L + 1) / 2) * 2) := e1
      _ ≤ 2 ^ (L + 1) := Nat.pow_le_pow_right (by norm_num) e2
      _ = 2 * n := h2A
  have hVY : 2 ^ ((L + 2) / 2) ≤ 2 * 2 ^ ((L + 1) / 2) := by
    have e1 : (L + 2) / 2 ≤ (L + 1) / 2 + 1 := by omega
    calc 2 ^ ((L + 2) / 2) ≤ 2 ^ ((L + 1) / 2 + 1) := Nat.pow_le_pow_right (by norm_num) e1
      _ = 2 * 2 ^ ((L + 1) / 2) := by rw [Nat.pow_succ]; ring
  have hsqrtV : Nat.sqrt (2 * n) ≤ 2 ^ ((L + 2) / 2) := by
    have e1 : ((L + 2) / 2) * 2 ≤ L + 2 := by omega
    have e2 : (2 ^ ((L + 2) / 2)) ^ 2 = 2 ^ (((L + 2) / 2) * 2) :=
      (Nat.pow_mul 2 ((L + 2) / 2) 2).symm
    have e4 : 2 * n ≤ (2 ^ ((L + 2) / 2)) ^ 2 := by
      calc 2 * n = 2 ^ (L + 1) := h2A.symm
        _ ≤ 2 ^ (((L + 2) / 2) * 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = (2 ^ ((L + 2) / 2)) ^ 2 := e2.symm
    by_contra hcon
    push_neg at hcon
    have hsq : (2 ^ ((L + 2) / 2)) ^ 2 < 2 * n := by
      have h5 := Nat.sqrt_le' (2 * n)
      have h8 : (2 ^ ((L + 2) / 2)) ^ 2 < (Nat.sqrt (2 * n)) ^ 2 :=
        Nat.pow_lt_pow_left hcon (by norm_num)
      calc (2 ^ ((L + 2) / 2)) ^ 2 < (Nat.sqrt (2 * n)) ^ 2 := h8
        _ ≤ 2 * n := h5
    omega
  have hcardS : (smallSet n).card ≤ 3 * 2 ^ ((L + 1) / 2) := by
    have e0 : smallSet n ⊆ Finset.range (Nat.sqrt (2 * n) + 1) := by
      intro p hmem
      have hm := Finset.mem_filter.1 hmem
      exact Finset.mem_range.2 (by omega)
    have e1 := Finset.card_le_card e0
    rw [Finset.card_range] at e1
    omega
  have f2 : (L + 1) * (smallSet n).card * 4 ≤ 2 * n := by
    have t1 : (L + 1) * (smallSet n).card ≤ 3 * ((L + 1) * 2 ^ ((L + 1) / 2)) := by
      have h := Nat.mul_le_mul_right (L + 1) hcardS
      calc (L + 1) * (smallSet n).card = (smallSet n).card * (L + 1) := Nat.mul_comm _ _
        _ ≤ 3 * 2 ^ ((L + 1) / 2) * (L + 1) := h
        _ = 3 * ((L + 1) * 2 ^ ((L + 1) / 2)) := by ring
    have t2 : 12 * ((L + 1) * 2 ^ ((L + 1) / 2))
        ≤ 2 ^ ((L + 1) / 2) * 2 ^ ((L + 1) / 2) := by
      have h := Nat.mul_le_mul hY1 (Nat.le_refl (2 ^ ((L + 1) / 2)))
      calc 12 * ((L + 1) * 2 ^ ((L + 1) / 2)) = (12 * (L + 1)) * 2 ^ ((L + 1) / 2) := by ring
        _ ≤ 2 ^ ((L + 1) / 2) * 2 ^ ((L + 1) / 2) := h
    calc (L + 1) * (smallSet n).card * 4 = 4 * ((L + 1) * (smallSet n).card) := by ring
      _ ≤ 4 * (3 * ((L + 1) * 2 ^ ((L + 1) / 2))) := Nat.mul_le_mul_left _ t1
      _ = 12 * ((L + 1) * 2 ^ ((L + 1) / 2)) := by ring
      _ ≤ 2 ^ ((L + 1) / 2) * 2 ^ ((L + 1) / 2) := t2
      _ = (2 ^ ((L + 1) / 2)) ^ 2 := (pow_two _).symm
      _ ≤ 2 * n := hYsq
  -- the four-way accounting chain, in ℕ
  have hsplit := central_four_split n hn0
  rw [strip_prod_eq_one n hn0, one_mul] at hsplit
  rw [large_prod_eq n hn0] at hsplit
  -- hsplit : C = P_small * (P_mid * ∏ largeSet p)
  have hb1 := small_prod_le n hn0
  have hb2 := mid_prod_le n hn0
  have hch : Nat.choose (n + n) n = Nat.choose (2 * n) n := by
    rw [show n + n = 2 * n from by ring]
  rw [hch] at hsplit hb1 hb2
  have hlarge_le2n : ∀ p ∈ largeSet n, p ≤ 2 * n := by
    intro p hmem
    have hm := Finset.mem_filter.1 hmem
    have hm2 := Finset.mem_filter.1 hm.1
    have hm3 := Finset.mem_filter.1 hm2.1
    exact Nat.le_of_lt_succ (Finset.mem_range.1 (Finset.mem_filter.1 hm3.1).1)
  have hb3 : ∏ p ∈ largeSet n, p ≤ (2 * n) ^ (largeSet n).card :=
    Finset.prod_le_pow_card _ _ _ hlarge_le2n
  have hsub : largeSet n ⊆ primesInterval L := by
    intro p hmem
    have hm := Finset.mem_filter.1 hmem
    have hnlt : n < p := hm.2
    have hprime : p.Prime :=
      (Finset.mem_filter.1 (Finset.mem_filter.1 (Finset.mem_filter.1 hm.1).1).1).2
    have hle : p ≤ 2 * n := hlarge_le2n p hmem
    have h2ge2 : (2:ℕ) ≤ 2 ^ L := by
      calc (2:ℕ) = 2 ^ 1 := rfl
        _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hnot2n : ¬(2 * n).Prime := by
      have e1 : 2 * n = 2 * 2 ^ L := by rw [← h2A, Nat.pow_succ]
      rw [e1]
      exact Nat.not_prime_mul (by norm_num) (by have := h2ge2; omega)
    have hlt : p < 2 * n := by
      rcases Nat.lt_or_ge p (2 * n) with h | h
      · exact h
      · have hEq : p = 2 * n := le_antisymm hle h
        exact absurd (hEq ▸ hprime) hnot2n
    simp only [primesInterval, Finset.mem_filter, Finset.mem_Ico]
    rw [h2A]
    refine ⟨⟨?_, hlt⟩, hprime⟩
    first
      | exact hnlt.le
      | (rw [← hn_def]; exact hnlt.le)
  have hcl : (largeSet n).card ≤ k := Finset.card_le_card hsub
  have hb34 : ∏ p ∈ largeSet n, p ≤ (2 * n) ^ k := by
    refine le_trans hb3 ?_
    exact Nat.pow_le_pow_right (by omega) hcl
  have hchain : Nat.choose (2 * n) n
      ≤ (2 * n) ^ (smallSet n).card * ((4 : ℕ) ^ (2 * n / 3) * (2 * n) ^ k) := by
    calc Nat.choose (2 * n) n
        = (∏ p ∈ smallSet n, p ^ (Nat.choose (2 * n) n).factorization p)
            * ((∏ p ∈ midSet n, p ^ (Nat.choose (2 * n) n).factorization p)
            * (∏ p ∈ largeSet n, p)) := hsplit
      _ ≤ (2 * n) ^ (smallSet n).card
            * ((∏ p ∈ midSet n, p ^ (Nat.choose (2 * n) n).factorization p)
            * (∏ p ∈ largeSet n, p)) := Nat.mul_le_mul_right _ hb1
      _ ≤ (2 * n) ^ (smallSet n).card
            * ((4 : ℕ) ^ (2 * n / 3) * (∏ p ∈ largeSet n, p)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hb2)
      _ ≤ (2 * n) ^ (smallSet n).card * ((4 : ℕ) ^ (2 * n / 3) * (2 * n) ^ k) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hb34)
  -- E1's ℕ-core: the row-sum argument directly (central_binom_big is its
  -- real-form shadow; here we stay in ℕ to avoid cast bridges)
  have hbb2 : ((4:ℕ) ^ n : ℕ) ≤ (2 * n + 1) * (Nat.choose (2 * n) n) := by
    have hle : ∀ k ∈ Finset.range (2 * n + 1), Nat.choose (2 * n) k ≤ Nat.choose (2 * n) n :=
      fun k _ => by
        have h := Nat.choose_le_middle k (2 * n)
        rwa [Nat.mul_div_cancel_left _ (show (0:ℕ) < 2 by norm_num)] at h
    have hsum : (2:ℕ) ^ (2 * n) ≤ (2 * n + 1) * Nat.choose (2 * n) n := by
      have h1 : ∑ k ∈ Finset.range (2 * n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n) :=
        Nat.sum_range_choose (2 * n)
      calc (2:ℕ) ^ (2 * n) = ∑ k ∈ Finset.range (2 * n + 1), Nat.choose (2 * n) k := h1.symm
        _ ≤ ∑ _k ∈ Finset.range (2 * n + 1), Nat.choose (2 * n) n :=
            Finset.sum_le_sum fun k hk => hle k hk
        _ = (2 * n + 1) * Nat.choose (2 * n) n := by
            rw [Finset.sum_const, smul_eq_mul]; simp
    have hp4 : ((4:ℕ) ^ n : ℕ) = (2:ℕ) ^ (2 * n) := by
      rw [show (4:ℕ) = 2 ^ 2 from rfl, Nat.pow_mul]
    rw [hp4]
    exact hsum
  have hnat : ((4:ℕ) ^ n : ℕ) ≤ (2 * n + 1)
      * ((2 * n) ^ (smallSet n).card * ((4 : ℕ) ^ (2 * n / 3) * (2 * n) ^ k)) := by
    calc ((4:ℕ) ^ n : ℕ) ≤ (2 * n + 1) * (Nat.choose (2 * n) n) := hbb2
      _ ≤ (2 * n + 1) * ((2 * n) ^ (smallSet n).card
            * ((4 : ℕ) ^ (2 * n / 3) * (2 * n) ^ k)) :=
            Nat.mul_le_mul_left _ hchain
  -- powers of two
  have hpow4 : ((4:ℕ) ^ n : ℕ) = 2 ^ (2 * n) := by
    rw [Nat.pow_mul]
  have hterm : (2 * n) ^ (smallSet n).card * ((4 : ℕ) ^ (2 * n / 3) * (2 * n) ^ k)
      = 2 ^ ((L + 1) * ((smallSet n).card + k) + 2 * (2 * n / 3)) := by
    have e1 : (2 * n) ^ (smallSet n).card = 2 ^ ((L + 1) * (smallSet n).card) := by
      rw [← h2A, ← Nat.pow_mul]
    have e2 : (2 * n) ^ k = 2 ^ ((L + 1) * k) := by
      rw [← h2A, ← Nat.pow_mul]
    have e3 : (4 : ℕ) ^ (2 * n / 3) = 2 ^ (2 * (2 * n / 3)) := by
      have h4 : (4 : ℕ) = 2 ^ 2 := rfl
      rw [h4, ← Nat.pow_mul]
    rw [e1, e2, e3, ← Nat.pow_add, ← Nat.pow_add]
    congr 1
    ring
  have hbound : (2 * n + 1) ≤ 2 ^ (L + 2) := by
    have e1 : 2 ^ (L + 2) = 2 * n * 2 := by rw [Nat.pow_succ, h2A]
    omega
  have hexact : 2 ^ (2 * n)
      ≤ 2 ^ ((L + 2) + ((L + 1) * ((smallSet n).card + k) + 2 * (2 * n / 3))) := by
    calc 2 ^ (2 * n) = (4:ℕ) ^ n := hpow4.symm
      _ ≤ (2 * n + 1) * ((2 * n) ^ (smallSet n).card
            * ((4 : ℕ) ^ (2 * n / 3) * (2 * n) ^ k)) := hnat
      _ ≤ (2 ^ (L + 2)) * ((2 * n) ^ (smallSet n).card
            * ((4 : ℕ) ^ (2 * n / 3) * (2 * n) ^ k)) := Nat.mul_le_mul_right _ hbound
      _ ≤ (2 ^ (L + 2)) * (2 ^ ((L + 1) * ((smallSet n).card + k)
            + 2 * (2 * n / 3))) := by rw [hterm]
      _ = 2 ^ ((L + 2) + ((L + 1) * ((smallSet n).card + k) + 2 * (2 * n / 3))) := by
          rw [← Nat.pow_add (2:ℕ) (L + 2)
            (((L + 1) * ((smallSet n).card + k) + 2 * (2 * n / 3)))]
  have hexp : 2 * n ≤ (L + 2) + ((L + 1) * ((smallSet n).card + k) + 2 * (2 * n / 3)) := by
    rcases Nat.lt_or_ge ((L + 2) + ((L + 1) * ((smallSet n).card + k) + 2 * (2 * n / 3)))
        (2 * n) with h | h
    · exact absurd (Nat.pow_lt_pow_right (by norm_num : (1:ℕ) < 2) h)
        (Nat.not_lt.2 hexact)
    · exact h
  -- the count bound
  have hsplit2 : (L + 1) * ((smallSet n).card + k)
      = (L + 1) * (smallSet n).card + (L + 1) * k := by ring
  have hQ : n ≤ 7 * ((L + 1) * k) := by
    have f3 : 42 * (L + 2) ≤ n := two_pow_ge_42_add L (by omega)
    omega
  have hfinal : n ≤ 12 * (L * k) := by
    calc n ≤ 7 * ((L + 1) * k) := hQ
      _ = (7 * (L + 1)) * k := by ring
      _ ≤ (12 * L) * k := Nat.mul_le_mul_right k (by omega)
      _ = 12 * (L * k) := by ring
  -- cast into ℝ
  have hfin2 : ((n : ℕ) : ℝ) ≤ (12:ℝ) * ((L:ℝ) * (k:ℝ)) := by
    have h : ((n : ℕ) : ℝ) ≤ (((12 * (L * k) : ℕ) : ℝ)) := Nat.cast_le.2 hfinal
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat] at h
    exact h
  have hcastn : ((n : ℕ) : ℝ) = (2 : ℝ) ^ L := by
    rw [hn_def]
    exact Nat.cast_pow 2 L
  rw [hcastn] at hfin2
  first
    | rw [div_le_iff₀ (Nat.cast_pos.2 hL1)]
    | skip
  have hr : (1:ℝ)/12 * (12 * ((L:ℝ) * (k:ℝ))) = (L:ℝ) * (k:ℝ) := by ring
  have hr2 : (1:ℝ)/12 * (12 * ((k:ℝ) * (L:ℝ))) = (k:ℝ) * (L:ℝ) := by ring
  linarith [hfin2, hr, hr2]

/-- The discharge: the collision bound O3 without the `hcount`/`hpos`
hypotheses — `erdos_dyadic_primes` supplies the witnesses (K = 1/c₀, L* = L₀),
so O3 and the L5.2 union bound become unconditional number theory. -/
theorem L2_5_prime_collision_unconditional :
    ∃ (K : ℝ) (Lstar : ℕ), 0 < K ∧ ∀ L, Lstar ≤ L → ∀ (D : ℤ) (B : ℕ),
      D ≠ 0 → 1 ≤ B → ((D.natAbs : ℝ) < (2 : ℝ) ^ B) →
      (badPrimes L D : ℝ) / (primesInterval L).card
        ≤ K * (B : ℝ) * (L : ℝ) / (2 : ℝ) ^ L := by
  obtain ⟨c₀, L₀, hc₀, hcount⟩ := erdos_dyadic_primes
  refine L2_5_prime_collision c₀ hc₀ (max L₀ 1) ?_ ?_
  · intro L hL
    exact hcount L (le_trans (Nat.le_max_left L₀ 1) hL)
  · intro L hL
    have hL1 : 0 < L := lt_of_lt_of_le (by norm_num) (le_trans (Nat.le_max_right L₀ 1) hL)
    have h1 : (0:ℝ) < c₀ * (2:ℝ)^L / L :=
      div_pos (mul_pos hc₀ (by positivity)) (Nat.cast_pos.2 hL1)
    exact Nat.cast_pos.1 (lt_of_lt_of_le h1
      (hcount L (le_trans (Nat.le_max_left L₀ 1) hL)))

end SubsetSumL25
