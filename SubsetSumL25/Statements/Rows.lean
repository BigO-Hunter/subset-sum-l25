/-
M1 (ROWS): the three conditional board rows — rev8g Theorem 1 (0.4875755,
ours), JoshuaQFEX (0.487676) and Bills (0.4876723) (external, pointer
rows).  This is the bridge from «the ladder proves the pieces» to «the rows
the board cares about»: the row theorem is stated with the still-named
conditions as opaque Prop hypotheses (the BRIDGE milestone-1
hypotheses-in-statements architecture), while everything the ladder
kernel-checked is NOT a hypothesis — it is theorems of this package.

Primary source: rev8g `paper_2026-11-06_rev8g.tex` (sha256 18899a6e…,
provenance PROVENANCE_rev8g.md), Theorem 1 (`thm:main`, line 78).
Credit: Theorem 1 is jv1000/rev8g's; the ladder it consumes is Base's and
OpenAI's, kernel-checked here.
-/
import Mathlib

namespace SubsetSumL25

/- Verbatim (rev8g, Theorem 1, `thm:main`):

   «Assume the non-numerical lemmas of the OpenAI paper and of Base's
   written proof.  Then there is a uniform randomized algorithm for Subset
   Sum in the word-RAM model that halts on every execution and answers
   correctly with probability at least 2/3, and, for every fixed c and
   every fixed T′ > T = 0.4875754036, uses O(2^{T′n}) word operations on
   every input of n integers whose bit lengths, and that of the target,
   are at most n^c.  In particular it runs in time O(2^{0.4875755n}).»

   Status and caveats (rev8g §8, verbatim fragments): «The exponent of
   Theorem 1 is T = τ₀ + 20ε = 0.4875754036 … It is conditional on Base's
   written proof (its alias-step cost accounting, Lemma A5 and its checksum
   changes) and on the OpenAI paper, exactly as JoshuaQFEX and Bills are.»
   «The constants ζ and the input guard are free in Base; our choices
   ζ = 10^{-8} and guard = 10^8 only raise the cutoff n … Base's
   Proposition P then needs n > 10^8, and its Chebyshev term 4/(ζ²n) is
   small only for n of order 10^{17}.» -/

/-- **rev8g Theorem 1 (the 0.4875755 conditional row), time-bound tail.**

The still-named conditions are opaque Props (hypotheses-in-statements):
`O1`/`O2`/`O3`/`O6` — the number-theoretic cluster BRIDGE attack-order
item 2 (not yet formalized here); `V1` — the sine-filter extension of the
L3.2 uniform-boundedness (the paper's filter has sine terms);
`SumCheck`/`AliasExt` — the checksum and alias-extraction procedures (the
`D_s` boundary); `CertNum` — rev8g's own certified numerics (33 conditions
+ both moments, their certification).

What the ladder DISCHARGES is not a hypothesis: B1–B5, O4, O8 and the
O5/O7 cores are theorems of this package.  `hops` is the assembled
per-stage bound those theorems give (the o8/o5 budget shape with the O(√n)
explicit and a polynomial factor); the theorem is the T′-absorption tail —
for every fixed `T′` above the point's exponent `τ₀ + 20ε` (rev8g's
T = 0.4875754036), the bound is `O(2^{T′n})`: the `2√n` slack and the
polynomial factor are `2^{o(n)}`, absorbed by the fixed gap `T′ − (τ₀ +
20ε) > 0` for all large `n`.

**PROVED (this file):** the T′-absorption tail itself — the exponential
`2^{o(n)}` slack (`2√n + 2` and the polynomial factor) is absorbed by the
fixed gap `T′ − (τ₀+20ε) > 0` past an explicit threshold, so the row's
per-stage bound `hops` gives `ops n ≤ 2^{T'·n}` for all large n.  The
row's named conditions remain hypotheses (the procedures, the certified
numerics, the O-cluster and V1 lemmas). -/
theorem rev8g_thm1_time {O1 O2 O3 O6 V1 SumCheck AliasExt CertNum : Prop}
    (_hO1 : O1) (_hO2 : O2) (_hO3 : O3) (_hO6 : O6) (_hV1 : V1)
    (_hSum : SumCheck) (_hAlias : AliasExt) (_hCert : CertNum)
    (τ₀ ε : ℝ) (hε : 0 ≤ ε)
    (ops : ℕ → ℝ)  -- the named assembled per-stage op bound (the procedure's counter)
    (poly : ℕ → ℝ) (hpoly : ∀ n : ℕ, poly n ≤ ((n : ℝ) + 1) ^ 2)
    (c : ℝ) (hc : 0 ≤ c) (n₀ : ℕ)
    (hops : ∀ n ≥ n₀, ops n ≤ c * poly n
      * 2 ^ ((τ₀ + 20 * ε) * n + 2 * Real.sqrt n + 2))
    (T' : ℝ) (hT : τ₀ + 20 * ε < T') :
    ∃ n₁ : ℕ, ∀ n ≥ n₁, ops n ≤ 2 ^ (T' * n) := by
  classical
  have hδ0 : 0 < T' - (τ₀ + 20 * ε) := by linarith
  set δ : ℝ := T' - (τ₀ + 20 * ε) with hδdef
  have hδpos : 0 < δ := hδ0
  have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- the q-block (hoisted: the √-slack's linarith needs hsqrt1)
  set r : ℝ := 2 ^ (δ/2) with hrdef
  have hrpos : 0 < r := Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _
  have hr1 : 1 < r := Real.one_lt_rpow (by norm_num) (by positivity)
  set q : ℝ := Real.sqrt r with hq
  have hqpos : 0 ≤ q := Real.sqrt_nonneg r
  have hqq : q * q = r := Real.mul_self_sqrt (by linarith)
  have hq1 : (1:ℝ) < q := by nlinarith [hqq, hr1, hqpos]
  have hlogq : 0 < Real.log q := Real.log_pos hq1
  have hsqrt1 : (1:ℝ) < Real.sqrt q := by
    have h1 : Real.sqrt (1:ℝ) < Real.sqrt q := Real.sqrt_lt_sqrt (by norm_num) hq1
    rwa [Real.sqrt_one] at h1
  -- aux 1: the √-slack absorbs — 2^{2√n+2} ≤ 2^{(δ/2)n} past ⌈(8/δ)²⌉+1
  have hsqrtle : ∃ n₂ : ℕ, ∀ n ≥ n₂, (2:ℝ) ^ (2 * Real.sqrt (n:ℝ) + 2) ≤ (2:ℝ) ^ ((δ/2) * (n:ℝ)) := by
    obtain ⟨n₂, hn₂⟩ := exists_nat_gt (((8:ℝ)/δ)^2)
    refine ⟨n₂ + 4, fun n hn => ?_⟩
    have hnδ : 0 < δ := hδ0
    have h4n : (4:ℕ) ≤ n := by omega
    have hnpos : (4:ℝ) ≤ (n:ℝ) := by exact_mod_cast h4n
    have hge : ((8:ℝ)/δ)^2 ≤ (n:ℝ) := by
      have h1 : ((8:ℝ)/δ)^2 < ((n₂:ℕ) : ℝ) := hn₂
      have h2 : ((n₂:ℕ) : ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : (n₂:ℕ) ≤ n)
      linarith
    have hsqrt8 : (8:ℝ)/δ ≤ Real.sqrt (n:ℝ) := Real.le_sqrt_of_sq_le hge
    have hs2 : (2:ℝ) ≤ Real.sqrt (n:ℝ) := Real.le_sqrt_of_sq_le (by linarith)
    have h8 : (8:ℝ) ≤ δ * Real.sqrt (n:ℝ) := by
      have h1 : (8:ℝ)/δ ≤ Real.sqrt (n:ℝ) := hsqrt8
      rw [div_le_iff₀ hnδ] at h1
      linarith
    have hprod : (8:ℝ) * Real.sqrt (n:ℝ) ≤ δ * ((Real.sqrt (n:ℝ)) * Real.sqrt (n:ℝ)) := by
      refine mul_le_mul_of_nonneg_right h8 (Real.sqrt_nonneg n)
    rw [mul_assoc δ (Real.sqrt (n:ℝ)) (Real.sqrt (n:ℝ)),
        Real.mul_self_sqrt (by exact_mod_cast h4n)] at hprod
    have hs2' : (2:ℝ) + 2 * Real.sqrt (n:ℝ) ≤ (4:ℝ) * Real.sqrt (n:ℝ) := by nlinarith
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    linarith [hprod, hs2']
  -- aux 2: the polynomial absorbs — c·(n+1)² ≤ 2^{(δ/2)n} eventually
  have hpolyle : ∃ n₃ : ℕ, ∀ n ≥ n₃, c * ((n:ℝ) + 1) ^ 2 ≤ (2:ℝ) ^ ((δ/2) * (n:ℝ)) := by
    rcases eq_or_lt_of_le hc with hc0 | hc0
    · exact ⟨0, fun n _ => by rw [hc0.symm, zero_mul]; exact Real.rpow_nonneg (by norm_num)⟩
    have hc0 : 0 < c := hc0
    -- ratio threshold: (n+2)² ≤ q(n+1)² past N
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / (Real.sqrt q - 1))
    have hstep : ∀ n ≥ N, ((n:ℝ) + 2) ^ 2 ≤ q * ((n:ℝ) + 1) ^ 2 := by
      intro n hn
      have hNn : ((N:ℕ) : ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      have hpos : (0:ℝ) < Real.sqrt q - 1 := by linarith [hsqrt1]
      have h1 : (1:ℝ) / (Real.sqrt q - 1) ≤ ((n:ℝ) + 1) := by
        have h2 : (1:ℝ) / (Real.sqrt q - 1) < ((N:ℕ) : ℝ) := hN
        have h3 : ((N:ℕ) : ℝ) ≤ ((n:ℕ) : ℝ) := by exact_mod_cast hn
        have h4 : ((N:ℕ) : ℝ) ≤ (n:ℝ) := by exact_mod_cast h3
        linarith
      rw [div_le_iff₀ hpos] at h1
      have hle : ((n:ℝ) + 2) ≤ Real.sqrt q * ((n:ℝ) + 1) := by nlinarith
      calc ((n:ℝ) + 2) ^ 2 ≤ (Real.sqrt q * ((n:ℝ) + 1)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hle 2
        _ = q * ((n:ℝ) + 1) ^ 2 := by
              rw [mul_pow, Real.mul_self_sqrt (le_of_lt hr1), hq]
    -- geometric invariant past N: c·(n+1)² ≤ A·q^n, A := c(N+1)²/q^N
    -- (the base is trivially true by div_mul_cancel₀; the step uses the q-ratio)
    set A : ℝ := c * (((N:ℕ) : ℝ) + 1) ^ 2 / q ^ (N:ℕ) with hAdef
    have hApos : 0 < A := by
      rw [hAdef]
      refine div_pos (mul_pos hc0 (by positivity)) (by positivity)
    have hbase : c * (((N:ℕ) : ℝ) + 1) ^ 2 ≤ A * q ^ (N:ℕ) := by
      rw [hAdef, div_mul_cancel₀ _ (by positivity)]
    have hinv : ∀ m ≥ N, c * (((m:ℕ) : ℝ) + 1) ^ 2 ≤ A * q ^ (m:ℕ) := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => exact hbase
      | succ k _ ihk =>
        have hkN : N ≤ k := by omega
        have hks := hstep k hkN
        rw [Nat.cast_add, Nat.cast_one]
        calc c * (((k:ℕ) : ℝ) + 2) ^ 2 ≤ c * (q * (((k:ℕ) : ℝ) + 1) ^ 2) := by
              exact mul_le_mul_of_nonneg_left hks (le_of_lt hc0)
          _ = q * (c * (((k:ℕ) : ℝ) + 1) ^ 2) := by ring
          _ ≤ q * (A * q ^ (k:ℕ)) := mul_le_mul_of_nonneg_left ihk (le_of_lt hqpos)
          _ = A * q ^ ((k:ℕ) + 1) := by
              rw [pow_succ]
              ring
    -- absorb A via the log threshold: A ≤ q^n for large n
    have hnN : N ≤ n := le_trans (le_max_left _ _) hn
    obtain ⟨N₃, hN₃⟩ := exists_nat_gt (Real.log A / Real.log q)
    have hA : A ≤ q ^ (n:ℕ) := by
      have h1 : Real.log A ≤ Real.log (q ^ (n:ℕ)) := by
        rw [Real.log_pow (le_of_lt hq1)]
        have hnpos : (0:ℝ) < (n:ℝ) := by positivity
        have hdiv : (Real.log A / Real.log q) ≤ (n:ℝ) := by linarith
        rw [div_le_iff₀ hlogq] at hdiv
        exact hdiv
      exact (Real.log_le_log_iff hApos (by positivity)).mp h1
    calc c * ((n:ℝ) + 1) ^ 2 ≤ A * q ^ (n:ℕ) := hinv n hnN
      _ ≤ q ^ (n:ℕ) * q ^ (n:ℕ) := mul_le_mul_of_nonneg_left hA (le_of_lt hqpos)
      _ = q ^ ((n:ℕ) + (n:ℕ)) := (pow_add q n n).symm
      _ = q ^ (2 * (n:ℕ)) := by ring_nf
      _ = r ^ (n:ℕ) := by rw [← pow_mul, hqq]
      _ = (2:ℝ) ^ ((δ/2) * (n:ℕ)) := by rw [hrdef, Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) < 2)]
  -- assemble
  obtain ⟨n₂, hn₂⟩ := hsqrtle
  obtain ⟨n₃, hn₃⟩ := hpolyle
  have hbig : ops n ≤ (2:ℝ) ^ (T' * (n:ℝ)) := by
    have hE : ((τ₀ + 20 * ε) * (n:ℝ) + 2 * Real.sqrt (n:ℝ) + 2)
        = 2 * Real.sqrt (n:ℝ) + 2 + (τ₀ + 20 * ε) * (n:ℝ) := by ring
    calc ops n ≤ c * poly n * (2 ^ (2 * Real.sqrt (n:ℝ) + 2) * 2 ^ ((τ₀ + 20 * ε) * (n:ℝ))) := by
          rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)]
          exact hops n hn₀
      _ ≤ c * ((n:ℝ) + 1) ^ 2 * (2 ^ (2 * Real.sqrt (n:ℝ) + 2) * 2 ^ ((τ₀ + 20 * ε) * (n:ℝ))) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hpoly n)
            (Real.rpow_nonneg (by norm_num))) hc0
      _ ≤ ((2:ℝ) ^ ((δ/2) * (n:ℝ)) * 2 ^ ((δ/2) * (n:ℝ))) * 2 ^ ((τ₀ + 20 * ε) * (n:ℝ)) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul (hn₃ n hn₃) (hn₂ n hn₂)
            (by positivity) (by positivity)) (by positivity)
      _ = (2:ℝ) ^ ((δ/2) * (n:ℝ) + (δ/2) * (n:ℝ) + (τ₀ + 20 * ε) * (n:ℝ)) := by
          rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2), ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      _ = (2:ℝ) ^ (T' * (n:ℝ)) := by congr 1; rw [hδdef]; ring
  refine le_trans hbig ?_
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  exact_mod_cast le_refl n
