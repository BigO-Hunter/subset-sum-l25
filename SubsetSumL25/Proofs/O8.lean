/-
M2 (O8): proofs of Base §5.2's word-RAM accounting.  Primary-source quotes
live in `Statements/O8.lean`; this file is the statement-of-record for
everything proved here.

Boundary (D7): all statements count word operations / elementary steps in
Base's own counters; no Light-step translation is imported.
-/
import Mathlib
import SubsetSumL25.Statements.O8

namespace SubsetSumL25

/-- The cap of §5.2 Step 6, as a real bound. -/
noncomputable def o8Cap (τ₀ n : ℝ) : ℝ := 2 ^ (⌈τ₀ * n⌉ + ⌈n ^ (0.7 : ℝ)⌉)

/-- The Step-6 cap fits inside Thm A part 2's budget exponent: the two
ceilings cost one unit each (`⌈x⌉ < x+1`), absorbed by the `+2n^{0.7}` slack.
The slack needs `2 ≤ n^{0.7}` — the paper's «sufficiently large n» made
explicit (n ≥ 2^{10/7}); below that the absorption is genuinely false
(n = 1/2: cap = 2² > 2^{1.46}). -/
theorem o8_cap_absorb {τ₀ n : ℝ} (hn07 : 2 ≤ n ^ (0.7 : ℝ)) :
    o8Cap τ₀ n ≤ (2 : ℝ) ^ (τ₀ * n + 2 * n ^ (0.7 : ℝ)) := by
  -- NB: in this pin `⌈x⌉` for `x : ℝ` is ℤ-valued (`Int.ceil`), so the cap's
  -- `2 ^ (…)` is integer-exponent zpow; bridge with `Real.rpow_intCast`.
  have h1 : ((⌈τ₀ * n⌉ : ℤ) : ℝ) < τ₀ * n + 1 := Int.ceil_lt_add_one _
  have h2 : ((⌈n ^ (0.7 : ℝ)⌉ : ℤ) : ℝ) < n ^ (0.7 : ℝ) + 1 := Int.ceil_lt_add_one _
  have hexp : ((⌈τ₀ * n⌉ + ⌈n ^ (0.7 : ℝ)⌉ : ℤ) : ℝ) ≤ τ₀ * n + 2 * n ^ (0.7 : ℝ) := by
    rw [Int.cast_add]
    linarith
  rw [o8Cap, ← Real.rpow_intCast]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp

/-- §5.2 Step 6's envelope: the ten counted categories with each category at
most `C` sum to at most `10·C`. -/
theorem o8_cap_envelope {C : ℝ} (S : ℕ → ℝ)
    (hitem : ∀ i ∈ Finset.range 10, S i ≤ C) :
    ∑ i ∈ Finset.range 10, S i ≤ (10 : ℝ) * C := by
  calc ∑ i ∈ Finset.range 10, S i
      ≤ ∑ _i ∈ Finset.range 10, C := Finset.sum_le_sum hitem
    _ = (10 : ℝ) * C := by rw [Finset.sum_const, nsmul_eq_mul]; simp

/-- Thm A part 2 (§5.1), the formalizable skeleton: the ten elementary-step
totals within `cap · P` (P = the named per-category word-cost bound) sum to
within `16·P·2^{τ₀n+2n^{0.7}}`. -/
theorem o8_time_bound {τ₀ n P : ℝ} (hn07 : 2 ≤ n ^ (0.7 : ℝ)) (hP : 0 ≤ P) (S : ℕ → ℝ)
    (hcat : ∀ i ∈ Finset.range 10, S i ≤ o8Cap τ₀ n * P) :
    ∑ i ∈ Finset.range 10, S i ≤ (16 : ℝ) * P * 2 ^ (τ₀ * n + 2 * n ^ (0.7 : ℝ)) := by
  have h02 : (0 : ℝ) ≤ 2 := by norm_num
  have hcap0 : 0 ≤ o8Cap τ₀ n := by
    rw [o8Cap, ← Real.rpow_intCast]
    exact Real.rpow_nonneg h02 _
  have h1016 : (10 : ℝ) ≤ 16 := by norm_num
  have h16P : 0 ≤ (16 : ℝ) * P := by linarith
  have hstep1 : ∑ i ∈ Finset.range 10, S i ≤ (10 : ℝ) * (o8Cap τ₀ n * P) := by
    refine le_trans (Finset.sum_le_sum hcat) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    simp
  have hstep2 : (10 : ℝ) * (o8Cap τ₀ n * P)
      ≤ (16 : ℝ) * P * 2 ^ (τ₀ * n + 2 * n ^ (0.7 : ℝ)) := by
    have hcp : 0 ≤ o8Cap τ₀ n * P := mul_nonneg hcap0 hP
    calc (10 : ℝ) * (o8Cap τ₀ n * P) ≤ 16 * (o8Cap τ₀ n * P) :=
        mul_le_mul_of_nonneg_right h1016 hcp
      _ = 16 * P * o8Cap τ₀ n := by ring
      _ ≤ 16 * P * 2 ^ (τ₀ * n + 2 * n ^ (0.7 : ℝ)) :=
          mul_le_mul_of_nonneg_left (o8_cap_absorb hn07) h16P
  exact le_trans hstep1 hstep2

/-- §5.2 Step 3's verbatim two-sided trial-count bound. -/
theorem o8_trial_count_bound {n Shat e T : ℝ} (hn : 0 ≤ n) (hS : 0 < Shat)
    (hS1 : Shat ≤ 1) (hT : T = n ^ 7 * 2 ^ e * ⌈1 / Shat⌉) :
    n ^ 7 * 2 ^ (Real.logb 2 (1 / Shat) + e) ≤ T
      ∧ T ≤ 2 * n ^ 7 * 2 ^ (Real.logb 2 (1 / Shat) + e) := by
  have hx : 0 < 1 / Shat := one_div_pos.mpr hS
  have hrpow : (2 : ℝ) ^ (Real.logb 2 (1 / Shat) + e) = (1 / Shat) * 2 ^ e := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hx]
  have hge1 : (1 : ℝ) ≤ 1 / Shat := by
    have hstep : (1 : ℝ) / 1 ≤ (1 : ℝ) / Shat :=
      div_le_div_iff₀ (by norm_num : (0 : ℝ) < 1) hS |>.mpr (by linarith)
    simpa using hstep
  have hpos : 0 ≤ n ^ 7 * 2 ^ e := by
    have hn7 : 0 ≤ n ^ 7 := pow_nonneg hn 7
    have he2 : 0 < (2 : ℝ) ^ e := by positivity
    exact mul_nonneg hn7 (le_of_lt he2)
  have hceil : (1 : ℝ) / Shat ≤ ⌈1 / Shat⌉ := Int.le_ceil _
  have hceil2 : ⌈1 / Shat⌉ ≤ 2 * (1 / Shat) := by
    linarith [Int.ceil_lt_add_one (1 / Shat), hge1]
  constructor
  · rw [hT, hrpow]
    calc n ^ 7 * ((1 / Shat) * 2 ^ e) = (n ^ 7 * 2 ^ e) * (1 / Shat) := by ring
      _ ≤ (n ^ 7 * 2 ^ e) * ⌈1 / Shat⌉ := mul_le_mul_of_nonneg_left hceil hpos
  · rw [hT, hrpow]
    calc n ^ 7 * 2 ^ e * ⌈1 / Shat⌉ ≤ n ^ 7 * 2 ^ e * (2 * (1 / Shat)) :=
        mul_le_mul_of_nonneg_left hceil2 hpos
      _ = 2 * n ^ 7 * ((1 / Shat) * 2 ^ e) := by ring

/-- «Halts every execution», checkable core: `K` trials each consuming at
least one counted step, with the running prefix within the cap, give `K ≤ cap`. -/
theorem o8_trials_le_cap {cap K : ℕ} (S : ℕ → ℕ) (h1 : ∀ i, 1 ≤ S i)
    (hcap : ∑ i ∈ Finset.range K, S i ≤ cap) :
    K ≤ cap := by
  have hKle : K ≤ ∑ i ∈ Finset.range K, S i := by
    calc K = ∑ _i ∈ Finset.range K, 1 := by rw [Finset.sum_const]; simp
      _ ≤ ∑ i ∈ Finset.range K, S i := Finset.sum_le_sum (fun i _ => h1 i)
  exact le_trans hKle hcap

/-- §5.8 bullet 5's «at most 2^{O(n)} draws», explicit form. -/
theorem o8_draws_le {n cap K : ℕ} (hcap1 : 1 ≤ cap) (hK : K ≤ cap) :
    n ^ 2 + 2 + 3 * K ≤ (n ^ 2 + 5) * cap := by
  have h1 : n ^ 2 + 2 + 3 * K ≤ n ^ 2 + 2 + 3 * cap := by omega
  have h2 : n ^ 2 + 2 + 3 * cap ≤ (n ^ 2 + 5) * cap := by
    obtain ⟨cap', rfl⟩ : ∃ c, cap = c + 1 := ⟨cap - 1, by omega⟩
    have hd : 0 ≤ n ^ 2 * cap' := Nat.zero_le _
    have h7 : 0 ≤ 2 * cap' := Nat.zero_le _
    have hsplit : (n ^ 2 + 5) * (cap' + 1)
        = n ^ 2 * cap' + 5 * cap' + (n ^ 2 + 5) := by ring
    omega
  omega

end SubsetSumL25
