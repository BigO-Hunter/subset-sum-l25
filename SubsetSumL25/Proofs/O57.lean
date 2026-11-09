/-
M2 (O5+O7): proofs of the tail-rung cores.  Primary-source quotes live in
`Statements/O57.lean`; this file is the statement-of-record for everything
proved here.

Consumers wired per the handoff (not re-proved): B3's `cor_A6_per_alias`
for O7's completeness union bound; the O8 cap/budget proof patterns.
-/
import Mathlib
import SubsetSumL25.Statements.O57
import SubsetSumL25.Proofs.A5

namespace SubsetSumL25

/-- O5's every-run operation cap. -/
noncomputable def o5Cap (τ ε n : ℝ) : ℝ :=
  2 ^ (⌈(τ + 20 * ε) * n⌉ + ⌈Real.sqrt n⌉)

/-- O7's every-run records cap. -/
noncomputable def o7Cap (τ n : ℝ) : ℕ := 2 ^ (⌈τ * n⌉.toNat)

/-- Thm 4.1's budget absorption. -/
theorem o5_cap_absorb (τ ε n : ℝ) :
    o5Cap τ ε n ≤ (2 : ℝ) ^ ((τ + 20 * ε) * n + 2 * Real.sqrt n + 2) := by
  -- NB: the ceilings are ℤ-valued at this pin (the O8 discovery) — the cap's
  -- 2^(…) is integer-exponent zpow; bridge with Real.rpow_intCast.
  have h1 : ((⌈(τ + 20 * ε) * n⌉ : ℤ) : ℝ)
      ≤ (τ + 20 * ε) * n + 1 := by
    linarith [Int.ceil_lt_add_one ((τ + 20 * ε) * n)]
  have h2 : ((⌈Real.sqrt n⌉ : ℤ) : ℝ) ≤ Real.sqrt n + 1 := by
    linarith [Int.ceil_lt_add_one (Real.sqrt n)]
  have hexp : ((⌈(τ + 20 * ε) * n⌉ + ⌈Real.sqrt n⌉ : ℤ) : ℝ)
      ≤ (τ + 20 * ε) * n + 2 * Real.sqrt n + 2 := by
    rw [Int.cast_add]
    linarith [Real.sqrt_nonneg n]
  rw [o5Cap, ← Real.rpow_intCast]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp

/-- Thm 4.1's per-execution op bound. -/
theorem o5_time_bound {τ ε n P : ℝ} (hP : 0 ≤ P) (S : ℕ → ℝ)
    (hcat : ∀ i ∈ Finset.range 10, S i ≤ o5Cap τ ε n * P) :
    ∑ i ∈ Finset.range 10, S i
      ≤ (16 : ℝ) * P * 2 ^ ((τ + 20 * ε) * n + 2 * Real.sqrt n + 2) := by
  have h02 : (0 : ℝ) ≤ 2 := by norm_num
  have hcap0 : 0 ≤ o5Cap τ ε n := by
    rw [o5Cap, ← Real.rpow_intCast]
    exact Real.rpow_nonneg h02 _
  have h1016 : (10 : ℝ) ≤ 16 := by norm_num
  have h16P : 0 ≤ (16 : ℝ) * P := by linarith
  have hstep1 : ∑ i ∈ Finset.range 10, S i ≤ (10 : ℝ) * (o5Cap τ ε n * P) := by
    refine le_trans (Finset.sum_le_sum hcat) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    simp
  have hstep2 : (10 : ℝ) * (o5Cap τ ε n * P)
      ≤ (16 : ℝ) * P * 2 ^ ((τ + 20 * ε) * n + 2 * Real.sqrt n + 2) := by
    have hcp : 0 ≤ o5Cap τ ε n * P := mul_nonneg hcap0 hP
    calc (10 : ℝ) * (o5Cap τ ε n * P) ≤ 16 * (o5Cap τ ε n * P) :=
        mul_le_mul_of_nonneg_right h1016 hcp
      _ = 16 * P * o5Cap τ ε n := by ring
      _ ≤ 16 * P * 2 ^ ((τ + 20 * ε) * n + 2 * Real.sqrt n + 2) :=
          mul_le_mul_of_nonneg_left (o5_cap_absorb τ ε n) h16P
  exact le_trans hstep1 hstep2

/-- Thm 4.1's accuracy guarantee, MSE ≤ 1/8. -/
theorem o5_mse_le {ι : Type*} {Ω : Finset ι} (hΩ : Ω.Nonempty) {Xbar : ι → ℝ}
    {V μ : ℝ} (hμ : 0 ≤ μ) {N : ℕ} (hN : 0 < N)
    (hMSE : Ω.expect (fun ω => (Xbar ω - V) ^ 2) ≤ μ / N) (hμ8 : 8 * μ ≤ (N:ℝ)) :
    Ω.expect (fun ω => (Xbar ω - V) ^ 2) ≤ 1 / 8 := by
  refine le_trans hMSE ?_
  rcases eq_or_lt_of_le hμ with hμ0 | hμpos
  · rw [← hμ0, zero_div]
    norm_num
  · exact (div_le_div_iff₀ (Nat.cast_pos.mpr hN)
      (by norm_num : (0:ℝ) < 8)).mpr (by linarith)

/-- Thm 5.1's every-run records bound, checkable core. -/
theorem o7_records_le_cap {τ n K : ℕ} (S : ℕ → ℕ) (h1 : ∀ i, 1 ≤ S i)
    (hcap : ∑ i ∈ Finset.range K, S i ≤ o7Cap τ n) :
    K ≤ o7Cap τ n := by
  have hKle : K ≤ ∑ i ∈ Finset.range K, S i := by
    calc K = ∑ _i ∈ Finset.range K, 1 := by rw [Finset.sum_const]; simp
      _ ≤ ∑ i ∈ Finset.range K, S i := Finset.sum_le_sum (fun i _ => h1 i)
  exact le_trans hKle hcap

/-- Thm 5.1's completeness union bound, consuming B3's
`cor_A6_per_alias`. -/
theorem o7_union_le {ι : Type*} {A : Finset ι} {m : ι → ℝ} {p : ℝ} {T : ℕ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hTp : 1 ≤ (T:ℝ) * p)
    (hm : ∀ a ∈ A, m a ≤ (1 - p) ^ T) :
    (∑ a ∈ A, m a) ≤ A.card * Real.exp (-(1:ℝ)) := by
  refine le_trans (Finset.sum_le_sum hm) ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_left (cor_A6_per_alias hp0 hp1 hTp) (by positivity)

end SubsetSumL25
