/-
M5CorA6 (DS): the two compilation-heavy pieces of Corollary A6, split out of
`Proofs/M5.lean` so each module compiles inside the host's lean-kill window
(see wound 2125609440).  Same milestone (DS-M5), same statements-of-record;
`Proofs/M5.lean` documents the ladder position.
-/
import Mathlib
import SubsetSumL25.Proofs.M5

namespace SubsetSumL25

theorem cor_A6_coverageTp {δ gM Ŝ e_n p : ℝ} (hS : 0 < Ŝ)
    (htail : Ŝ ≤ (2:ℝ) ^ (2 * δ) * (2:ℝ) ^ (-gM))
    (hE : (2:ℝ) ^ (2 * δ) ≤ (2:ℝ) ^ e_n)
    (n : ℕ) (T : ℕ) (hT : (T:ℝ) = (n:ℝ) ^ 7 * (2:ℝ) ^ e_n * ⌈1 / Ŝ⌉)
    (hn1 : 1 ≤ n)
    (hp : (2:ℝ) ^ (-gM) / (n:ℝ) ^ 6 ≤ p) :
    (n:ℝ) ≤ (T:ℝ) * p := by
  have hcnt := @trial_count_ge n δ gM Ŝ e_n hS htail hE T hT
  have h2pos : ∀ r : ℝ, 0 < (2:ℝ)^r := fun r => Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) r
  have hnR : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
  have hn0 : (0:ℝ) < (n:ℝ) := by linarith
  -- n⁷·2^{gM}·(2^{−gM}/n⁶) = n
  have hL : (n:ℝ) ^ 7 * (2:ℝ) ^ gM * ((2:ℝ) ^ (-gM) / (n:ℝ) ^ 6) = (n:ℝ) := by
    have hinv : (2:ℝ) ^ gM * (2:ℝ) ^ (-gM) = 1 := by
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2) gM, mul_inv_cancel₀ (h2pos gM).ne']
    have h7 : (n:ℝ) ^ 7 = (n:ℝ) ^ 6 * (n:ℝ) := by rw [← pow_succ]
    have hne : (n:ℝ) ^ 6 ≠ 0 := ne_of_gt (pow_pos hn0 6)
    calc (n:ℝ) ^ 7 * (2:ℝ) ^ gM * ((2:ℝ) ^ (-gM) / (n:ℝ) ^ 6)
        = (n:ℝ) ^ 7 * (2:ℝ) ^ gM * (2:ℝ) ^ (-gM) / (n:ℝ) ^ 6 :=
          (mul_div_assoc' ((n:ℝ) ^ 7 * (2:ℝ) ^ gM) ((2:ℝ) ^ (-gM)) ((n:ℝ) ^ 6))
      _ = (n:ℝ) ^ 7 * 1 / (n:ℝ) ^ 6 := by rw [mul_assoc, hinv]
      _ = (n:ℝ) ^ 7 / (n:ℝ) ^ 6 := by rw [mul_one]
      _ = (n:ℝ) := by rw [h7]; exact mul_div_cancel_left₀ _ hne
  have hmul := mul_le_mul hcnt hp (by positivity) (by positivity)
  rw [hL] at hmul
  exact hmul

/-- Corollary A6's union bound: if every alias in a finite family is missed
with probability ≤ `e^{−n}`, the family's total miss probability is at most
`#A·e^{−n}`. -/

theorem cor_A6_union_le {α : Type*} (A : Finset α) (miss : α → ℝ) {n : ℕ}
    (h : ∀ a ∈ A, miss a ≤ Real.exp (-((n:ℝ)))) :
    ∑ a ∈ A, miss a ≤ (A.card : ℝ) * Real.exp (-((n:ℝ))) := by
  calc ∑ a ∈ A, miss a ≤ ∑ _a ∈ A, Real.exp (-((n:ℝ))) := Finset.sum_le_sum h
    _ = (A.card : ℝ) * Real.exp (-((n:ℝ))) := by
        rw [Finset.sum_const, nsmul_eq_mul]

set_option maxHeartbeats 1200000 in
/-- Corollary A6's o(1): the paper's «(nN₀+1)2^n e^{−n} = o(1)» — the count
of (target, subset) pairs, with the exec-side constant `N₀` (the (F1)
dictionary constant, ≥ 0), times `2^n·e^{−n} = (2/e)^n`.  The polynomial
factor is absorbed by `summable_pow_mul_geometric_of_norm_lt_one` at `2/e`,
using `2 < e`. -/
theorem cor_A6_union_o1 {N₀ : ℝ} (hN₀ : 0 ≤ N₀) :
    Filter.Tendsto (fun n : ℕ => ((n:ℝ) * N₀ + 1) * (2:ℝ) ^ n * Real.exp (-((n:ℝ))))
      Filter.atTop (nhds 0) := by
  classical
  set r : ℝ := (2:ℝ) / Real.exp 1 with hrdef
  have hr0 : (0:ℝ) < r := by
    rw [hrdef]; exact div_pos (by norm_num) (Real.exp_pos 1)
  have hr1 : r < 1 := by
    rw [hrdef, div_lt_one (Real.exp_pos 1)]
    exact Real.exp_one_gt_two
  have hrnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [abs_of_pos hr0]
  have hrpow : ∀ n : ℕ, (2:ℝ) ^ n * Real.exp (-((n:ℝ))) = r ^ n := by
    intro n
    have hexpo : (-(n:ℝ)) = (n:ℕ) * (-1:ℝ) := by ring
    rw [hrdef, hexpo, Real.exp_nat_mul, ← mul_pow, div_eq_mul_inv, ← Real.exp_neg]
  have hpos : ∀ n : ℕ, (0:ℝ) ≤ ((n:ℝ) * N₀ + 1) * (2:ℝ) ^ n * Real.exp (-((n:ℝ))) := by
    intro n
    have hx : (0:ℝ) ≤ 2 := by norm_num
    have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have h1 : (0:ℝ) ≤ (n:ℝ) * N₀ + 1 := by nlinarith [hN₀, hn0]
    have h2 : (0:ℝ) ≤ (2:ℝ) ^ n * Real.exp (-((n:ℝ))) := by positivity
    nlinarith [h1, h2]
  have hbound : ∀ n : ℕ, ((n:ℝ) * N₀ + 1) * (2:ℝ) ^ n * Real.exp (-((n:ℝ)))
      ≤ (N₀ + 1) * (((n:ℝ) + 1) * r ^ n) := by
    intro n
    have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have h1 : (0:ℝ) ≤ (n:ℝ) * N₀ + 1 := by nlinarith [hN₀, hn0]
    have hle : (n:ℝ) * N₀ + 1 ≤ (N₀ + 1) * ((n:ℝ) + 1) := by
      nlinarith [hn0]
    have hrpow' : (2:ℝ) ^ n * Real.exp (-((n:ℝ))) = r ^ n := hrpow n
    have hrnn : (0:ℝ) ≤ r ^ n := le_of_lt (by
      rw [← hrpow']
      exact mul_pos (pow_pos (by norm_num : (0:ℝ) < 2) n) (Real.exp_pos _))
    have hstep : ((n:ℝ) * N₀ + 1) * r ^ n
        ≤ ((N₀ + 1) * ((n:ℝ) + 1)) * r ^ n :=
      mul_le_mul_of_nonneg_right hle hrnn
    calc ((n:ℝ) * N₀ + 1) * (2:ℝ) ^ n * Real.exp (-((n:ℝ)))
        = ((n:ℝ) * N₀ + 1) * r ^ n := by rw [mul_assoc, hrpow']
      _ ≤ ((N₀ + 1) * ((n:ℝ) + 1)) * r ^ n := hstep
      _ = (N₀ + 1) * (((n:ℝ) + 1) * r ^ n) := mul_assoc (N₀ + 1) ((n:ℝ) + 1) (r ^ n)
  have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hrnorm
  have h0 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0 hrnorm
  have hshift : Summable (fun n : ℕ => ((n:ℝ) + 1) * r ^ n) := by
    have hadd : Summable fun n : ℕ => (n:ℝ) * r ^ n + r ^ n :=
      (h1.congr fun b => by simp).add (h0.congr fun b => by simp)
    have heq : (fun n : ℕ => ((n:ℝ) + 1) * r ^ n)
        = fun n : ℕ => (n:ℝ) * r ^ n + r ^ n := by
      funext n; ring
    rw [heq]
    exact hadd
  have hconst : Summable (fun n : ℕ => (N₀ + 1) * (((n:ℝ) + 1) * r ^ n)) := by
    have := hshift.const_smul (N₀ + 1)
    simpa [smul_eq_mul] using this
  exact squeeze_zero hpos hbound hconst.tendsto_atTop_zero

end SubsetSumL25
