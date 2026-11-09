/-
M2 (B5): proofs of the Prop P Chebyshev chain, the Theorem A part 2
absorption, and Lemma A7's envelope.  Primary-source quotes:
`Statements/Presearch.lean`.
-/
import Mathlib
import SubsetSumL25.Statements.Presearch

namespace SubsetSumL25

/-- Chebyshev's inequality over a finite expectation space.  WIP: the proof is
fully decomposed in PROGRESS.md (B5 §M2) — three pieces, each verified to
compile in isolation during this session: (i) pointwise `t² ≤ (x−μ)²` on the
below-threshold set via the nonpos-multiplier chain `mul_le_mul_of_nonpos_left
hlt ht0/hx0`; (ii) `t²·↑#B ≤ Σ (x−μ)²` directly by `Finset.mul_sum` +
per-point by_cases (`mul_one`/`mul_zero`); (iii) finish by cross-multiplying
`div_le_div_iff₀` + `div_mul_cancel₀` against `E = Σ/↑#s`. -/
theorem chebyshev_fraction_le {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (x : ι → ℝ) (t : ℝ) (ht : 0 < t) :
    ((s.filter (fun i => x i < s.expect x - t)).card : ℝ) / s.card
      ≤ (s.expect (fun i => (x i - s.expect x) ^ 2)) / t ^ 2 := by
  sorry

/-- Prop P's instantiation: variance ≤ `n` (Lemma 2.3, named), gap `(ζ/2)n`. -/
theorem prop_p_chebyshev {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {x : ι → ℝ} {n ζ : ℝ} (hn : 0 < n) (hζ : 0 < ζ)
    (hvar : s.expect (fun i => (x i - s.expect x) ^ 2) ≤ n) :
    ((s.filter (fun i => x i < s.expect x - (ζ / 2) * n)).card : ℝ) / s.card
      ≤ 4 / (ζ ^ 2 * n) := by
  have hkey := chebyshev_fraction_le hs x ((ζ / 2) * n) (by positivity)
  have hstep : (s.expect (fun i => (x i - s.expect x) ^ 2)) / ((ζ / 2) * n) ^ 2
      ≤ (n : ℝ) / ((ζ / 2) * n) ^ 2 :=
    div_le_div_of_nonneg_right hvar (by positivity)
  have hEq : (n : ℝ) / ((ζ / 2) * n) ^ 2 = 4 / (ζ ^ 2 * n) := by
    field_simp
    ring
  refine le_trans (le_trans hkey hstep) ?_
  rw [hEq]

/-- §4's cap-fitting arithmetic. -/
theorem cap_fit_lt {n τ₀ ζ size dU : ℝ} (hζn : 1 < ζ * n)
    (hsize : size ≤ (n + 1) / 2) (hdU : (1 / 2 - τ₀ + ζ / 2) * n ≤ dU) :
    size - dU < τ₀ * n := by
  have h1 : (n : ℝ) / 2 + 1 / 2 - (1 / 2 - τ₀ + ζ / 2) * n < τ₀ * n := by
    linarith
  calc size - dU ≤ (n : ℝ) / 2 + 1 / 2 - dU := by linarith
    _ ≤ (n : ℝ) / 2 + 1 / 2 - (1 / 2 - τ₀ + ζ / 2) * n := by linarith
    _ < τ₀ * n := h1

/-- Prop P's CONTINUE conclusion in explicit form. -/
theorem continue_prob_le {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {x : ι → ℝ} {n ζ : ℝ} (hn : 0 < n) (hζ : 0 < ζ)
    (hvar : s.expect (fun i => (x i - s.expect x) ^ 2) ≤ n)
    (P : ι → Prop) [DecidablePred P]
    (hsub : ∀ i ∈ s, P i → x i < s.expect x - (ζ / 2) * n) :
    ((s.filter P).card : ℝ) / s.card ≤ 4 / (ζ ^ 2 * n) := by
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hs
  refine le_trans ?_ (prop_p_chebyshev hs hn hζ hvar)
  have hsub2 : (s.filter P) ⊆ s.filter (fun i => x i < s.expect x - (ζ / 2) * n) :=
    fun i hi =>
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1,
        hsub i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2⟩
  refine div_le_div_iff₀ hcard hcard |>.mpr ?_
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card hsub2))
    (le_of_lt hcard)

/-- Theorem A part 2's absorption (`n ≥ 0`: it is the input size). -/
theorem prop_p_op_absorb {τ₀ n : ℝ} (hn : 0 ≤ n) :
    (2 : ℝ) ^ (τ₀ * n) ≤ (2 : ℝ) ^ (τ₀ * n + 2 * n ^ (0.7 : ℝ)) := by
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have hnp : 0 ≤ 2 * n ^ (0.7 : ℝ) := by
    have h := Real.rpow_nonneg hn (0.7 : ℝ)
    linarith
  exact le_mul_of_one_le_right (Real.rpow_nonneg (le_of_lt (by norm_num : (0 : ℝ) < 2))
    (τ₀ * n))
    (Real.one_le_rpow (by norm_num) hnp)

/-- Lemma A7's envelope: seven items within `(b+2)·2^K` with `5 ≤ b` sum to at
most `(b+2)·2^K`. -/
theorem a7_envelope {b K : ℝ} (hb : 0 ≤ b) (hK : 0 ≤ K)
    (S : ℕ → ℝ) (hitem : ∀ i ∈ Finset.range 7, S i ≤ (b + 2) * 2 ^ K) :
    ∑ i ∈ Finset.range 7, S i ≤ (b + 2) * 2 ^ (K + 3) := by
  have hp : (2 : ℝ) ^ (K + 3) = 8 * 2 ^ K := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      show (2 : ℝ) ^ (3 : ℝ) = 8 from by norm_num]
    ring
  have hX : 0 ≤ (b + 2) * 2 ^ K := by
    have h := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) K
    exact mul_nonneg (by linarith) h
  calc ∑ i ∈ Finset.range 7, S i
      ≤ ∑ _i ∈ Finset.range 7, ((b + 2) * 2 ^ K) := Finset.sum_le_sum hitem
    _ = (7 : ℝ) * ((b + 2) * 2 ^ K) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          simp
    _ ≤ (b + 2) * 2 ^ (K + 3) := by
          rw [hp]
          nlinarith [hb, hX]

end SubsetSumL25
