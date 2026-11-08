/-
M2 (B3): proofs of the Step 1 / Step 3 / Step 4-(F4) / Step 6 / Cor-A6 spine of
Base's Lemma A5.  Primary source quotes live in `Statements/A5.lean`; this file
is the statement-of-record for everything proved here.

Consumes: `L2_5_prime_collision` (via `pair_collision_le`) — the paper's (F4).
-/
import Mathlib
import SubsetSumL25.Statements.A5
import SubsetSumL25.Proofs.PrimeCollision
import SubsetSumL25.Proofs.CorD

namespace SubsetSumL25

variable {n : ℕ}

/-- `2^{−g_M} = E_V 2^{−d(V)}` — BRIDGE row B3's use of the symbol, as a theorem.
`v ≤ |M|` is the nonemptiness certificate (an empty `expect` is `0`, and
`logb 2 0` would make `gM` junk). -/
theorem two_pow_neg_gM (c : Fin n → ℤ) {M : Finset (Fin n)} {v : ℕ} (hv : v ≤ M.card) :
    (2 : ℝ) ^ (-(gM c M v))
      = (M.powersetCard v).expect (fun V => (2 : ℝ) ^ (-(deficiency c V))) := by
  classical
  have hne : (M.powersetCard v).Nonempty := Finset.powersetCard_nonempty.mpr hv
  have hsum : (0 : ℝ) < ∑ V ∈ M.powersetCard v, (2 : ℝ) ^ (-(deficiency c V)) :=
    Finset.sum_pos (fun V _ => Real.rpow_pos_of_pos (by norm_num) _) hne
  have hcardpos : 0 < (M.powersetCard v).card := Finset.card_pos.mpr hne
  have hcard : (0 : ℝ) < ((M.powersetCard v).card : ℝ) := by exact_mod_cast hcardpos
  have hpos : (0 : ℝ) < (M.powersetCard v).expect (fun V => (2 : ℝ) ^ (-(deficiency c V))) := by
    rw [Finset.expect_eq_sum_div_card]
    positivity
  unfold gM
  rw [neg_neg]
  exact Real.rpow_logb (by norm_num) (by norm_num) hpos

/-- Step 1 arithmetic: `C(m,⌊m/2⌋)2^{−m} ≥ 1/(m+1)`.  Pigeonhole over the
`m+1` layers, each at most the middle one (`Nat.choose_le_middle`). -/
theorem middle_choose_div_two_pow_ge_inv (m : ℕ) :
    1 / ((m : ℝ) + 1) ≤ (Nat.choose m (m / 2) : ℝ) / 2 ^ m := by
  have hsum : (∑ j ∈ Finset.range (m + 1), Nat.choose m j) = 2 ^ m := Nat.sum_range_choose m
  have hle : (∑ j ∈ Finset.range (m + 1), Nat.choose m j)
      ≤ (m + 1) * Nat.choose m (m / 2) := by
    calc (∑ j ∈ Finset.range (m + 1), Nat.choose m j)
        ≤ ∑ _j ∈ Finset.range (m + 1), Nat.choose m (m / 2) :=
          Finset.sum_le_sum fun j _ => Nat.choose_le_middle j m
      _ = (m + 1) * Nat.choose m (m / 2) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id]
  have h2 : 2 ^ m ≤ (m + 1) * Nat.choose m (m / 2) := by rw [← hsum]; exact hle
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have h2m : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have h2' : (2 : ℝ) ^ m ≤ ((m : ℝ) + 1) * (Nat.choose m (m / 2) : ℝ) := by
    have h := h2
    have h' : ((2 ^ m : ℕ) : ℝ) ≤ (((m + 1) * Nat.choose m (m / 2) : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at h'
    exact h'
  rw [div_le_div_iff₀ hm1 h2m]
  nlinarith [h2']

/-- Step 3: deleting the bad part of a `[0,1]`-valued average costs at most the
bad probability. -/
theorem expect_bad_indicator_ge {α : Type*} (s : Finset α) (bad : α → Prop)
    [DecidablePred bad] (f : α → ℝ) (_hf0 : ∀ a ∈ s, 0 ≤ f a)
    (hf1 : ∀ a ∈ s, f a ≤ 1) :
    s.expect f - ((s.filter bad).card : ℝ) / s.card
      ≤ s.expect (fun a => if bad a then 0 else f a) := by
  classical
  rw [Finset.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card, div_sub_div_same]
  by_cases hn : s.card = 0
  · simp [hn]
  have hcard : (0 : ℝ) < (s.card : ℝ) := by
    have : 0 < s.card := Nat.pos_of_ne_zero hn
    exact_mod_cast this
  have hkey : ∑ a ∈ s, (if bad a then 0 else f a)
      = ∑ a ∈ s, f a - ∑ a ∈ s, (if bad a then f a else 0) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by split_ifs <;> simp
  have hbad : ∑ a ∈ s, (if bad a then f a else 0) ≤ ((s.filter bad).card : ℝ) := by
    rw [← Finset.sum_filter]
    calc ∑ a ∈ s.filter bad, f a ≤ ∑ _a ∈ s.filter bad, (1 : ℝ) :=
          Finset.sum_le_sum fun a ha => hf1 a (Finset.mem_filter.mp ha).1
      _ = ((s.filter bad).card : ℝ) := by simp
  rw [hkey, div_le_div_iff₀ hcard hcard]
  nlinarith [hbad]

/-- `badPrimes` is exactly «Pr[P′ ∣ D]» for a uniform `P′`. -/
theorem expect_dvd_eq_badPrimes {L : ℕ} {D : ℤ} :
    (primesInterval L).expect (fun (p : ℕ) => if (↑p : ℤ) ∣ D then (1 : ℝ) else 0)
      = (badPrimes L D : ℝ) / (primesInterval L).card := by
  classical
  have hiff : ∀ p : ℕ, (↑p : ℤ) ∣ D ↔ p ∣ D.natAbs := by
    intro p
    rw [← Int.natAbs_dvd_natAbs (a := (↑p : ℤ)) (b := D), Int.natAbs_natCast]
  have hfil : (primesInterval L).filter (fun (p : ℕ) => (↑p : ℤ) ∣ D)
      = (primesInterval L).filter (fun p => p ∣ D.natAbs) := by
    refine Finset.filter_congr (p := fun p : ℕ => (↑p : ℤ) ∣ D)
      (q := fun p : ℕ => p ∣ D.natAbs) ?_
    intro p _
    exact hiff p
  rw [Finset.expect_eq_sum_div_card, Finset.sum_boole]
  simp only [badPrimes]
  rw [hfil]

/-- Step 4's (F4) instance in expectation form: (F4) — which
`L2_5_prime_collision` proves — transfers verbatim to «Pr[P′ ∣ D] ≤ …». -/
theorem pair_collision_le {L : ℕ} {K : ℝ} {D : ℤ} {B : ℕ}
    (hF4 : (badPrimes L D : ℝ) / (primesInterval L).card
      ≤ K * (B : ℝ) * (L : ℝ) / (2 : ℝ) ^ L) :
    (primesInterval L).expect (fun (p : ℕ) => if (↑p : ℤ) ∣ D then (1 : ℝ) else 0)
      ≤ K * (B : ℝ) * (L : ℝ) / (2 : ℝ) ^ L := by
  rw [expect_dvd_eq_badPrimes]
  exact hF4

/-- Step 6 threshold: with `m, v ≤ N`, `N ≥ 1` and `128K₀ ≤ N²`, the product
bound `2^{−g_M}/(32K₀n²(m+1)(v+1))` already beats `2^{−g_M}n^{−6}`.  This is
the checkable content of «the threshold for n does not depend on I, s, P or M». -/
theorem lem_A5_threshold {G K₀ : ℝ} (hG : 0 < G) (hK₀ : 1 ≤ K₀) {m v N : ℕ}
    (hN1 : 1 ≤ N) (hm : m ≤ N) (hv : v ≤ N) (hN : 128 * K₀ ≤ (N : ℝ) ^ 2) :
    G / (32 * K₀ * ((N : ℝ)) ^ 2 * ((m : ℝ) + 1) * ((v : ℝ) + 1))
      ≥ G / (N : ℝ) ^ 6 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hmR : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hm
  have hvR : (v : ℝ) ≤ (N : ℝ) := by exact_mod_cast hv
  have hm1 : ((m : ℝ) + 1) ≤ 2 * (N : ℝ) := by linarith
  have hv1 : ((v : ℝ) + 1) ≤ 2 * (N : ℝ) := by linarith
  have hden : (0 : ℝ) < 32 * K₀ * (N : ℝ) ^ 2 * ((m : ℝ) + 1) * ((v : ℝ) + 1) := by
    have : (0 : ℝ) < ((m : ℝ) + 1) := by positivity
    have : (0 : ℝ) < ((v : ℝ) + 1) := by positivity
    positivity
  have h6 : (0 : ℝ) < (N : ℝ) ^ 6 := by positivity
  rw [ge_iff_le, div_le_div_iff₀ h6 hden]
  -- `G * (32K₀N²(m+1)(v+1)) ≤ G * N⁶`
  have hmain : 32 * K₀ * (N : ℝ) ^ 2 * ((m : ℝ) + 1) * ((v : ℝ) + 1) ≤ (N : ℝ) ^ 6 := by
    have h1 : ((m : ℝ) + 1) * ((v : ℝ) + 1) ≤ 4 * (N : ℝ) ^ 2 := by
      nlinarith [hm1, hv1, hNpos]
    have h2 : 32 * K₀ * (N : ℝ) ^ 2 * (4 * (N : ℝ) ^ 2) ≤ (N : ℝ) ^ 6 := by
      have hNK : 128 * K₀ ≤ (N : ℝ) ^ 2 := hN
      nlinarith [hNK, hNpos]
    calc 32 * K₀ * (N : ℝ) ^ 2 * ((m : ℝ) + 1) * ((v : ℝ) + 1)
        = 32 * K₀ * (N : ℝ) ^ 2 * (((m : ℝ) + 1) * ((v : ℝ) + 1)) := by ring
      _ ≤ 32 * K₀ * (N : ℝ) ^ 2 * (4 * (N : ℝ) ^ 2) := by
          have hpos : (0 : ℝ) ≤ 32 * K₀ * (N : ℝ) ^ 2 := by positivity
          exact mul_le_mul_of_nonneg_left h1 hpos
      _ ≤ (N : ℝ) ^ 6 := h2
  nlinarith [hmain, hG]

/-- Step 6 product: given the good-hit average `Q ≥ 2^{−g_M}/(2(v+1))`, the
paper's multiplicative chain lands on `2^{−g_M}/(32K₀n²(m+1)(v+1))`. -/
theorem lem_A5_product {G K₀ Q : ℝ} {m v : ℕ} (hG : 0 < G) (hK₀ : 1 ≤ K₀)
    (hQ : G / (2 * ((v : ℝ) + 1)) ≤ Q) :
    G / (32 * K₀ * ((m : ℝ) + 1) * ((v : ℝ) + 1))
      ≤ (1 / ((m : ℝ) + 1)) * (1 / 2) * Q / (8 * K₀) := by
  have hm1 : (0 : ℝ) < ((m : ℝ) + 1) := by positivity
  have hv1 : (0 : ℝ) < ((v : ℝ) + 1) := by positivity
  have hK : (0 : ℝ) < K₀ := by linarith
  have hRHS : (1 / ((m : ℝ) + 1)) * (1 / 2) * Q / (8 * K₀)
      = Q / (16 * K₀ * ((m : ℝ) + 1)) := by
    field_simp
    ring
  rw [hRHS, div_le_div_iff₀ (by positivity) (by positivity)]
  have hGle : G ≤ Q * (2 * ((v : ℝ) + 1)) := by
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ((v : ℝ) + 1))).mp hQ
    linarith [h]
  have hmul := mul_le_mul_of_nonneg_right hGle (by positivity : (0 : ℝ) ≤ 16 * K₀ * ((m : ℝ) + 1))
  nlinarith [hmul, hm1, hv1, hK]

/-- Corollary A6, per alias: `T` independent trials with per-trial hit
probability `p ∈ [0,1]` and `Tp ≥ 1` miss with probability `≤ e^{−1}`
(the paper's `Tp ≥ n` gives `e^{−n}` by the same chain). -/
theorem cor_A6_per_alias {p : ℝ} {T : ℕ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hTp : 1 ≤ (T : ℝ) * p) :
    (1 - p) ^ T ≤ Real.exp (-(1 : ℝ)) := by
  have h0 : (0 : ℝ) ≤ 1 - p := by linarith
  have h1 : 1 - p ≤ Real.exp (-p) := Real.one_sub_le_exp_neg p
  have h2 : (1 - p) ^ T ≤ (Real.exp (-p)) ^ T := pow_le_pow_left₀ h0 h1 T
  have h3 : (Real.exp (-p)) ^ T = Real.exp (-((T : ℝ) * p)) := by
    rw [← Real.exp_nat_mul]
    ring_nf
  have h4 : Real.exp (-((T : ℝ) * p)) ≤ Real.exp (-(1 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    linarith
  linarith [h2, h3.le, h3.ge, h4]

end SubsetSumL25
