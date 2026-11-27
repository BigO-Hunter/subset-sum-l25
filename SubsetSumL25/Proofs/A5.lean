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

/-- `2^{−g_M} = E_V 2^{−d(V)}` — rung B3's use of the symbol, as a theorem.
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

/-- Step 1 identity: conditioning a uniform subset on `|F| = σ` gives the uniform
`σ`-subset average, scaled by `C(m,σ)2^{−m}`.  Holds for every `σ` (both sides
are `0` when `σ > |M|`), which is why no size hypothesis is needed. -/
theorem powerset_expect_ite_card (M : Finset (Fin n)) {σ : ℕ} (g : Finset (Fin n) → ℝ) :
    ((Nat.choose M.card σ : ℝ) / 2 ^ M.card) * (M.powersetCard σ).expect g
      = (M.powerset).expect (fun F => if F.card = σ then g F else 0) := by
  classical
  rw [Finset.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card, Finset.card_powerset,
    Finset.card_powersetCard]
  by_cases hσ : σ ≤ M.card
  · have hC : (0 : ℝ) < (Nat.choose M.card σ : ℝ) := by exact_mod_cast Nat.choose_pos hσ
    have hsum : ∑ F ∈ M.powerset, (if F.card = σ then g F else 0)
        = ∑ S ∈ M.powersetCard σ, g S := by
      rw [Finset.powersetCard_eq_filter, ← Finset.sum_filter]
    rw [hsum]
    field_simp
    push_cast
    ring
  · have hlt : M.card < σ := by omega
    have hC0 : Nat.choose M.card σ = 0 := Nat.choose_eq_zero_of_lt hlt
    have hP : M.powersetCard σ = ∅ := by
      rw [Finset.powersetCard_eq_empty]
      omega
    have hfil : M.powerset.filter (fun F => F.card = σ) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro F hF
      rw [Finset.mem_powerset] at hF
      have := Finset.card_le_card hF
      omega
    rw [← Finset.sum_filter, hfil]
    simp [hC0, hP]

/-- Step 3 assembly — the rung's Corollary D consumer: Corollary D's bound
(`hcorD`), the good sets dominating `a_k` (`hgood`, Step 2) and the A4 bad
fraction (`hbad`, `hδ`) give the good-hit average at half strength,
`E_S[1_good B_S/C(σ,k)] ≥ 2^{−g_M}/(2(v+1))`. -/
theorem good_hit_expect_ge (c : Fin n → ℤ) {M : Finset (Fin n)} {k σ v δn : ℕ}
    (B : Finset (Fin n) → ℕ) (good : Finset (Fin n) → Prop) [DecidablePred good]
    (hσ : σ ≤ M.card)
    (hCpos : (0 : ℝ) < (Nat.choose σ k : ℝ))
    (hBle : ∀ S, B S ≤ Nat.choose σ k)
    (hgood : ∀ S ∈ M.powersetCard σ, good S →
      layerDensity c S k ≤ (B S : ℝ) / (Nat.choose σ k : ℝ))
    (hcorD : (2 : ℝ) ^ (-(gM c M v)) / ((v : ℝ) + 1)
      ≤ (M.powersetCard σ).expect (fun S => layerDensity c S k))
    (hδ : (2 : ℝ) ^ (-(δn : ℝ)) ≤ (2 : ℝ) ^ (-(gM c M v)) / (2 * ((v : ℝ) + 1)))
    (hbad : ((M.powersetCard σ).filter (fun S => ¬ good S)).card
      ≤ (2 : ℝ) ^ (-(δn : ℝ)) * (M.powersetCard σ).card) :
    (2 : ℝ) ^ (-(gM c M v)) / (2 * ((v : ℝ) + 1))
      ≤ (M.powersetCard σ).expect
          (fun S => if good S then (B S : ℝ) / (Nat.choose σ k : ℝ) else 0) := by
  classical
  have hne : (M.powersetCard σ).Nonempty := Finset.powersetCard_nonempty.mpr hσ
  have hcardpos : (0 : ℝ) < ((M.powersetCard σ).card : ℝ) := by
    have : 0 < (M.powersetCard σ).card := Finset.card_pos.mpr hne
    exact_mod_cast this
  -- `0 ≤ a_k ≤ 1`
  have hak0 : ∀ S ∈ M.powersetCard σ, 0 ≤ layerDensity c S k := by
    intro S _
    unfold layerDensity
    positivity
  have hak1 : ∀ S ∈ M.powersetCard σ, layerDensity c S k ≤ 1 := by
    intro S hS
    have hSc : S.card = σ := (Finset.mem_powersetCard.mp hS).2
    unfold layerDensity
    rw [hSc, div_le_one hCpos]
    have h1 : (layerSupport c S k).card ≤ Nat.choose σ k := by
      calc (layerSupport c S k).card ≤ (S.powersetCard k).card := Finset.card_image_le
        _ = Nat.choose S.card k := Finset.card_powersetCard k S
        _ = Nat.choose σ k := by rw [hSc]
    exact_mod_cast h1
  -- step C first: the bad fraction is at most `2^{−δn}`
  have hbadR : ((M.powersetCard σ).filter (fun S => ¬ good S)).card
      / ((M.powersetCard σ).card : ℝ) ≤ (2 : ℝ) ^ (-(δn : ℝ)) := by
    calc ((M.powersetCard σ).filter (fun S => ¬ good S)).card
          / ((M.powersetCard σ).card : ℝ)
        ≤ ((2 : ℝ) ^ (-(δn : ℝ)) * ((M.powersetCard σ).card : ℝ))
            / ((M.powersetCard σ).card : ℝ) := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hcardpos)
          exact_mod_cast hbad
      _ = (2 : ℝ) ^ (-(δn : ℝ)) := by field_simp
  -- step A: deleting the bad sets costs at most their probability
  have hA0 := expect_bad_indicator_ge (M.powersetCard σ) (fun S => ¬ good S)
    (fun S => layerDensity c S k) hak0 hak1
  have hAeq : (M.powersetCard σ).expect (fun S => if ¬ good S then 0 else layerDensity c S k)
      = (M.powersetCard σ).expect (fun S => if good S then layerDensity c S k else 0) := by
    refine Finset.expect_congr rfl ?_
    intro S
    by_cases hg : good S <;> simp [hg]
  have hA : (M.powersetCard σ).expect (fun S => layerDensity c S k) - (2 : ℝ) ^ (-(δn : ℝ))
      ≤ (M.powersetCard σ).expect (fun S => if good S then layerDensity c S k else 0) := by
    rw [← hAeq]
    linarith [hA0, hbadR]
  -- step B: on good sets, `a_k ≤ B/C`
  have hB : (M.powersetCard σ).expect (fun S => if good S then layerDensity c S k else 0)
      ≤ (M.powersetCard σ).expect
          (fun S => if good S then (B S : ℝ) / (Nat.choose σ k : ℝ) else 0) := by
    refine Finset.expect_le_expect fun S hS => ?_
    by_cases hg : good S
    · rw [if_pos hg, if_pos hg]; exact hgood S hS hg
    · rw [if_neg hg, if_neg hg]
  have hchain : (2 : ℝ) ^ (-(gM c M v)) / ((v : ℝ) + 1) - (2 : ℝ) ^ (-(δn : ℝ))
      ≤ (M.powersetCard σ).expect
          (fun S => if good S then (B S : ℝ) / (Nat.choose σ k : ℝ) else 0) := by
    have h1 : (2 : ℝ) ^ (-(gM c M v)) / ((v : ℝ) + 1) - (2 : ℝ) ^ (-(δn : ℝ))
        ≤ (M.powersetCard σ).expect (fun S => layerDensity c S k) - (2 : ℝ) ^ (-(δn : ℝ)) := by
      linarith [hcorD]
    exact le_trans h1 (le_trans hA hB)
  have hv1 : (0 : ℝ) < (v : ℝ) + 1 := by positivity
  have h2 : (2 : ℝ) ^ (-(gM c M v)) / ((v : ℝ) + 1)
        - (2 : ℝ) ^ (-(gM c M v)) / (2 * ((v : ℝ) + 1))
      = (2 : ℝ) ^ (-(gM c M v)) / (2 * ((v : ℝ) + 1)) := by
    field_simp
    ring
  have hfin : (2 : ℝ) ^ (-(gM c M v)) / (2 * ((v : ℝ) + 1))
      ≤ (2 : ℝ) ^ (-(gM c M v)) / ((v : ℝ) + 1) - (2 : ℝ) ^ (-(δn : ℝ)) := by
    linarith [hδ, h2]
  exact le_trans hfin hchain

/-- Step 4 end: the residue bijection behind «a uniform j′ hits an occupied
residue with probability `#occupied/P′`». -/
theorem hit_prob_eq_occupied (W : Finset ℤ) {p : ℕ} (hp : 0 < p) :
    (Finset.range p).expect
        (fun (j : ℕ) => if ∃ x ∈ W, x % (p : ℤ) = (↑j : ℤ) then (1 : ℝ) else 0)
      = ((W.image (fun x => x % (p : ℤ))).card : ℝ) / p := by
  classical
  have hpz : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp
  have hpne : (p : ℤ) ≠ 0 := ne_of_gt hpz
  have hcard : ((Finset.range p).filter
      (fun (j : ℕ) => ∃ x ∈ W, x % (p : ℤ) = (↑j : ℤ))).card
      = (W.image (fun x => x % (p : ℤ))).card := by
    refine Finset.card_bij (fun (j : ℕ) (_ : j ∈ _) => (j : ℤ)) ?_ ?_ ?_
    · intro j hj
      obtain ⟨-, x, hx, hxj⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_image.mpr ⟨x, hx, hxj⟩
    · intro j₁ _ j₂ _ heq
      exact_mod_cast heq
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      have h1 : 0 ≤ x % (p : ℤ) := Int.emod_nonneg x hpne
      have h2 : x % (p : ℤ) < (p : ℤ) := Int.emod_lt_of_pos x hpz
      refine ⟨(x % (p : ℤ)).toNat, ?_, Int.toNat_of_nonneg h1⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr (by omega), x, hx, (Int.toNat_of_nonneg h1).symm⟩
  rw [Finset.expect_eq_sum_div_card, Finset.sum_boole, hcard, Finset.card_range]

/-- Step 4 occupancy: colliding pairs are the only thing that reduces the number
of occupied residue classes (`#occupied ≥ |W| − #collisions`), via one chosen
representative per class. -/
theorem occupied_ge_card_sub_collisions (W : Finset ℤ) {p : ℕ} (hp : 0 < p) :
    W.card ≤ (W.image (fun x => x % (p : ℤ))).card + collisionPairs W p := by
  classical
  have hpz : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp
  set f : ℤ → ℤ := fun x => x % (p : ℤ) with hf
  set fib : ℤ → Finset ℤ := fun y => W.filter (fun x => f x = y) with hfib
  have hfib_ne : ∀ y ∈ W.image f, (fib y).Nonempty := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨x, by rw [hfib]; exact Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
  set r : ℤ → ℤ := fun y => if h : (fib y).Nonempty then h.choose else 0 with hr
  have hr_spec : ∀ y ∈ W.image f, r y ∈ W ∧ f (r y) = y := by
    intro y hy
    have h := hfib_ne y hy
    have h1 : r y = h.choose := by rw [hr]; exact dif_pos h
    rw [h1]
    have h2 : h.choose ∈ W.filter (fun x => f x = y) := h.choose_spec
    exact Finset.mem_filter.mp h2
  have hr_mem : ∀ y ∈ W.image f, r y ∈ W := fun y hy => (hr_spec y hy).1
  have hr_res : ∀ y ∈ W.image f, f (r y) = y := fun y hy => (hr_spec y hy).2
  set T : Finset ℤ := W.filter (fun x => x ≠ r (f x)) with hT
  -- each non-representative collides with its class representative
  have h2 : T.card ≤ collisionPairs W p := by
    have hmaps : Set.MapsTo (fun x => (x, r (f x))) ↑T
        ↑((W.product W).filter (fun q => q.1 ≠ q.2 ∧ (p : ℤ) ∣ (q.1 - q.2))) := by
      intro x hx
      obtain ⟨hxW, hxne⟩ := Finset.mem_filter.mp hx
      have hfx : f x ∈ W.image f := Finset.mem_image.mpr ⟨x, hxW, rfl⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hxW, ?_⟩, hxne, ?_⟩
      · exact hr_mem _ (Finset.mem_image.mpr ⟨x, hxW, rfl⟩)
      · have heq : f x = f (r (f x)) := (hr_res _ (Finset.mem_image.mpr ⟨x, hxW, rfl⟩)).symm
        exact Int.dvd_iff_emod_eq_zero.mpr (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp heq)
    have hinj : Set.InjOn (fun x => (x, r (f x))) ↑T := by
      intro x _ x' _ h
      exact congrArg Prod.fst h
    exact Finset.card_le_card_of_injOn _ hmaps hinj
  -- the representatives are exactly one per occupied class
  have h1 : W.card = T.card + (W.image f).card := by
    have hsplit := Finset.card_filter_add_card_filter_not (s := W)
      (p := fun x => x = r (f x))
    have hcomp : W.filter (fun x => ¬ (x = r (f x))) = T := by
      rw [hT]
    have hS : (W.filter (fun x => x = r (f x))).card = (W.image f).card := by
      refine Finset.card_bij (fun (x : ℤ) (_ : x ∈ _) => f x) ?_ ?_ ?_
      · intro x hx
        exact Finset.mem_image.mpr ⟨x, (Finset.mem_filter.mp hx).1, rfl⟩
      · intro x₁ hx₁ x₂ hx₂ heq
        have hx1 : x₁ = r (f x₁) := (Finset.mem_filter.mp hx₁).2
        have hx2 : x₂ = r (f x₂) := (Finset.mem_filter.mp hx₂).2
        rw [hx1, hx2, heq]
      · intro y hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        have hfx : f x ∈ W.image f := Finset.mem_image.mpr ⟨x, hx, rfl⟩
        refine ⟨r (f x), ?_, hr_res (f x) hfx⟩
        rw [Finset.mem_filter]
        exact ⟨hr_mem (f x) hfx, by rw [hr_res (f x) hfx]⟩
    rw [hcomp] at hsplit
    omega
  omega

/-- Step 4 second moment: `E_{P′} Σ_y z_y² ≤ |W| + K₀n²|W|²2^{−γm}`, in the
collision form — each of the at most `|W|²` ordered pairs contributes at most the
(F4) per-pair bound.  Needs `0 ≤ K₀` (the paper has `K₀ ≥ 1`) so that the
diagonal pairs' zero contribution is bounded. -/
theorem collisionPairs_expect_le (W : Finset ℤ) {L : ℕ} {K₀ : ℝ} (hK₀ : 0 ≤ K₀)
    (hpair : ∀ x ∈ W, ∀ x' ∈ W, x ≠ x' →
      (primesInterval L).expect (fun (p : ℕ) => if (↑p : ℤ) ∣ (x - x') then (1 : ℝ) else 0)
        ≤ K₀ / (2 : ℝ) ^ L) :
    (primesInterval L).expect (fun p => (collisionPairs W p : ℝ))
      ≤ (W.card : ℝ) ^ 2 * (K₀ / (2 : ℝ) ^ L) := by
  classical
  set P : Finset ℕ := primesInterval L with hP
  have hK : (0 : ℝ) ≤ K₀ / (2 : ℝ) ^ L := by positivity
  -- `collisionPairs` as a sum of indicators over the ordered pairs
  have hcp : ∀ p : ℕ, (collisionPairs W p : ℝ)
      = ∑ q ∈ W.product W,
          (if q.1 ≠ q.2 ∧ (↑p : ℤ) ∣ (q.1 - q.2) then (1 : ℝ) else 0) := by
    intro p
    have h := Finset.card_filter
      (fun q : ℤ × ℤ => q.1 ≠ q.2 ∧ (↑p : ℤ) ∣ (q.1 - q.2)) (W.product W)
    rw [collisionPairs, h]
    push_cast
    rfl
  -- per-pair expectation bound
  have hterm : ∀ q ∈ W.product W,
      P.expect (fun p => (if q.1 ≠ q.2 ∧ (↑p : ℤ) ∣ (q.1 - q.2) then (1 : ℝ) else 0))
        ≤ K₀ / (2 : ℝ) ^ L := by
    intro q hq
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hq
    by_cases hne : q.1 = q.2
    · have hzero : (fun p : ℕ => (if q.1 ≠ q.2 ∧ (↑p : ℤ) ∣ (q.1 - q.2) then (1 : ℝ) else 0))
          = fun _ => 0 := by
        funext p
        rw [if_neg]
        exact fun h => h.1 hne
      rw [hzero, Finset.expect_eq_sum_div_card]
      simp only [Finset.sum_const_zero, zero_div]
      exact hK
    · have heq : ∀ p : ℕ, (if q.1 ≠ q.2 ∧ (↑p : ℤ) ∣ (q.1 - q.2) then (1 : ℝ) else 0)
          = (if (↑p : ℤ) ∣ (q.1 - q.2) then (1 : ℝ) else 0) := by
        intro p
        by_cases hX : (↑p : ℤ) ∣ (q.1 - q.2) <;> simp [hne, hX]
      simp only [heq]
      exact hpair q.1 h1 q.2 h2 hne
  -- inner sum bound
  have hinner : ∀ q ∈ W.product W,
      ∑ p ∈ P, (if q.1 ≠ q.2 ∧ (↑p : ℤ) ∣ (q.1 - q.2) then (1 : ℝ) else 0)
        ≤ (P.card : ℝ) * (K₀ / (2 : ℝ) ^ L) := by
    intro q hq
    rcases Finset.eq_empty_or_nonempty P with hem | hne
    · rw [hem]
      simp
    · have hpos : 0 < P.card := Finset.card_pos.mpr hne
      have hcard : (0 : ℝ) < (P.card : ℝ) := by exact_mod_cast hpos
      have h := hterm q hq
      rw [Finset.expect_eq_sum_div_card, div_le_iff₀ hcard] at h
      calc ∑ p ∈ P, (if q.1 ≠ q.2 ∧ (↑p : ℤ) ∣ (q.1 - q.2) then (1 : ℝ) else 0)
          ≤ (K₀ / (2 : ℝ) ^ L) * (P.card : ℝ) := h
        _ = (P.card : ℝ) * (K₀ / (2 : ℝ) ^ L) := by ring
  rw [Finset.expect_eq_sum_div_card]
  have hrew : ∑ p ∈ P, (collisionPairs W p : ℝ)
      = ∑ p ∈ P, ∑ q ∈ W.product W,
          (if q.1 ≠ q.2 ∧ (↑p : ℤ) ∣ (q.1 - q.2) then (1 : ℝ) else 0) :=
    Finset.sum_congr rfl fun p _ => hcp p
  rw [hrew, Finset.sum_comm]
  rcases Finset.eq_empty_or_nonempty P with hem | hne
  · rw [hem]
    simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero, div_zero]
    positivity
  · have hpos : 0 < P.card := Finset.card_pos.mpr hne
    have hcard : (0 : ℝ) < (P.card : ℝ) := by exact_mod_cast hpos
    rw [div_le_iff₀ hcard]
    calc ∑ q ∈ W.product W,
          ∑ p ∈ P, (if q.1 ≠ q.2 ∧ (↑p : ℤ) ∣ (q.1 - q.2) then (1 : ℝ) else 0)
        ≤ ∑ _q ∈ W.product W, ((P.card : ℝ) * (K₀ / (2 : ℝ) ^ L)) :=
          Finset.sum_le_sum hinner
      _ = ((W.product W).card : ℝ) * ((P.card : ℝ) * (K₀ / (2 : ℝ) ^ L)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (W.card : ℝ) ^ 2 * (K₀ / (2 : ℝ) ^ L) * (P.card : ℝ) := by
          have hc : ((W.product W).card : ℝ) = (W.card : ℝ) * (W.card : ℝ) := by
            have hnat : (W.product W).card = W.card * W.card := Finset.card_product W W
            rw [hnat]
            push_cast
            ring
          rw [hc]
          ring

/-- **Base Lemma A5 (one trial), conditional form.** Verbatim conclusion:
«After the trial, D_s contains the key of the class of I with probability at
least 2^{−g_M}n^{−6}.»

The three probabilistic stages are supplied as the two proved inequalities they
amount to:

* `hQ` — Steps 1–3: `Q = E_S[1_good B_S/C(σ,k)] ≥ 2^{−g_M}/(2(v+1))`
  (`good_hit_expect_ge`, the Corollary D consumer), with `G = 2^{−g_M}`;
* `hstep5` — Steps 4–6: the hit probability multiplied by the `1/2` (Markov over
  `P′`), the `1/(m+1)` (Step 1) and the `1/(8K₀n²)` (uniform `j′`) factors, and
  transferred to the trial's success probability (Step 5: «a hit is recovered»,
  plus the independence of the `F`, `P′`, `j′` draws).

The conclusion is the paper's numeric bound with `n` written as `N`; the
threshold `128K₀ ≤ N²` is explicit, which is what «the threshold for n does not
depend on I, s, P or M» asserts. -/
theorem Base_lem_A5 {G K₀ Q Pr : ℝ} {m v N : ℕ} (hG : 0 < G) (hK₀ : 1 ≤ K₀)
    (hN1 : 1 ≤ N) (hm : m ≤ N) (hv : v ≤ N) (hN : 128 * K₀ ≤ (N : ℝ) ^ 2)
    (hQ : G / (2 * ((v : ℝ) + 1)) ≤ Q)
    (hstep5 : (1 / ((m : ℝ) + 1)) * (1 / 2) * Q / (8 * K₀ * (N : ℝ) ^ 2) ≤ Pr) :
    G / (N : ℝ) ^ 6 ≤ Pr := by
  have hprod := lem_A5_product (G := G) (K₀ := K₀) (Q := Q) (m := m) (v := v) hG hK₀ hQ
  have hthr := lem_A5_threshold (G := G) (K₀ := K₀) hG hK₀ hN1 hm hv hN
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have h2 : G / (32 * K₀ * ((m : ℝ) + 1) * ((v : ℝ) + 1)) / (N : ℝ) ^ 2
      ≤ ((1 / ((m : ℝ) + 1)) * (1 / 2) * Q / (8 * K₀)) / (N : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right hprod (le_of_lt hN2)
  calc G / (N : ℝ) ^ 6
      ≤ G / (32 * K₀ * (N : ℝ) ^ 2 * ((m : ℝ) + 1) * ((v : ℝ) + 1)) := hthr
    _ = G / (32 * K₀ * ((m : ℝ) + 1) * ((v : ℝ) + 1)) / (N : ℝ) ^ 2 := by
        field_simp
        try ring
    _ ≤ ((1 / ((m : ℝ) + 1)) * (1 / 2) * Q / (8 * K₀)) / (N : ℝ) ^ 2 := h2
    _ = (1 / ((m : ℝ) + 1)) * (1 / 2) * Q / (8 * K₀ * (N : ℝ) ^ 2) := by
        field_simp
        try ring
    _ ≤ Pr := hstep5

end SubsetSumL25
