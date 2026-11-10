import Mathlib
import SubsetSumL25.Row.KapilaAlgo

open Filter
open scoped Topology

namespace SubsetSumL25.Row

open BigOSpeedrun.SubsetSum

/-! ### The exponent gap

§1 of Base: «Since `τ₀ + 20ε = 0.4876902 < 0.4877`, the gap absorbs every
factor `2^{O(n^{0.7})} poly(n+n^c)`.»  This section proves exactly that
sentence, in the form the row theorem consumes. -/

theorem slack_pos : (0 : ℝ) < slack := by
  rw [slack]; norm_num

theorem tau0_eps_slack : tau0 + 20 * epsPat + slack = alphaRow := by
  rw [tau0, epsPat, slack, alphaRow]; norm_num

/-- For `0 < r < 1` and `c > 0`, eventually `n^r ≤ c·n`. -/
theorem eventually_rpow_le_mul {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {c : ℝ} (hc : 0 < c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (n : ℝ) ^ r ≤ c * (n : ℝ) := by
  have h1r : 0 < 1 - r := by linarith
  have htend : Tendsto (fun x : ℝ => x ^ (1 - r)) atTop atTop := tendsto_rpow_atTop h1r
  have hev : ∀ᶠ x : ℝ in atTop, 1 / c ≤ x ^ (1 - r) :=
    htend.eventually (eventually_ge_atTop (1 / c))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
  set N : ℕ := Nat.ceil (max (max N₀ 1) 1) + 1 with hNdef
  refine ⟨N, ?_⟩
  intro n hn
  have hle : max (max N₀ 1) 1 ≤ (n : ℝ) := by
    have h1 : max (max N₀ 1) 1 ≤ (Nat.ceil (max (max N₀ 1) 1) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (max (max N₀ 1) 1) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (by omega : Nat.ceil (max (max N₀ 1) 1) ≤ n)
    linarith
  have hN : N₀ ≤ (n : ℝ) :=
    le_trans (le_trans (le_max_left N₀ 1) (le_max_left (max N₀ 1) 1)) hle
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := le_trans (le_max_right (max N₀ 1) 1) hle
  have hpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hge : 1 / c ≤ (n : ℝ) ^ (1 - r) := hN₀ (n : ℝ) hN
  have hrew : (n : ℝ) ^ r = (n : ℝ) / (n : ℝ) ^ (1 - r) := by
    have h := Real.rpow_sub (x := (n : ℝ)) hpos (1 : ℝ) (1 - r)
    rw [show (1 : ℝ) - (1 - r) = r by ring] at h
    rw [h, Real.rpow_one]
  rw [hrew, div_eq_mul_inv]
  have hinv : ((n : ℝ) ^ (1 - r))⁻¹ ≤ c := by
    have h1 : 1 / (n : ℝ) ^ (1 - r) ≤ 1 / (1 / c) :=
      one_div_le_one_div_of_le (by positivity) hge
    simp only [one_div] at h1
    simpa using h1
  calc (n : ℝ) * ((n : ℝ) ^ (1 - r))⁻¹ ≤ (n : ℝ) * c :=
        mul_le_mul_of_nonneg_left hinv (le_of_lt hpos)
    _ = c * (n : ℝ) := by ring

/-- Eventually `n^A ≤ 2^{b·n}`: a fixed power is beaten by any positive
exponential rate (`Real.isLittleO_log_id_atTop` is the logarithm's
sub-linearity, transported by `Real.rpow_def_of_pos`). -/
theorem eventually_pow_le_two_rpow {A b : ℝ} (hA : 0 < A) (hb : 0 < b) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (n : ℝ) ^ A ≤ (2 : ℝ) ^ (b * (n : ℝ)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set e : ℝ := b * Real.log 2 / A with he
  have hepos : 0 < e := by
    rw [he]
    positivity
  have hlittle : (fun x : ℝ => Real.log x) =o[atTop] (fun x : ℝ => x) :=
    Real.isLittleO_log_id_atTop
  have hbnd := hlittle.bound hepos
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hbnd
  set N : ℕ := Nat.ceil (max (max N₀ 1) 1) + 1 with hNdef
  refine ⟨N, ?_⟩
  intro n hn
  have hle : max (max N₀ 1) 1 ≤ (n : ℝ) := by
    have h1 : max (max N₀ 1) 1 ≤ (Nat.ceil (max (max N₀ 1) 1) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (max (max N₀ 1) 1) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (by omega : Nat.ceil (max (max N₀ 1) 1) ≤ n)
    linarith
  have hN : N₀ ≤ (n : ℝ) :=
    le_trans (le_trans (le_max_left N₀ 1) (le_max_left (max N₀ 1) 1)) hle
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := le_trans (le_max_right (max N₀ 1) 1) hle
  have hpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog_abs : |Real.log (n : ℝ)| ≤ e * (n : ℝ) := by
    have h1 := hN₀ (n : ℝ) hN
    simpa using h1
  have hlognn : Real.log (n : ℝ) ≤ e * (n : ℝ) := by
    have h2 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
    calc Real.log (n : ℝ) = |Real.log (n : ℝ)| := (abs_of_nonneg h2).symm
      _ ≤ e * (n : ℝ) := hlog_abs
  rw [Real.rpow_def_of_pos hpos, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply Real.exp_le_exp.2
  have hmul : Real.log (n : ℝ) * A ≤ e * (n : ℝ) * A :=
    mul_le_mul_of_nonneg_right hlognn (le_of_lt hA)
  calc Real.log (n : ℝ) * A ≤ e * (n : ℝ) * A := hmul
    _ = Real.log 2 * (b * (n : ℝ)) := by
      rw [he]
      field_simp

/-- **The sub-exponential leg of §1's gap**: `2^{2n^{0.7}} ≤ 2^{(slack/2)n}`
eventually — the paper's «the gap absorbs every factor `2^{O(n^{0.7})}`». -/
theorem subexp_absorb :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (2 : ℝ) ^ (2 * (n : ℝ) ^ (0.7 : ℝ)) ≤ (2 : ℝ) ^ ((slack / 2) * (n : ℝ)) := by
  obtain ⟨N₁, hN₁⟩ := eventually_rpow_le_mul (r := (0.7 : ℝ)) (by norm_num) (by norm_num)
    (c := slack / 8) (by have := slack_pos; linarith)
  refine ⟨max N₁ 1, ?_⟩
  intro n hn
  have hn1 : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 1 ≤ n := le_trans (le_max_right _ _) hn
    exact_mod_cast (by omega : 0 < n)
  have h1 : (n : ℝ) ^ (0.7 : ℝ) ≤ (slack / 8) * (n : ℝ) := hN₁ n hn1
  have hexp : 2 * (n : ℝ) ^ (0.7 : ℝ) ≤ (slack / 2) * (n : ℝ) := by
    have hs := slack_pos
    nlinarith
  exact (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).2 hexp

/-- **The polynomial leg of §1's gap**: `(n + n^c + 2)^K ≤ 2^{(slack/2)n}`
eventually — the paper's «and every factor … `poly(n+n^c)`». -/
theorem poly_absorb (c K : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ((n : ℝ) + (n : ℝ) ^ ((c : ℕ) : ℝ) + 2) ^ K ≤ (2 : ℝ) ^ ((slack / 2) * (n : ℝ)) := by
  rcases Nat.eq_zero_or_pos K with hK | hKpos
  · subst hK
    refine ⟨2, ?_⟩
    intro n hn
    have hone : ((n : ℝ) + (n : ℝ) ^ ((c : ℕ) : ℝ) + 2) ^ 0 = 1 := by simp
    rw [hone]
    exact Real.one_le_rpow (by norm_num) (by have := slack_pos; positivity)
  · set cc : ℕ := max c 1 with hcc
    have hcc1 : 1 ≤ cc := le_max_right c 1
    have hccc : c ≤ cc := le_max_left c 1
    set A : ℝ := (cc : ℝ) * (K : ℝ) with hA_def
    have hApos : 0 < A := by
      have h1 : (0 : ℝ) < (cc : ℝ) := by exact_mod_cast (by omega : 0 < cc)
      have h2 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos
      rw [hA_def]; positivity
    obtain ⟨N₁, hN₁⟩ := eventually_pow_le_two_rpow (A := A) (b := slack / 4) hApos
      (by have := slack_pos; linarith)
    refine ⟨max (max N₁ 2) (Nat.ceil (8 * (K : ℝ) / slack) + 1), ?_⟩
    intro n hn
    have hN1 : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hn2 : 2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hgt : 1 < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hnpos
    have hle_cc : (n : ℝ) ≤ (n : ℝ) ^ ((cc : ℕ) : ℝ) := by
      have h1 : (n : ℝ) ^ ((1 : ℕ) : ℝ) ≤ (n : ℝ) ^ ((cc : ℕ) : ℝ) :=
        (Real.rpow_le_rpow_left_iff hgt).2 (by exact_mod_cast hcc1)
      simpa using h1
    have hle_c : (n : ℝ) ^ ((c : ℕ) : ℝ) ≤ (n : ℝ) ^ ((cc : ℕ) : ℝ) :=
      (Real.rpow_le_rpow_left_iff hgt).2 (by exact_mod_cast hccc)
    have hsum : (n : ℝ) + (n : ℝ) ^ ((c : ℕ) : ℝ) + 2 ≤ 4 * (n : ℝ) ^ ((cc : ℕ) : ℝ) := by
      have h2 : (2 : ℝ) ≤ 2 * (n : ℝ) ^ ((cc : ℕ) : ℝ) := by nlinarith [hle_cc, hnpos]
      nlinarith [hle_cc, hle_c, h2]
    have hsum0 : (0 : ℝ) ≤ (n : ℝ) + (n : ℝ) ^ ((c : ℕ) : ℝ) + 2 := by positivity
    have hK0 : (0 : ℝ) ≤ (K : ℝ) := by exact_mod_cast Nat.zero_le K
    have hrew : ((n : ℝ) + (n : ℝ) ^ ((c : ℕ) : ℝ) + 2) ^ K
        = ((n : ℝ) + (n : ℝ) ^ ((c : ℕ) : ℝ) + 2) ^ ((K : ℕ) : ℝ) :=
      (Real.rpow_natCast _ K).symm
    have hstep1 : ((n : ℝ) + (n : ℝ) ^ ((c : ℕ) : ℝ) + 2) ^ ((K : ℕ) : ℝ)
        ≤ (4 * (n : ℝ) ^ ((cc : ℕ) : ℝ)) ^ ((K : ℕ) : ℝ) :=
      Real.rpow_le_rpow hsum0 hsum hK0
    have hstep2 : (4 * (n : ℝ) ^ ((cc : ℕ) : ℝ)) ^ ((K : ℕ) : ℝ)
        = (2 : ℝ) ^ (2 * (K : ℝ)) * (n : ℝ) ^ A := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity)]
      have h42 : (4 : ℝ) = (2 : ℝ) ^ ((2 : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]; norm_num
      have h4 : (4 : ℝ) ^ ((K : ℕ) : ℝ) = (2 : ℝ) ^ (2 * (K : ℝ)) := by
        rw [h42, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      have hp : ((n : ℝ) ^ ((cc : ℕ) : ℝ)) ^ ((K : ℕ) : ℝ) = (n : ℝ) ^ A := by
        rw [← Real.rpow_mul hn0, hA_def]
      rw [h4, hp]
    have hfour : (2 : ℝ) ^ (2 * (K : ℝ)) ≤ (2 : ℝ) ^ ((slack / 4) * (n : ℝ)) := by
      refine (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).2 ?_
      have hs := slack_pos
      have hK' : (8 * (K : ℝ)) / slack ≤ (n : ℝ) := by
        have h8 : (8 * (K : ℝ)) / slack ≤ (Nat.ceil (8 * (K : ℝ) / slack) : ℝ) := Nat.le_ceil _
        have h9 : Nat.ceil (8 * (K : ℝ) / slack) + 1 ≤ n := le_trans (le_max_right _ _) hn
        have h10 : (Nat.ceil (8 * (K : ℝ) / slack) : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast (by omega : Nat.ceil (8 * (K : ℝ) / slack) ≤ n)
        linarith
      have hk : 8 * (K : ℝ) ≤ slack * (n : ℝ) := by
        rw [div_le_iff₀ hs] at hK'
        linarith
      nlinarith
    have hpoly : (n : ℝ) ^ A ≤ (2 : ℝ) ^ ((slack / 4) * (n : ℝ)) := hN₁ n hN1
    have hmul : (2 : ℝ) ^ (2 * (K : ℝ)) * (n : ℝ) ^ A
        ≤ (2 : ℝ) ^ ((slack / 4) * (n : ℝ)) * (2 : ℝ) ^ ((slack / 4) * (n : ℝ)) := by
      apply mul_le_mul hfour hpoly (by positivity) (by positivity)
    have hjoin : (2 : ℝ) ^ ((slack / 4) * (n : ℝ)) * (2 : ℝ) ^ ((slack / 4) * (n : ℝ))
        = (2 : ℝ) ^ ((slack / 2) * (n : ℝ)) := by
      rw [← Real.rpow_add (by norm_num)]
      congr 1
      ring
    calc ((n : ℝ) + (n : ℝ) ^ ((c : ℕ) : ℝ) + 2) ^ K
        = ((n : ℝ) + (n : ℝ) ^ ((c : ℕ) : ℝ) + 2) ^ ((K : ℕ) : ℝ) := hrew
      _ ≤ (4 * (n : ℝ) ^ ((cc : ℕ) : ℝ)) ^ ((K : ℕ) : ℝ) := hstep1
      _ = (2 : ℝ) ^ (2 * (K : ℝ)) * (n : ℝ) ^ A := hstep2
      _ ≤ (2 : ℝ) ^ ((slack / 2) * (n : ℝ)) := le_trans hmul (le_of_eq hjoin)

/-- **§1's gap, in one lemma**: §7's runtime envelope's sub-exponential and
polynomial factors are absorbed by the slack between `τ₀ + 20ε` and `0.4877`. -/
theorem runtime_absorb (c K : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (2 : ℝ) ^ ((tau0 + 20 * epsPat) * (n : ℝ)) * (2 : ℝ) ^ (2 * (n : ℝ) ^ (0.7 : ℝ))
        * ((n : ℝ) + (n : ℝ) ^ ((c : ℕ) : ℝ) + 2) ^ K
      ≤ (2 : ℝ) ^ (alphaRow * (n : ℝ)) := by
  obtain ⟨N₁, hN₁⟩ := subexp_absorb
  obtain ⟨N₂, hN₂⟩ := poly_absorb c K
  refine ⟨max (max N₁ N₂) 1, ?_⟩
  intro n hn
  have hN1 : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hN2 : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have : 1 ≤ n := le_trans (le_max_right _ _) hn
    exact_mod_cast this
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hsub := hN₁ n hN1
  have hpol := hN₂ n hN2
  have hbase : (0 : ℝ) < (2 : ℝ) ^ ((tau0 + 20 * epsPat) * (n : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hmono1 : (2 : ℝ) ^ ((tau0 + 20 * epsPat) * (n : ℝ)) * (2 : ℝ) ^ (2 * (n : ℝ) ^ (0.7 : ℝ))
      ≤ (2 : ℝ) ^ ((tau0 + 20 * epsPat) * (n : ℝ)) * (2 : ℝ) ^ ((slack / 2) * (n : ℝ)) :=
    mul_le_mul_of_nonneg_left hsub (le_of_lt hbase)
  have hstep : (2 : ℝ) ^ ((tau0 + 20 * epsPat) * (n : ℝ)) * (2 : ℝ) ^ ((slack / 2) * (n : ℝ))
      = (2 : ℝ) ^ ((tau0 + 20 * epsPat + slack / 2) * (n : ℝ)) := by
    rw [← Real.rpow_add (by norm_num)]
    congr 1
    ring
  calc (2 : ℝ) ^ ((tau0 + 20 * epsPat) * (n : ℝ)) * (2 : ℝ) ^ (2 * (n : ℝ) ^ (0.7 : ℝ))
        * ((n : ℝ) + (n : ℝ) ^ ((c : ℕ) : ℝ) + 2) ^ K
      = ((2 : ℝ) ^ ((tau0 + 20 * epsPat) * (n : ℝ)) * (2 : ℝ) ^ (2 * (n : ℝ) ^ (0.7 : ℝ)))
        * ((n : ℝ) + (n : ℝ) ^ ((c : ℕ) : ℝ) + 2) ^ K := by ring
    _ ≤ ((2 : ℝ) ^ ((tau0 + 20 * epsPat) * (n : ℝ)) * (2 : ℝ) ^ ((slack / 2) * (n : ℝ)))
        * (2 : ℝ) ^ ((slack / 2) * (n : ℝ)) := by
      apply mul_le_mul hmono1 hpol (by positivity) (by positivity)
    _ = (2 : ℝ) ^ ((tau0 + 20 * epsPat + slack) * (n : ℝ)) := by
      rw [hstep, ← Real.rpow_add (by norm_num)]
      congr 1
      ring
    _ = (2 : ℝ) ^ (alphaRow * (n : ℝ)) := by
      rw [← tau0_eps_slack]

end SubsetSumL25.Row
