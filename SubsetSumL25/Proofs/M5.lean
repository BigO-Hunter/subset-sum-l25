/-
M5 (DS): Lemma A5 Step 6 (the product) + Corollary A6 (the e^{−n} coverage
union bound), in the concrete DS parameterization.  This file is the
statement-of-record for what is proved; the verbatim source and the milestone
ladder live in `Statements/DS.lean`.

Primary source: `a-kapila/maths-proofs` @ 44c34961,
`subset-sum/PROOF_0.4877.tex` §5.6 (sha256
b397531cc5997e88c439d5290774861b46a34aa32d9cd71fa7dcced130359298).

DS-M5 Step 6 (product) — verbatim:
    «Step 6 (product). The draws of F, P' and j' are independent. Steps 1--5
    give a success probability of at least
    [1/(m+1)]·E_S[1_good·(1/2)·B_S/(8K₀n²C(σ,k))] ≥ 2^{−g_M}/(32K₀n²(m+1)(v+1))
    ≥ 2^{−g_M}n^{−6} for all large n.»

DS-M5 Corollary A6 (coverage union bound) — verbatim:
    «The T trials for a pair (s, q) are independent, and T ≥ n⁷2^{F̂} ≥ n⁷2^{g_M}
    by Lemma A3(1). By Lemma A5, all of them miss a fixed alias with carry q
    with probability at most (1 − 2^{−g_M}n^{−6})^T ≤ e^{−n}. There are at most
    (nN₀+1)2^n pairs of a target and a subset, and (nN₀+1)2^n e^{−n} = o(1).»

Parameterization: in M4 the (F4) constant is explicit as `c := K·B·L/2^L`
(the paper's `K₀n²2^{−γm}`; the bit bound «differences have at most
ηn + log n + 3 bits» enters through it — instance data, D7 boundary).  The
paper's `B_S = |W_S|` is a set cardinality, so `B := W.card` directly (the
paper defines `B_S = |W_S|` at §5.6 Step 3).  The bridge `c·2^{γm} = K₀·N²`
is instance data; the seam's squeeze uses `2^{γm} ≤ C(σ,k)` (S4) and
`B_S ≤ C(σ,k)` (W_S is the image of the k-subsets).

Cast-discipline: ℝ for the probabilities, ℕ for the counts; `exact_mod_cast`
at the ℕ↔ℝ boundary only.
-/
import Mathlib
import SubsetSumL25.Statements.Defs
import SubsetSumL25.Proofs.M4

namespace SubsetSumL25

/-! ### DS-M4's recorded seam — the two-case squeeze -/

/-- M4's recorded seam, discharged: the paper's final squeeze
`min(B_S 2^{−γm}, 1) ≥ B_S/C(σ,k)` — the two-case arithmetic on C̄'s shape,
using `2^{γm} ≤ C(σ,k)` (S4) and `B_S ≤ C(σ,k)` (W_S is the image of the
k-subsets).  Case `B_S ≤ 2^{γm}`: `min(B_S 2^{−γm}, 1) ≥ B_S 2^{−γm} ≥
B_S/2^{γm} ≥ B_S/C(σ,k)`.  Case `2^{γm} < B_S`: `min = 1 ≥ B_S/C(σ,k)`. -/
theorem min_two_pow_neg_ge_div {b C : ℝ} {g : ℕ} (hb : 0 ≤ b) (hC : 0 < C)
    (h2 : (2:ℝ)^((g:ℝ)) ≤ C) (hbC : b ≤ C) : min (b * (2:ℝ)^(-(g:ℝ))) 1 ≥ b / C := by
  have h2pos : (0:ℝ) < (2:ℝ)^((g:ℝ)) := Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) ((g:ℝ))
  have hneg : (2:ℝ)^(-(g:ℝ)) = 1 / (2:ℝ)^((g:ℝ)) := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2) ((g:ℝ)), inv_eq_one_div]
  have hr0 : (0:ℝ) ≤ (2:ℝ)^(-(g:ℝ)) := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (-(g:ℝ))
  have hprodinv : (2:ℝ)^(-(g:ℝ)) * (2:ℝ)^((g:ℝ)) = 1 := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2) ((g:ℝ)), inv_mul_cancel₀ h2pos.ne']
  by_cases hle : b ≤ (2:ℝ)^((g:ℝ))
  · have hmin : min (b * (2:ℝ)^(-(g:ℝ))) 1 = b * (2:ℝ)^(-(g:ℝ)) :=
      min_eq_left (by nlinarith [hle, hr0, hprodinv])
    rw [hmin, hneg, ← div_eq_mul_one_div, ge_iff_le]
    exact (div_le_div_iff₀ hC h2pos).mpr (by
      rw [mul_comm b ((2:ℝ)^((g:ℝ))), mul_comm b C]
      exact mul_le_mul_of_nonneg_right h2 hb)
  · have hlt : (2:ℝ)^((g:ℝ)) < b := by linarith
    have h1 : 1 < b * (2:ℝ)^(-(g:ℝ)) := by nlinarith [hlt, hr0, hprodinv]
    rw [min_eq_right (le_of_lt h1)]
    exact (div_le_one hC).mpr hbC

/-- The display identity: `min(B 2^{−γm}, 1) = 2^{−γm}·min(B, 2^{γm})` —
the same exponent on both sides, so no rpow-splitting is needed. -/
theorem min_two_pow_neg_eq (b : ℝ) (g : ℕ) :
    min (b * (2:ℝ)^(-(g:ℝ))) 1 = (2:ℝ)^(-(g:ℝ)) * min b ((2:ℝ)^((g:ℝ))) := by
  have h2g : (0:ℝ) < (2:ℝ)^((g:ℝ)) := Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) ((g:ℝ))
  have hneg : (2:ℝ)^(-(g:ℝ)) = 1 / (2:ℝ)^((g:ℝ)) := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2) ((g:ℝ)), inv_eq_one_div]
  have hr0 : (0:ℝ) ≤ (2:ℝ)^(-(g:ℝ)) := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (-(g:ℝ))
  have hprodinv : (2:ℝ)^(-(g:ℝ)) * (2:ℝ)^((g:ℝ)) = 1 := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2) ((g:ℝ)), inv_mul_cancel₀ h2g.ne']
  by_cases hle : b ≤ (2:ℝ)^((g:ℝ))
  · have h1 : b * (2:ℝ)^(-(g:ℝ)) ≤ 1 := by nlinarith [hle, hr0, hprodinv]
    rw [min_eq_left h1, min_eq_left hle]
    ring
  · have hlt : (2:ℝ)^((g:ℝ)) < b := by linarith
    have h1 : 1 < b * (2:ℝ)^(-(g:ℝ)) := by nlinarith [hlt, hr0, hprodinv]
    rw [min_eq_right (le_of_lt h1), min_eq_right (le_of_lt hlt), hneg,
      one_div_mul_cancel h2g.ne']

/-! ### Step 4's occupancy display — the two-case second moment -/

/-- The two-case arithmetic on C̄'s shape, in algebraic form: on the
good-prime event `Σ_y z_y² ≤ C`, `B²/C ≥ min(B, 2^{γm})/(4c·2^{γm})` —
the inequality the paper reads through the Cauchy–Schwarz occupancy
(«at least min(B_S, 2^{γm})/(4K₀n²) residues are occupied»).  Consumes
M4's `card_sq_le_sum_sq_mul_occupied` for the occupancy reading and feeds
the Step-4 j′-display directly. -/
theorem sq_div_ge_min_div (W : Finset ℤ) {p : ℕ} (hp : 0 < p) {g : ℕ} {C : ℕ} {c : ℝ}
    (hC : 0 < C) (hc : 0 < c)
    (hsq : ∑ y ∈ W.image (fun x => x % (p:ℤ)), (W.filter (fun x => x % (p:ℤ) = y)).card ^ 2 ≤ C)
    (hc2 : (1:ℝ) ≤ c * (2:ℝ)^((g:ℝ)))
    (h1 : (W.card:ℝ) ≤ (2:ℝ)^((g:ℝ)) → (C:ℝ) ≤ 4 * c * (2:ℝ)^((g:ℝ)) * (W.card:ℝ))
    (h2 : (2:ℝ)^((g:ℝ)) < (W.card:ℝ) → (C:ℝ) ≤ 4 * c * (W.card:ℝ) ^ 2) :
    min ((W.card:ℝ)) ((2:ℝ)^((g:ℝ))) / (4 * c * (2:ℝ)^((g:ℝ)))
      ≤ ((W.card:ℝ)) ^ 2 / (C:ℝ) := by
  classical
  have h2g : (0:ℝ) < (2:ℝ)^((g:ℝ)) := Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) ((g:ℝ))
  have hC' : (0:ℝ) < (C:ℝ) := by exact_mod_cast hC
  rcases Nat.eq_zero_or_pos W.card with hB0 | hB0
  · -- empty W: the bound is 0
    have hmin0 : min ((W.card:ℝ)) ((2:ℝ)^((g:ℝ))) = 0 := by
      rw [hB0, Nat.cast_zero]
      exact min_eq_left (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) ((g:ℝ)))
    rw [hmin0, zero_div]
    exact by positivity
  · have hBpos : (0:ℝ) < (W.card:ℝ) := by exact_mod_cast hB0
    have hBne : (W.card:ℝ) ≠ 0 := ne_of_gt hBpos
    by_cases hcase : (W.card:ℝ) ≤ (2:ℝ)^((g:ℝ))
    · -- case B ≤ 2^{γm}: B²/C ≥ B²/(4c2^{γm}·B) = B/(4c2^{γm}) = min/(4c2^{γm})
      have hbound : (C:ℝ) ≤ 4 * c * (2:ℝ)^((g:ℝ)) * (W.card:ℝ) := h1 hcase
      have hden : (0:ℝ) < 4 * c * (2:ℝ)^((g:ℝ)) * (W.card:ℝ) := by positivity
      have hmin : min ((W.card:ℝ)) ((2:ℝ)^((g:ℝ))) = (W.card:ℝ) := min_eq_left hcase
      rw [hmin]
      calc (W.card:ℝ) / (4 * c * (2:ℝ)^((g:ℝ)))
          = (W.card:ℝ) ^ 2 / (4 * c * (2:ℝ)^((g:ℝ)) * (W.card:ℝ)) := by
            field_simp [hBne]
        _ ≤ (W.card:ℝ) ^ 2 / (C:ℝ) :=
              (div_le_div_iff₀ hden hC').mpr
                (mul_le_mul_of_nonneg_left hbound (by positivity))
    · -- case 2^{γm} < B: B²/C ≥ B²/(4cB²) = 1/(4c) = 2^{γm}/(4c2^{γm}) = min/(4c2^{γm})
      have hlt : (2:ℝ)^((g:ℝ)) < (W.card:ℝ) := by linarith
      have hbound : (C:ℝ) ≤ 4 * c * (W.card:ℝ) ^ 2 := h2 hlt
      have hden : (0:ℝ) < 4 * c * (W.card:ℝ) ^ 2 := by positivity
      have hmin : min ((W.card:ℝ)) ((2:ℝ)^((g:ℝ))) = (2:ℝ)^((g:ℝ)) :=
        min_eq_right (le_of_lt hlt)
      have hident1 : (2:ℝ)^((g:ℝ)) / (4 * c * (2:ℝ)^((g:ℝ))) = 1 / (4 * c) := by
        field_simp [h2g.ne']
      have hident2 : 1 / (4 * c) = (W.card:ℝ) ^ 2 / (4 * c * (W.card:ℝ) ^ 2) := by
        field_simp [hBne, hc.ne']
      rw [hmin, hident1, hident2]
      exact (div_le_div_iff₀ hden hC').mpr
        (mul_le_mul_of_nonneg_left hbound (by positivity))

/-- Step 4's occupancy display: on the good-prime event `Σ_y z_y² ≤ C`, at
least `min(B, 2^{γm})/(4c·2^{γm})` residues are occupied — the paper's
«at least min(B_S, 2^{γm})/(4K₀n²) residues are occupied» with the explicit
constant (`c·2^{γm}` is the paper's `K₀n²`).  The two case-bounds are the
paper's «If B_S ≤ 2^{γm}, the right side is at most 2K₀n²B_S. Otherwise it is
at most 2K₀n²B_S²2^{−γm}», fed for the Markov-inflated bound `C`.  Consumes
M4's Cauchy–Schwarz occupancy (`card_sq_le_sum_sq_mul_occupied`). -/
theorem occupied_ge_min_div (W : Finset ℤ) {p : ℕ} (hp : 0 < p) {g : ℕ} {C : ℕ} {c : ℝ}
    (hC : 0 < C) (hc : 0 < c)
    (hsq : ∑ y ∈ W.image (fun x => x % (p:ℤ)), (W.filter (fun x => x % (p:ℤ) = y)).card ^ 2 ≤ C)
    (hc2 : (1:ℝ) ≤ c * (2:ℝ)^((g:ℝ)))
    (h1 : (W.card:ℝ) ≤ (2:ℝ)^((g:ℝ)) → (C:ℝ) ≤ 4 * c * (2:ℝ)^((g:ℝ)) * (W.card:ℝ))
    (h2 : (2:ℝ)^((g:ℝ)) < (W.card:ℝ) → (C:ℝ) ≤ 4 * c * (W.card:ℝ) ^ 2) :
    min ((W.card:ℝ)) ((2:ℝ)^((g:ℝ))) / (4 * c * (2:ℝ)^((g:ℝ)))
      ≤ ((W.image (fun x => x % (p:ℤ))).card : ℝ) := by
  classical
  -- C–S: B² ≤ Σz²·occ ≤ C·occ (M4's card_sq_le_sum_sq_mul_occupied)
  have h2nat : ((W.card:ℝ) ^ 2) ≤ (((∑ y ∈ W.image (fun x => x % (p:ℤ)),
      (W.filter (fun x => x % (p:ℤ) = y)).card ^ 2 : ℕ)) : ℝ)
        * ((W.image (fun x => x % (p:ℤ))).card : ℝ) := by
    exact_mod_cast card_sq_le_sum_sq_mul_occupied W hp
  have hBC : ((W.card:ℝ) ^ 2) / (C:ℝ)
      ≤ ((W.image (fun x => x % (p:ℤ))).card : ℝ) := by
    have hC' : (0:ℝ) < (C:ℝ) := by exact_mod_cast hC
    have hCC : (((∑ y ∈ W.image (fun x => x % (p:ℤ)),
        (W.filter (fun x => x % (p:ℤ) = y)).card ^ 2 : ℕ)) : ℝ)
          * ((W.image (fun x => x % (p:ℤ))).card : ℝ) ≤ (C:ℝ)
            * ((W.image (fun x => x % (p:ℤ))).card : ℝ) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hsq) (by positivity)
    have hmain : ((W.card:ℝ) ^ 2) ≤ ((W.image (fun x => x % (p:ℤ))).card : ℝ) * (C:ℝ) := by
      linarith [le_trans h2nat hCC,
        mul_comm ((W.image (fun x => x % (p:ℤ))).card : ℝ) (C:ℝ)]
    exact (div_le_iff₀ hC').mpr hmain
  exact le_trans (sq_div_ge_min_div W hp hC hc hsq hc2 h1 h2) hBC

/-! ### Step 4 + the j′ draw — the per-good-S display and the seam -/

/-- Step 4's per-prime conclusion with the `P′ < 2^{1+γm}` step: on the
good-prime event `Σ_y z_y² ≤ C`, a uniform `j′` hits an occupied residue with
probability at least `min(B 2^{−γm}, 1)/(8c·2^{γm})` — the paper's display
`min(B_S 2^{−γm}, 1)/(8K₀n²)` with `c·2^{γm} := K₀n²`.  Consumes M4's
`hit_prob_ge_of_sum_sq_le` and the occupancy display above. -/
theorem hit_prob_ge_min_display (W : Finset ℤ) {p : ℕ} (hp : 0 < p) {g : ℕ} {C : ℕ} {c : ℝ}
    (hC : 0 < C) (hc : 0 < c)
    (hsq : ∑ y ∈ W.image (fun x => x % (p:ℤ)), (W.filter (fun x => x % (p:ℤ) = y)).card ^ 2 ≤ C)
    (hc2 : (1:ℝ) ≤ c * (2:ℝ)^((g:ℝ)))
    (h1 : (W.card:ℝ) ≤ (2:ℝ)^((g:ℝ)) → (C:ℝ) ≤ 4 * c * (2:ℝ)^((g:ℝ)) * (W.card:ℝ))
    (h2 : (2:ℝ)^((g:ℝ)) < (W.card:ℝ) → (C:ℝ) ≤ 4 * c * (W.card:ℝ) ^ 2)
    (hpP : (p:ℝ) < (2:ℝ)^(((g:ℝ)+1))) :
    min ((W.card:ℝ) * (2:ℝ)^(-(g:ℝ))) 1 / (8 * c * (2:ℝ)^((g:ℝ)))
      ≤ (Finset.range p).expect
          (fun (j : ℕ) => if ∃ x ∈ W, x % (p:ℤ) = (↑j : ℤ) then (1 : ℝ) else 0) := by
  classical
  have hp2 : (0:ℝ) < (2:ℝ) := by norm_num
  have h2g : (0:ℝ) < (2:ℝ)^((g:ℝ)) := Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) ((g:ℝ))
  have hC' : (0:ℝ) < (C:ℝ) := by exact_mod_cast hC
  -- 1/P′ ≥ 2^{−(γm+1)}
  have hP' : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
  have hexp0 : (((g:ℝ)+1) + (-((g:ℝ)+1))) = 0 := by ring
  have hkey1 : (2:ℝ)^(((g:ℝ)+1)) * (2:ℝ)^(-(((g:ℝ)+1))) = 1 := by
    rw [← Real.rpow_add hp2, hexp0, Real.rpow_zero]
  have hkey2 : (2:ℝ)^(-(((g:ℝ)+1))) * (p:ℝ) < 1 := by
    have hmul : (p:ℝ) * (2:ℝ)^(-(((g:ℝ)+1))) < (2:ℝ)^(((g:ℝ)+1)) * (2:ℝ)^(-(((g:ℝ)+1))) :=
      mul_lt_mul_of_pos_right hpP (by positivity)
    rw [mul_comm] at hmul
    linarith [hkey1, hmul]
  have hinv : (2:ℝ)^(-(((g:ℝ)+1))) < (1:ℝ) / (p:ℝ) :=
    (lt_div_iff₀ hP').mpr hkey2
  -- B²/(P′·C) ≤ occ/P′ and occ/P′ ≥ occ·2^{−(γm+1)}
  have hsq2 := sq_div_ge_min_div W hp hC hc hsq hc2 h1 h2
  -- the display reshuffle
  have hsplit : (2:ℝ)^(-(((g:ℝ)+1))) = (2:ℝ)^(-(g:ℝ)) * (2:ℝ)^(-(1:ℝ)) := by
    have hexp : (-(g:ℝ)) + (-(1:ℝ)) = -(((g:ℝ)+1)) := by ring
    have h := Real.rpow_add hp2 (-(g:ℝ)) (-(1:ℝ))
    rw [hexp] at h
    exact h
  have h21 : (2:ℝ)^(-(1:ℝ)) ≠ 0 :=
    (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) (-(1:ℝ))).ne'
  have hdisp : min ((W.card:ℝ) * (2:ℝ)^(-(g:ℝ))) 1 / (8 * c * (2:ℝ)^((g:ℝ)))
      = min ((W.card:ℝ)) ((2:ℝ)^((g:ℝ)))
          * ((2:ℝ)^(-(((g:ℝ)+1))) / (4 * c * (2:ℝ)^((g:ℝ)))) := by
    rw [min_two_pow_neg_eq, mul_div_assoc, hsplit]
    field_simp [hc.ne', h2g.ne', h21]
    try ring
  -- min·(r/d) ≤ (B²/C)·r ≤ (B²/C)·(1/p) = B²/(p·C) ≤ hit
  have hchain : min ((W.card:ℝ)) ((2:ℝ)^((g:ℝ)))
        * ((2:ℝ)^(-(((g:ℝ)+1))) / (4 * c * (2:ℝ)^((g:ℝ))))
      ≤ ((W.card:ℝ)) ^ 2 / ((p:ℝ) * (C:ℝ)) := by
    have h1 : min ((W.card:ℝ)) ((2:ℝ)^((g:ℝ)))
          * ((2:ℝ)^(-(((g:ℝ)+1))) / (4 * c * (2:ℝ)^((g:ℝ))))
        = (min ((W.card:ℝ)) ((2:ℝ)^((g:ℝ))) / (4 * c * (2:ℝ)^((g:ℝ))))
            * (2:ℝ)^(-(((g:ℝ)+1))) := by
      rw [mul_div_assoc', div_mul_eq_mul_div]
    have h3 : ((W.card:ℝ)) ^ 2 / (C:ℝ) * ((1:ℝ) / (p:ℝ))
        = ((W.card:ℝ)) ^ 2 / ((p:ℝ) * (C:ℝ)) := by
      field_simp [hP'.ne', hC'.ne']
    rw [h1]
    calc (min ((W.card:ℝ)) ((2:ℝ)^((g:ℝ))) / (4 * c * (2:ℝ)^((g:ℝ))))
          * (2:ℝ)^(-(((g:ℝ)+1))) ≤
          ((W.card:ℝ)) ^ 2 / (C:ℝ) * (2:ℝ)^(-(((g:ℝ)+1))) :=
          mul_le_mul_of_nonneg_right hsq2 (by positivity)
      _ ≤ ((W.card:ℝ)) ^ 2 / (C:ℝ) * ((1:ℝ) / (p:ℝ)) :=
          mul_le_mul_of_nonneg_left (le_of_lt hinv) (by positivity)
      _ = ((W.card:ℝ)) ^ 2 / ((p:ℝ) * (C:ℝ)) := h3
  have hM4 := hit_prob_ge_of_sum_sq_le W hp hC hsq
  calc min ((W.card:ℝ) * (2:ℝ)^(-(g:ℝ))) 1 / (8 * c * (2:ℝ)^((g:ℝ)))
      = min ((W.card:ℝ)) ((2:ℝ)^((g:ℝ)))
          * ((2:ℝ)^(-(((g:ℝ)+1))) / (4 * c * (2:ℝ)^((g:ℝ)))) := hdisp
    _ ≤ ((W.card:ℝ)) ^ 2 / ((p:ℝ) * (C:ℝ)) := hchain
    _ ≤ (Finset.range p).expect
          (fun (j : ℕ) => if ∃ x ∈ W, x % (p:ℤ) = (↑j : ℤ) then (1 : ℝ) else 0) := hM4

/-- The seam applied: on the good-prime event, a uniform `j′` hits with
probability at least `B/(8c·2^{γm}·C(σ,k))` — the paper's
`B_S/(8K₀n²C(σ,k))`, the per-good-S leaf of the Step-6 product.  Consumes
the display above and M4's recorded seam (discharged as
`min_two_pow_neg_ge_div`). -/
theorem hit_prob_ge_seam (W : Finset ℤ) {p : ℕ} (hp : 0 < p) {g : ℕ} {C : ℕ} {c Cσ : ℝ}
    (hC : 0 < C) (hc : 0 < c) (hCσ : 0 < Cσ)
    (hsq : ∑ y ∈ W.image (fun x => x % (p:ℤ)), (W.filter (fun x => x % (p:ℤ) = y)).card ^ 2 ≤ C)
    (hc2 : (1:ℝ) ≤ c * (2:ℝ)^((g:ℝ)))
    (h1 : (W.card:ℝ) ≤ (2:ℝ)^((g:ℝ)) → (C:ℝ) ≤ 4 * c * (2:ℝ)^((g:ℝ)) * (W.card:ℝ))
    (h2 : (2:ℝ)^((g:ℝ)) < (W.card:ℝ) → (C:ℝ) ≤ 4 * c * (W.card:ℝ) ^ 2)
    (hpP : (p:ℝ) < (2:ℝ)^(((g:ℝ)+1)))
    (h2C : (2:ℝ)^((g:ℝ)) ≤ Cσ)
    (hBC : (W.card:ℝ) ≤ Cσ) :
    ((W.card:ℝ)) / (8 * c * (2:ℝ)^((g:ℝ)) * Cσ)
      ≤ (Finset.range p).expect
          (fun (j : ℕ) => if ∃ x ∈ W, x % (p:ℤ) = (↑j : ℤ) then (1 : ℝ) else 0) := by
  have hdisp := hit_prob_ge_min_display W hp hC hc hsq hc2 h1 h2 hpP
  have hseam' : ((W.card:ℝ)) ≤ min ((W.card:ℝ) * (2:ℝ)^(-(g:ℝ))) 1 * Cσ :=
    (div_le_iff₀ hCσ).mp
      (min_two_pow_neg_ge_div (by exact_mod_cast (Nat.zero_le W.card)) hCσ h2C hBC)
  have hseam : ((W.card:ℝ)) / (8 * c * (2:ℝ)^((g:ℝ)) * Cσ)
      ≤ min ((W.card:ℝ) * (2:ℝ)^(-(g:ℝ))) 1 / (8 * c * (2:ℝ)^((g:ℝ))) :=
    (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      (by nlinarith [hseam', hCσ])
  exact le_trans hseam hdisp

/-! ### Step 6 (product) — the display line and the threshold -/

/-- Step 6's display line: with the Step-3 input
`E_S[1_good·B_S/C(σ,k)] ≥ 2^{−g_M}/(2(v+1))` (DS-M3's discharged form, as
`hQ`), the trial's success probability dominates
`2^{−g_M}/(32c·2^{γm}(m+1)(v+1))` — the paper's
`2^{−g_M}/(32K₀n²(m+1)(v+1))`.  The trial transfer
«(1/(m+1))·(1/2)·(1/(8K₀n²))·E_S ≤ Pr» is `htr` — the independence of the
F, P′, j′ draws (exec-side, D7 boundary); the display's arithmetic (the
constant pulled through the expectation) is proved. -/
theorem step6_product_expect {M : Finset (Fin n)} {σ : ℕ} (B : Finset (Fin n) → ℕ)
    (good : Finset (Fin n) → Prop) [DecidablePred good] {G c Cσ : ℝ} {g m v : ℕ} {Pr : ℝ}
    (hG : 0 < G) (hc : 0 < c)
    (hQ : G / (2 * ((v:ℝ)+1)) ≤ (M.powersetCard σ).expect
            (fun S => if good S then (B S : ℝ) / Cσ else 0))
    (htr : (1/(((m:ℝ))+1)) * (1/2) * (1/(8 * c * (2:ℝ)^((g:ℝ))))
            * (M.powersetCard σ).expect
                (fun S => if good S then (B S : ℝ) / Cσ else 0) ≤ Pr) :
    G / (32 * c * (2:ℝ)^((g:ℝ)) * (((m:ℝ))+1) * ((v:ℝ)+1)) ≤ Pr := by
  classical
  have h2g : (0:ℝ) < (2:ℝ)^((g:ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  set k : ℝ := 1 / (16 * c * (2:ℝ)^((g:ℝ))) with hkdef
  have hk0 : (0:ℝ) < k := by
    rw [hkdef]
    exact div_pos (by norm_num) (by positivity)
  have hpull : k * ((M.powersetCard σ).expect
        (fun S => if good S then (B S : ℝ) / Cσ else 0))
      = (M.powersetCard σ).expect
        (fun S => k * (if good S then (B S : ℝ) / Cσ else 0)) :=
    Finset.mul_expect _ _ _
  have hkmid : (1:ℝ) / 2 * (1/(8 * c * (2:ℝ)^((g:ℝ)))) = k := by
    rw [hkdef]
    field_simp
    ring
  rw [mul_assoc ((1:ℝ)/(((m:ℝ))+1)) (1/2) (1/(8*c*(2:ℝ)^((g:ℝ))))] at htr
  rw [hkmid] at htr
  -- htr : ((1/(m+1))·k)·E ≤ Pr  (the transfer, now in k-form)
  have hlow : k * (G / (2 * ((v:ℝ)+1)))
      ≤ k * ((M.powersetCard σ).expect
          (fun S => if good S then (B S : ℝ) / Cσ else 0)) :=
    mul_le_mul_of_nonneg_left hQ hk0.le
  calc G / (32 * c * (2:ℝ)^((g:ℝ)) * (((m:ℝ))+1) * ((v:ℝ)+1))
      = (1/(((m:ℝ))+1)) * (k * (G / (2 * ((v:ℝ)+1)))) := by
        rw [hkdef]
        field_simp
        ring
    _ ≤ (1/(((m:ℝ))+1)) * ((k * (M.powersetCard σ).expect
          (fun S => if good S then (B S : ℝ) / Cσ else 0))) :=
          mul_le_mul_of_nonneg_left hlow (by positivity)
    _ ≤ Pr := by rw [← mul_assoc]; exact htr

/-- Step 6's threshold: `G/(32c·2^{γm}(m+1)(v+1)) ≥ G/N⁶` under
`128c·2^{γm} ≤ N⁴` — `lem_A5_threshold`'s argument in the `c·2^{γm} = K₀n²`
parameterization (its `128K₀ ≤ N²` becomes `128c·2^{γm} ≤ N⁴`, since the
paper's `n²` is absorbed into `c·2^{γm}`). -/
theorem step6_threshold {G c : ℝ} {g m v N : ℕ} (hG : 0 < G) (hc : 0 < c)
    (hN1 : 1 ≤ N) (hm : m ≤ N) (hv : v ≤ N)
    (hN : 128 * c * (2:ℝ)^((g:ℝ)) ≤ (N:ℝ)^4) :
    G / (N:ℝ)^6 ≤ G / (32 * c * (2:ℝ)^((g:ℝ)) * (((m:ℝ))+1) * ((v:ℝ)+1)) := by
  have hN1R : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hmR : (m:ℝ) ≤ (N:ℝ) := by exact_mod_cast hm
  have hvR : (v:ℝ) ≤ (N:ℝ) := by exact_mod_cast hv
  have hm1 : ((m:ℝ)+1) ≤ 2 * (N:ℝ) := by linarith
  have hv1 : ((v:ℝ)+1) ≤ 2 * (N:ℝ) := by linarith
  have hden : (0:ℝ) < 32 * c * (2:ℝ)^((g:ℝ)) * (((m:ℝ))+1) * ((v:ℝ)+1) := by
    have hA : (0:ℝ) < ((m:ℝ)+1) := by positivity
    have hB : (0:ℝ) < ((v:ℝ)+1) := by positivity
    positivity
  have h6 : (0:ℝ) < (N:ℝ)^6 := by positivity
  rw [div_le_div_iff₀ h6 hden]
  have hmain : 32 * c * (2:ℝ)^((g:ℝ)) * (((m:ℝ))+1) * ((v:ℝ)+1) ≤ (N:ℝ)^6 := by
    have h1 : ((m:ℝ)+1) * ((v:ℝ)+1) ≤ 4 * (N:ℝ)^2 := by nlinarith
    calc 32 * c * (2:ℝ)^((g:ℝ)) * (((m:ℝ))+1) * ((v:ℝ)+1)
        = 32 * c * (2:ℝ)^((g:ℝ)) * (((m:ℝ)+1) * ((v:ℝ)+1)) := by ring
      _ ≤ 32 * c * (2:ℝ)^((g:ℝ)) * (4 * (N:ℝ)^2) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ (N:ℝ)^6 := by nlinarith [hN, hNpos]
  nlinarith [hmain, hG]

/-- The abstract Step-6 instance: under the instance bridge
`c·2^{γm} = K₀·N²` (instance data — the DS parameterization of (F4) against
the paper's absolute `K₀`), the concrete display transfers into B3's abstract
`hstep5` form, and the per-trial probability beats `2^{−g_M}·N^{−6}`.  This
is where B3's `lem_A5_product` and `lem_A5_threshold` are consumed. -/
theorem step6_pr_ge_threshold {G K₀ c Q Pr : ℝ} {g m v N : ℕ} (hG : 0 < G) (hK₀ : 1 ≤ K₀)
    (hN1 : 1 ≤ N) (hm : m ≤ N) (hv : v ≤ N) (hN : 128 * K₀ ≤ (N:ℝ)^2)
    (hbridge : c * (2:ℝ)^((g:ℝ)) = K₀ * (N:ℝ)^2)
    (hQ : G / (2 * ((v:ℝ)+1)) ≤ Q)
    (htr : (1/(((m:ℝ))+1)) * (1/2) * Q / (8 * c * (2:ℝ)^((g:ℝ))) ≤ Pr) :
    G / (N:ℝ)^6 ≤ Pr := by
  have hbridge' : 8 * c * (2:ℝ)^((g:ℝ)) = 8 * (K₀ * (N:ℝ)^2) := by
    rw [mul_assoc (8:ℝ) c ((2:ℝ)^((g:ℝ))), hbridge]
  rw [hbridge', ← mul_assoc (8:ℝ) K₀ ((N:ℝ)^2)] at htr
  have hprod := lem_A5_product (G := G) (K₀ := K₀) (Q := Q) (m := m) (v := v) hG hK₀ hQ
  have hthr := lem_A5_threshold (G := G) (K₀ := K₀) hG hK₀ hN1 hm hv hN
  have hN2 : (0:ℝ) < (N:ℝ) ^ 2 := by positivity
  have h2 : G / (32 * K₀ * ((m:ℝ) + 1) * ((v:ℝ) + 1)) / (N:ℝ) ^ 2
      ≤ ((1 / ((m:ℝ) + 1)) * (1 / 2) * Q / (8 * K₀)) / (N:ℝ) ^ 2 :=
    div_le_div_of_nonneg_right hprod (le_of_lt hN2)
  calc G / (N:ℝ) ^ 6
      ≤ G / (32 * K₀ * (N:ℝ) ^ 2 * ((m:ℝ) + 1) * ((v:ℝ) + 1)) := hthr
    _ = G / (32 * K₀ * ((m:ℝ) + 1) * ((v:ℝ) + 1)) / (N:ℝ) ^ 2 := by
        field_simp
        try ring
    _ ≤ ((1 / ((m:ℝ) + 1)) * (1 / 2) * Q / (8 * K₀)) / (N:ℝ) ^ 2 := h2
    _ = (1 / ((m:ℝ) + 1)) * (1 / 2) * Q / (8 * K₀ * (N:ℝ) ^ 2) := by
        field_simp
        try ring
    _ ≤ Pr := htr

/-! ### Corollary A6 — the e^{−n} coverage union bound -/

/-- Corollary A6's engine, extracted and generalized from B3's
`cor_A6_per_alias` (whose internal chain this reproduces): `T` trials with
per-trial hit probability `p ∈ [0,1]` miss with probability at most
`e^{−pT}` — the paper's «(1 − 2^{−g_M}n^{−6})^T ≤ e^{−n}» before the count
input.  `cor_A6_per_alias` remains the statement-of-record for the `Tp ≥ 1`
instance. -/
theorem exp_one_sub_pow_le {p : ℝ} {T : ℕ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) ^ T ≤ Real.exp (-((T:ℝ) * p)) := by
  have h0 : (0:ℝ) ≤ 1 - p := by linarith
  have h1 : 1 - p ≤ Real.exp (-p) := Real.one_sub_le_exp_neg p
  have h2 : (1 - p) ^ T ≤ (Real.exp (-p)) ^ T := pow_le_pow_left₀ h0 h1 T
  have h3 : (Real.exp (-p)) ^ T = Real.exp (-((T:ℝ) * p)) := by
    rw [← Real.exp_nat_mul]
    ring_nf
  exact le_trans h2 (le_of_eq h3)

/-- Corollary A6's miss bound: `T` trials with per-trial probability `p` and
`Tp ≥ n` miss a fixed alias with probability at most `e^{−n}`. -/
theorem cor_A6_miss_le {p : ℝ} {T n : ℕ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hTp : (n:ℝ) ≤ (T:ℝ) * p) :
    (1 - p) ^ T ≤ Real.exp (-((n:ℝ))) := by
  have h := exp_one_sub_pow_le (T := T) hp0 hp1
  exact le_trans h (Real.exp_le_exp.mpr (by linarith))

end SubsetSumL25
