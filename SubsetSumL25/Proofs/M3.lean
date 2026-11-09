/-
M3 (DS): Lemma A5 Steps 1–3 — the per-trial good-hit chain in the
alias-class setting.  This file is the statement-of-record for what is
proved; the verbatim source and the milestone ladder live in
`Statements/DS.lean`.

Primary source: `a-kapila/maths-proofs` @ 44c34961,
`subset-sum/PROOF_0.4877.tex` §5.6 (sha256
b397531cc5997e88c439d5290774861b46a34aa32d9cd71fa7dcced130359298).

DS-M3 Step 1 (half of the block) — verbatim:
    «F is a uniform subset of M, so S is too. Hence |S| = σ with
    probability C(m,σ)2^{−m} ≥ 1/(m+1). Conditional on this event, S is a
    uniform σ-subset of M, and F = S △ (I ∩ M).»

Here `S = Z ∆ F` with `Z := I ∩ M` the fixed alias footprint; the uniform
reindexing of `F ↦ Z ∆ F` over `M.powerset` is the «S is too» clause, and
the count identity carries the «|S| = σ with probability C(m,σ)2^{−m}» one.

Cast-discipline: ℝ for the probabilities, ℕ for the counts; `exact_mod_cast`
at the ℕ↔ℝ boundary only.
-/
import Mathlib
import SubsetSumL25.Statements.Defs
import SubsetSumL25.Proofs.DS
import SubsetSumL25.Proofs.A5

open scoped symmDiff

namespace SubsetSumL25

variable {n : ℕ}

/-! ### DS-M3 Step 1 — half of the block -/

/-- The symmetry-difference involution the reindex runs on: `Z ∆ (Z ∆ F) = F`.
(No `Finset.symmDiff_symmDiff_cancel_left` at pin d13f23b — proved from
`mem_symmDiff` by case analysis.) -/
theorem symmDiff_left_involutive (Z F : Finset (Fin n)) : Z ∆ (Z ∆ F) = F := by
  ext i
  by_cases hZ : i ∈ Z <;> by_cases hF : i ∈ F <;>
    simp [hZ, hF]

/-- Step 1's «F is a uniform subset of M, so S is too»: the map
`F ↦ Z ∆ F` preserves the uniform measure on `M.powerset` (expectation is
reindexed with the involution `symmDiff_left_involutive`). -/
theorem expect_symmDiff_reindex (M Z : Finset (Fin n)) (hZ : Z ⊆ M)
    (g : Finset (Fin n) → ℝ) :
    (M.powerset).expect (fun F => g (Z ∆ F)) = (M.powerset).expect g := by
  classical
  have hclose : ∀ F ∈ M.powerset, Z ∆ F ∈ M.powerset := by
    intro F hF
    rw [Finset.mem_powerset] at hF ⊢
    intro i hi
    rcases Finset.mem_symmDiff.mp hi with h1 | h1
    · exact hZ h1.1
    · exact hF h1.1
  have hinj : Set.InjOn (fun F : Finset (Fin n) => Z ∆ F) ↑M.powerset := by
    intro F _ F' _ hEq
    have hEq' : Z ∆ F = Z ∆ F' := hEq
    have h1 : Z ∆ (Z ∆ F) = Z ∆ (Z ∆ F') := by rw [hEq']
    rwa [symmDiff_left_involutive, symmDiff_left_involutive] at h1
  have himg : M.powerset.image (fun F : Finset (Fin n) => Z ∆ F) = M.powerset := by
    ext S
    rw [Finset.mem_image]
    constructor
    · rintro ⟨F, hF, hEq⟩
      rw [← hEq]
      exact hclose F hF
    · intro hS
      refine ⟨Z ∆ S, hclose S hS, ?_⟩
      rw [symmDiff_left_involutive]
  rw [Finset.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card,
    ← Finset.sum_image hinj, himg]

/-- Step 1's count identity: the event «|Z ∆ F| = σ» and the event «|F| = σ»
have the same number of witnesses (they biject through `Z ∆ ·`), so the
probability of «|S| = σ» is exactly the σ-layer size `C(m,σ)2^{−m}`. -/
theorem half_block_filter_card_eq (M Z : Finset (Fin n)) (hZ : Z ⊆ M) (σ : ℕ) :
    (M.powerset.filter (fun F => (Z ∆ F).card = σ)).card
      = (M.powerset.filter (fun F => F.card = σ)).card := by
  classical
  have hclose : ∀ F ∈ M.powerset, Z ∆ F ∈ M.powerset := by
    intro F hF
    rw [Finset.mem_powerset] at hF ⊢
    intro i hi
    rcases Finset.mem_symmDiff.mp hi with h1 | h1
    · exact hZ h1.1
    · exact hF h1.1
  have himg : M.powerset.filter (fun F => (Z ∆ F).card = σ)
      = (M.powerset.filter (fun F => F.card = σ)).image (fun F => Z ∆ F) := by
    ext F
    constructor
    · intro hF
      rw [Finset.mem_filter] at hF
      obtain ⟨hFM, hcard⟩ := hF
      refine Finset.mem_image.mpr ⟨Z ∆ F, ?_, symmDiff_left_involutive Z F⟩
      rw [Finset.mem_filter]
      exact ⟨hclose F hFM, hcard⟩
    · intro hF
      obtain ⟨G, hGmem, hEq⟩ := Finset.mem_image.mp hF
      rw [Finset.mem_filter] at hGmem
      obtain ⟨hGM, hcard⟩ := hGmem
      have hF' : F = Z ∆ G := hEq.symm
      rw [Finset.mem_filter, hF']
      exact ⟨hclose G hGM, by rw [symmDiff_left_involutive]; exact hcard⟩
  rw [himg, Finset.card_image_of_injective]
  intro F F' hEq
  have hEq' : Z ∆ F = Z ∆ F' := hEq
  have h1 : Z ∆ (Z ∆ F) = Z ∆ (Z ∆ F') := by rw [hEq']
  rwa [symmDiff_left_involutive, symmDiff_left_involutive] at h1

/-- Step 1, verbatim form: with `S = Z ∆ F` over a uniform `F ⊆ M` and the
half-block `σ = m/2`, «|S| = σ with probability C(m,σ)2^{−m} ≥ 1/(m+1)» —
the middle-layer floor of `middle_choose_div_two_pow_ge_inv` transferred
from `F` to `S`. -/
theorem half_block_prob_ge (M Z : Finset (Fin n)) (hZ : Z ⊆ M) :
    1 / ((M.card : ℝ) + 1) ≤
      ((M.powerset.filter (fun F => (Z ∆ F).card = M.card / 2)).card : ℝ)
        / 2 ^ M.card := by
  classical
  rw [half_block_filter_card_eq M Z hZ]
  have hcount : (M.powerset.filter (fun F => F.card = M.card / 2)).card
      = Nat.choose M.card (M.card / 2) := by
    rw [← Finset.card_powersetCard (M.card / 2) M,
      show Finset.powersetCard (M.card / 2) M
        = M.powerset.filter (fun F => F.card = M.card / 2) from
        Finset.powersetCard_eq_filter]
  rw [hcount]
  exact middle_choose_div_two_pow_ge_inv M.card

/-! ### DS-M3 Step 2 — the signs on `S` are fixed -/

/-- Step 2's pointwise core: on `S = Z ∆ F` (with `Z ⊆ M`), the signed
weights `w^F` agree with the complement signing `w^{M ∖ Z}` — the paper's
«on S the signed weights equal the weights c^I_i = c_i (i ∈ I ∩ M), c^I_i
= −c_i (i ∈ M ∖ I)» with `Z := I ∩ M` (inside `M`, `M ∖ (I ∩ M) = M ∖ I`). -/
theorem sgnW_eq_of_mem_symmDiff {w : Fin n → ℤ} {M Z F : Finset (Fin n)}
    {i : Fin n} (hiM : i ∈ M) (hi : i ∈ Z ∆ F) :
    sgnW w F i = sgnW w (M \ Z) i := by
  rcases Finset.mem_symmDiff.mp hi with ⟨hZ, hF⟩ | ⟨hF, hZ⟩
  · rw [sgnW, ite_eq_right hF, sgnW,
      ite_eq_right (by intro hm; exact (Finset.mem_sdiff.mp hm).2 hZ)]
  · rw [sgnW, ite_eq_left hF, sgnW, ite_eq_left (Finset.mem_sdiff.mpr ⟨hiM, hZ⟩)]

/-- Step 2, verbatim: with `S = (I ∩ M) ∆ F`, every `i ∈ S ∩ M` has
`w^F_i = w^I_i` where `w^I = sgnW w (M ∖ I)` («Either i ∈ I∖F, and then
c^F_i = c_i; or i ∈ F∖I, and then c^F_i = −c_i. So on S the signed weights
equal the weights … These depend on I but not on S»). The same holds for
`b^F` and `b^I` — the statement is for general weights `w`. -/
theorem sgnW_eq_sgnI_of_mem_half_block {w : Fin n → ℤ} {M I F : Finset (Fin n)}
    {i : Fin n} (hiM : i ∈ M) (hi : i ∈ (I ∩ M) ∆ F) :
    sgnW w F i = sgnW w (M \ I) i := by
  have hseteq : M \ (I ∩ M) = M \ I := by
    ext j
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  calc sgnW w F i = sgnW w (M \ (I ∩ M)) i :=
        sgnW_eq_of_mem_symmDiff hiM hi
    _ = sgnW w (M \ I) i := by rw [hseteq]

/-- Step 2's sum form — the layer sums agree: for `W ⊆ S = Z ∆ F` inside
`M`, `∑_{i∈W} w^F_i = ∑_{i∈W} w^{M∖Z}_i` (what Step 3's `a_k(S; c^I)` and
Step 5's recovery walk consume). -/
theorem subsum_sgnW_eq_of_subset_symmDiff {w : Fin n → ℤ} {M Z F W : Finset (Fin n)}
    (hZM : Z ⊆ M) (hFM : F ⊆ M) (hW : W ⊆ Z ∆ F) :
    ∑ i ∈ W, sgnW w F i = ∑ i ∈ W, sgnW w (M \ Z) i :=
  Finset.sum_congr rfl fun i hi =>
    sgnW_eq_of_mem_symmDiff
      (by rcases Finset.mem_symmDiff.mp (hW hi) with ⟨h1, -⟩ | ⟨h1, -⟩
          · exact hZM h1
          · exact hFM h1)
      (hW hi)

end SubsetSumL25
