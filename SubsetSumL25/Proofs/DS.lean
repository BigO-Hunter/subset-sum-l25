/-
M2-core (D_s): the alias-class dictionary's mathematical core — the
statement-of-record.  Sources and the milestone ladder live in
`Statements/DS.lean`.  The exec machinery (balanced trees, sorting, the op
cap) is abstracted to a Finset of key-triples per the D7 boundary: the
procedure statements stay named.

Cast-discipline: the arithmetic is ℤ-natural throughout; no cast injection.
-/
import Mathlib
import SubsetSumL25.Statements.DS
import SubsetSumL25.Statements.Defs
open scoped symmDiff

namespace SubsetSumL25

variable {n : ℕ}

/-! ### §5.2 — signed weights and keys -/

/-- The signed weights (§5.2): `w^F_i = (−1)^{[i∈F]} w_i`. -/
def sgnW (w : Fin n → ℤ) (F : Finset (Fin n)) (i : Fin n) : ℤ :=
  if i ∈ F then -w i else w i

/-- (5.1): `w^F(Z) = w(Z ∆ F) − w(F)` for every `Z` — the identity the
trial walk (Lemma A5 Step 5) uses to convert reduced sums into unreduced
ones. -/
theorem subsum_sgnW_eq (w : Fin n → ℤ) (F Z : Finset (Fin n)) :
    ∑ i ∈ Z, sgnW w F i = subsum w (Z ∆ F) - subsum w F := by
  classical
  have hdisj1 : Disjoint (Z \ F) (Z ∩ F) := by
    rw [Finset.disjoint_left]
    intro i hi hmem
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_inter.mp hmem).2
  have hdisj2 : Disjoint (Z \ F) F := by
    rw [Finset.disjoint_left]
    intro i hi hmem
    exact (Finset.mem_sdiff.mp hi).2 hmem
  have hdisj3 : Disjoint (Z \ F) (F \ Z) := by
    rw [Finset.disjoint_left]
    intro i hi hmem
    exact (Finset.mem_sdiff.mp hmem).2 (Finset.mem_sdiff.mp hi).1
  have hdisj4 : Disjoint (Z ∩ F) (F \ Z) := by
    rw [Finset.disjoint_left]
    intro i hi hmem
    exact (Finset.mem_sdiff.mp hmem).2 (Finset.mem_inter.mp hi).1
  have h1 : ∑ i ∈ Z \ F, sgnW w F i = ∑ i ∈ Z \ F, w i :=
    Finset.sum_congr rfl fun i hi => by
      have hiF : i ∉ F := (Finset.mem_sdiff.mp hi).2
      rw [sgnW, if_neg hiF]
  have h2 : ∑ i ∈ Z ∩ F, sgnW w F i = -∑ i ∈ Z ∩ F, w i := by
    have h2' : ∑ i ∈ Z ∩ F, sgnW w F i = ∑ i ∈ Z ∩ F, (-w i) :=
      Finset.sum_congr rfl fun i hi => by
        rw [sgnW, if_pos (Finset.mem_inter.mp hi).2]
    rw [h2', Finset.sum_neg_distrib]
  have hstepL : ∑ i ∈ Z, sgnW w F i
      = ∑ i ∈ Z \ F, w i - ∑ i ∈ Z ∩ F, w i := by
    have hmem : (Z \ F) ∪ (Z ∩ F) = Z := by
      ext i; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
      by_cases hF : i ∈ F <;> simp [hF]
    conv_lhs => rw [← hmem]
    rw [Finset.sum_union hdisj1, h1, h2, sub_eq_add_neg]
  have hkey : subsum w (Z ∆ F) - subsum w F
      = ∑ i ∈ Z \ F, w i - ∑ i ∈ Z ∩ F, w i := by
    show (Z ∆ F).sum w - F.sum w = (Z \ F).sum w - (Z ∩ F).sum w
    have hun : Z ∆ F = (Z \ F) ∪ (F \ Z) := by
      rw [Finset.symmDiff_def]
    have hFsplit : F.sum w = (Z ∩ F).sum w + (F \ Z).sum w := by
      have hFmem : F = (Z ∩ F) ∪ (F \ Z) := by
        ext i
        rw [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
        by_cases hZ : i ∈ Z
        · refine ⟨fun h => Or.inl ⟨hZ, h⟩, ?_⟩
          rintro (⟨_, h⟩ | ⟨h, _⟩)
          · exact h
          · exact h
        · refine ⟨fun h => Or.inr ⟨h, hZ⟩, ?_⟩
          rintro (⟨hz, h⟩ | ⟨h, _⟩)
          · exact absurd hz hZ
          · exact h
      conv_lhs => rw [hFmem]
      rw [Finset.sum_union hdisj4]
    conv_lhs => lhs; rw [hun]
    rw [Finset.sum_union hdisj3, hFsplit]
    ring
  rw [hstepL, hkey]

/-- The key of a set (§5.2): `κ(A) = (c(A), b(A))`. -/
def keyOf (c b : Fin n → ℤ) (A : Finset (Fin n)) : ℤ × ℤ :=
  (subsum c A, subsum b A)

/-- The key-value (§5.2): `Φ_S(κ) = Σ_{A ⊆ S, κ(A) = κ} χ(A)` — «store each
distinct key once with Φ_L(κ) = Σ_{A⊆L: κ(A)=κ} χ(A)». -/
noncomputable def phi (χ : Finset (Fin n) → ℂ) (c b : Fin n → ℤ)
    (S : Finset (Fin n)) (κ : ℤ × ℤ) : ℂ :=
  ∑ A ∈ S.powerset.filter (fun A => keyOf c b A = κ), χ A

/-- The class of `(κ_L, κ_R, Z)` (§5.3): all `A ∪ Z ∪ B` with `A ⊆ L`,
`B ⊆ R`, `κ(A) = κ_L`, `κ(B) = κ_R`.  In the procedure `L`, `R`, `Z` are
pairwise disjoint (`Z ⊆ M`, `M ∩ L = M ∩ R = ∅`, `L ∩ R = ∅`). -/
noncomputable def cls (c b : Fin n → ℤ) (L R : Finset (Fin n))
    (κL κR : ℤ × ℤ) (Z : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  ((L.powerset.filter (fun A => keyOf c b A = κL)).product
    (R.powerset.filter (fun B => keyOf c b B = κR))).image
    (fun p => p.1 ∪ Z ∪ p.2)

/-- Alias of `t_s` (§5.3): `b(I) = T_{s,q}`, `c(I) ≡ b(I) (mod P)`, and
`c(I) ≠ t_s` — «either every member is an alias of t_s or none is». -/
def IsAlias (P : ℕ) (T ts : ℤ) (c b : Fin n → ℤ) (I : Finset (Fin n)) : Prop :=
  subsum b I = T ∧ subsum c I % P = subsum b I % P ∧ subsum c I ≠ ts

/-- The class of `(κ_L, κ_R, Z)` is an alias class (§5.3): every member is
an alias. -/
def IsAliasClass (P : ℕ) (T ts : ℤ) (c b : Fin n → ℤ)
    (K : Finset (Finset (Fin n))) : Prop :=
  ∀ I ∈ K, IsAlias P T ts c b I

/-! ### §5.3 — the member-shared-key lemma and the A1 transfer

DS-M1.5 (the first proof target of the next session): the Finset plumbing for
`subsum_eq_of_mem_cls` (all members of a class share their (c, b)-sums once
`L`, `R`, `Z` are pairwise disjoint) and `isAliasClass_of_mem_alias`
(Lemma A1's class-level transfer: one alias member ⇒ the class is an alias
class).  The statements are fixed; the Finset obtain-chains fight the
powerset-product memberships and are deferred with the ledger note in
`Statements/DS.lean`.

-/

/-! ### §5.3 — members of a class share their key -/

/-- All members of a class have the same `c`- and `b`-sums (§5.3: «All
members of a class have the same c(I) and the same b(I)») — the sums factor
through the class key and `Z` once `L`, `R`, `Z` are pairwise disjoint. -/
theorem subsum_eq_of_mem_cls (L R Z : Finset (Fin n)) (hlz : Disjoint L Z)
    (hrz : Disjoint R Z) (hlr : Disjoint L R) {c b : Fin n → ℤ}
    {κL κR : ℤ × ℤ} {I : Finset (Fin n)}
    (hI : I ∈ cls c b L R κL κR Z) :
    subsum c I = κL.1 + subsum c Z + κR.1 ∧ subsum b I = κL.2 + subsum b Z + κR.2 := by
  rw [cls, Finset.mem_image] at hI
  obtain ⟨p, hp⟩ := hI
  obtain ⟨hA, hB⟩ := Finset.mem_product.mp hp.1
  obtain ⟨hAp, hAc⟩ := Finset.mem_filter.mp hA
  obtain ⟨hBp, hBc⟩ := Finset.mem_filter.mp hB
  rw [← hp.2]
  have hAL : p.1 ⊆ L := Finset.mem_powerset.mp hAp
  have hBR : p.2 ⊆ R := Finset.mem_powerset.mp hBp
  have hAz : Disjoint p.1 Z := hlz.mono_left hAL
  have hBz : Disjoint p.2 Z := hrz.mono_left hBR
  have hApB : Disjoint p.1 p.2 := hlr.mono hAL hBR
  have hAzB : Disjoint (p.1 ∪ Z) p.2 := by
    rw [Finset.disjoint_left]
    intro x hx hb
    rcases Finset.mem_union.1 hx with hx' | hx'
    · exact Finset.disjoint_left.mp hApB hx' hb
    · exact Finset.disjoint_left.mp hBz hb hx'
  have hsum : subsum c (p.1 ∪ Z ∪ p.2) = subsum c p.1 + subsum c Z + subsum c p.2 := by
    simp only [subsum, Finset.sum_union hAzB, Finset.sum_union hAz]
  have hsumb : subsum b (p.1 ∪ Z ∪ p.2) = subsum b p.1 + subsum b Z + subsum b p.2 := by
    simp only [subsum, Finset.sum_union hAzB, Finset.sum_union hAz]
  have hc1 : subsum c p.1 = κL.1 := congrArg Prod.fst hAc
  have hb1 : subsum b p.1 = κL.2 := congrArg Prod.snd hAc
  have hc2 : subsum c p.2 = κR.1 := congrArg Prod.fst hBc
  have hb2 : subsum b p.2 = κR.2 := congrArg Prod.snd hBc
  exact ⟨by rw [hsum, hc1, hc2], by rw [hsumb, hb1, hb2]⟩

/-- Lemma A1's content, class-level (§5.3: «either every member is an alias
of t_s or none is»): if one member of the class is an alias, the class is an
alias class. -/
theorem isAliasClass_of_mem_alias (L R Z : Finset (Fin n)) (hlz : Disjoint L Z)
    (hrz : Disjoint R Z) (hlr : Disjoint L R) {c b : Fin n → ℤ}
    {κL κR : ℤ × ℤ} {I : Finset (Fin n)}
    {P : ℕ} {T ts : ℤ} (hI : I ∈ cls c b L R κL κR Z)
    (hIA : IsAlias P T ts c b I) :
    IsAliasClass P T ts c b (cls c b L R κL κR Z) := by
  obtain ⟨hIc, hIb⟩ := subsum_eq_of_mem_cls L R Z hlz hrz hlr hI
  intro J hJ
  obtain ⟨hJc, hJb⟩ := subsum_eq_of_mem_cls L R Z hlz hrz hlr hJ
  refine ⟨?_, ?_, ?_⟩
  · rw [hJb, ← hIb]; exact hIA.1
  · rw [hJc, ← hIc, hJb, ← hIb]; exact hIA.2.1
  · rw [hJc, ← hIc]; exact hIA.2.2

/-! ### (5.2) — the class-sum identity (DS-M1's closing piece)

The per-term χ-split (χ (A ∪ Z ∪ B) = χ A · χ Z · χ B for A ⊆ L, B ⊆ R,
from the χ-multiplicativity + the pairwise disjointness) was this session's
target: the `Finset.union_assoc` reassociation + the two hχ-instantiations
land, but the mono_right/mono_left slot-elaboration on the disjointness
transports fought the unifier past budget.  Battle-notes for the next
session: the A-side transport needs `Disjoint.mono_left hAL hlz` FIRST
(composing the A-narrowing before the t-widening); the B-side is
`(hrz.mono_left hBR).symm`; the t-widening subset is
`(Finset.subset_union_left : Z ⊆ Z ∪ B)` with its type ascription EXACTLY
`Z ⊆ Z ∪ B` (the unifier determines the t'-slot from the outer hχ only
after the Disjoint-arg is pinned).  After the per-term split: the
`Finset.sum_product` assembly over the pair-set with the union-map's
injectivity (recover `A = (I \ Z) ∩ L`), then the D_s closure corollary.

-/

end SubsetSumL25
