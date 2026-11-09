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

/-! ### (5.2) — the class-sum identity (DS-M1's closing piece) -/

/-- The per-term χ-split: for `A ⊆ L`, `B ⊆ R`, the phase of `A ∪ Z ∪ B`
factors as `χ A · χ Z · χ B` (phases add over disjoint unions). -/
theorem chi_split (hlz : Disjoint L Z) (hrz : Disjoint R Z)
    (hlr : Disjoint L R) {χ : Finset (Fin n) → ℂ}
    (hχ : ∀ A B : Finset (Fin n), Disjoint A B → χ (A ∪ B) = χ A * χ B)
    {A B : Finset (Fin n)} (hAL : A ⊆ L) (hBR : B ⊆ R) :
    χ (A ∪ Z ∪ B) = χ A * χ Z * χ B := by
  have hAzB : Disjoint A (Z ∪ B) := by
    rw [Finset.disjoint_left]
    intro x hx hb
    rcases Finset.mem_union.1 hb with h | h
    · exact Finset.disjoint_left.mp hlz (hAL hx) h
    · exact Finset.disjoint_left.mp hlr (hAL hx) (hBR h)
  rw [show A ∪ Z ∪ B = A ∪ (Z ∪ B) from Finset.union_assoc A Z B,
    hχ A (Z ∪ B) hAzB,
    hχ Z B (hrz.mono_left hBR).symm]
  ring

/-! ### The union-map recoveries (DS-M1.6) -/

/-- Recovery A: `A` is recoverable from the union-map's value by the
pairwise disjointness — the `A`-side of the injectivity. -/
theorem recovery_A {A B L R Z : Finset (Fin n)} (hlz : Disjoint L Z)
    (hlr : Disjoint L R) (hAL : A ⊆ L) (hBR : B ⊆ R) :
    A = ((A ∪ Z ∪ B) \ Z) ∩ L := by
  refine Finset.ext fun i => ⟨fun h => ?_, fun h => ?_⟩
  · refine Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨?_, ?_⟩, hAL h⟩
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl h)))
    · exact Finset.disjoint_left.mp hlz (hAL h)
  · obtain ⟨h₁, h₃⟩ := Finset.mem_inter.mp h
    obtain ⟨h₄, h₅⟩ := Finset.mem_sdiff.mp h₁
    rcases Finset.mem_union.mp h₄ with h' | h'
    · rcases Finset.mem_union.mp h' with h'' | h''
      · exact h''
      · exact absurd h'' (Finset.disjoint_left.mp hlz h₃)
    · exact absurd (hBR h') (Finset.disjoint_left.mp hlr h₃)

/-- Recovery B: `B` is recoverable from the union-map's value by the
pairwise disjointness — the `B`-side of the injectivity. -/
theorem recovery_B {A B L R Z : Finset (Fin n)} (hlz : Disjoint L Z)
    (hrz : Disjoint R Z) (hlr : Disjoint L R) (hAL : A ⊆ L) (hBR : B ⊆ R) :
    B = ((A ∪ Z ∪ B) \ Z) ∩ R := by
  refine Finset.ext fun i => ⟨fun h => ?_, fun h => ?_⟩
  · refine Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨?_, ?_⟩, hBR h⟩
    · exact Finset.mem_union.mpr (Or.inr h)
    · exact Finset.disjoint_left.mp hrz (hBR h)
  · obtain ⟨h₁, h₃⟩ := Finset.mem_inter.mp h
    obtain ⟨h₄, h₅⟩ := Finset.mem_sdiff.mp h₁
    rcases Finset.mem_union.mp h₄ with h' | h'
    · rcases Finset.mem_union.mp h' with h'' | h''
      · exact (Finset.disjoint_left.mp hlr (hAL h'') h₃).elim
      · exact absurd h'' h₅
    · exact h'

/-- The bridge between the two product spellings: `cls`'s body writes the
dot-notation `Finset.product`, while Mathlib's `×ˢ` notation (and hence
`Finset.sum_product` and friends) elaborates to the generic `SProd.sprod`
instance wrapper. The two are definitionally equal, but `rw`'s pattern
matcher works at reducible transparency and cannot see through the wrapper —
this `rfl`-lemma makes the alignment explicit for the rewrites below. -/
theorem finset_product_eq_sprod {α β : Type} (s : Finset α) (t : Finset β) :
    Finset.product s t = s ×ˢ t := rfl

/-! ### (5.2) — the union-map injectivity and the class-sum identity -/

/-- The union map of the class construction is injective on the filtered
product of the `κ`-consistent subsets: `(A ∪ Z ∪ B)` determines `(A, B)` once
`L`, `R`, `Z` are pairwise disjoint (the two recoveries, assembled).  This is
the `Set.InjOn` side-condition of `Finset.sum_image` in (5.2), stated at fully
concrete types — the standalone statement survives the `rw` elaboration order
where an inline by-proof (elaborated against `Set.InjOn ?g ↑?s` before goal
unification) cannot. -/
theorem cls_union_injOn (hlz : Disjoint L Z) (hrz : Disjoint R Z) (hlr : Disjoint L R)
    {c b : Fin n → ℤ} {κL κR : ℤ × ℤ} :
    Set.InjOn (fun p : Finset (Fin n) × Finset (Fin n) => p.1 ∪ Z ∪ p.2)
      ((L.powerset.filter (fun A => keyOf c b A = κL)).product
        (R.powerset.filter (fun B => keyOf c b B = κR))) := by
  rintro ⟨A₁, B₁⟩ h₁ ⟨A₂, B₂⟩ h₂ heq
  have h₁' : A₁ ∈ L.powerset.filter (fun A => keyOf c b A = κL)
      ∧ B₁ ∈ R.powerset.filter (fun B => keyOf c b B = κR) := Finset.mem_product.mp h₁
  have h₂' : A₂ ∈ L.powerset.filter (fun A => keyOf c b A = κL)
      ∧ B₂ ∈ R.powerset.filter (fun B => keyOf c b B = κR) := Finset.mem_product.mp h₂
  obtain ⟨hAp₁, -⟩ := Finset.mem_filter.mp h₁'.1
  obtain ⟨hBp₁, -⟩ := Finset.mem_filter.mp h₁'.2
  obtain ⟨hAp₂, -⟩ := Finset.mem_filter.mp h₂'.1
  obtain ⟨hBp₂, -⟩ := Finset.mem_filter.mp h₂'.2
  have hA₁L : A₁ ⊆ L := Finset.mem_powerset.mp hAp₁
  have hB₁R : B₁ ⊆ R := Finset.mem_powerset.mp hBp₁
  have hA₂L : A₂ ⊆ L := Finset.mem_powerset.mp hAp₂
  have hB₂R : B₂ ⊆ R := Finset.mem_powerset.mp hBp₂
  have hA₁ := recovery_A hlz hlr hA₁L hB₁R
  have hA₂ := recovery_A hlz hlr hA₂L hB₂R
  have hB₁ := recovery_B hlz hrz hlr hA₁L hB₁R
  have hB₂ := recovery_B hlz hrz hlr hA₂L hB₂R
  rw [show A₁ ∪ Z ∪ B₁ = A₂ ∪ Z ∪ B₂ from heq] at hA₁ hB₁
  exact Prod.ext (hA₁.trans hA₂.symm) (hB₁.trans hB₂.symm)

/-- (5.2): the class-sum identity — the phase-sum over a class factors as
`Φ_L(κ_L)·Φ_R(κ_R)·χ(Z)` («Since phases add, Σ_{I ∈ C} χ(I) =
Φ_L Φ_R χ_Z»). -/
theorem class_sum_eq (hlz : Disjoint L Z) (hrz : Disjoint R Z)
    (hlr : Disjoint L R) {χ : Finset (Fin n) → ℂ}
    (hχ : ∀ A B : Finset (Fin n), Disjoint A B → χ (A ∪ B) = χ A * χ B)
    {κL κR : ℤ × ℤ} :
    ∑ I ∈ cls c b L R κL κR Z, χ I
      = phi χ c b L κL * phi χ c b R κR * χ Z := by
  classical
  rw [cls, Finset.sum_image (f := χ) (cls_union_injOn hlz hrz hlr),
    finset_product_eq_sprod]
  rw [Finset.sum_product
    (f := fun p : Finset (Fin n) × Finset (Fin n) => χ (p.1 ∪ Z ∪ p.2))]
  rw [phi, phi]
  rw [Finset.sum_congr rfl fun A hAs => Finset.sum_congr rfl fun B hBt =>
    chi_split hlz hrz hlr hχ
      (Finset.mem_powerset.mp (Finset.mem_filter.mp hAs).1)
      (Finset.mem_powerset.mp (Finset.mem_filter.mp hBt).1)]
  rw [← Finset.sum_mul_sum _ _ (fun A => χ A * χ Z) χ, ← Finset.sum_mul]
  ring

/-! ### The partition machinery and the D_s closure -/

/-- The key-triple of a class is unique: the pairwise disjointness of
`L`, `R`, `Z ⊆ M`, `M ⊥ L`, `M ⊥ R` makes the union-map canonical
(`A = I ∩ L`, `B = I ∩ R`, `Z = I \ (L ∪ R)`), so the same `I` cannot lie
in two classes with distinct keys. -/
theorem mem_cls_key_unique (hlr : Disjoint L R) (hLm : Disjoint L M)
    (hRm : Disjoint R M) {c b : Fin n → ℤ} {Z Z' : Finset (Fin n)}
    (hZm : Z ⊆ M) (hZ'm : Z' ⊆ M)
    {κL κR κL' κR' : ℤ × ℤ} {I : Finset (Fin n)}
    (hI : I ∈ cls c b L R κL κR Z) (hI' : I ∈ cls c b L R κL' κR' Z') :
    κL = κL' ∧ κR = κR' ∧ Z = Z' := by
  classical
  rw [cls, Finset.mem_image] at hI hI'
  obtain ⟨p, hp⟩ := hI
  obtain ⟨q, hq⟩ := hI'
  obtain ⟨hA₁, hB₁⟩ := Finset.mem_product.mp hp.1
  obtain ⟨hA₂, hB₂⟩ := Finset.mem_product.mp hq.1
  obtain ⟨hA₁p, hA₁c⟩ := Finset.mem_filter.mp hA₁
  obtain ⟨hB₁p, hB₁c⟩ := Finset.mem_filter.mp hB₁
  obtain ⟨hA₂p, hA₂c⟩ := Finset.mem_filter.mp hA₂
  obtain ⟨hB₂p, hB₂c⟩ := Finset.mem_filter.mp hB₂
  have hAL₁ : p.1 ⊆ L := Finset.mem_powerset.mp hA₁p
  have hBR₁ : p.2 ⊆ R := Finset.mem_powerset.mp hB₁p
  have hAL₂ : q.1 ⊆ L := Finset.mem_powerset.mp hA₂p
  have hBR₂ : q.2 ⊆ R := Finset.mem_powerset.mp hB₂p
  have hIeq : I = p.1 ∪ Z ∪ p.2 := hp.2.symm
  have hIeq' : I = q.1 ∪ Z' ∪ q.2 := hq.2.symm
  have hZlr : Disjoint Z (L ∪ R) := by
    rw [Finset.disjoint_left]
    intro i hi hmem
    rcases Finset.mem_union.mp hmem with h | h
    · exact Finset.disjoint_left.mp hLm h (hZm hi)
    · exact Finset.disjoint_left.mp hRm h (hZm hi)
  have hZlr' : Disjoint Z' (L ∪ R) := by
    rw [Finset.disjoint_left]
    intro i hi hmem
    rcases Finset.mem_union.mp hmem with h | h
    · exact Finset.disjoint_left.mp hLm h (hZ'm hi)
    · exact Finset.disjoint_left.mp hRm h (hZ'm hi)
  have hAL : p.1 = I ∩ L := by
    refine Finset.ext fun i => ⟨fun h => Finset.mem_inter.mpr ⟨?_, hAL₁ h⟩, fun h => ?_⟩
    · rw [hIeq]; exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl h)))
    · obtain ⟨hIbig, hIL⟩ := Finset.mem_inter.mp h
      rw [hIeq] at hIbig
      rcases Finset.mem_union.mp hIbig with h | h
      · rcases Finset.mem_union.mp h with h | h
        · exact h
        · exact (Finset.disjoint_left.mp hLm hIL (hZm h)).elim
      · exact (Finset.disjoint_left.mp hlr hIL (hBR₁ h)).elim
  have hAL' : q.1 = I ∩ L := by
    refine Finset.ext fun i => ⟨fun h => Finset.mem_inter.mpr ⟨?_, hAL₂ h⟩, fun h => ?_⟩
    · rw [hIeq']; exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl h)))
    · obtain ⟨hIbig, hIL⟩ := Finset.mem_inter.mp h
      rw [hIeq'] at hIbig
      rcases Finset.mem_union.mp hIbig with h | h
      · rcases Finset.mem_union.mp h with h | h
        · exact h
        · exact (Finset.disjoint_left.mp hLm hIL (hZ'm h)).elim
      · exact (Finset.disjoint_left.mp hlr hIL (hBR₂ h)).elim
  have hBL : p.2 = I ∩ R := by
    refine Finset.ext fun i => ⟨fun h => Finset.mem_inter.mpr ⟨?_, hBR₁ h⟩, fun h => ?_⟩
    · rw [hIeq]; exact Finset.mem_union.mpr (Or.inr h)
    · obtain ⟨hIbig, hIR⟩ := Finset.mem_inter.mp h
      rw [hIeq] at hIbig
      rcases Finset.mem_union.mp hIbig with h | h
      · rcases Finset.mem_union.mp h with h | h
        · exact (Finset.disjoint_left.mp hlr (hAL₁ h) hIR).elim
        · exact (Finset.disjoint_left.mp hRm hIR (hZm h)).elim
      · exact h
  have hBL' : q.2 = I ∩ R := by
    refine Finset.ext fun i => ⟨fun h => Finset.mem_inter.mpr ⟨?_, hBR₂ h⟩, fun h => ?_⟩
    · rw [hIeq']; exact Finset.mem_union.mpr (Or.inr h)
    · obtain ⟨hIbig, hIR⟩ := Finset.mem_inter.mp h
      rw [hIeq'] at hIbig
      rcases Finset.mem_union.mp hIbig with h | h
      · rcases Finset.mem_union.mp h with h | h
        · exact (Finset.disjoint_left.mp hlr (hAL₂ h) hIR).elim
        · exact (Finset.disjoint_left.mp hRm hIR (hZ'm h)).elim
      · exact h
  have hZeq : Z = I \ (L ∪ R) := by
    refine Finset.ext fun i => ⟨fun h => Finset.mem_sdiff.mpr ⟨?_, ?_⟩, fun h => ?_⟩
    · rw [hIeq]; exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h)))
    · exact fun hmem => Finset.disjoint_left.mp hZlr h hmem
    · obtain ⟨hIi, hLR⟩ := Finset.mem_sdiff.mp h
      rw [hIeq] at hIi
      rcases Finset.mem_union.mp hIi with h | h
      · rcases Finset.mem_union.mp h with h | h
        · exact absurd (Finset.mem_union.mpr (Or.inl (hAL₁ h))) hLR
        · exact h
      · exact absurd (Finset.mem_union.mpr (Or.inr (hBR₁ h))) hLR
  have hZeq' : Z' = I \ (L ∪ R) := by
    refine Finset.ext fun i => ⟨fun h => Finset.mem_sdiff.mpr ⟨?_, ?_⟩, fun h => ?_⟩
    · rw [hIeq']; exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h)))
    · exact fun hmem => Finset.disjoint_left.mp hZlr' h hmem
    · obtain ⟨hIi, hLR⟩ := Finset.mem_sdiff.mp h
      rw [hIeq'] at hIi
      rcases Finset.mem_union.mp hIi with h | h
      · rcases Finset.mem_union.mp h with h | h
        · exact absurd (Finset.mem_union.mpr (Or.inl (hAL₂ h))) hLR
        · exact h
      · exact absurd (Finset.mem_union.mpr (Or.inr (hBR₂ h))) hLR
  have hPQ : p.1 = q.1 := hAL.trans hAL'.symm
  have hPQ2 : p.2 = q.2 := hBL.trans hBL'.symm
  refine ⟨?_, ?_, hZeq.trans hZeq'.symm⟩
  · have hkrw : keyOf c b p.1 = keyOf c b q.1 := by rw [hPQ]
    exact (hA₁c.symm.trans hkrw).trans hA₂c
  · have hkrw : keyOf c b p.2 = keyOf c b q.2 := by rw [hPQ2]
    exact (hB₁c.symm.trans hkrw).trans hB₂c

/-- Distinct key-triples give disjoint classes (the partition property of the
class dictionary, on `Z ⊆ M` keys). -/
theorem cls_disjoint_of_key_ne (hlr : Disjoint L R) (hLm : Disjoint L M)
    (hRm : Disjoint R M) {c b : Fin n → ℤ}
    {k k' : (ℤ × ℤ) × (ℤ × ℤ) × Finset (Fin n)}
    (hZm : k.2.2 ⊆ M) (hZ'm : k'.2.2 ⊆ M) (hk : k ≠ k') :
    Disjoint (cls c b L R k.1 k.2.1 k.2.2) (cls c b L R k'.1 k'.2.1 k'.2.2) := by
  rw [Finset.disjoint_left]
  rintro I hI hI'
  obtain ⟨e₁, e₂, e₃⟩ :=
    mem_cls_key_unique hlr hLm hRm hZm hZ'm hI hI'
  exact hk (Prod.ext e₁ (Prod.ext e₂ e₃))

instance IsAlias.instDecidablePred (P : ℕ) (T ts : ℤ) {n : ℕ} (c b : Fin n → ℤ) :
    DecidablePred (IsAlias P T ts c b) := fun I => inferInstanceAs
      (Decidable (subsum b I = T ∧ subsum c I % P = subsum b I % P ∧ subsum c I ≠ ts))

/-- The alias set `A_s(P)`: all key-subsets that are aliases of the target. -/
def aliasSet (P : ℕ) (T ts : ℤ) (c b : Fin n → ℤ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (IsAlias P T ts c b)

/-- The D_s closure — the dictionary's content (§5.3: «if D_s contains every
alias class of t_s, then the exact output sum equals Σ_{I∈A_s(P)} χ(I)»):
over a sound (Lemma A1) and complete (Corollary A6's coverage, as a
hypothesis) dictionary of `Z ⊆ M` key-triples, the class-sums assemble to
the alias-set sum.  The exec machinery stays abstracted behind `dict`
(the D7 boundary). -/
theorem ds_closure (hlr : Disjoint L R) (hLm : Disjoint L M) (hRm : Disjoint R M)
    {c b : Fin n → ℤ} {P : ℕ} {T ts : ℤ} {χ : Finset (Fin n) → ℂ}
    (dict : Finset ((ℤ × ℤ) × (ℤ × ℤ) × Finset (Fin n)))
    (hZm : ∀ k ∈ dict, k.2.2 ⊆ M)
    (hcover : ∀ I ∈ aliasSet P T ts c b,
      ∃ k ∈ dict, I ∈ cls c b L R k.1 k.2.1 k.2.2)
    (hsound : ∀ k ∈ dict, ∀ J ∈ cls c b L R k.1 k.2.1 k.2.2,
      IsAlias P T ts c b J) :
    ∑ k ∈ dict, ∑ I ∈ cls c b L R k.1 k.2.1 k.2.2, χ I
      = ∑ I ∈ aliasSet P T ts c b, χ I := by
  classical
  have hpw : ((dict : Set ((ℤ × ℤ) × (ℤ × ℤ) × Finset (Fin n)))).PairwiseDisjoint
      (fun k : (ℤ × ℤ) × (ℤ × ℤ) × Finset (Fin n) =>
        cls c b L R k.1 k.2.1 k.2.2) := by
    intro k hk k' hk' hne
    exact cls_disjoint_of_key_ne hlr hLm hRm (hZm k hk) (hZm k' hk') hne
  have hunion : dict.biUnion
      (fun k : (ℤ × ℤ) × (ℤ × ℤ) × Finset (Fin n) =>
        cls c b L R k.1 k.2.1 k.2.2)
      = aliasSet P T ts c b := by
    ext I
    rw [Finset.mem_biUnion, aliasSet, Finset.mem_filter]
    constructor
    · rintro ⟨k, hk, hIk⟩
      exact ⟨Finset.mem_univ I, hsound k hk I hIk⟩
    · rintro ⟨huniv, halias⟩
      obtain ⟨k, hk, hIk⟩ :=
        hcover I (Finset.mem_filter.mpr ⟨Finset.mem_univ I, halias⟩)
      exact ⟨k, hk, hIk⟩
  rw [← Finset.sum_biUnion hpw, hunion]

end SubsetSumL25
