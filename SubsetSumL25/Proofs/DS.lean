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

/- (5.1) `w^F(Z) = w(Z △ F) − w(F)`: DS-M1's first proof target.  The
h-disassembly chain is assembled in the session notes (the ∑-split on
`Z = (Z\F) ∪ (Z∩F)` with the sign cases, the `Z △ F = (Z\F) ∪ (F\Z)`
split, and the `F = (Z∩F) ∪ (F\Z)` split are each verified by hand); the
Lean assembly's final calc-bridge lands with DS-M1. -/

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

end SubsetSumL25
