/-
Base (a-kapila) B4 — Theorem B's region analysis: the §6.1 region partition,
Lemma B2 (domination), and the a_Γ ≤ 3/4 per-row guard.

Primary source: `a-kapila/maths-proofs` @ 44c34961, `subset-sum/PROOF_0.4877.tex`
(sha256 b397531cc5997e88c439d5290774861b46a34aa32d9cd71fa7dcced130359298), §6.1
(regions + certificate data), §6.3 (Lemma B2).  Verified against the primary text (rung B4, «matches»).  Credit: regions,
certificates and Lemma B2 are Base's; the region-predicate shape follows Bills'
`Regions.lean` template (yannouli-ss verification/lean), credited in STMTS.md
§B4.  The certificate numerics (Prop B's 430 integrals, Appendix C rows) are
separately certified and enter here only as data.

Verbatim (PROOF_0.4877.tex §6.1):

    Regions.  Put b₀ = 1, b₁ = 1.25, b₂ = 1.6, b₃ = 2, b₄ = 2.6, b₅ = 3.5,
    b₆ = 5, b₇ = 8, b₈ = 15 and b₉ = ∞.  A real number W lies in the region ρ₀
    if W ≤ Γ, and in the region ρᵢ (1 ≤ i ≤ 9) if Γb_{i−1} < W ≤ Γbᵢ.

    Every certificate has Σ_t z_t ≤ 418.36.

Verbatim (§6.3, Lemma B2 and its proof's two cases):

    Lemma B2 (domination).  Let π be a sampled pattern, v = v*(π), and ρ the
    region of W_{v,π}.  Let z and G be the certificate data for (v, ρ).  Then
    every frequency k of pattern π satisfies
        −α_π U_{v,π} ≤ −Δ + (1/n)Σ_{i=1}^n z·G(x_i) + 6ε Σ_t z_t.

    … the rows have errors at most 3ε, 4ε, 6ε, (4a_Γ+3)ε, 4ε and 4ε. …
    [z·Ḡ ≥ z₀G^π₀ − 6ε Σ_t z_t.]
    Region ρ₀.  Here W_{v,π} ≤ Γ, so α_π = 1.  Sampling means U_{v,π} < Δ.  Then
    G^π₀ = Δ − U_{v,π} > 0 and z₀ ≥ 1 give −U_{v,π} = −Δ + G^π₀ ≤ −Δ + z₀G^π₀.
    Region ρᵢ, i ≥ 1.  Here W_{v,π} > Γb_{i−1} ≥ Γ.  So α_π = Γ/W_{v,π} <
    1/b_{i−1} ≤ z₀, and α_π a_Γ W_{v,π} = Δ.  Sampling means α_π U_{v,π} < Δ,
    that is, G^π₀ = a_Γ W_{v,π} − U_{v,π} > 0.  Then −α_π U_{v,π} = −Δ +
    α_π G^π₀ ≤ −Δ + z₀ G^π₀.

Scope (rung B4): the region structure and the domination argument are
formalized; Prop B's 430 integral bounds are separately certified and enter as
data.  Theorem B itself is an *algorithm* statement (FAIL / estimates / error
/ word count) — like Lemma A5's `D_s`, it is outside this package; the §6.1 +
§6.3 content above is the rung.  The empty-expect audit finds nothing to carry:
B4 has no `Finset.expect` anywhere (its hypotheses are pointwise), so there is
no silent-`0` degeneracy class in this file.

This file now holds the two shared DEFINITIONS (`bandUpper`, `inRegion`) plus
pointers: every theorem of rung B4 is PROVED, with its statement-of-record
in `Proofs/ThmB.lean`:

    bandUpper_step, bandUpper_mono        (the band order, §6.1's table)
    region_existence / region_disjoint / region_unique   (Bills' trio)
    row_errors_le_six_eps                 (the a_Γ ≤ 3/4 per-row guard)
    z_dot_Gbar_ge                         (Lemma B2's display)
    lem_B2_region_zero / lem_B2_region_band / lem_B2_domination
-/
import Mathlib

namespace SubsetSumL25

/-- The nine finite band tops of §6.1: b₀ = 1, b₁ = 1.25, b₂ = 1.6, b₃ = 2,
b₄ = 2.6, b₅ = 3.5, b₆ = 5, b₇ = 8, b₈ = 15 (exactly Bills' list — template
credited).  `bandUpper 9 = 0` is junk: the ninth region has no upper bound. -/
noncomputable def bandUpper : ℕ → ℝ
  | 0 => 1
  | 1 => 5 / 4
  | 2 => 8 / 5
  | 3 => 2
  | 4 => 13 / 5
  | 5 => 7 / 2
  | 6 => 5
  | 7 => 8
  | 8 => 15
  | _ => 0

/-- Base §6.1 verbatim: «A real number W lies in the region ρ₀ if W ≤ Γ, and in
the region ρᵢ (1 ≤ i ≤ 9) if Γb_{i−1} < W ≤ Γbᵢ» — ρ₉'s upper bound is absent
(b₉ = ∞).  Indices above 9 are not regions; the lemmas take `i ≤ 9`. -/
def inRegion (Γ W : ℝ) : ℕ → Prop
  | 0 => W ≤ Γ
  | (i + 1) => Γ * bandUpper i < W ∧ (i + 1 = 9 ∨ W ≤ Γ * bandUpper (i + 1))

end SubsetSumL25
