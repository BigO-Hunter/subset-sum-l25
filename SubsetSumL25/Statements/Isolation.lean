/-
OpenAI Lemma 2.1 («Isolation», setup.tex lem:isolation), MVV-style isolation.

Verbatim statement (setup.tex):

    For every choice of the tie weights, there is a subset I⊆[n] with a(I)=t if
    and only if there are s∈{0,…,nN₀} and I⊆[n] with c(I)=t_s.  If the original
    instance has a solution, then with probability at least 11/12 at least one
    transformed target t_s has exactly one representing subset.

with C = 1+nN₀, c_i = C·a_i + u_i, t_s = C·t + s, u_i iid uniform in {1,…,N₀},
N₀ a power of two with 12n ≤ N₀ < 24n (eq. (1) `eq:transformed`).

Translation notes (details in STMTS.md):
* tie weights `u_i ∈ {1,…,N₀}` are modeled by `Fin N₀`; the +1 shift is
  irrelevant to both parts of the lemma.
* the power-of-two property of N₀ is used only for bit-length accounting
  downstream; it is not needed for either part proved here and is omitted.
* probability = fraction of the uniform finite space `(Fin n → Fin N₀)`,
  stated as a rational inequality; `Pr ≥ 11/12` on that space.
* `sorry`: M1 placeholder — proof target is Proofs/Isolation.lean (M3).
-/
import SubsetSumL25.Statements.Defs

namespace SubsetSumL25

variable {n : ℕ}

/-- The transformed weight system of eq. (1): `C = 1+nN₀`, `c_i = C·a_i + u_i`,
`t_s = C·t + s` for `0 ≤ s ≤ nN₀`. -/
def transformedC (n N₀ : ℕ) : ℤ := 1 + n * N₀

theorem L2_1_isolation_prob (a : Fin n → ℤ) (t : ℤ) (N₀ : ℕ)
    (hN₀ : 12 * n ≤ N₀)
    (hsol : ∃ I : Finset (Fin n), subsum a I = t) :
    (11 : ℚ) / 12 ≤
      ((Finset.univ.filter (fun u : Fin n → Fin N₀ =>
          ∃ s ≤ n * N₀, ∃ I : Finset (Fin n),
            (Finset.univ.filter (fun J : Finset (Fin n) =>
                subsum (fun i => transformedC n N₀ * a i + ((u i : ℕ) : ℤ)) J
                  = transformedC n N₀ * t + s)).card = 1)).card : ℚ) /
      (Fintype.card (Fin n → Fin N₀) : ℚ) := by
  sorry

end SubsetSumL25
