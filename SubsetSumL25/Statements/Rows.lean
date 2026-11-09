/-
M1 (ROWS): the three conditional board rows — rev8g Theorem 1 (0.4875755,
ours), JoshuaQFEX (0.487676) and Bills (0.4876723) (external, pointer
rows).  This is the bridge from «the ladder proves the pieces» to «the rows
the board cares about»: the row theorem is stated with the still-named
conditions as opaque Prop hypotheses (the BRIDGE milestone-1
hypotheses-in-statements architecture), while everything the ladder
kernel-checked is NOT a hypothesis — it is theorems of this package.

Primary source: rev8g `paper_2026-11-06_rev8g.tex` (sha256 18899a6e…,
provenance PROVENANCE_rev8g.md), Theorem 1 (`thm:main`, line 78).
Credit: Theorem 1 is jv1000/rev8g's; the ladder it consumes is Base's and
OpenAI's, kernel-checked here.
-/
import Mathlib

namespace SubsetSumL25

/- Verbatim (rev8g, Theorem 1, `thm:main`):

   «Assume the non-numerical lemmas of the OpenAI paper and of Base's
   written proof.  Then there is a uniform randomized algorithm for Subset
   Sum in the word-RAM model that halts on every execution and answers
   correctly with probability at least 2/3, and, for every fixed c and
   every fixed T′ > T = 0.4875754036, uses O(2^{T′n}) word operations on
   every input of n integers whose bit lengths, and that of the target,
   are at most n^c.  In particular it runs in time O(2^{0.4875755n}).»

   Status and caveats (rev8g §8, verbatim fragments): «The exponent of
   Theorem 1 is T = τ₀ + 20ε = 0.4875754036 … It is conditional on Base's
   written proof (its alias-step cost accounting, Lemma A5 and its checksum
   changes) and on the OpenAI paper, exactly as JoshuaQFEX and Bills are.»
   «The constants ζ and the input guard are free in Base; our choices
   ζ = 10^{-8} and guard = 10^8 only raise the cutoff n … Base's
   Proposition P then needs n > 10^8, and its Chebyshev term 4/(ζ²n) is
   small only for n of order 10^{17}.» -/

/-- **rev8g Theorem 1 (the 0.4875755 conditional row), time-bound tail.**

The still-named conditions are opaque Props (hypotheses-in-statements):
`O1`/`O2`/`O3`/`O6` — the number-theoretic cluster BRIDGE attack-order
item 2 (not yet formalized here); `V1` — the sine-filter extension of the
L3.2 uniform-boundedness (the paper's filter has sine terms);
`SumCheck`/`AliasExt` — the checksum and alias-extraction procedures (the
`D_s` boundary); `CertNum` — rev8g's own certified numerics (33 conditions
+ both moments, their certification).

What the ladder DISCHARGES is not a hypothesis: B1–B5, O4, O8 and the
O5/O7 cores are theorems of this package.  `hops` is the assembled
per-stage bound those theorems give (the o8/o5 budget shape with the O(√n)
explicit and a polynomial factor); the theorem is the T′-absorption tail —
for every fixed `T′` above the point's exponent `τ₀ + 20ε` (rev8g's
T = 0.4875754036), the bound is `O(2^{T′n})`: the `2√n` slack and the
polynomial factor are `2^{o(n)}`, absorbed by the fixed gap `T′ − (τ₀ +
20ε) > 0` for all large `n`.

WIP: the absorption tail is this row's first proof obligation (precisely
reported sorry; M2 next session). -/
theorem rev8g_thm1_time {O1 O2 O3 O6 V1 SumCheck AliasExt CertNum : Prop}
    (_hO1 : O1) (_hO2 : O2) (_hO3 : O3) (_hO6 : O6) (_hV1 : V1)
    (_hSum : SumCheck) (_hAlias : AliasExt) (_hCert : CertNum)
    (τ₀ ε : ℝ) (hε : 0 ≤ ε)
    (ops : ℕ → ℝ)  -- the named assembled per-stage op bound (the procedure's counter)
    (poly : ℕ → ℝ) (hpoly : ∀ n : ℕ, poly n ≤ ((n : ℝ) + 1) ^ 2)
    (c : ℝ) (hc : 0 ≤ c) (n₀ : ℕ)
    (hops : ∀ n ≥ n₀, ops n ≤ c * poly n
      * 2 ^ ((τ₀ + 20 * ε) * n + 2 * Real.sqrt n + 2))
    (T' : ℝ) (hT : τ₀ + 20 * ε < T') :
    ∃ n₁ : ℕ, ∀ n ≥ n₁, ops n ≤ 2 ^ (T' * n) := by
  sorry

/- Pointer rows (external, NOT restated — their own sources stand):
* **JoshuaQFEX 0.487676** — «a retuning of Base by JoshuaQFEX» (rev8g
  abstract/results table); conditional on the OpenAI proof.  Statement
  source: JoshuaQFEX's paper (Big O Speedrun listing).  Not in this
  package's sources; fetching its verbatim statement is the first task of
  that row's verification work.
* **Bills 0.4876723** — subset-sum-conditional-refinement, conditional
  0.4876723 (v1.0.0, 21 Oct; v1.1.0 verification supplement, commit
  590bb68, 22 Oct), Claimed/rank 1 on Big O Speedrun.  Local source:
  `subset-sum-subclassic/yannouli-ss/` (the B4 entry decision examined its
  Regions/RowMargins template).  Its 430 enclosures are the ones Base's
  status row references («430 premises certified here and in [13]»).
* **rev8g Theorem 3** (0.4873408, ternary) needs the open statement [S] —
  not one of the three conditional rows; excluded per BRIDGE note (i). -/

end SubsetSumL25
