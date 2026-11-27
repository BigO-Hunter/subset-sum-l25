/-
M1 (O8): Base §5.2's word-RAM accounting — verbatim quotes and pointers.
This file holds NO declarations: the statement-of-record for everything is
`Proofs/O8.lean` (M2 proved all six).

This is Base's OWN accounting (rung O8, "paper-only"); the bit-cost →
Light-step translation is D7 (L5's) and is deliberately NOT imported — every
statement counts word operations / elementary steps in Base's own counters.

Primary source: `a-kapila/maths-proofs` @ 44c34961,
`subset-sum/PROOF_0.4877.tex` (sha256
b397531cc5997e88c439d5290774861b46a34aa32d9cd71fa7dcced130359298), §5.1 (Thm A),
§5.2 (the procedure, Step 3 and Step 6, closing accounting paragraph), §5.8
(bullet 5, «A capped execution makes at most 2^{O(n)} draws»).  Cross-checked against the primary text (rungs O8 and B5).  Credit: the accounting
is Base's; this package formalizes it.
-/
import Mathlib

namespace SubsetSumL25

/- Verbatim §5.1, Theorem A part 2:
   «On every execution the procedure uses at most
   2^{τ₀ n + 2n^{0.7}} poly(n+b+2) word operations.»

   Verbatim §5.2 Step 6 (the cap):
   «Count the elementary steps of Steps 1--5: subsets enumerated, merge
   operations, masks listed, keys sorted, records formed, records visited,
   members expanded, dictionary operations, terms summed, and trial divisions.
   Return FAIL as soon as the count would exceed 2^{⌈τ₀n⌉+⌈n^{0.7}⌉}.
   Also return FAIL if a bounded sampler fails.»

   Verbatim §5.2, the closing accounting paragraph:
   «Each step costs poly(n+b) word operations.  Keys have O(b + log n) bits,
   masks have m bits, and the dictionaries are balanced search trees.  The
   finite-precision sums use n² fractional bits (Section 6.2).  With the cap,
   this proves part 2 of Theorem A.»

   Verbatim §5.2 Step 3 (the trial count):
   «… T = n⁷ 2^{e_n} ⌈1/Ŝ⌉ … where e_n is an integer with 2n^{0.6} ≤ e_n ≤
   2n^{0.6}+1.  Then n⁷2^{F̂} ≤ T ≤ 2n⁷2^{F̂}.»  with
   F̂ = log(1/Ŝ) + e_n and Ŝ = (1/n²)∑_{j=1}^{n²} 2^{−d(V_j)}.

   Verbatim §5.8, failure bullet 5:
   «A bounded sampler fails.  A capped execution makes at most 2^{O(n)} draws,
   so this has probability 2^{O(n)}(2^{−n³} + e^{−c₀n²}) = o(1).»

Declarations (all in `Proofs/O8.lean`, all proved — see STMTS.md §O8 for the
proved-vs-named ledger):

* `o8Cap`               — Step 6's cap 2^{⌈τ₀n⌉+⌈n^{0.7}⌉} as a def.
* `o8_cap_absorb`       — cap ≤ 2^{τ₀n+2n^{0.7}} (hyp. `2 ≤ n^{0.7}`: the
                          paper's «sufficiently large n» made explicit —
                          below that the absorption is genuinely false).
* `o8_cap_envelope`     — ten counted categories ≤ C ⟹ ∑ ≤ 10·C.
* `o8_time_bound`       — part 2's display with the poly(n+b+2) slot as
                          named `P`: ∑ ≤ 16·P·2^{τ₀n+2n^{0.7}}.
* `o8_trial_count_bound`— Step 3's verbatim n⁷2^{F̂} ≤ T ≤ 2n⁷2^{F̂}
                          (needs only 0 < Ŝ ≤ 1; `Shat` in Lean).
* `o8_trials_le_cap`    — «halts every execution»'s checkable core: K ≤ cap.
* `o8_draws_le`         — «2^{O(n)} draws» explicit: 2+n²+3K ≤ (n²+5)·cap.

Statement-hygiene notes carried from M1:

* `Ŝ` (combining circumflex) is not a valid Lean identifier — the Lean name
  is `Shat`.
* `o8Cap` is `noncomputable` (ℝ division dependency).
* Empty-expect audit: no `Finset.expect` in any O8 statement; the only
  division is `1/Ŝ`, guarded by explicit `0 < Ŝ`; `n ≥ 0` stated on every
  rpow consumer (no negative-base junk).  `Ŝ ≤ 1` follows in-application from
  proved L2.2 (`d(V) ≥ 0`) plus the draw structure; carried as hypothesis
  because the `V_j` draws are algorithm data.
-/

end SubsetSumL25
