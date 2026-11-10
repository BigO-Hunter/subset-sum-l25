# Filing draft — `ss/kapila 0.4877` (DO NOT POST YET)

Status: **DRAFT, not ready to file.** The bound literal, the form shape and the
package layout are cutting-ready; the theorem behind them is not yet
unconditional. This file exists so that the *last* step is mechanical — fill
two blanks, post — instead of being re-derived under time pressure.

## What would be filed (issue route, exact headings, exact order)

Per `verifier/docs/targets.md#subset-sum` and `own-claims-lane/SHARED.md` §1:
the subset-sum problem is issue-route only; the form's headings are fixed and a
header mismatch stalls the acknowledgement. Body ends at `Bound`.

```
Problem

Subset Sum (https://bigospeedrun.com/subset-sum)

Repository URL

<SUBMISSION REPO URL — blank until the package is filed>

Commit SHA

<COMMIT SHA OF THE ARTIFACT — blank until the package is filed>

Bound

4877/10000
```

Notes on the literal (measured, not guessed):

* **`4877/10000`** is the canonical bound string — the row's `0.4877` as a
  reduced rational, `q > 0`, `0 ≤ p/q ≤ 1`. The row assembly proves exactly
  `BigOSpeedrun.SubsetSum.SolvedInTime (4877 / 10000 : Rat)`
  (`SubsetSumL25.Row.kapila_row`), so the filed literal and the proved literal
  are byte-identical. `Rat.den = 10000`, `Rat.num = 4877` are both pinned by
  `norm_num` inside `rowHorizon_bigO`.
* Do **not** file `0.4877` or `48770/100000` — the gate compares rationals, but
  the board's canonical rendering is the reduced form.
* Gate reminder (SHARED.md §1): a proof run starts only if the bound matches or
  beats the best Lean-Verified result on that board. `4877/10000` is below the
  verified `1/2` row, so it qualifies.

## Package layout (the 3sum/CHD "documented layout", subset-sum profile)

```
<repo>/
  Submission.lean                     -- imports SubsetSumL25.Row.KapilaRow,
                                         exports  theorem Race.bound :
                                         BigOSpeedrun.SubsetSum.SolvedInTime
                                           (4877 / 10000 : Rat)
  Submission/Statement.lean           -- the trusted statement, COPIED UNCHANGED
                                         (verifier challenges/subset-sum/
                                          Statement.lean, sha256
                                          3dc6567e9ee2232f90aae5e3ac4f5a8a3b7e5e34b242861edfe0e9d5189934aa,
                                          verifier commit 4cfb6db)
  Submission/...                      -- the SubsetSumL25 tree the assembly imports
  manifest.json                       -- {"problem": "subset-sum", "bound": "4877/10000"}
```

Profile facts already verified for this pin: toolchain `leanprover/lean4:v4.34.1`,
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` (the DFT pin the subset-sum
README names), ≤ 20 MB per file, three permitted file kinds.

## What must become unconditional before posting

The row theorem is

```lean
theorem kapila_row (R : Routines)
    (hcorr : ∀ n x, 2 ≤ n → CorrectAt R n x)   -- §7 correctness (compose 4 measured cores)
    (henv : ∀ c, R.WithinEnvelope c)            -- §7 running-time bullets
    (hD7 : D7 R)                                -- the named seam: one List Instr + outcome agreement
    : SolvedInTime (4877 / 10000 : Rat)
```

`hD7` and `hcorr` are the two remaining obligations, and they are the *same*
boundary seen from two sides (exec refinement / sample-space identification).
Nothing about the exponent is open: `τ₀ + 20ε = 0.4876902 < 0.4877` is proved
(`tau0_eps_slack`), and its absorption of `2^{O(n^0.7)} poly(n+n^c)` is proved
(`runtime_absorb`).

Posting this draft as-is would be a false claim: it would present a conditional
theorem as an unconditional one. That is the one failure mode this lane must
not commit.

## Attribution (fixed text for the issue body's closing line)

The mathematics is **a-kapila's** (`a-kapila/maths-proofs` @ 44c34961,
`subset-sum/PROOF_0.4877.tex`, sha256 b397531c…298), with the OpenAI preprint
(2026-10-04) underneath it and Bills/jv1000's re-derivations as cross-checks.
Our contribution is **verification infrastructure**: the lemma layer
(O1–O8, B1–B5, the DS ladder) and this row's assembly. We claim no
mathematics.
