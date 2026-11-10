/-
Filing stub for `ss/kapila 0.4877` — NOT yet an unconditional proof.

Per `submission/KAPILA_ROW_FILING_DRAFT.md`, this file becomes:

    import Submission.Statement
    import SubsetSumL25.Row.KapilaRow

    theorem Race.bound : BigOSpeedrun.SubsetSum.SolvedInTime (4877 / 10000 : Rat) :=
      SubsetSumL25.Row.kapila_row <Routines witness> <hcorr> <henv> <hD7>

The three arguments are the row's remaining obligations (`CorrectAt`,
`WithinEnvelope`, `D7`); supplying them is the next milestone.  Keeping this
stub in the tree, rather than a `sorry`, keeps the gap visible as a *term*
rather than as an axiom.
-/
