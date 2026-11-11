/-
Minimal certification that the §C14.6 exit-composition lemmas rest only on the house
triple.  It imports ONLY the module under test (not the whole row), so it certifies the
final olean cheaply -- the full KapilaRowAxioms.lean banner drags in every module in the
row and needs far more memory than this host can spare at load ~100.
-/
import SubsetSumL25.Row.KapilaCmpSegStrideProg

open SubsetSumL25.Row

#print axioms cmpSegStride_to_guard
#print axioms cmpSegStride_run_step
#print axioms cmpSegStride_run_halts
