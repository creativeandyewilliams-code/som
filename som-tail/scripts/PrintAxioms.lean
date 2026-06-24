/-!
# PrintAxioms — axiom disclosure for all load-bearing theorems

Run with `lake env lean scripts/PrintAxioms.lean` from the som-tail directory.

For the clean theorems (N1–N4) the expected trusted base is only:
  `propext`, `Classical.choice`, `Quot.sound`
(the mathlib-standard trio). If `sorryAx` appears in any N1–N4 theorem, that
is a defect and must be reported prominently. For `reversal` (N5), `sorryAx`
is expected and confirms the obligation is genuinely open.
-/
import SomTail

-- N1 supporting
#print axioms SomTail.trunc_factors
#print axioms SomTail.tower_refines

-- N1 headline
#print axioms SomTail.hist_agree
#print axioms SomTail.tail_xA
#print axioms SomTail.tail_xB
#print axioms SomTail.nondescent

-- N2
#print axioms SomTail.tail_iff_sigma02

-- N3
#print axioms SomTail.tail_decided_with_jump

-- N4
#print axioms SomTail.coding_correct

-- N5 (sorry expected — sorryAx will appear)
#print axioms SomTail.reversal
