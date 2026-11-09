import CrownVConv3

/-!
Axiom audit for the r11 classification endpoint.  Run with the lane check
environment; prints the closure of each top-level declaration.  Only
propext, Classical.choice, Quot.sound are permitted.
-/

namespace CrownV

#print axioms CrownV.validFam_of_cutset
#print axioms CrownV.cutset_iff_fam
#print axioms CrownV.cutsetFam_of_valid
#print axioms CrownV.vcut_ccnt_iff
#print axioms CrownV.cutWitness
#print axioms CrownV.famEq_mixed

end CrownV
