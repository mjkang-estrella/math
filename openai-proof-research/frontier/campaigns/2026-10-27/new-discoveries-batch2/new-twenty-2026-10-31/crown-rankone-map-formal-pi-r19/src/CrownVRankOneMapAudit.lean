import CrownVRankOneMap

/-! # r19 scoped axiom audit

`#print axioms` for the rank-one map and every theorem introduced by
`CrownVRankOneMap.lean`, under the same runner and caps.  Only `propext`,
`Classical.choice`, `Quot.sound` may appear.  This audit module is not
counted as production. -/

#print axioms CrownV.rankOneHom
#print axioms CrownV.rankOneHom_C
#print axioms CrownV.rankOneHom_X
#print axioms CrownV.rankOneHom_xx
#print axioms CrownV.rankOneHom_yy
#print axioms CrownV.rankOneHom_xy
#print axioms CrownV.rankOneHom_minor
#print axioms CrownV.allPairMinorIdeal
#print axioms CrownV.allPairMinorIdeal_le_ker
