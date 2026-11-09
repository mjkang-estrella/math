import CrownVFullSidePrime
import CrownVCoordDiff

/-! # r18 scoped axiom audit

`#print axioms` for every theorem introduced by this lane's two new modules,
plus the completed r17 difference lemma checked from its sealed readonly
olean through the same runner. Only `propext`, `Classical.choice`,
`Quot.sound` may appear. -/

#print axioms CrownV.coordKer_isPrime
#print axioms CrownV.coordSpan_isPrime
#print axioms CrownV.pcXside_isPrime
#print axioms CrownV.pcYside_isPrime
#print axioms CrownV.coordKill_sub_mem_span
