import CrownVGreedyPrefix

/-! # r21 scoped axiom audit

`#print axioms` for every declaration introduced by `CrownVGreedyPrefix.lean`:
the two literal finite-sum definitions, the truncation step lemma, the main
greedy prefix identity, and its below-budget corollary.  Only `propext`,
`Classical.choice`, `Quot.sound` may appear.  This audit module is not
counted as production. -/

#print axioms CrownV.greedyPre
#print axioms CrownV.greedyStep
#print axioms CrownV.greedyStepAux
#print axioms CrownV.greedyPrefix_sum
#print axioms CrownV.greedyPrefix_sum_of_le
