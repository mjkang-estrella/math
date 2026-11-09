import CrownVGreedyUnique

/-!
# Scoped axiom audit for CrownVGreedyUnique

Prints the kernel axiom profile of every declaration newly introduced by
`CrownVGreedyUnique`.  Scope: the single new theorem of this lane;
`greedyPre`/`greedyStep` are the already-audited r21 imports.
-/

#print axioms CrownV.greedy_terminal_unique
