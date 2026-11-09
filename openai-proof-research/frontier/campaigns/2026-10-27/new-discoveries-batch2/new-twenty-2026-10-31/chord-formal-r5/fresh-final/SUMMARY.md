# MathDB 329080 — Round 5

PARTIAL, NOT ACCEPTED. Root decides. No credit is claimed.

Merged the two required branch packets: 138 inherited Lean files, 33 shared filenames byte-identical, zero conflicts. Every inherited source remains byte-identical to its packet.

New full-scope target: the exact graph-window obligation `Chord.Comb4.OddCycleWindow`, proved as `Chord.Round5.oddCycleWindow_proved`. Its shortest odd closed-walk argument supplies either a triangle or an injective five-chord crossing path. The graph uses lower endpoints and includes a proved conversion from graph coloring to the frozen endpoint coloring. Consequently TriangleReduction is proved conditional only on MonochromaticSplit.

New BandErasure preparation identifies the exact omitted endpoint pair and proves that both omitted endpoints define the same C-successor swap. The general suppression identity itself remains open.

`Chord5Final.lean` merges the model and combinatorial reductions. Its intended endpoint remains conditional on exactly BandErasure, EndEdgeSurgery, MonochromaticSplit and TriangleRigiditySix. The n=4 classification and the n=1,2 literal refutation are unconditional inherited results. DartBridge remains an additional statement-fidelity obligation under the root ruling. No unconditional intended Conjecture 3.4 is claimed.

See results.json for actual strict rebuild, per-module leanchecker, extraction replay and LOCAL/upstream audit receipts. PROOF.md lists exact remaining mathematics. REPRODUCE.md explains the naming conflict in the brief and the resumable capped replay. All new modules follow the Chord5*.lean naming restriction.

The new `Chord5EndFace.lean` also identifies the frozen end-face trace predicate exactly with the genuine face-permutation SameCycle relation, without assuming surgery. Independent Python regressions check all 4,948,900 band deletions through n=5 and every simple graph through six vertices; these are numerical checks only.

`Chord5OrbitFive.lean` proves that the frozen equivalence at five chords reduces to explicit dihedral conjugacy and that all chosen triangles have the same six endpoints in any equivalent copy of r3Block 5. This addresses one necessary rigidity transport step; TriangleRigiditySix remains open.
