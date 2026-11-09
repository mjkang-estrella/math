# Round 4A: partial implementation, not acceptance

Closed in full scope: `Chord.Model3.SwapCycleLaw`, by the sorry-free theorem
`Chord.Model4.swapCycleLaw_proved`. This is the first of the two round-3A surgery
Props. General `BandErasure` remains OPEN. Consequently `deletion_proved` is not
present, and EulerRealization and Heredity remain conditional on BandErasure.
No combinatorial Props were attempted. Root decides; no acceptance or credit is claimed.

The new proof suppresses one point of an arbitrary finite permutation. Suppression
preserves the number of orbits when the point is not fixed; adding a fixed point
adds exactly one orbit, including when the remaining type is empty. An induction
on the finite type then proves the exact successor-swap disjunction.

Additional certified results: the exact BandErasure identity for deletions from
one and two chords; a simultaneous-suppression criterion using a retraction and
local orbit steps; and the full-scope local formula identifying the swapped face
map with deletion of the two C-edge flips before backbone compression.

All 46 inherited formal modules and the inherited audit source stay byte-identical.
The final intended theorem remains explicitly conditional on BandErasure,
RepresentativeExistence, FiveChordLemma, TriangleReduction and TriangleRigidity.
It does not satisfy the requested endpoint conditional only on combinatorial Props.
The n = 4 endpoint still requires FourChordEnumeration; literal small-size
refutations remain unconditional. DartBridge is unchanged and remains open.

See results.json and replay logs for measured validation and module hashes.
