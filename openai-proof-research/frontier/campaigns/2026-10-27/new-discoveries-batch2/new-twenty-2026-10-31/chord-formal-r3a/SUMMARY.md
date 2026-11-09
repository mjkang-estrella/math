# Round 3A: partial implementation, not acceptance

The requested general theorem `deletion_proved : Chord.Deletion` is NOT proved.
No previously open model Prop closed. EulerRealization and Heredity remain
conditional on Deletion, through the unchanged round-2A reductions. No work was
done on the parallel lane's combinatorial Props. Root decides acceptance; zero
credit is claimed.

New proved results:

- The frozen cycle evaluator equals the cardinality of the SameCycle quotient,
  including singleton orbits. For positive diagrams this identifies the actual
  boundary count with the quotient of the certified three-half-edge face map.
- Orbit counts are invariant under orbit-preserving equivalences, inversion,
  conjugation, and permutation intertwining. A section meeting every ambient
  orbit and reflecting SameCycle induces an orbit-count equality.
- The literal deletion equation holds for all deletions from one chord to zero,
  and from two chords to one, with the actual restricted assignment.
- Two explicit unproved surgery Props imply general Deletion, and consequently
  EulerRealization and Heredity. These are reductions, not closed targets.

`ChordModel3Final` restates the intended endpoint conditional on exactly Deletion,
RepresentativeExistence, FiveChordLemma, TriangleReduction, TriangleRigidity.
The four-chord endpoint remains conditional on FourChordEnumeration. The literal
small-size refutation remains unconditional.

All 41 inherited modules are byte-identical to the frozen round-2A archive whose
SHA256 is ecf5383aea8e309460520702f6bbbf87d6d85b774fddd36debd2434bfd7f80fa.
See results.json and VALIDATION.md for measured validation status.
