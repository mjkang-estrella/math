# r3a: Part A remains incomplete, zero credit

`endpoint_of_finite (h : Nut8.FiniteObstruction) : Nut8.Target` is NOT proved
or declared. No inhabitant of Target is provided. This packet fails the task's
acceptance condition. Root has not accepted it. Campaign counts are unchanged.

A2 is now proved over the reals from the actual inherited graph predicates by
`nut_circulant_quotient`. A4 is proved by `full_kernel_det_adjugate` and its
integer specialization. Connectivity is proved by `nut_connected`. The source
cyclic-subgroup definition is equivalent to Circulant by
`cyclicGroupCirculant_iff`. Cubic cancellation and same-entry character coherence
are proved, but they have not been assembled into the frozen graph grammar.

## Remaining Part A obligations

1. A3: derive `Admissible (signedQuotient m (coordinateGraph G L) ε) ε s`
   from Cubic G, Nut G, Circulant 8 G, using compatible witnesses from the
   quotient extraction. Prove the absolute row sum, entry bound, diagonal
   alternatives, positivity in the trivial-character branch, and
   SupportConnected for this SAME matrix. In particular:
   - transport cubic degree through the equivalence;
   - turn `neighbor_character_coherent` into equality between absolute signed
     entry and the number of actual neighbors in that orbit;
   - prove the resulting unsignedQuotient is the actual unsigned quotient;
   - transfer graph connectivity to support cuts;
   - pair internal shifts b and -b and classify the nonzero self-inverse shift
     as m/2, with the shared sign s = ε^(m/2);
   - use connectivity on eight quotient vertices to exclude isolated vertices,
     triple edges, and diagonal magnitude three;
   - assemble every clause of the exact immutable Admissible predicate.
2. Compose A3 with `integer_full_kernel_det_adjugate` and the assumed
   FiniteObstruction to obtain the exact endpoint_of_finite with no additional
   hypotheses. The current matrix theorem intentionally does NOT assert
   Admissible and cannot be fed to FiniteObstruction.

No counterexample to the frozen interface was found; these are unproved
implementation obligations, not evidence that the interface is inconsistent.
There is no hidden replacement definition and no bridge assumed as an axiom.

FiniteObstruction itself belongs to the parallel r3b lane. Its proof and root
acceptance are not asserted here. A rational-nullity transfer is not supplied;
all new nullity and fullness results use the real field required by Nut.
