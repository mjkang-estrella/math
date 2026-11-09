# Round 7 proof record

## What is proved

Chord7EndLocal proves symbolic formulas for every n >= 3 and every old assignment c. Write p=2n, q=2n+1, and number the six appended half-edges Pp,Np,Cp,Pq,Nq,Cq as k=0,...,5. In the new face permutation:

- Old P0 goes to Pq when q is true, and Cq when q is false.
- Old N_(2n-1) goes to Cp when p is true, and Np when p is false.
- Np goes to Cq when q is true, and Nq when q is false.
- Cp goes to Nq when q is true, and Pq when q is false.
- Pq goes to Pp when p is true, and Cp when p is false.
- Cq goes to Np when p is true, and Pp when p is false.

The two exit formulas are Pp -> old f(P0) and Nq -> old f(N_(2n-1)). Every old input other than P0 and N_(2n-1) has exactly its old face successor. These facts are also arbitrary-size Lean theorems (append_face_exits and append_face_unchanged).

For false/true, P0 -> Pq -> Cp -> Nq. For true/false, P0 -> Cq -> Np -> Nq. Thus opposite sides put P0 and Nq in the same genuine face cycle. Round5.endSame_iff_sameCycle transfers this to the exact frozen EndSame predicate. This proves endSame_append_opposite without BandErasure or any surgery hypothesis.

Chord7EndBand defines the literal Subdiagram from r3Block n to r3Block (n+1) by retaining endpoint numbers. On equal sides the omitted adjacent chord is innermost monochromatic. Round6.innermost_distinct puts its C half-edges in different cycles. The refined successor-swap theorem and BandErasure then give b(new)=b(old)+1. Only BandErasure is assumed in boundary_append_equal.

Chord7Compression proves a local contraction criterion, plus a rank criterion for reaching each retained representative. At retained points r(g(e x))=f x. At omitted points r(g y)=r y and rank(g y)<rank y. Strong induction gives SameCycle g (e(r y)) y. The inherited orbitCount_of_retraction then gives equality of orbit counts. In particular, a closed cycle entirely within the omitted set is impossible under this certificate. Unlike a direct Euler argument, this route does not assume parity or genus realizability.

## Limits and remaining mathematical work

BandErasure is unchanged and unproved. The new rank criterion has NOT been instantiated for its actual subdiagram embedding. One must define the representative map on the six omitted half-edges, prove retained transitions using the increasing endpoint enumeration, and handle n=0 with the already proved annulus case. Counting V-E+F alone would be circular here: the accepted genus definition does not supply independent integrality before deletion is established. The route through a canonical first-return retraction avoids that circularity, but its order-arithmetic verification remains substantial.

EndEdgeSurgery is unchanged and unproved. Its opposite-side EndSame conjunct is now unconditional, and its equal-side count follows from BandErasure. Remaining are equal-side preservation/reflection of old end connectivity and the opposite-side count with the sign selected by old EndSame. For a complete stand-alone surgery proof, use the certified exit and unchanged-old transition formulas with a rank certificate onto the old face permutation with a singleton extra face for equal sides, and onto its end-edge successor swap for opposite sides. The six-point formulas alone do not prove that compression.

TriangleRigiditySix is unchanged and unproved. Round5's selected-triangle endpoint uniqueness does not yet establish the common-arc, adjacent-pair, and global dihedral reconstruction steps. This round adds no rigidity theorem.

## One-more-round assessment

BandErasure: uncertain, and not responsibly promised after its repeated prior failures. A dedicated rank-certificate implementation has a concrete route, but arbitrary subdiagram order compression is still missing.

EndEdgeSurgery: plausible in one focused round because its six exceptional points and opposite-side connectivity are now symbolic theorems. Still no guarantee: actual orbit-count transport must be supplied.

TriangleRigiditySix: unlikely to close in one short round without sustained cyclic-order infrastructure. The finite five-chord core transport is available; the global assembly is not.

No unconditional intended conjecture, deletion_proved, EulerRealization, Heredity, RepresentativeExistence, or MonochromaticSplit is claimed here.

## Explicit next-step rank tables (not Lean certificates)

Let u=P0, v=N_(2n-1), and f be the old face permutation. Retract each old dart to itself. The following table records the proposed retractions and ranks for the six new darts k=0,...,5. The symbol * denotes one extra singleton face in the small permutation; retain its representative at k=2 for false/false, and k=5 for true/true. For unequal sides the small permutation is f * swap u v; for equal sides it is f extended by the fixed point *.

| p,q | r(0),r(1),r(2),r(3),r(4),r(5) | ranks 0,1,2,3,4,5 |
|---|---|---|
| false,false | f(u), f(v), *, *, f(v), f(u) | 1,2,0,1,1,2 |
| true,true | f(u), *, f(v), f(u), f(v), * | 1,1,2,2,1,0 |
| false,true | f(u), f(u), f(v), f(v), f(v), f(u) | 1,3,2,3,1,2 |
| true,false | f(u), f(v), f(u), f(u), f(v), f(v) | 1,2,3,2,1,3 |

The symbolic transition theorems explain these entries. The independent regression tests check the retained-transition equation and strict rank descent for these tables on all tested assignments. They do not instantiate orbitCount_of_rank or sameCycle_iff_of_rank in Lean. A continuation should define these maps literally, prove their local certificate equations, and then invoke the new generic theorems. This finite table setup is more concrete than a proposed unnamed compression equivalence, but it remains unfinished formalization work.
