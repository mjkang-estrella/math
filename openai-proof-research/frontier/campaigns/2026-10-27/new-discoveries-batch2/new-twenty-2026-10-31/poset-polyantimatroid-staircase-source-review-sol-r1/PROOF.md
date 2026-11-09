# Independent ordinary proof for MathDB317443

Status: mathematical content PASS for the supplied literal and cached 0806.2096v1 geometric definitions. Scientific acceptance is HOLD; procedure is STOP/QUARANTINE pending root adjudication of the automatic guard rejection. This document is a retained ordinary argument, not an acceptance or permission to resume acquisition. No mathematical program, enumeration, solver, formal tool or child was used.

## Exact endpoint and conventions

The target is the negation of: every finite three-dimensional poset poly-antimatroid is a step staircase (v1 Conjecture3.10). A point is a multiset on three named letters; containment is coordinatewise order, removing/adding one occurrence changes one coordinate by one, multiset intersection is coordinatewise minimum, and multiset union is coordinatewise maximum. It is not additive multiset sum. Definition1.1(A2), transferred to multisets as the paragraph before Definition1.4 requires, reads: for A not <= B there is a coordinate t with A_t>B_t and B+e_t feasible. Neither A>B in every coordinate nor |A|>|B| is assumed. Definition3.9 additionally requires meet closure.

Definitions3.1-3.3 define actual closed integer interval cuboids and their geometric union. There is no quotient by arbitrary lattice isomorphism, re-embedding, affine change of basis, or substitution of convex hull. A regular sequence has coordinatewise nondecreasing lower corners, with at least one strict adjacent inequality; adjacent cuboids overlap in the indicated corner inequalities; upper corners likewise increase with at least one strict inequality. The first-origin condition prints superscript0 although the sequence begins C1. We do not correct or exploit that mismatch: nonexistence below holds even if the origin condition is deleted, as well as the overlap and all upper-corner ordering conditions. It therefore handles both natural index conventions without changing the target.

## Feasible set and admissibility

Let S={(x,y,z) in {0,1,2}^3 : (x=2 => y>=1), (y=2 => z>=1), (z=2 => x>=1)}.
It is finite, nonempty, normalized at (0,0,0), and has maximum (2,2,2). The whole binary cube is feasible; in particular 000,100,010,001 are affinely independent, giving affine dimension3 and three active underlying letters. Each coordinate also attains2. This is not a lower-dimensional embedding accident.

Accessibility can be checked directly without a table. If a feasible point has a coordinate equal2, reduce such a coordinate to1. Its own antecedent becomes false and its possible role as a prerequisite remains satisfied, because that prerequisite only requires >=1. If no coordinate is2, every positive coordinate is1 and can be reduced to0: none of the three antecedents holds. Thus each nonzero point admits deletion of one occurrence, never a negative count, and the result remains in S.

For the full augmentation axiom, fix arbitrary A,B in S with A not <= B, and choose any deficit coordinate t (A_t>B_t). If B_t=0, incrementing t to1 creates no new antecedent and cannot harm any existing prerequisite. If B_t=1, necessarily A_t=2. Let p(t) be its prerequisite coordinate: p(x)=y,p(y)=z,p(z)=x. If B_p(t)>=1, increment t to2 and all implications hold. If B_p(t)=0, feasibility of A_t=2 gives A_p(t)>=1, so p(t) is itself a deficit coordinate; increment p(t) from0 to1, which is feasible by the first case. These exhaust the possible counts, because a deficit coordinate cannot have B_t=2. The increment is always in A minus B in the multiplicity sense. The argument covers incomparable points, all cardinality relations, equality in the other coordinates, and every cyclic prerequisite case.

For meet closure, if min(A_x,B_x)=2, then both x coordinates are2, hence both y coordinates are>=1 and their minimum is>=1; cycle the letters to obtain the other implications. For join closure, if max(A_x,B_x)=2, at least one x coordinate is2 and its corresponding y coordinate is>=1, hence the maximum y coordinate is>=1; cycle again. Bounds are preserved in both cases. Thus S satisfies all standing axioms, required union closure, and Definition3.9, not just lattice closure.

## Six-element poset and the exact bridge

Use six distinct elements x1,y1,z1,x2,y2,z2, lower level {x1,y1,z1}, upper level {x2,y2,z2}. The only strict comparabilities are
x1<x2, y1<x2; y1<y2, z1<y2; z1<z2, x1<z2.
There is no strict chain of length2, so these comparabilities plus equality give a partial order (in particular no transitive extra comparabilities are missing).
The three disjoint chains are x1<x2,y1<y2,z1<z2. Every ideal meets each in an initial segment. Send an ideal to the three segment lengths. Cross comparabilities impose exactly the three implications defining S. Conversely take the initial segments specified by a point of S: within-chain predecessors are included, and the three cross predecessors are included precisely by those implications. All lower elements have no predecessors, so this exhausts ideal conditions. These two maps are inverse, inclusion corresponds to coordinatewise order, and intersections/unions correspond to min/max.

Independently, deletion of a maximal member of a nonempty ideal removes the last member of its chain. If I not subset J, choose a minimal element u of I minus J. Every strict predecessor belongs to I and, by minimality, to J. Hence J union {u} is an ideal. Earlier elements on the same coordinate chain are in J and later elements cannot be in J, so this adds exactly one occurrence in a coordinate whose count in I is greater. This supplies a second full augmentation bridge, with no unjustified invocation of a set-union theorem for arbitrary multisets.

## Every cuboid representation is obstructed

Suppose, for any positive finite m, S is the union of cuboids D1,...,Dm with nondecreasing lower corners l1,...,lm. Every Di is then a subset of S. No assumption of disjointness, irredundancy, positive length in every coordinate, canonical slicing, or uniqueness of witness assignment is made.

The feasible points a=(2,1,0), b=(0,2,1), c=(1,0,2) lie respectively in some Di,Dj,Dk. For Di, its lower z coordinate is0: its interval contains a and its lower corner belongs to Di subset S subset {0,1,2}^3. Its lower y coordinate is at most1; if it were0, the closed interval product would contain (2,0,0), since the x interval contains2 and z interval contains0. That point is forbidden, so l_i,y=1. Thus l_i=(r,1,0) for some r in {0,1,2}.

Similarly Dj containing b must have l_j,x=0 and l_j,z=1, or it contains forbidden (0,2,0). Thus l_j=(0,s,1). Dk containing c must have l_k,y=0 and l_k,x=1, or it contains forbidden (0,0,2). Thus l_k=(1,0,t).

If j<=i then monotonicity gives l_j,z<=l_i,z, that is 1<=0. Consequently i<j. If k<=j then l_k,x<=l_j,x gives 1<=0, so j<k. If i<=k then l_i,y<=l_k,y gives 1<=0, so k<i. We obtain i<j<k<i, impossible.

All equal-index possibilities are included in those contradictions. Closed boundaries guarantee that the forbidden corner points belong to a product interval when the stated lower bound is0; coordinate intervals of length0 cause no exception. Even singleton boxes, which Definition3.1 excludes by |C|>1, would not help. Redundant boxes and arbitrary overlaps do not change the witness-index argument. If m=0 is allowed as a separate convention its union is empty, whereas S is nonempty. Hence there is no representation of any length satisfying even weak lower-corner monotonicity. A fortiori no regular sequence in the source works.

Coordinate permutation preserves axis-aligned cuboids and coordinatewise order; applying its inverse to a hypothetical representation gives a forbidden representation of S. The same is true of any uniform integer translation, by subtracting the translation from every corner. Thus the obstruction survives these geometric conventions, whether or not the translated shape itself retains normalized accessibility. No source definition allows arbitrary order-isomorphic re-embeddings or general affine transformations; the latter can destroy digital cuboids and are not silently identified with this conjecture. We make no separate theorem about all abstract lattice embeddings.

## Scope of the conclusion

This proves a full proper-dimensional finite counterexample to v1 Conjecture3.10 under its geometric definitions. The first-index typo is irrelevant to the obstruction. It does not refute Corollary3.11/Conjecture3.12 about convex dimension. Three chains generating a lattice under coordinatewise union are a different structural demand from a linearly ordered sequence of cuboids. No convex-dimension bound is disproved here. No minimality, count of feasible points, parametric amplification, worldwide novelty, final2009 equivalence, formal correctness or acceptance is asserted.
