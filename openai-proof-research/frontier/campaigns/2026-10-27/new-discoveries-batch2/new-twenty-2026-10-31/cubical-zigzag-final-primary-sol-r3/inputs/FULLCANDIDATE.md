# 378413: finite cubical quotient with a type-I zigzag self-intersection

AUTHOR ORDINARY NEGATION ONLY — scientific PARK, zero credit, no dispatch. This is a complete proposed ordinary counterexample to the literal/source Conjecture 2.8, not an independent review or accepted result. Root must adjudicate source finality, domain significance, prior art and procedure. No mathematical program or enumeration was used.

## Exact endpoint and source

Original literal and all original JSON bytes/tokens are in original-bindings.json, key378413. Deza–Dutour math/0405279v1, printed pp2–5: a d-dimensional complex is a finite bounded ranked poset with maximal chains of length d+2 and every rank-two interval thin. It is not required to be simplicial, a convex-polytope boundary, orientable, or spherical. Definition2.3 sets T=σ_(d+1)…σ_1, acting rightmost first. Definition2.5(i) declares type-I self-intersection when σ_1(f) belongs to the same T-orbit. Conjecture2.8 says every zigzag in every odd-dimensional complex has signature(0,0). Printed p5 was rendered and visually inspected; see sources/zigzag-page5.png. No figure is needed for the proposed construction.

Proposed negation: there exists such a finite complex of dimension3 and a flag f for which σ_1(f)=T^30(f). This implies a positive type-I count regardless of the convention for counting paired incidences. No value for the whole signature or orbit length is claimed.

## Cubical cover and deck group

Let Q be the unit cubical cell decomposition of R^3. Its cells are products I1×I2×I3, where each I is either {a} or [a,a+1] for integer a. Inclusion is incidence, dimension is the number of interval factors. Let τ1,τ2,τ3 be translations by100 in the three coordinate directions, and let

 g(x,y,z)=(11−x,y+10,z+10).

Let Γ be the group they generate. It preserves Q. The translation subgroup L=100Z^3 is normal: g reverses τ1 and commutes with τ2,τ3. Also g^2 translates by(0,20,20), and g^10 translates by(0,100,100), so every Γ element is uniquely represented modulo L by g^j with 0≤j<10. The ten cosets are distinct because their y-translations are10j modulo100.

For a nonidentity element h=t g^j in this normal form, if j≠0 the y-displacement is100b+10j, of absolute value at least10. If j=0, h is a nonzero100-integer translation, of sup displacement at least100. Consequently every nonidentity deck transformation displaces EVERY point by sup distance at least10. This also proves freeness; the reflection has no fixed point after its y,z translations. It is stronger than merely saying the action is free on vertices.

Take cell orbits under Γ. Define [A]≤[B] if A is included in a representative of [B]. This is a partial order: dimensions strictly increase at a proper incidence, and transitivity follows by translating representatives to align the middle cell. Add a global bottom0 and top1. Finiteness follows already from the subgroup100Z^3: only finitely many unit cubical cells modulo it. Quotienting further preserves finiteness.

## All complex hypotheses, with quotient incidence paid

The displacement bound ensures each individual closed unit cube maps injectively to the quotient. More generally, the closed star of any cell is contained in a coordinate box of side at most3. No two points in such a box can be deck-equivalent: their sup distance is at most3, less than10. Therefore local face/coface incidences have unique compatible lifts once a contained cell is fixed. This is the exact covering assertion used below; mere freeness would not suffice.

Ranks are0 for bottom,1 for vertices,2 for edges,3 for squares,4 for cubes,5 for top. Each nontrivial cell belongs to some cube; any incomplete cubical chain can be completed within a cube. Thus all maximal chains are bottom<vertex<edge<square<cube<top, of length5=3+2. Ranks cannot collapse because Γ preserves cell dimension.

Every rank-two interval has exactly two intermediate elements. There are exactly four cases: bottom to edge (its two endpoints), vertex to square (the two square edges at that vertex), edge to cube (the two incident square faces inside that cube), and square to global top (the two cubes on its two sides). In the first three cases lift the top cell; the displacement bound prevents either extra quotient incidences or identification of the two intermediate faces. In the last case lift the square; its two incident cubes remain distinct, since a deck transformation identifying them while fixing a square representative would have displacement at most2 somewhere. Any quotient cube incident to that square lifts uniquely to one of those two. This exhausts all rank-two intervals. Hence K is precisely a source-defined3-dimensional complex. The underlying cubical manifold and its cell-star connectivity also show there is no disconnected pathological interval being exploited, though these stronger properties are not required.

## The flag calculation, without computation

In the covering complex let f be the flag with vertex(0,0,0), edge[0,1]×{0}×{0}, square[0,1]×[0,1]×{0}, cube[0,1]^3. Apply σ1, thenσ2, thenσ3, thenσ4. The vertex first moves to(1,0,0); the edge becomes the positive-y edge there; the square becomes the yz-square at x=1; the cube becomes[1,2]×[0,1]×[0,1]. This is Tf. Its ordered coordinate directions are(y,z,x). The same four operations move next in y, giving T²f at vertex(1,1,0), cube[1,2]×[1,2]×[0,1], ordered directions(z,x,y). A third step moves in z, giving T³f=f+(1,1,1), with the original ordered directions(x,y,z).

Translation equivariance now proves by ordinary induction T^(3a)f=f+(a,a,a) for every nonnegative integer a. In particular T^30f has vertex(10,10,10), positive-x edge, positive-xy square, and cube[10,11]^3. The flag σ1T^30f has vertex(11,10,10) and the same edge, square and cube as T^30f. Applying g to the four faces of f gives EXACTLY those four faces. Thus

 gf=σ1 T^30 f.

Deck actions commute with every σi, because they preserve incidence and the unique alternative face, hence also with T. Pass to quotient flags using q. Then q(f)=q(gf)=σ1 T^30 q(f). Apply the involution σ1 to obtain

 σ1 q(f)=T^30 q(f).

The two flags are distinct because σ1 changes between the two distinct endpoints of an edge. Since T is a permutation on the finite flag set, its orbit is a finite zigzag. Definition2.5(i) therefore gives a type-I self-intersection. Its signature is not(0,0), completing the proposed negation.

## Alternatives tested and strongest objections

A polygon in dimension1 already looks problematic under the printed general definition: its two directed T-orbits are interchanged by σ1 and reversal, suggesting type-II intersections. I do NOT promote this endpoint observation; it could be a low-dimensional convention correction. The construction above is dimension3, uses only typeI, and avoids reversal conventions.

For orientable3-complexes, flag bipartition would rule out this particular mechanism: T is a product of four adjacency flips and preserves the part, while σ1 reverses it. A naive torus quotient by translations likewise keeps the signed coordinate frame and cannot identify σ1f with a T iterate. The glide reflection is essential. There is NO claimed counterexample among oriented complexes or convex4-polytope boundaries. A routine-adaptation exclusion would require an actual primary theorem covering the constructed quotient and this exact signature bridge, not just the observation that glide quotients are standard.

Strongest significance objection: the intended conjecture may implicitly concern orientable or spherical objects, making this a domain repair. Strongest contrary case: the source explicitly defines arbitrary thin finite posets, discusses nonoriented maps, imposes no orientability in Conjecture2.8, and the proposed example is a regular local cubical3-manifold rather than a degenerate1-dimensional endpoint. Root must decide this; no significance PASS is self-issued.

## Source/prior/acceptance gates

Actual 2017v3 Deza–Pankov1509.03754 was acquired. Its definitions and pp1–9 were read: it works with simplicial thin chamber complexes and Coxeter complexes, and uses vertex-shadow simplicity, not the exact old σ1 signature condition. Those passages do not supply this cubical quotient or its selfintersection argument. This is a bounded nonmatch, NOT a complete companion/final proof audit. Its remainder, 2018 final, another identified lengths paper, and any final of the2004 original remain unpaid. No concrete matching public proof was identified in the three bounded searches. Four public registry root artifacts are inherited unavailable and were not retried/reconstructed; no current complete registry clearance or worldwide novelty assertion.

Exact allowlisted historical results were reconciled before investment. Neighbor378416's separate join-of-simplex-boundaries proposal and378417's Lins triality formulas are not this target or this construction; their qualifications do not transfer. No protected peer or quarantined body was used.

Network ceased after the separate tree-final automatic cookie redirect cycle. Original failure/ledger retained in NETWORK-STOP.md. There is no qualified survivor, independent fidelity/significance review, formal execution, source-only replay, paper acceptance or credit. The dormant plan is a proposal for review only, not dispatch authorization.
