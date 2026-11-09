# Ordinary attempts and source exclusions

These are discovery notes, not an acceptance, formal certificate, or priority claim. No Lean, solver, numerical search or enumeration was run.

## 381186: complete source exclusion, not a new candidate

Chin-Hung Lin, *Applications of zero forcing number to the minimum rank problem* (2011), Section 3, Example 10, Figure 2, printed p.7 (PDF p.13), already refutes the exact closure assertion. The figure was rendered and visually inspected. Its path number uses vertex-disjoint induced paths, including singletons, consistent with the assigned 2013 source's convention.

Use core K4 on {a,c,d,e}. Let H add two leaves b,v at a. Let G be the path x-v-y with distinguished middle vertex v. Their vertex sum J has edges of K4 and ab,av,vx,vy. This is literally the printed construction, without modification.

G has P=Z=1. For H, the three core twins c,d,e force at least two initial blue vertices among them: if two are white, no blue vertex can distinguish them. Likewise the leaf twins b,v require at least one initial blue vertex. Thus Z(H)>=3. The set {c,d,b} forces a, then e, then v, so Z(H)=3. A cover {b-a-c,d-e,v} gives P(H)<=3. For two paths to cover H, the two leaf vertices must either be on the same path, which then is b-a-v and leaves a triangle, or on different paths, of which at most one can contain a and reach the core. The other is a singleton, leaving too much of K4 for one induced path. Thus P(H)=3.

For J, two of c,d,e and one of x,y must initially be blue by the twin obstruction. A blue set of size three therefore consists exactly of such vertices. Its blue core vertices each see the two white vertices a and the remaining core vertex. The blue fork leaf can force v, but v then sees both a and the other fork leaf white. No further force is possible. Hence Z(J)>=4. The set {c,d,b,x} forces a,e,v,y, so Z(J)=4. A three-path cover is {x-v-y,b-a-c,d-e}. For a two-path cover, if x,y are on one path that path is x-v-y, leaving K4 and b for a single induced path, impossible. Otherwise their paths can cover core vertices only by passing through v and then a; vertex disjointness allows only one of the paths to do this. The other fork leaf is singleton, and the core-containing path cannot contain all four vertices of K4. Thus P(J)=3. This proves the exact negation from the printed object. Zero discovery eligibility.

The earlier proof attempt was to merge optimal forcing chains through v. It fails because existence of some optimal forcing-chain cover does not make every optimal induced-path cover a forcing-chain cover. Restricting to the strong PZ property would repair the gluing argument, but Lin's Theorem 11 already supplies that stronger-hypothesis result. It is not the literal problem.

## 358153: complete published-preprint scope bridge

The relevant source quantity is rho(F)=Delta(F)/|F|, not ordinary diversity gamma. The original source Conjecture 6.1 has the same inequality as the record. Huang–Liu–Lu–Wu arXiv:2607.02589, Theorem 1 and Section 3.1 pp.5–6, already give counterexamples for every constant C, hence C=100. This proof body was read, including its construction and degree calculations. It is an existing claim, not journal authentication or an independent full-paper audit.

Let n=ceil(Dk), with D>100, and choose a k-set X outside a fixed seven-point Fano plane. Take X itself, together with all Li union R, where Li is one of the seven Fano lines and R is a (k-3)-set outside the plane meeting X. Two line-extensions intersect because Fano lines intersect; each meets X by construction. Thus the family is intersecting (merely saying that every member meets X would not suffice).

Put Q=C(n-7,k-3)-C(n-7-k,k-3). Then |F|=7Q+1; every plane point has degree 3Q. Points of X have degree 1+7 C(n-8,k-4), and other outside points have no greater degree. As k grows at fixed D, Q/C(n-7,k-3)->1 and C(n-7,k-3)/C(n-3,k-3)->((D-1)/D)^4. Choosing D>100 makes 7((D-1)/D)^4>1 and 7/(3D)<1. Therefore for sufficiently large k the size threshold holds and Delta=3Q, giving rho=3Q/(7Q+1)<3/7. This is a full exact-scope existing refutation. Formalizing or choosing a concrete instance adds no discovery credit.

## 358502: sustained path mechanism, parked

Literal target is ALL l,k and ALL edge-colored tournaments on l^(k-1)+1 vertices; paths have distinct vertices and length counts edges. Source Conjecture 5.3 differs explicitly from the walk formulation Conjecture 1.7.

Attempt A: assign to every vertex a vector of maximal monochromatic path lengths ending there and use a pigeonhole/product bound. The key monotonicity fails: on an edge u->v of color a, a maximal a-path ending at u may already contain v. Appending v then produces a walk, not a path. Thus the coordinate need not strictly increase on that edge. Collapsing monochromatic strongly connected components does not repair the proof: a component may contain long paths while contracting it loses both rainbow and length data.

Attempt B: partition vertices by maximal lengths, delete a last color, and induct on k as in the walk argument. An internal edge in a part can close a monochromatic directed cycle rather than contradict the maximal length. Choosing a canonical maximal path or breaking ties does not remove this obstruction. A needed replacement lemma would bound these exceptional cycle-containing classes while preserving the multiplicative l factor; none is proved here.

Attempt C: target a finite counterexample at l=2,k=3. Avoiding a monochromatic two-edge path forces incoming and outgoing color sets at each vertex to be disjoint. Avoiding a rainbow three-edge path imposes overlapping equalities on each directed four-vertex path. A useful certificate would need an explicit tournament and complete color table plus proofs covering every directed length-two and length-three path, on exactly five vertices. No such table is constructed. This is a specific semantic target, not a request for an unbounded generic solver. The source's cycle obstruction alone is not a counterexample. No Pi assignment is qualified; no all-version/citing clearance claimed.

## 329032: sustained collapse mechanism, parked

The target is a simplicial collapse ONTO the particular labeled cyclic-polytope boundary subcomplex, for every admissible n,k,l, not just homotopy equivalence to an abstract sphere. Source Conjecture 5.11 follows the explicit embedding theorem.

Attempt A: delete maximal circular intervals successively, pairing each non-boundary face with a coface. Being in a unique circular interval does not ensure a free face: the same face may lie in other maximal intervals, especially in the l>=1 range where arcs overlap in several components. A valid certificate must prove uniqueness of the remaining maximal coface at EACH deletion, and must never pair away a face of the specified boundary.

Attempt B: order faces by their complementary cyclic gaps and match at the first excessive gap. This gives a plausible local rule but changes which gap is first after insertion of the matching vertex. The involution and acyclicity obligations are unproved. Even an acyclic matching with sphere-like critical cells would not automatically leave exactly the desired boundary; a relative matching with no critical cells outside that boundary is needed.

Attempt C: induct using the known homotopy recurrence for nerve complexes. A homotopy pushout or suspension equivalence does not furnish a sequence of free-face removals compatible with the embedded boundary. The precise missing lemma is a relative collapse reducing (N(n,k),boundary C_(2l+2)(n)) to a smaller such pair while preserving boundary labels. No lemma or obstruction is obtained, so there is no full construction or Pi route. Small parameter collapses would not resolve the universal target.

## 317450: source-fidelity obstruction before coefficient calculations

All four arXiv PDFs were fetched and text-indexed. In the inspected primary material the established compatibility is the LEFT H-coaction on H_CK, Theorem 8, with multiplication in tensor positions 1,3; it yields convolution automorphisms and antipode identities on characters. The record instead invokes an unspecified transported GL coproduct, m^(2,4), and S_GL. A quick dualization or a one-tree coefficient computation cannot be trusted without the exact transport, symmetry factors, domain and unit conventions. The inspected versions' GL mentions explain graded duality but do not supply the record's precise formula as an open conjecture. Do not relabel Theorem 8 as a proof of these equations. This is a source-fidelity hold, not a resolved/refuted claim or a qualified finite calculation.
