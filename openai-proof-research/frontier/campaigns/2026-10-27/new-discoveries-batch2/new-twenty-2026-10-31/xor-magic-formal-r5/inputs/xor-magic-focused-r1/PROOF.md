# MathDB 372205: literal obstruction and corrected constructive theorem

Status: ordinary mathematical argument and exact Python certificates only. No Lean endpoint; no acceptance or credit claimed. This file does NOT prove the literal Conjecture 25. Its closed endpoint is impossible. The constructive theorem below addresses the corrected range and requires independent review.

## Source fidelity

Primary source: Cichacz–Grochowski–Zuazua, arXiv:2512.19278v1, Sections 1, 3, 4. Live abs and v1 HTML were fetched on 2026-11-02 UTC (2026-11-01 Los Angeles). Abs lists only v1, submitted 2025-12-22. The literal definition requires a simple CONNECTED graph, a bijection to F2^n, and zero, not an arbitrary constant, neighbourhood sum.

Theorem 5 explicitly uses n > 3. Theorems 17 and 18 give bases at n = 4,5,6,7; Corollary 20 adds powers by Cartesian products and the proof of Theorem 5 inducts by n -> n+4. Those products establish existence of some degrees, not all degrees. Theorem 17 gives open degrees {5,7,9,11} at n=4, {5,7,9,11,13,15,27} at n=5, 9 at n=6 and 13 at n=7. Theorem 18 gives their closed complement degrees. Proposition 24 forbids closed degrees {0,2,2^n-4,2^n-2} and open degrees {1,3,2^n-3,2^n-1}. Order 8 has no examples of the required parity types.

Conjecture 25 does not explicitly quantify n. Its intended nonempty scope is n >= 4; interpreting its displayed sets as inequalities gives empty open sets for n <= 3, but a closed degree 4 at n=3, again contradicting Proposition 24. That endpoint ambiguity is not a discovery.

Even for n >= 4 the literal closed interval is 4,6,...,2^n-4. This includes the forbidden 2^n-4. In particular the assignment's characterization of closed {4,6,8,10} as the full displayed range at n=4 is incorrect: the displayed range also includes 12. The intended corrected upper endpoint is 2^n-6. The nearby source prose also gives an incorrect exclusion set and uses "odd degree" for an even-degree list. We do not silently repair the literal target.

## Literal nonexistence proof

For n >= 2 the XOR of all labels of F2^n is zero: each coordinate equals one exactly 2^(n-1) times, an even number. Thus for every vertex v,

    XOR(closed neighbours in G at v) = XOR(open neighbours in complement G at v).

This identity does not require the complement to be connected. Suppose G has degree 2^n-4 and a closed zero-XOR bijection. Its complement H is cubic and has an open zero-XOR bijection. Let z have label zero. Choose a neighbour u of z in H; cubic regularity guarantees one. The two other neighbours a,b of u are distinct, and their labels satisfy label(a)+label(b)=0. In F2^n this implies label(a)=label(b), contradicting injectivity. Therefore the closed degree 2^n-4 demanded in the literal conjecture is impossible for EVERY n >= 4. This is precisely an already stated obstruction in Proposition 24; it receives zero novelty credit.

## Corrected theorem (ordinary proof, not formalized)

For every n >= 4, there exist connected simple open zero-XOR graphs on F2^n of every odd degree 5 <= d <= 2^n-5, and closed zero-XOR graphs of every even degree 4 <= d <= 2^n-6.

Here is a constructive proof, including the connection argument omitted by a purely linear lift. Finite seed and factor certificates are in outputs/. The Python checker is not a Lean kernel certificate.

### Four-fold lift lemma

Let G have m vertices, be connected and d-regular with d >= 4, be open zero-XOR with odd d or closed zero-XOR with even d. Assume both G and its complement have decompositions into perfect matchings. Assume the union F of the first two matchings of G has a cycle whose length L is not divisible by 3.

Use F4 = F2[w]/(w^2+w+1). Orient each cycle of F. On each oriented edge use slope w in the forward direction and w^-1 in reverse; on other edges use slope 1. For a fixed orientation u -> v of each edge, write slope a_e and use the affine bijection x -> a_e x+c_e between its fibres. Reversing gives a_e^-1 x+a_e^-1 c_e.

Let D:F4^m -> F4^E send a vertex vector b to (b_v+a_e b_u)_e. Let B:F4^E -> F4^m have column e=(u,v) equal to 1 at u and a_e^-1 at v. The constant term in the neighbour-label sum is exactly Bc. We select c in ker B but outside im D.

Such c always exists. The kernel of D is zero: transporting b around the distinguished cycle multiplies it by w^L != 1, hence b=0 there and then everywhere by connectivity. The left kernel of B satisfies the identical edge relation y_v=a_e y_u, so B has rank m. Therefore dim ker B=|E|-m=(d/2-1)m >= m. On the other hand BD is a nonzero matrix, since its (u,v) entry for any edge uv is a nonzero unit and no second edge can cancel that entry in a simple graph. As D is injective, dim(im D intersect ker B)=dim ker(BD) <= m-1. Hence ker B is not contained in im D. Explicitly compute a nullspace basis and take the first basis vector outside im D. Membership in im D can be tested by propagation for the four possible values at a root. This deterministic algorithm is implemented in scripts/lift.py.

The lift has vertices (u,x) with labels (label(u),x), giving a bijection to F2^(n+2). Its degree is d and it is simple because edges only join distinct base fibres using bijections. Its first neighbourhood coordinate is the original G sum (with the vertex added in the closed case). At each vertex of F the two twisted neighbour maps contribute slopes w and w^-1, with d-2 other identity slopes. Writing epsilon=0 for open and 1 for closed, the second coordinate has linear coefficient

    (d-2) + w + w^-1 + epsilon = d + 1 + epsilon = 0 in F4,

using w+w^-1=1 and the required parity. The constant coefficient is Bc=0.

Connectivity: the holonomy group at a base vertex is a subgroup H of the affine group of F4, with scalar parts in {1,w,w^2}. Its scalar image is nontrivial, because the distinguished cycle has scalar w^L. If H contains a nonzero translation t, conjugating by an element with scalar w or w^2 gives another translation independent of t over F2; these translations act transitively on F4. If H contains no nonzero translation, its scalar map is injective, so it is cyclic of order 3 and fixes a common point. Transporting that point to every base vertex gives a section b with c=Db, contradicting our choice. Consequently H is transitive; every fibre is reachable from every other because G is connected, so the lift is connected.

Every base perfect matching lifts to a perfect matching, so G's decomposition persists. The complement also decomposes into perfect matchings. Split its internal K4 in each fibre into three matchings. Over each base G matching, split the K4,4 minus its designated matching into three matchings, using nonzero translations of its output coordinate. Over each base complement matching split the full K4,4 into four matchings. These are disjoint and cover precisely the complement.

Finally, the lifted union of the first two matchings still has a cycle of length not divisible by 3. The affine holonomy around the original length-L cycle has scalar w^L != 1, hence has one fixed point and one orbit of length 3. The lifted cycles have lengths L and 3L, so the length-L cycle persists. This proves all hypotheses needed to iterate the lift.

### Degree interpolation lemma

Let h be the four-fold lift of G. Select k whole perfect matchings of G (0 <= k <= d). Over those base edges replace the designated matching by its complement in K4,4. This raises the degree by 2k. Select j whole perfect matchings of the base complement (0 <= j <= m-1-d), and insert full K4,4 blocks there, raising the degree by 4j. No edges are duplicated and no loops are added.

A full fibre has label sum zero in both coordinates: the first is repeated four times and the sum of all F4 elements is zero. Therefore a matching and its three-edge complement contribute the same label sum at each vertex, and full blocks contribute zero. The graph keeps its original open or closed zero-XOR type and has degree d+2k+4j.

If k=0, it contains the connected lift h. If k>0, any replaced block K4,4 minus a matching is connected, so all four vertices in each of its endpoint fibres are mutually connected. A matching or a triple block over any adjacent base edge propagates this property to the next fibre. Since the original quotient G is connected, the entire graph is connected. Added full blocks cannot hurt connectivity.

As k,j vary, these degrees cover every integer of the parity of d from d to 4m-4-d. After dividing the increments by 2 this is the union of intervals [2j,2j+d]; consecutive intervals overlap since d >= 4.

### Seeds and induction

For powers 4 and 5 use closed degree-4 and open degree-5 seeds, together with certified perfect matching decompositions of each seed and its complement. All are exactly checked, and the distinguished unions have cycle lengths:

* m=16, closed degree 4: [16]. Graph: outputs/base-16-4-1.json.
* m=16, open degree 5: [16]. Graph: ../expanded-corpus-r90/outputs/xor-16-5.json (immutable hashed input).
* m=32, closed degree 4: [32]. Graph: outputs/seed-32-4-1.json, the complement of the authors' open degree-27 example.
* m=32, open degree 5: [8,16,8]. Graph: outputs/seed-32-5-0.json, the authors' example.

The matching certificates have corresponding *-factors-0.json and *-factors-1.json names in outputs/. All decomposition edges, degrees, simplicity, identity label sums and connectivity are checked by exact integer operations; no floating-point solver conclusion is trusted as a proof of feasibility. The solver only proposes finite edge/matching lists.

The lift lemma inductively produces such low-degree seeds at every n >= 4 (separately in each parity of n). At N=2^n with n >= 6, interpolation from the seeds at m=N/4 gives open degrees 5,7,...,N-9 and closed degrees 4,6,...,N-8. The missing open degrees N-7 and N-5 are complements of the constructed closed degrees 6 and 4. The missing corrected closed degree N-6 is the complement of constructed open degree 5. Every complement used here has degree at least N/2 and is connected: if disconnected, each component would have at least degree+1 vertices, impossible for two components on N vertices. The XOR complement identity proves the desired types.

For n=4 Theorems 17 and 18 give all corrected degrees. Local exact certificates also cover all of them via cached open degrees 5 and 7, the fetched author open degree 9, and the local closed degree 4 and their complements.

For n=5, the source and local certificates cover open degrees 5,7,9,11,13,15,27 and their closed complements. The local closed graphs of degrees 8,10,12,14 give open degrees 23,21,19,17. Finally outputs/symmetric-32-6.json is a closed degree-6 graph, whose complement has open degree 25. Its exact verification includes connectivity of both graphs. It was found by imposing the order-3 label symmetry that cycles low-bit values 1 -> 2 -> 3 -> 1 and fixes low-bit value 0; there are 184 edge orbits. This closes every corrected base case. The symmetry is only a search aid, not a hypothesis of the theorem.

Thus there are no remaining ordinary mathematical parameter gaps in the corrected theorem, subject to independent review of the general lemmas above. There is no way to append the literal closed degree N-4.

## Formal and novelty limits

No literal Lean theorem asserting Conjecture 25 can be produced consistently, since its forbidden endpoint contradicts the short proof above. No Lean proof of the corrected construction was completed, no kernel decide certificate checker was built, and no leanchecker/fresh Lean replay/local-declaration audit was performed. Python exact verification and negative controls are separate evidence, not formalization. No Lean packet is asserted. The constructive theorem remains an unaccepted research candidate, with zero credit.

Batal's full article was not accessible (publisher 403); secondary quotations are not a body audit. Registry HEADs were checked, not their complete current proof bodies. The bounded literature checks do not certify worldwide novelty. See PRIOR-ART.md and receipts/.
