# Ordinary proof: no cubic 8-circulant nut graph

DRAFT, AI-assisted; zero accepted credit. All graphs are finite and simple. A nut graph has real adjacency nullity exactly one and a full nonzero kernel vector. An 8-circulant graph admits a cyclic automorphism group with eight equal vertex orbits. See paper.md for bibliography, validation and novelty limits.

**Theorem.** No graph is simultaneously cubic, nut and 8-circulant.


## 2. Semiregular coordinates and the kernel character

Suppose for contradiction that G is a cubic nut graph and that a generator sigma has eight equal orbits of size m. The graph is nonempty, so m is positive. Choose representatives r_i, for 0 <= i < 8. The map (i,a) -> sigma^a(r_i), with a in Z/mZ, is a bijection. Distinct representatives lie in distinct orbits, and equality within an orbit occurs exactly when the exponents differ by a multiple of m. Thus sigma acts in these coordinates by (i,a) -> (i,a+1).

For completeness, an element sigma^k fixes one vertex precisely when m divides k. This condition is independent of the vertex, so the common orbit length is also the order of sigma. This proves the asserted semiregularity and justifies taking exponents modulo m. The case m = 1 is included: it represents the identity action on eight vertices, not a family omitted from the theorem.

Let T be pullback by sigma on real vertex functions. Adjacency preservation gives A(G)T = TA(G), by reindexing the neighbor sum. Hence T preserves the one-dimensional kernel. If u is a nonzero full kernel vector, there is a real scalar epsilon with Tu = epsilon u. Since T^m is the identity and u is nonzero, epsilon^m = 1. A real root of unity is a sign: epsilon = 1, or epsilon = -1 and m is even.

Put v_i = u(i,0). Iterating the identity gives

`u(i,a) = epsilon^a v_i,     v_i != 0 for every i.`

There is one epsilon for the whole kernel line. Independent orbit signs cannot be chosen. This elementary representation-theoretic observation is the compatibility needed below; the existence of constant or alternating orbit entries is already familiar in nut-graph theory (see Lemma 5 of [1]).

The character chi(a) = epsilon^a is well-defined on Z/mZ because epsilon^m = 1. It satisfies chi(a+b) = chi(a)chi(b) and chi(-a) = chi(a). The latter identity uses that every character value is 1 or -1. Define the shift set

`S_ij = { b in Z/mZ : (i,0) is adjacent to (j,b) }.`

Translation invariance describes all other adjacency fibers from these sets. Edge reversal yields S_ji = -S_ij; looplessness gives 0 not in S_ii. These are statements about the original simple graph, not additional assumptions about an abstract quotient.

The finite vertex universe in the formal target imposes no extra hypothesis: every ordinary finite graph is representable on Fin n. Likewise, decidable equality and adjacency impose no mathematical restriction on finite graphs. Empty and singleton graphs fail the nut predicate before orbit arguments are used.




## 3. The symmetric signed quotient and its kernel

Define the integral matrix C of order eight by

`C_ij = sum { chi(b) : b in S_ij }.`

Edge reversal and chi(-b) = chi(b) give C_ij = C_ji. In particular C is symmetric even when epsilon is negative. Evaluating A(G)u = 0 at the representatives gives Cv = 0, where v has every coordinate nonzero.

This alone does not prove that C has nullity one. The missing direction is provided by a lift valid for every real vector w on the eight orbits. Define (Lw)(i,a) = chi(a)w_i. Reindexing neighbors using translation invariance gives the exact identity

`(A(G)Lw)(i,a) = chi(a) (Cw)_i.`

Therefore L maps ker C linearly into ker A(G). Evaluation at a = 0 is a left inverse, so L is injective, including on kernels. Since the graph kernel has dimension one and Cv = 0 with v nonzero, C has nullity exactly one. This rules out any reduction that merely finds a full vector in a larger quotient kernel.

A nut graph is connected. Indeed, if a nontrivial partition into components existed, restrict its full kernel vector to one component and set it to zero elsewhere. No edges cross the partition, so the restricted vector remains in the adjacency kernel. It is nonzero and has a zero coordinate, contrary to the fact that every nonzero vector on that line is full. This cut argument is also used formally and does not assume connectedness in the definition of Nut.

**Cofactor criterion.** For a real symmetric matrix C of order eight, nullity one with a full kernel generator is equivalent to

`det C = 0 and (adj C)_ii != 0 for every i.`

Here (adj C)_ii is the determinant of the principal matrix deleting row and column i. To prove the forward implication without division, suppose that minor is singular. Extend a nonzero vector in its kernel by inserting zero in position i, obtaining x. Then Cx is supported only at i. Pair with the full kernel vector v: symmetry gives v^t Cx = (Cv)^t x = 0. Since v_i is nonzero, the remaining coordinate of Cx is zero. Thus x is a nonzero kernel vector with a zero coordinate, a contradiction.

Conversely, determinant zero and a nonzero order-seven minor imply rank seven. The adjugate is nonzero, its columns lie on the kernel line, and symmetry makes it a nonzero scalar multiple of vv^t for a kernel generator v. Nonzero diagonal entries then imply v_i != 0 for every i. Only the forward implication is needed by the graph reduction. Integer determinants and cofactors agree with their real images, so the necessary condition can be refuted entirely by exact integer arithmetic.




## 4. Cubicity forces a coherent local grammar

At (i,0), each neighbor (j,b) contributes chi(b)v_j to the kernel equation. Two neighbors in the same orbit cannot carry opposite character signs: their terms would cancel, leaving the third neighbor's value equal to zero. Fullness excludes this. With three neighbors in the same orbit, a sum of three signs is odd and nonzero, so their common nonzero orbit value cannot satisfy the kernel equation either. Consequently each nonempty fiber has coherent character signs, and

`|C_ij| = |S_ij|,     sum_j |C_ij| = 3.`

The off-diagonal support of C is connected. Otherwise a proper nonempty subset of orbit labels would have no nonzero C entry crossing its cut. Coherence identifies a nonzero entry with the presence of an actual edge fiber. The union of those graph orbits would therefore define a nontrivial cut with no graph edge across it, contradicting connectivity of G.

These facts also bound every entry in magnitude by two. If an off-diagonal entry had magnitude three, its endpoints would have no remaining absolute row weight; they would form a component of at most two labels. A diagonal entry of magnitude three would isolate its label. Both contradict connected support on eight labels.

Internal shifts are invariant under b -> -b and do not contain zero. A singleton internal shift therefore satisfies b = -b with b nonzero. In a cyclic group this forces m even and b = m/2. Its character contribution is the SAME sign

`s = epsilon^(m/2)`

at every singleton internal fiber in every orbit. This is the quotient semi-edge. A pair of internal shifts contributes +2 or -2 by coherence and represents a quotient loop. Thus

`C_ii is in {0, 2, -2, s},     s is in {1, -1}.`

When m = 1, no internal shift exists and every diagonal is zero. When m = 2, the sole possible nonzero internal shift is the involution, so each diagonal is zero or epsilon. No exception or lower bound on m is needed. For epsilon = 1 all entries are nonnegative. The formal predicate Admissible records this positivity condition in addition to symmetry, the absolute row sum, entry bound, diagonal alternatives, signs, and connected support.

For enumeration we use a larger class, Structural, that drops only the positivity condition in the trivial-character branch. Formally Structural C s is Admissible C (-1) s. Every graph-derived Admissible matrix lies in this class. It is intentional that not every Structural matrix need arise from a cyclic cover. Excluding a larger class is sufficient, and allows arbitrary vertex-sign switching without incorrectly asserting preservation of entrywise positivity.




## 5. Complete finite coverage of supports and augmentations

Let H be the simple off-diagonal support graph of a Structural matrix C: distinct i and j are adjacent exactly when C_ij is nonzero. The absolute row sum shows degree at most three, and the cut condition gives connectedness. The support catalogue has, for orders 1 through 8, respectively

`1, 1, 2, 6, 10, 29, 64, 194` representatives.

A list with the right count would not prove coverage. The formal proof instead uses induction with checked extension certificates. For a connected graph of order at least two, take a leaf of a spanning tree. Deleting that vertex leaves the tree on the remaining vertices connected; hence the induced graph there is connected too. Deletion preserves the degree bound. Transport this smaller graph to the inductive catalogue representative.

The removed vertex's neighbor mask is nonempty and has at most three selected vertices. Each selected old vertex has degree strictly below three in the deleted graph because restoring the removed edge raises its degree by one. These are exactly the eligible extension conditions. Conversely, extending a catalogue graph by such a mask describes the original transported graph. Executable bit encodings are connected to actual adjacency by proved no-carry and row-major encoding identities, so the argument is about graphs rather than unchecked codes.

For every eligible extension of each catalogue representative, stored data specifies a target catalogue code and a permutation. The checker verifies that the permutation is a bijection and preserves every adjacency bit. Checker soundness supplies an actual graph isomorphism. There are 1,722 extension witnesses across the seven induction steps, including 1,158 at the final step. Composing the inductive relabelling and checked isomorphism proves coverage for arbitrary connected subcubic graphs on eight vertices. The one-vertex base case is code zero. Redundancy in the catalogue would be harmless to this coverage theorem.

Fix one of the 194 support representatives. Put U_ij = |C_ij|. Every support edge has weight one or two. Choose exactly the subset D of edges whose weight is two. For each vertex i, its diagonal magnitude is forced by the deficit

`U_ii = 3 - sum_(j != i) U_ij.`

Discard negative or oversized deficits. This exhausts the unsigned matrices permitted by the grammar. The formal augmentation theorem recovers the doubled-edge subset from an arbitrary Structural C and proves literal membership in the finite image, rather than relying on a generator's informal completeness.

The resulting enumeration contains 669 unsigned augmentation records. These are not asserted to be 669 nonisomorphic pregraphs; [1] reports 534 after isomorphism reduction. Keeping harmless duplicates avoids an unnecessary isomorphism argument at this stage. The older route's unsigned-kernel pretest is not required: all normalized signed cases are covered below, including those that pretest would already exclude.




## 6. Switching, enumeration and arithmetic obstruction

For each support, checked tree data provides a root and an ordering with parent p(i) < i for nonroot vertices, after a recorded permutation. Choose vertex signs d_i recursively, starting with d_0 = 1 and choosing d_i so that d_p(i) C_p(i),i d_i is positive. Set C' = DCD, where D is diagonal with entries d_i. Then every parent edge has positive weight one or two. This normalizes doubled edges as well as simple edges.

Because D^2 is the identity, switching preserves nullity and fullness. It also preserves absolute entries, support, diagonal entries, determinant and each diagonal cofactor: every determinant factor from the deleted diagonal matrix is squared. Relabelling permutes cofactors and preserves determinant. These identities transport an obstruction for a normalized representative back to the original matrix. Only Structural invariance is needed, as explained in Section 4.

For a fixed unsigned augmentation U and ordered tree, the free sign slots are the non-tree support edges and the diagonals of magnitude two. A doubled off-tree edge has one sign slot, not two independent signs. Diagonals of magnitude one all receive the single sign s; zero diagonals have no sign. Let E be the subset of free slots chosen negative. Giving negative slots value -U_ij and all other entries value U_ij, with magnitude-one diagonals replaced by s, reconstructs every normalized Structural matrix. Symmetry uses one shared slot per unordered off-diagonal edge.

SignedEnumeration proves this image-membership statement. Per-support finite-image equalities then connect those same labelled matrices and trees to the regenerated certificate lists. This matters because an older batch used different support labels and normalization trees: equality of raw matrices cannot be inferred merely from equality up to permutation and switching. The final packet uses certificates regenerated in the required labels.

The checked enumeration has 9,172 normalized matrices. The obstruction split is

`8,208 certificates det C = k with k != 0;`

`964 certificates (adj C)_ii = 0 for a specified i.`

Either certificate contradicts the necessary cofactor condition of Section 3. The sparse dimension-indexed Laplace evaluator in VerifiedDet is proved equal to Matrix.det in every dimension; a separate specialization identifies the principal cofactor. Its evaluated equalities are kernel-reduced proofs, not numerical approximations, external-solver assertions or native oracle results. The regenerated matrix certificates are distributed over 287 modules and assembled into 194 per-support bundles.

Now start with a hypothetical graph. Sections 2-4 produce an Admissible matrix satisfying the cofactor condition. Catalogue coverage relabels its Structural support to one of the 194 codes. Augmentation and switching put it in a finite signed image. Its certificate excludes the cofactor condition, and invariance transports the contradiction back. This proves the theorem for all positive orbit sizes, without enumerating voltage assignments or bounding graph order.

