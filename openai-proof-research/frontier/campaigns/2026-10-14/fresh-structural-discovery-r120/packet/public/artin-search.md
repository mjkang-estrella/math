# Artin search: a spherical stopping argument and the remaining interface

This is preselection research under the stipulated truth of all pinned source operations. No full target was frozen, and this note is not a candidate, nomination, independent correctness review, or contribution assessment. The contemplated full problem was uniform computation of a standard subset and a conjugating word for the entire intersection of two explicitly given parabolics in every finite-rank Artin group. No complexity bound was contemplated. Spherical acting type is not a permitted replacement for that scope.

The actual r114 screen already states precisely that full algorithmic problem and the missing lower-neighbor search. It was read before the calculation below. This round explores a concrete stopping mechanism inside that interface, rather than claiming that the algorithmic headline is new. The calculation was done before any freeze; there was no freeze later either.

## Exact paid operations

Write E_L(x)=B_x P_{f,L} for the source's finite framed family, in the fixed finite ambient Artin diagram S. The reference is [Parabolic intersections, pinned source](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Parabolic-intersections-in-Artin-groups-September-23-2026/build/sections/07_spherical.tex). For spherical Y, its h(a) is the largest total degree of the tests e_alpha E_L(ax), with alpha over the unfolded Y and L over all labels, and is minus infinity when every such test vanishes. The relevant operations are `lay:height-change`, `sph:no-chain`, `sph:common-extension`, `sph:proper-support`, and `sph:containment`.

In particular, the common-extension statement is a bounded-height statement, not merely the existence of common fractions: for a,b in A_Y there are positive p,q with pa=qb and h(pa) at most max(h(a),h(b)). The source already proves proper-support containment of the stabilizer using that statement. If a color has acyclic tests on every family member, its evaluation cone fixes every member, and its inverse does as well. These are paid operations.

The exact finite arithmetic required to construct the test complexes is also paid: `cor:membership` in [08_stabilizers.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Parabolic-intersections-in-Artin-groups-September-23-2026/build/sections/08_stabilizers.tex) constructs the cyclotomic coefficient field, quotient diagram bases, trace-dual maps and finite algebra, tensors the word complexes, and cancels invertible entries. The calculation below does not replace these operations by unspecified computability over C.

## Prefreeze calculation

Fix spherical Y and arbitrary ambient x. Define

    H(Y,x) = {s in A_Y : E_L(sx) is isomorphic to E_L(x) for every L}.

The following is a proposed exact extraction of this spherical relative stabilizer from the stipulated operations. There is no running-time assertion and no independent proof gate.

If h(1)=-infinity, the source acyclicity argument gives H(Y,x)=A_Y. Otherwise put H0=h(1), and start with p=1. At each stage compute all tests for the family at px. Search the finitely many i in Y for which (i) some test at an unfolded vertex of color i is nonzero and (ii) h(sigma_i p)<=H0. If a color exists, choose the first in a fixed ordering and replace p by sigma_i p. If none exists, stop. Each individual stage is finite exact arithmetic. Positive height monotonicity keeps h(p)=H0.

Here is the termination argument, including the point that testing a fixed list of colors cyclically is unnecessary. Suppose the sequence were infinite. Let J be the colors used infinitely often. After discarding a finite initial segment, every remaining move has its color in J, and each color of J occurs infinitely often. This J is nonempty and spherical. At the start of this tail, some J-test is nonzero: the very next chosen move satisfies condition (i). Thus h_J at that tail's starting family is finite. Throughout the tail, h_J is bounded above by H0, since J is a subset of Y. Partition the tail into consecutive finite blocks, each containing every color of J. Their positive products have support exactly J. Applied to the relative family based at this tail's starting word, `sph:no-chain` prohibits precisely this sequence. This contradiction proves termination. J need not be known by the algorithm.

At termination, let Z be the colors of Y all of whose tests are acyclic. Every generator in Z fixes the entire terminal family. We claim that any positive b with h(bp)<=H0 has support in Z. Read a positive spelling of b in action order. Every intermediate endpoint has height at most H0 by monotonicity. If a first letter outside Z existed, all preceding letters would fix the family at px. That outside letter would therefore have the same nonzero tests and the same bounded-height transition as at px, contrary to termination. Consequently every permitted positive continuation is supported in Z.

Now take s in H(Y,x). Covariance gives h(ps)=h(p) and h(bps)=h(bp) for every positive b. The source common-extension lemma applied to p and ps gives positive a,b such that

    ap=bps,       h(ap)=h(bps)<=h(p)<=H0.

Both a and b are permitted continuations at p, so both lie in A_Z. Hence s=p^{-1}b^{-1}ap lies in p^{-1}A_Zp. Conversely, A_Z fixes the family at px, and applying B_p^{-1} gives the opposite containment. The calculated output is therefore

    H(Y,x)=p^{-1} A_Z p.

The empty Y case returns the trivial group. The test-zero case returns Y. No dimension, word-length, large-parameter, or commuting simplification is used within this spherical calculation. Its spherical hypothesis is nonetheless a strict restriction of the contemplated full algorithm, so it is retained only as support.

## Why this does not complete the full algorithm

For nonspherical acting Y, the source proof uses vertices (T,A_T z), with T spherical and z in A_Yx, in a well-founded harmonic-height filtration. A minimum vertex gives stabilizer containment in a smaller parabolic (with the invisible-factor case handled separately). `ht:minima` proves connectedness for endpoints already known to be minima. It does not recognize a minimum from a finite search prefix.

The finite upper choices can be computed. A lower choice requires a representative w in an entire spherical coset A_T z with a prescribed cap above a layer q and an eligible open coordinate: its actual layer count must be less than the harmonic value, or equal with the allowed sign. The stopping calculation above controls total test height and acyclicity. It does not decide these simultaneous capped-layer inequalities. No implication between its terminality condition and the absence of such a representative was proved.

Cap accessibility uses finite reduced Coxeter words and negative operations to obtain a cap. The cap-hull implication assumes a bound at **every** capped representative before deducing a Weyl-orbit hull constraint. Neither implication supplies the missing reverse certificate. Enumerating candidate parabolics and checking their finitely many generators certifies containment in the intersection; it does not certify the reverse inclusion. A finite descending-rank bound does not fix that stopping problem.

The K(pi,1) companion was followed further late in this round, before any freeze. Its complete `residues.tex`, especially `prop:residue-sublevels`, gives a strict sublevel that is empty or contractible, and a special closed sublevel that is nonempty and contractible under its positive-null-vector exterior hypotheses. The strict proof uses a universal inequality over capped representatives at its source. The special closed nonemptiness proof invokes `prop:isolated-layer`. These stronger paid conclusions have been checked against the attempted search: they settle their special closed case but do not provide a finite emptiness test for the general strict sublevel. Finitely many layer-count height values do not imply finitely many coset vertices. The companion is not silently reduced to an introduction.

## Primary reductions actually examined

Heng--Licata [2412.15919v1](https://arxiv.org/pdf/2412.15919v1), Proposition7.11, gives Gaussian elimination for the twist-image word problem. Proposition7.14 recovers a positive finite-type Garside normal form from the full categorical action; its proof is omitted there in favor of Brav--Thomas. This is not an inspected algorithm deciding the layer predicate of one transported framed family. Their unframed faithfulness conjecture is irrelevant to the stipulated framed detector and is not used to question it.

Cumplido--Gebhardt--Gonzalez-Meneses--Wiest [1712.06727v3](https://arxiv.org/pdf/1712.06727v3), Definition7.1 and Proposition7.2, use recurrent summit sets and twisted cycling to identify an element's parabolic closure in a spherical ambient group. Theorem9.5's full intersection proof chooses an element maximizing its closure invariant in the intersection, then uses Garside normal forms, cycling, and a large-power support argument. Those actual proofs were read late after the spherical calculation, not retroactively claimed as earlier inputs. Their ambient group is spherical; the inspected maximum-selection argument is not a finite emptiness procedure for the arbitrary ambient capped predicate above. No assertion that the entire spherical algorithm literature lacks an answer is made.

Baumann--Kamnitzer's [author manuscript](https://irma.math.unistra.fr/~baumann/mvquiver.pdf), Sections2.2--2.3, defines the positive and negative reflection functors using kernel and cokernel. Proposition2.5 gives adjunction, the head/socle exact sequences, and the triple identities. Lemma2.6 gives stabilization of Sigma_i on the specified zero-socle subcategory. It does not give unconditional idempotence on all modules. For example, for the doubled A2 quiver take one-dimensional spaces at j and i, a nonzero map j->i and zero reverse map. This satisfies the preprojective relation. In the kernel construction Sigma_i replaces the i-space first by zero and then, on applying it again, by a one-dimensional space. Thus the two results differ. This only excludes the unconditional functor-identification shortcut. It is not a counterexample to a source family, finite multigenerator orbit, capped search, or the full algorithm. No such realization claim has been made.

The remaining task is exact: construct a finite certificate deciding the general spherical-coset eligible-coordinate predicate, or a different terminating full minimum-selection mechanism. No such operation is supplied here. The full arbitrary-type algorithm remains unclosed in this round, and there is no nominee.
