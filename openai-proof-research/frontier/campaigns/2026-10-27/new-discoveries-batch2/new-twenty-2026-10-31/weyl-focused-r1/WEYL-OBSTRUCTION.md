# MathDB321049: constructive investigation, unresolved

This is not a solution and receives zero credit. The primary manuscript was read directly by reference: ../lane-2/weyl.txt, Sections 4.1–4.3, printed pp.20–27; its PDF hash is recorded in provenance.json. Source Conjecture 4.14 quantifies over irreducible integral-reflection root systems of rank at least two, including E/F/G and BC. No restriction to A/B/C/D is permissible.

## Exact relation and ray reduction

A vertex is a Borel positive set B. Boundary is the union of B\B' over co-maximal B', and core is its complement in B. Co-maximality means that the only Borel sets containing B∩B' are B and B'. For distinct B,D, adjacency is equivalent to B\D being contained in one Borel core: D\B=−(B\D), and opposite Borels have opposite cores. Equality can be allowed as a padded step, but is not a graph edge.

**Ray-invariance lemma (ordinary proof).** Replace each root direction by any nonempty finite set of positive multiples on the same ray, retaining negative rays. A Borel set is determined by its positive rays. Both root configurations have exactly the same such sets: a functional avoiding their finitely many root hyperplanes gives a chamber, and inside every chamber it can be perturbed to avoid all finitely many equal-value hyperplanes required by F(Φ). Thus positive-ray sets, their intersections, and their inclusion relations correspond. The preceding definition of co-maximality uses only these operations, so co-maximal pairs correspond. A ray is in a boundary exactly when it is lost in a co-maximal pair. All roots on that ray are lost together. Boundaries, cores, differences, and the existential core-containment adjacency therefore correspond. This proves a graph isomorphism, without assuming a reduced-system base formula.

In standard coordinates B_n has roots ±e_i, ±e_i±e_j; C_n has ±2e_i, ±e_i±e_j; BC_n has both coordinate lengths. Their rays coincide, hence Γ_s(B_n)≅Γ_s(C_n)≅Γ_s(BC_n), uniformly in n. In BC, a simple coordinate root and its double both lie in the boundary. Deleting only the short simple root would produce the wrong graph. This handles the nonreduced convention but does not prove the diameter claim for B_n.

## A uniform obstruction to involution and buffer constructions

For A_(N−1), let w reverse k consecutive labels and fix the others. Its inversion set is exactly every pair among those k labels. It is core-coverable iff N−k≥k−1 (k≥2).

Proof: in a Borel witness the k constrained labels must occur in their prescribed increasing order. Each adjacent pair in this subsequence must be separated by an outside label; otherwise their root is simple in the witness. These k−1 gaps require distinct outside labels. Conversely, if k−1 buffers exist, insert one in every gap; put unused labels anywhere. Every constrained pair is now separated, so every inversion root is positive and nonsimple, exactly the core condition.

Consequences: reversal of N−1 labels is an involution and is not a generator for every N≥4. Even reversal of all labels is a product of reflections in pairwise orthogonal roots (disjoint transpositions), but is not a generator. Therefore neither “every involution is a generator” nor “an orthogonal reflection product is a generator” can be used with two-involution factorizations to prove the conjecture. Also, a recursive construction cannot treat a large reversed parabolic block as a single core move using one outside buffer. This is an infinite-family obstruction, not another A2–A5 diameter sweep. It does not refute the conjecture.

## Fixed-core and subsystem routes

If the proposed witness is the starting Borel itself, no nontrivial move works: B\D⊆C_B implies D contains the entire boundary, in particular its simple base. Positivity on the base forces D=B. Thus paths need auxiliary witness Borels genuinely different from their endpoints. A cover of a difference by three cores alone does not provide two intermediate Borel sets: arbitrary sign assignments to roots need not be Borel sets (in A2, positive on α and β forces positive on α+β).

Source Lemma 4.7 embeds subsystem cores into ambient cores, but gluing a path requires controlling all roots outside that subsystem. The reversal/buffer family prevents assuming this automatically. Source connectivity induction increases intersections but concatenates paths with no uniform length bound. Neither it nor a density heuristic is reused as a proof.

## New bounded full-root diagnostics

core_diagnostic.py uses integer vectors, exact reflection permutations, and the positive-minus-simple formula only in reduced classical systems. It enumerates at most 1152 chambers, capped at 2000, and tests each inversion difference against every core. BFS is in the resulting exact root-permutation Cayley graph. Results in core-diagnostic.json:

B2: 8 chambers, degree 4, diameter 2;
B3: 48, degree 29, diameter 2;
B4: 384, degree 273, diameter 2;
C3: 48, degree 29, diameter 2;
D4: 192, degree 95, diameter 2;
F4: 1152, degree 996, diameter 2;
G2: 12, degree 8, diameter 2.

These are Python diagnostics, not Lean certificates. The program stores root permutations, not matrices for huge groups. It deliberately never enumerates E6/E7/E8. No finite parameter result is nominated.

## Exact remaining constructive obligation

For each reduced family A_n, B_n, D_n, uniformly in the allowed rank, construct for arbitrary Borels B,D two Borels H,K and three auxiliary Borels Q1,Q2,Q3 with

    B\H⊆C_Q1, H\K⊆C_Q2, K\D⊆C_Q3.

Equal consecutive vertices may be dropped. The ray lemma then transfers B_n to C_n and BC_n. E6/E7/E8 still require either the same uniform construction or bounded exact certificates with all core/adjacency bridges checked; F4/G2 diagnostics would also need kernel certificates. An abstract union-of-cores or product-of-involutions claim leaves precisely the Borel-realizability and separator obligations above. No concrete construction satisfying these survived this investigation. There is consequently no full Weyl Lean endpoint or asserted Weyl proof.
