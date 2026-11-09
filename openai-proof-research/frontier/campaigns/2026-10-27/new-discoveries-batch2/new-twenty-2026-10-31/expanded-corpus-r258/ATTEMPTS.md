# Sustained mathematical routes and their stopping points

## 326956: local link perturbations, not a numerical Lagrangian search

The current source's Conjecture 2 has every r≥3, not just r=3. Its Theorem 3 already proves the entire r=3 case. The source prints a witness with one edge beyond the allowed upper bound, so that witness and small modifications of it cannot be counted here. Gruslys–Letzter–Morrison, Hypergraph Lagrangians I, Theorems 1.2–1.3, actual body read: the principal range is proved for sufficiently large t; the r≥4 counterexamples are outside it. Neither statement is a full resolution or refutation of this literal conjecture.

Let the compulsory clique have s=t−1 vertices, and add one new vertex with link H of size q≤C(s−1,r−1). At the uniform clique weighting, the clique polynomial is L=C(s,r)/s^r and the new-vertex derivative is q/s^{r−1}. Thus the derivative after taking weight from the clique is q/s^{r−1}−rL≤0. Merely adding a new vertex with an irregular link gives no first-order improvement. Several new vertices each with fewer than the threshold number of incident edges also fail this first-order test; edges using several new vertices are higher order.

At equality q=C(s−1,r−1), use clique weights x_i=(1−ε)/s+ε z_i, Σz_i=0, and new weight ε. Put d_i=deg_H(i), dbar=(r−1)q/s, h=C(s−2,r−2)/s^{r−2}. Expanding the exact polynomial gives second coefficient

−r(r−1)L/2 − h Σ z_i²/2 + Σ d_i z_i/s^{r−2}.

Its maximum over tangent z is positive precisely when

Σ(d_i−dbar)² > ((s−1)/s) C(s−2,r−2)².

For the source's colex equality link (complete on s−1 of the s vertices), equality holds, so this is a flat splitting direction, not a new counterexample mechanism. A substantive finite candidate would require a different link satisfying the strict degree-variance inequality, followed by an explicit rational ε and exact positive polynomial evaluation. No such link is supplied. It may be impossible by a degree-square extremal inequality; that is the precise missing lemma. Arbitrary floating-point maximization would not settle it. No Pi execution is requested on this route until the later link-extremal literature and all explicit constructions are inventoried.

## 373197: quotient counting loses the naïve Boolean-lattice proof

Vatter's v3 (November 2026) still states Conjecture 2.1. Its final section reports partial composition results, not a proof of general principal permutation downsets. Distinct standardized patterns, rather than subsequence occurrences, are counted. Subset complementation or the Boolean lattice's symmetric chain decomposition does not descend to the quotient: different subsets yielding the same standardized pattern can have deletions/extensions with different equivalence classes. Counting C(n,k) is therefore the wrong sequence.

The source explicitly lists Murphy's 17-entry rank sequence and Stanton's (8,8,4,4) partition obstruction. The partition obstruction transfers to induced subgraphs of a union of cliques, but does not transfer to layered permutations: compositions retain the order of blocks. The source explains this distinction and reports verification for layered compositions of total length≤34. Reusing (8,8,4,4), whose total is24, cannot be offered as a new layered witness. The principal downsets of monotone compositions are already covered by the source's Corollary 2.5.

A genuine finite certificate would contain a permutation ρ and three ranks i<j<k with exact distinct-pattern counts a_i>a_j<a_k. A one-step drop alone is not a failure of unimodality. For each rank, enumerate all index subsets and their standardized images, deduplicate by the image permutation, and prove that this exact image set is the rank slice. A full certificate lists each image and one embedding and gives a covering map from every index subset; a trie/DAG can compress the latter. No new witness or bounded size warrant exists. Random search over permutations with 2^n subset enumeration is not justified in this source-review lane. The missing step is a structural family with a provable valley after the middle rank, not a Lean translation of a known partition example.

## 342517: source domains invalidate the easy injectivity shortcut

All-zero toric ideals are easy to manufacture by taking linearly independent support columns, for example the three pair-support vectors on three neurons. This does not refute the meaningful source conjecture: Beer et al.'s published discussion explicitly aims to classify well-formed codes, and their zero-ideal theorem has that hypothesis. A well-formed planar Euler code cannot simply consist of those three pair supports plus the empty word. Missing intervening zones obstruct a generic diagram.

The public ProbXiv comment dated August 17, 2026 gives {0000,1100,1010,0101,0011} with the single quadratic relation p12 p34−p13 p24. This is already public and itself acknowledges the well-formedness issue. Do not repackage that code, its independent-column predecessor, or its graph-family variants as a new result. Beer et al.'s journal Conjecture 1.6 remains within a discussion of well-formed codes. Lienkaemper v2 retracts an earlier proof and states a forward quadratic-Gröbner conjecture; a retracted proof is not clearance.

A uniform order works for every code on n neurons. Finding one order making a nonpierced code quadratic does not negate that quantifier. A valid new mechanism would need either an admissible nonpierced code quadratic for every order, or a finite family of admissible codes forcing incompatible monomial inequalities for every universal order. No such admissible family was established. No Gröbner computation or Pi formalization is requested.
