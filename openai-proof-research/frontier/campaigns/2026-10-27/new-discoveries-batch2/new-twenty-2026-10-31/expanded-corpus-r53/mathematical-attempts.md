# Exact route investigations — r53, 2026-11-01

No discovery credit or acceptance is asserted. Statements and raw provenance are in intake.json. Primary PDF URLs, dates, actual HTTP outcomes and byte hashes are in source-receipts.json and extra-source-receipts.json. Unversioned arXiv URLs were saved byte-for-byte; version labels below are those displayed in downloaded bodies.

## 359721: complete ordinary bridge, excluded as routine consequence

Read arXiv:2308.15598 §6.3, formula (3), Theorem60 and proof, Conjecture61; also Theorem53 and its actual proof in §6.2. This is the *weighted* model, not the unweighted lattice-point exponential family. Put M_j=a+d(b-j), with integers a,b>=1,d>=0. Vandermonde gives the literal coefficient c_{r,j}=binom(b,j)binom(M_j,r). For an arbitrary probability vector u on the finite pairs 0<=j<=b,0<=r<=M_j, let J,R have law u, mu=EJ, m=a+d(b-mu), rho=ER. Let h be binary entropy with continuous endpoints.

The source MLE calculation, or direct maximization of its two separated Bernoulli log likelihoods, gives exactly

D(u||T)=m h(rho/m)+b h(mu/b)-H(R,J)-E log binom(b,J)-E log binom(M_J,R).

This remains valid on boundary faces by continuous limits (0log0=0); m>=a>0. Write H(R,J)=H(J)+H(R|J). The last conditional entropy and binomial logarithm are nonnegative. The expression

b h(mu/b)-H(J)-E log binom(b,J)

is precisely divergence of the marginal distribution of J from the binomial model of b trials. Source Theorem53 with d=1,m=b bounds it by (b-1)log2. For b=1 it is identically zero, also matching the formula; one can check this directly without an m>1 convention. Hence

D(u||T) <= [a+db+b-1-d mu]log2.

This is the conjectured upper bound. If d>0 and mu>0, it is strict. If mu=0, nonnegative J is zero almost surely, and the entire problem is the binomial model of M_0=a+db trials. Theorem53 bounds divergence by (M_0-1)log2, strictly less than (M_0+b-1)log2 since b>=1. Thus the bound is pointwise strict for d>0. The displayed entropy expression is continuous on the compact finite simplex, so its maximum is attained and is strictly below the conjectured upper bound. This compactness step is essential; pointwise strictness alone would not settle the supremum.

For the lower bound choose u placing mass 1/2 at each of (0,0) and (a,b). Both coefficient weights are 1, mu=b/2, rho=a/2, m=a+db/2, and

D(u||T)=m h(a/(2m))+(b-1)log2.

For fixed a>0 the derivative of m h(a/(2m)) with respect to m is -log(1-a/(2m))>0 on m>=a. Its value at m=a is a log2. This proves the lower bound (strict if d>0). For d=0 the source box model B_{a,b}, Corollary57, attains (a+b-1)log2, so equality in the upper bound occurs exactly when d=0.

Disposition: full-scope ordinary proof via a direct marginal-entropy use of an explicit published theorem in the same paper. Under the user's rule excluding routine consequences with an explicit bridge, do not invest in Lean or claim substantive discovery. This is a conservative investigator disposition, subject to root review, not independent significance adjudication. No exhaustive literature priority claim. Unlike replacing the weighted trapezoid by surrounding boxes, this proof retains all literal coefficients and quantifiers.

## 359147 and 359148: algebraic connectivity, sustained but unresolved

Read arXiv:2307.07308 definitions/introduction, §4 tables, Conjectures6.1/6.2, and the relevant girth-bound discussion; retrieved the distinct lawful author-hosted version and checked its statement context. Published Wiley search lead has renumbered Conjectures7/8; no assertion of complete published-body audit. AC is the second smallest Laplacian eigenvalue for the regular graphs in question. Refuting an extremal statement requires more than a single high-AC low-girth graph: one needs an upper bound for *every* graph at the competing larger girth (and, for359147, a genuine global maximizer).

Three mechanisms were considered:

1. Small-degree exhaustive enumeration. graphs.py enumerates simple cubic graphs with N(0)={1,2,3}; every isomorphism class has such a labeling. Connectedness and girth are determined combinatorially. Spectra use floating eigvalsh and are diagnostics only. For orders6,8,10 the completed output reproduces the source trend: girth3/4 maxima approximately2/3 at6, 1.438447/2 at8; girth3/4/5 approximately1.120615/1.438447/2 at10. 7,552,132930 connected fixed-neighbor labelings respectively. This is not an independently kernel-certified exhaustive classification, and it proves neither conjecture.
2. Dense complement mechanism. A d-regular graph has L=dI-A. Disconnected complements can attain the natural AC=d plateau, but the obvious complete multipartite examples have forced girth3, or are K_{d,d} in the triangle-free case n=2d. The latter does not create a lower-girth tie: a (d-1)-regular complement on2d vertices with components of size>=d must have exactly two K_d components. Thus this shortcut supplies no counterexample. Ties or a disconnected d=2 loophole would also be poor campaign targets and are not promoted.
3. Sparse high-girth mechanism. A low-girth expander could in principle beat all graphs in a rarer higher-girth class. The Moore lower-order constraints and source girth spectral upper bounds help only when the upper bound is sharp or strong enough; the source explicitly says sharpness occurs only for Moore graphs. No pair with a certified separating bound was found. Growing the enumeration to12+ without a concrete separating mechanism is not warranted.

Remaining exact lemma: exhibit d,n,g1<g2 and an exact simple d-regular G1 of girth g1 with a rational spectral gap threshold t, together with a proof that all simple d-regular n-vertex girth-g2 graphs have AC<t. For359147 a proof of global optimality at smaller girth is additionally required. Finite spectral proof would need PSD/eigenvalue ordering, exact enumeration completeness or a general bound, and bridges to literal AC and girth. No Lean endpoint exists.

The initial optional graph-atlas attempt failed because networkx is absent; the error is retained in diagnostics.log. It was replaced by a self-contained combinatorial enumerator using system Python's existing numpy, with no dependency install or cache mutation.

## 359653: exact geometric refutation routes rejected; global classification remains open here

Read arXiv:2308.13107v2 introduction, exact congruence convention, Lemma2.1 proof, Lemma2.2 setup and Conjecture4.1. Source §2's solved three-triangle theorem is adjacent, not a solution of this target. The source explicitly counts collinear triples with distinct vertices. Therefore do not infer resolution from the contradictory MathDB references field saying solved.

A regular hexagon plus its center is a natural seven-point rival. It has squared-length signatures (unit circumradius)
(1,1,1), (1,1,3), (1,1,4), (1,3,4), (3,3,3).
The third signature is collinear but must be counted, so there are five, not four. Removing degenerate triples would change the source problem and is disallowed.

A second route searched triangular-lattice seven-subsets in the radius-two hexagonal disk (19 points,50388 subsets) and the4x4 square grid (11440 subsets). The finite code uses exact integer squared lengths, including all degenerate triples, aborting each subset only after a fifth distinct signature. No at-most-four examples were found. No statement about arbitrary plane sets follows.

A third structural route uses a diameter AB: each other vertex gives one of at most four side-length multisets for ABX. For a fixed diameter length D and a triangle class containing D, assigning the other two lengths gives at most four intersection points of the two circles about A and B (two orientations for unequal lengths, and two reflected choices). Consequently four classes alone yield only the crude n<=18, far from the required n<=7. Source Lemma2.1 narrows congruent triangles sharing AB to three symmetries; the source proof exploits the tighter three-class budget. With four classes, the extra orbit still has to be excluded by cross-triangle comparisons. No full finite reduction or proof eliminating all eight-point configurations was established. This is the precise global gap, not evidence of falsity or novelty.

## 359262: source definitions recovered, no eligible endpoint

Read arXiv:2307.12458 Definitions40,41,43, Examples42,44,45, Proposition46 and its actual proof (which explicitly omits some middle-segment technical details), Conjecture50. The objects are unbounded outcome regions equipped with finite update rules, not just a finite-board pattern. The initial colored set is not stated finite, and the definition does not impose maximal or irreducible segments. Artificial subdivision could inflate segment counts under a permissive reading; exploiting this is a definition correction, excluded by the campaign. Do not choose an interpretation merely to manufacture a small refutation.

The concrete game {(1,2),(2,3),(3,1)} has the source's three-region mechanism with updates(5,4),(3,5),(4,4),(4,5). Checking a board cannot certify the asymptotic segmentation or the universal k-dependent maximum. A viable endpoint would require a source-faithful invariant of irreducible segmentation (if intended), a proof of the universal upper bound, and constructions for all k!=2. No such invariant or proof was established. Park rather than widen to eventual periodicity, an adjacent conjecture.

## Body-verified prior exclusions

358937: read §6, Theorem6.6 and Claim6.7 proofs in arXiv2306.15702. Nonregular ultra-NT-balanced rhombic polyhedron graphs and their Cartesian products are explicitly supplied. This is a direct public refutation in the stated source; its internal cross-reference typos do not turn it into a new discovery.

359711: read the published Ramanujan Journal article DOI10.1007/s11139-024-00893-8 §5.5, Lemma5.7 with bijection proof, Theorem5.6 and its proof. The identity W_hat_max(n)=C_hat_max(n)/p_n and explicit prime/Mertens estimates yield e^gamma/n with vanishing relative error. This is exactly the MathDB asymptotic, already published. No Lean investment.

359719: read arXiv2308.15588v7 Theorem1.1 and the actual §6 algorithm/complexity discussion. It publicly claims the literal polynomial coloring endpoint and O(|E|(|V|+Delta)Delta^6) complexity. The long internal Tashkinov lemmas were not all read or audited. This is a public full-scope proof claim precluding fresh-discovery investment here, not an independent correctness certification of the entire proof or a journal-publication assertion.
