# Ordinary attempts and precise stopping points

No candidate is qualified, and no Pi execution is requested. These are mathematical attempts, not proofs of the reserved conjectures. No solver encoding, numerical sweep, Lean build or heavy enumeration was run.

## 379094: extremal pebbling configurations

Recover the source semantics first. Prices p(v) are integers at least two, a move from u to its neighbour v consumes p(u) pebbles and creates one at v. A configuration is t-solvable if every prescribed t-element target set can be covered by some legal move sequence. This is neither delivering t pebbles to a single root nor covering a fixed weighted target. The extremal unsolvable configuration may choose the target set on which it fails.

Attempt 1: choose an extremal unsolvable configuration and maximize the largest pile lexicographically. Two movable piles do not imply that one can consolidate them while preserving unsolvability and total size. A legal move changes total size by 1-p(u)<0. Replacing moves by free transfers has no established implication for reachability. Thus lexicographic maximality supplies no concentration lemma.

Attempt 2: use a distance potential for an uncovered root s at standard price two. The weight 2^(-dist(v,s)) is nonincreasing under every move: along an edge the receiving weight is at most twice the departure weight. Potential below one certifies inability to reach s. This is a valid ordinary lower-bound mechanism, but does not upper-bound solvability thresholds or show that all concentrated configurations at a given total are solvable. For multiple target vertices a single-root obstruction need not be sharp. No extremal theorem follows.

Attempt 3: force independent bottlenecks by separating target regions. Trees, paths and stars are natural controls, but the source already prints their stack/residue constructions and formula proofs (Theorems 12–14). Combining two stacks gives a lower bound only; it does not eliminate a larger unsolvable concentrated stack. A candidate would need an explicit graph, prices, t and exact comparison of unrestricted and conjectured-shape obstructions. None was found. An arbitrary bounded reachability search would not supply the missing mathematical mechanism or source qualification.

A future handoff requires an actual witness or a proved strict separation with a sound t-target semantic bridge, comparison with all source recipes, current registry and citing-body checks, then a root-authorized Pi task. No such handoff is qualified here.

## 317029: exact symmetric permutations

The source's Conjecture 1 is distinct from its Graham/asymptotic symmetry question and its inflatable-permutation conjecture. The MathDB negative-status quotation cannot clear Conjecture 1.

Attempt 1: double count extensions of j-pattern occurrences to k-subsets. Uniform k-counts imply uniform j-counts. Each j-subset is counted binom(n-j,k-j) times; each j-pattern appears equally often among all k-patterns. This recovers precisely the necessary divisibility conditions already printed by the source. It gives no new obstruction beyond alldiv_k(n).

Attempt 2: exploit the published theorem that a 4-symmetric permuton is uniform Lebesgue measure. Embedding a finite permutation into a permuton uses cells of positive mass. Independent sampling has repeated-cell events; the exact distinct-index pattern counts do not determine their contributions. Those collision terms cannot be dropped. Taking a sequence of hypothetical larger finite examples only gives a uniform limiting measure, which is consistent with existence. No contradiction at n=64 or another admissible n results.

Attempt 3: inversion and rank moment identities would need an exact nonnegative polynomial statistic determined by the 24 four-pattern counts, with a positive finite diagonal correction incompatible with zero. No such identity was derived. A factorial-size permutation search is not a qualified replacement. No finite certificate, uniform construction or execution handoff.

## 322013: locally conical reflection systems

Source support is the fixed space of a conjugate parabolic subgroup. A Quillen fiber must have a cone vertex belonging to every maximal face; contractibility alone is insufficient. Coxeter and Shephard constructions are already published in this source.

Attempt 1: use fixed-space intersections and parabolic subgroup containment to select a canonical cone vertex. The simplicial intersection property (source Theorems 13.3–13.4) constructs faces, but does not force all maximal fiber faces to share a vertex. Turning that implication into a theorem would be the missing step, not a consequence of simpliciality.

Attempt 2: seek a bad fiber in a remaining exceptional group. The conjecture quantifies existentially over well-generating R. Failure for one standard R, or nonisomorphism to a printed good system, would not refute it. One must obstruct every rank-sized reflection generating set of a chosen W, or prove a classification reducing them to explicitly covered orbits. No exact group or all-generators obstruction was obtained.

Attempt 3: extend real-chamber positivity used by the source to complex groups. The real inner-product order argument has no established analogue for arbitrary complex reflection chambers. The source's five remaining exceptional groups and other families cannot be disposed of by that transfer. No source-eligible finite mechanism survives.

All other targets have individual attempts and remaining lemmas in results.json. Parked means unresolved by this lane, not established globally open or impossible.
