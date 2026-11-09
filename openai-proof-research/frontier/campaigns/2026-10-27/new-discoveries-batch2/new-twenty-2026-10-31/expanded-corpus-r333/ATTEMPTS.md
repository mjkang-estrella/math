# Ordinary attempts, NEWr333

These are mathematical arguments written by Sol, without mathematical execution, enumeration, CAS, solver, Lean, or children. Zero accepted credit. Exact literal records and their quantifiers are retained separately. No novel full-scope endpoint has been qualified.

## 365492: intersection support, sustained optimization route

Primary: Gong, arXiv:2410.19076, both v1 and v2 (the latter submitted 19 February 2026), Section 3 constraints (1)–(6), Definition 6, Theorems 4–5 and their area argument, Section 8 Conjecture 1 and Proposition 7 with proof. Both downloaded versions state the same support conjecture. The abstract page supplies no journal reference. The companion 2308.15387 introduction concerns monochromatic support in complete graphs and multi-color connected components; that introductory comparison is not a proof of the present optimal-support property. All companion proofs and all figures have NOT been cleared.

Exact definitions: a,b are probability weights on subsets of [r]. Positive cross-support pairs intersect. Let a_i = sum_{R contains i} a(R) and b_i analogously. Minimize m=max_i(a_i+b_i). The question quantifies over EVERY optimum, not just an optimum with irredundant supports.

First route: weighted area. Expand
 sum_i a_i b_i = sum_{R,S} a(R)b(S)|R intersect S| >= 1.
For any feasible bound m, a_i b_i <= (a_i+b_i)^2/4 <= m^2/4, so 1 <= r m^2/4. Thus m >= 2/sqrt(r). If r=t^2, the t by t grid construction with one color per cell has a_i=b_i=1/t. Explicitly let the a-support consist of t row color sets and b-support of t column color sets, each with probability 1/t. Each row and column meet in one color. This attains 2/t. For ANY optimum at r=t^2 the inequalities must all be equalities; therefore
 sum_{R,S} a(R)b(S)(|R intersect S|-1)=0.
Every summand is nonnegative, and a positive cross-pair with intersection at least two would contribute strictly positively. This proves the desired property for all square r. This is a COMPLETE bridge from the source's area bound and grid construction; it is a source/classical subfamily consequence, NOT a new solution of the full problem.

The nonsquare obstruction is precise: optimum m may strictly exceed 2/sqrt(r). Then the area bound has slack, and a positive overlap does not contradict optimality. Replacing a rectangle's chosen color does not necessarily remove that color from any entire row or column. Support weights record touches, not cell areas. An existence theorem for a cleaned-up optimum would also be too weak for the literal "any" optimum.

Second route: normalized simultaneous deletion. Fix supported R,S. Delete epsilon of mass from a(R) and b(S), rescaling each side by 1/(1-epsilon). This preserves cross-intersection feasibility because it only removes support. The new marginal sum is exactly
 c_i(epsilon) = (c_i - epsilon(1_R(i)+1_S(i)))/(1-epsilon).
Its derivative at zero is c_i-1_R(i)-1_S(i). If every tight color lies in R union S, and m<1, all tight derivatives are negative. For small epsilon all slack colors remain below the old m, contradicting optimality. More generally unequal deletion rates x,y give tight derivative
 x(a_i-1_R(i))+y(b_i-1_S(i)).
A duplicate pair itself only makes two coordinates favorable; a tight color outside its union has derivative x a_i+y b_i >= 0. No proof was found that a violating pair covers the tight set, or that a combination of supported deletions makes every tight derivative negative. Proposition 7 solves the unique tight-color case, not this multi-color obstruction.

Third route: the fixed-support linear-program dual can certify a minimizing distribution on a face, but it cannot alone compare all other support pairs. Arbitrary convex mixtures of two feasible a,b pairs can create disjoint positive cross-pairs. Hence averaging is not a valid convexification of the whole optimization problem.

Precise residual: for arbitrary nonsquare r, show every feasible optimum with some supported |R intersect S|>=2 admits a strictly improving feasible perturbation, including changes of support if needed; or exhibit an exact optimum violating this property with a global lower-bound certificate. Neither exists here. No Pi plan.

## 365775: generic circumsphere rigidity, sustained rank and extension route

Primary: Beers–Harrington–Leygonie–Lim–Theran, arXiv:2411.08201v1 (only version on current abstract page), Definitions 63 and 65, Lemma 64 and its full generic-rank proof, Conjecture 66. Institutional PDF retained. The Shonan September 2024 report, printed page 17, is an earlier primary companion: it poses the complete r-uniform rigidity question and inductive constructions, with no resolving proof. The determinant naming/order in that report must not silently override the paper's Definition 63 equality.

For each (d+1)-subset sigma, use the actual paper's polynomial equality
 det Delta_sigma(P) det Lambda_sigma(Q)
 = det Delta_sigma(Q) det Lambda_sigma(P).
On the affine-independence locus these express equal circumradii. Local rigidity means a neighborhood U of P in which every equivalent Q is congruent to P by an affine Euclidean isometry. Generic means outside a proper algebraic subset, not a selected symmetric point cloud.

Rank route: let J be the Jacobian with respect to all coordinates of Q at Q=P. Isometry velocities are in its kernel. For full-dimensional clouds their dimension is d(d+1)/2. Lemma 64 explains why attaining rank dn-d(d+1)/2 at one regular configuration yields the generic local-rigidity criterion. Counting rows gives only an upper bound on rank; the conjectural inequality cannot supply a nonzero maximal minor.

A concrete all-scope induction was developed rather than a finite random test. In the intended full-dimensional range d>=2, n>=d+1, the first possible n is d+3: at d+1 there is one constraint against d(d+1)/2 shape dimensions; at d+2 there are d+2 constraints against d(d+3)/2; both fail for d>=2. At d+3, the excess of C(d+3,d+1) over d(d+3)-d(d+1)/2 is 3. For greater n the excess increases because the increment in constraint count is C(n,d), exceeding d. Thus the hard base can be formulated uniformly at n=d+3.

Assume the old n-point cloud has full rank. After removing its trivial isometry velocity, all old velocities vanish. For the new point x, the remaining constraints require
 grad_x R^2(sigma union {x}) dot v_x = 0
for every d-subset sigma of old points. If d of these gradients are independent, v_x=0. This reduces a possible induction to two explicit lemmas: (A) a nonzero maximal minor at n=d+3 for every d>=2; (B) existence of a simultaneous nonempty Zariski-open set where d new-point gradients are independent. Their conjunction with the source constant-rank argument would cover every allowed full-dimensional n, but neither lemma has been proved here.

I examined two symbolic specializations conceptually. Putting all points on a common sphere is unsuitable: equal radii at that special locus do not imply generic rank, and tangencies can destroy the desired minor. Putting points on a moment curve gives rational circumradius functions, but no noncancelling determinant formula for the needed minor was obtained. Complete graph distance rigidity cannot be imported: equal full-simplex radii do not give equality of individual edge lengths. The d=1 case alone is routine: pair radii are half distances, so complete pair constraints determine congruence.

Literal low-n defect: d=3,n=2 satisfies C(2,4)=0 >= 6-6, while the hypergraph has no edges and the distance between two points can vary in every neighborhood. For any distinct P=(p1,p2), Q_t=(p1,p1+(1+t)(p2-p1)) tends to P, has no constrained radii, and has a different distance for small nonzero t. The same under-span dimension-count issue occurs in other low-n regimes. This is an explicit complete bridge but only a missing-domain correction, excluded by the task. It does not solve the substantive full-dimensional conjecture. No Pi diagnostic or plan.

## 365645: cyclic exchange, complete elementary bridge and source-semantic exclusion

Primary v1 arXiv:2411.01061, definition immediately before Conjecture 7. Latest journal: Electronic Journal of Combinatorics 33(1) (2026), #P1.20, published 23 January 2026, printed page 14, definition immediately before Conjecture 19. Both explicitly use ONE cycle of distinct basis positions, moving e_j to the preceding cyclic position. Neither imposes a rank lower bound or identifies ordered tuples up to permutation. The current arXiv abstract page lists only v1; the journal is a separate later version. The earlier ELTE 2024 spring research report, pages 4–5, Conjecture 6, calls an exchange any transfer changing at most one element per basis; its prose allows the broader parallel interpretation. This distinction is material and prevents treating a terminology repair as an unqualified discovery.

Concrete ordinary refutation under the literal single-cycle definition:
Take U_{1,4} on {a,b,c,d}, with bases all four singleton sets. This is a rank-one matroid: the independent sets are empty and singletons, hereditary, with the augmentation axiom immediate because the only unequal independent cardinalities are zero and one. Its maximal independent sets are exactly singletons.
Let B=({a},{b},{c},{d}) and C=({b},{a},{d},{c}).
The multiset unions agree; hence the tuples are compatible. No zero-step sequence connects them. If one cyclic exchange connected them, every position would have to be selected since all four positions change. Thus q=4 and the selected indices list all four positions exactly once. Because each selected base is a singleton, the moved element at every position is forced. The induced successor map on positions is a 4-cycle. The required successor map instead is (1 2)(3 4): following the required successor twice returns to the starting position, whereas in a 4-cycle it does not. Contradiction. Two symmetric exchanges, at (1,2) and then (3,4), do connect them. Therefore the distance is exactly 2>r=1.

This is the complete classical permutation-cycle bridge, including matroid, compatibility, move semantics, and bound. It is not excluded merely for being easy: it is excluded here as a direct elementary cycle-structure/definition obstruction, reinforced by the predecessor's broader parallel wording, rather than a new matroid exchange mechanism. Under parallel moves the same tuples are connected in a single round. It cannot be sold as a refutation of that broader conjecture, White's conjecture, the weighted pair conjecture, or the source's actual split-matroid ordering theorem. No additional credit, no CANDIDATE.md, no execution plan.

## Other explicit exclusions and remaining gates

365339: source Conjecture 2 has t0 >= t1+t2; the record has >. For the two-element antichain t0=2. Any first informative comparison leaves one linear extension; any further comparison leaves it one, so t1+t2=2. Strictness fails. If only incomparable comparisons are admitted, there is no second informative comparison. This diagnoses the strict/weak endpoint error, not a new Gold Partition result.

365770: even the source v2 prints 2n+1. Take A={1,2}: A+A={2,3,4}, AA={1,2,4}, so left side is 27 while the printed right side is 3*25=75. More structurally A={1,2,...,2^(n-1)} has n(n+1)/2 distinct sums (binary expansion, including diagonal powers) and 2n-1 products (exponents 0 through 2n-2). Hence the left side is n(n+1)(2n-1)^2/2, strictly smaller than the printed expression for every n>=1. This is a complete public elementary geometric-progression bridge exposing the inconsistent constant and equality clause, not a qualified sum-product discovery. An irrational positive-real example cannot be silently scaled to integer points.

365399: the record's own definition of "trivially distinguishable" says a single P-equivalence class. Primary Definition 2.12/Remark 2.13 identify a single class as P-INDISTINGUISHABLE. The source instead calls distinguishability trivial if the M-class has a representative with an adjacent pair of nonconsecutive letters. Source Example 3.9 already supplies a quaternary refutation of Conjecture 2.16. Its words are bcbabcbcdcbcbbabcbccdccbb and cbbabbcbcdccbcbabcbcdcbcb; the source states their M-class is exactly those two and gives their common Parikh matrix, with differing ac, bd, acd, abd counts. To transport that public example one uses the source definitions: equal consecutive-alphabet subword counts imply M-equivalence; an unequal increasing-letter subword count implies distinct projected Parikh matrices; absence of adjacent nonconsecutive letters in every word of this two-element class rules out the source's trivial distinguishability. The two-element-class assertion is a primary source result, not recomputed here. The literal record's erroneous definition cannot replace the source's meaning. Ternary Theorem 3.8 and its proof are public. Journal DOI 10.1016/j.tcs.2025.115489 is identified, but its attempted public landing GET returned 403; no retry, journal-body clearance, or novelty claim.

For every other ID, results.json states the actual shallow/selected source depth and a precise mathematical obstruction. Downloaded bodies, index absences, and labels are never treated as proof review. No qualification claim extends to unread citing papers, figures, journal corrections, or the inaccessible Parikh journal body.

