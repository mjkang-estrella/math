# Ordinary attempts and precise stopping points

All reasoning here is ordinary symbolic mathematics. No mathematical enumeration, numerical experiment, solver, Lean execution or child delegation occurred. Accepted campaign count stays52/60, lane credit0. These are exactly the reserved targets.

## 370296: complete classical bridge, excluded, zero credit

Source v2 Lemma2.1 proves that P1-avoiding Stoimenow matchings are exactly nonnesting matchings. Its full proof was read: extremal nested arcs and absence of TypeI/II force a P1 occurrence, and P1 itself contains nesting. Section4.2.1 defines the FIFO matching of the ith up-step to the ith down-step; Remark4.6 states that Omega identifies matching nr with height of the corresponding (2+2,3+1)-free poset. Conjecture5.1 of v1 states all three polynomial equalities; v2 retains the matching/Dyck equality and explains the poset implication. Journal body is403, not cleared.

Here is the full matching/Dyck bridge, for every n, including n=0. Order a nonnesting matching's arcs by openers a1<...<an. Their closers satisfy b1<...<bn: an inversion would be a nesting. Put f(i)=the number of closers preceding ai. Then 0<=f(i)<i and f is nondecreasing. Conversely, any such sequence specifies a unique Dyck word: before the ith up-step put down-steps until exactly f(i) down-steps have appeared, and after the last up-step put the remaining down-steps. At each down-step there are enough unmatched openers because f(i)<i. FIFO pairing produces a nonnesting matching. The constructions are inverse.

Make vertices0,...,n, with root0 and parent of vertex i equal to f(i). Since f(i)<i, this is a rooted tree. Order children by their vertex labels. Nondecreasing f implies the labels are exactly breadth-first order: children of smaller-labelled parents precede children of larger-labelled parents; inductively depths are nondecreasing. Conversely, breadth-first labelling of any rooted ordered tree gives exactly such a parent sequence. Thus this is a bijection to rooted plane trees with n edges.

Let c(i) be the longest sequence of mutually disjoint arcs ending at arc i. An arc j precedes arc i disjointly exactly when j<=f(i). Consequently c(i)=1+max({c(j):1<=j<=f(i)} union {0}). These values are nondecreasing by induction, since f is nondecreasing. With c(0)=0, the recurrence is therefore c(i)=1+c(f(i)). This is precisely the depth recurrence for our tree. The maximum disjoint-arc count nr is its maximum depth. Traverse the ordered tree in contour order, writing U on the first traversal of an edge away from the root and D on its return. This standard bijection to Dyck paths has maximum height equal to tree depth, and its stack inverse is exact. The composite bijection preserves nr=height. Empty matching/tree/path have statistic0.

Applying the source Omega statistic-preserving bijection also gives the middle poset polynomial, so the full literal endpoint follows, not just a subfamily or one coefficient. This deduction is wholly a composition of FIFO, breadth-first and contour classical encodings and the source's already proved Omega bridge. It receives zero under the task's complete-classical-bridge exclusion, with the reduction made explicit; shortness alone is not the reason. No novelty or acceptance claim is made. No Pi execution is warranted for a zero-credit bridge. The source's printed P1 diagram was not independently visually audited; the proved Lemma2.1 equivalence is used instead. No claim of full journal/correction clearance.

Failed shortcut before this bridge: the paper's Gamma sends Dyck height to maximum crossing, not maximum noncrossing. Sending arcs through Gamma unchanged conflates the two statistics. The breadth-first re-encoding is essential. Likewise Narayana number formulas for mcr do not automatically give nr on P1 avoiders (the source proves nr=mcr only on the P2 class).

## 368228: weighted partition sum, sustained, not solved

Let sigma have n blocks of sizes a1,...,an, each positive. Coarsenings tau correspond to set partitions pi of [n]. Write a(B)=sum of ai over i in B. The exact expression is

F(a)=sum_pi (-1)^(n-|pi|)(|pi|-1)! product_{B in pi} (|B|-1)!/(a(B)-1)!.

This follows directly by translating both source factorial products, without dropping denominators. It shows dependence on the full size vector, not merely n. Normalize by product_i (ai-1)! to get weights

W(B)=(|B|-1)! product_{i in B}(ai-1)!/(a(B)-1)!.

Route1: cumulants. The normalized sum is (-1)^(n-1) times the formal joint cumulant with mixed-moment table W(B). All singleton W are1. The all-singleton-size case ai=1 has W(B)=1 and gives0 for n>1, the cumulant of a constant. For n=1 the original expression is1/(a1-1)!>0. For n=2 it is 1/((a1-1)!(a2-1)!)-1/(a1+a2-1)!>=0. These are symbolic base identities, not enumeration or a full result. The missing lemma is the alternating cumulant sign for arbitrary positive a. General negatively correlated moments do not imply alternating signs of all cumulants.

Route2: beta/simplex integrals. For each individual block B, W(B) is E[product_{i in B} Xi^(ai-1)] for a uniform point of the simplex of dimension |B|-1. This is the elementary Dirichlet integral. It gives positive weights but not a positive alternating sum. The simplex dimension changes with B. A single global Dirichlet distribution would have Gamma(n) and Gamma(n+sum(ai-1)) in its marginal formula, not Gamma(|B|) and Gamma(sum ai). Thus these are not automatically consistent moments of one fixed vector, and ordinary Dirichlet-cumulant theorems cannot be substituted.

Route3: merging blocks/sign-reversing cancellation. Pairing refinements and coarsenings changes the denominator from products of (a(B)-1)! to a merged factorial. Individual factorial inequalities explain the n=2 sign but do not supply multiplicity-compatible cancellations at arbitrary n; a partition can have many merge partners. The source deliberately removes these denominators to obtain its game-tree theorem. That theorem cannot be multiplied by one common positive constant to recover F because the denominators depend on pi. A coefficient-positive recurrence or a weight-preserving cancellation remains missing. No exact counterexample found by reasoning. Parked, not excluded by the easier theorem.

Available arXiv versions v1,v2,v3 all retain Conjecture1.1; the exact motivation/conjecture portions were compared. No journal DOI was reported in the inspected arXiv metadata. This is not a global journal/citation/correction search clearance.

## 367942: finite overlap, sustained until semantic/source hold

The literal field F_p and size parameter n are not linked. Its affine normalization also suppresses an inverse factor on the translated offset, harmless if offsets are universally quantified but relevant to literal fidelity. The only available cited arXiv version v1 does not contain the stated affine-half-interval formula in the text inspected. It cites the older Codes over Trees paper, whose complete body was not obtained. Angle brackets in the stronger slope exclusion might denote generated subgroup or another operation; these differ greatly over finite fields.

Literal reversal test: set n=7, p=11, t1=1, t2=-1=10, s1=0, s2=5. Then S7(0,1)={1,2,3,4}=S7(5,-1), but 10 is neither1 nor n-1=6 and4>ceil(7/3)=3. This is a direct exact set calculation in ordinary reasoning, not a run of an enumeration program. It exposes the missing intended n=p hypothesis (when p=n, reversal is excluded) and receives zero as a scope correction.

Intended-prime route: with p=n odd and t not +/-1, normalize to an interval I of (p+1)/2 residues and count lattice pairs (i,j) in I^2 satisfying i-tj=s mod p. A large overlap creates many parallel lattice hits; a proof must bound the maximum occupancy of this congruence lattice in a half-square. Cardinality pigeonhole only supplies lower bounds for intersection; Cauchy-Davenport on differences loses slope information. A consecutive-run argument must control returns after wrap-around, not just one uninterrupted run. Neither gives the exact ceil(p/3) bound for every slope. The stronger k-dependent bound needs a precise meaning for the excluded multiplicative set before a geometry-of-numbers or run-length lemma can even be stated. No source-qualified full theorem, no Pi plan.

## Other finite possibilities and parking

367232: local conjugator sets can each be nonempty while their intersection is empty. Any finite counterexample must use the paper's actual recursive M, not an arbitrary subgroup. No generic group substitution is an endpoint.

368386: the complement map B -> sum(A)-B proves h versus k-h sumset cardinality equality. Combining it with the published k>=3h+c regimes leaves a real middle band. For fixed h the source already covers sufficiently large k; that is not a new solution.

368524: Cartesian products multiply interval and hull sizes, so a product of known strong-hull groups is covered. A product argument leaves arbitrary irreducible Coxeter groups untouched and is not a candidate.

370747: the source's rectangle/product size inequality differs from the literal two individual bounds. The elementary exponential-size counterargument only corrects this transcription. The intended theorem is log-rank-equivalent and is parked.

The remaining per-ID mechanisms and precise gaps are in results.json. No qualified new ordinary endpoint survived; CANDIDATE.md is therefore not created, and no dormant plan is offered for an unresolved helper. All implementation and certificate activity awaits root separately if it ever selects a qualified result.
