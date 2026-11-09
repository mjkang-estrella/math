# R313 ordinary proof attempts and gaps

Fixed twenty only. Accepted campaign status 52/60; this lane credit 0. No Lean, solver, numerical or mathematical enumeration execution. This document records ordinary reasoning, including a complete but unqualified classical averaging bridge. No source label or short argument alone establishes substantive eligibility.

## 358612: full orbit-averaging bridge for the literal equivalence

Source: Hng, arXiv:2305.19925 v1 Conjecture 5.1, v2/v3 Conjecture 5.2. All versions define labelled graphs on [n], n >= k, with a uniformly selected ordered injective k-tuple and replacement using the row-stochastic rule R. Equality of distributions quantifies over all finite initial graphs, so n=k is permitted. This is essential: unlabeled output distributions would not identify simultaneous pair orbits by this argument.

Let X be the finite set of labelled simple graphs on [k], and let S_k act simultaneously on X x X. Define
  A_R(F,H) = (1/k!) sum_sigma R(sigma^-1 F, sigma^-1 H).
For B the orbit of (F,H), every orbit element has exactly |Stab(F,H)| preimages under sigma -> (sigma^-1 F,sigma^-1 H). Therefore
  A_R(F,H) = (1/|B|) sum_(F',H') in B R(F',H').
This establishes both directions between equality of orbit sums and equality of all A_R entries. The positive finite factors cancel; k=1 causes no exception.

On exactly k vertices, starting at F, the sampled ordered tuple is a permutation sigma. The drawn graph is sigma^-1 F, and the only replacement which produces the particular labelled target H is sigma^-1 H. Hence P_R(F,H)=A_R(F,H). Equality of process distributions implies equality of this one-step marginal, hence K2 implies K1. This avoids the initially considered falling-factorial/graphon interpolation route entirely.

Conversely suppose K1. For any n>=k, condition on the unordered sampled k-subset U. Fix any bijection f:[k]->U, and pull G[U] and a proposed local target J back to F and H. All k! orderings of U are equiprobable, so the conditional local transition probability is exactly A_R(F,H), independent of f. K1 makes these probabilities equal for R and R'. For any global target G', if edges outside pairs internal to U differ from G, that conditional probability is zero for both rules. Otherwise use the preceding formula. Average over the binomial(n,k) equiprobable U. This includes unchanged steps, targets with several possible supporting subsets, and overlapping localities: contributions are summed, not presumed uniquely supported.

Thus every finite transition matrix agrees. For any deterministic initial graph and any finite path G0,...,Gt, its probability is the product of the corresponding transition entries, by the time-homogeneous Markov definition. These products agree. Every finite-dimensional marginal is a sum of path probabilities; equality on cylinder events gives equality of the process laws on the countable product of the finite graph state space. Hence K1 implies K2 in the source's full literal scope.

Adversarial checks performed in ordinary reasoning: simultaneous relabelling rather than independent isomorphism; stabilizer multiplicities rather than free-action assumption; arbitrary real stochastic entries rather than rational-only rules; loops excluded by simple graphs; unchanged transitions and k=1; all n rather than only n=k; all time marginals rather than only an expected graph or graphon velocity. No graphon result is used.

Qualification: complete ordinary proof, not qualified new research. It is an explicit direct bridge through classical finite group averaging and equality of Markov kernels. Root must assess the substantive exclusion standard; this lane does not exclude merely because it is short or easy. Current bounded registry routing does not establish novelty. All arXiv versions' relevant definitions/conjecture were read, but the latest SIAM journal body/corrections remain unread after DOI 10.1137/25M1746811 returned 403. No retry or alternate protected route was attempted. No qualified CANDIDATE.md or execution authorization is claimed.

Dormant semantic plan, ONLY if root first clears source/significance: define labelled simple graphs as SimpleGraph (Fin k); real row-stochastic rules; relabel action of Equiv.Perm (Fin k); actual tuple-sampled transition on SimpleGraph (Fin n), including outside-U preservation; orbit sums as Finset sums over simultaneous orbit; equality of all finite path laws as semantic endpoint, with explicit bridge to equality of probability laws if required. Prove finite group fiber-count averaging, n=k identity, unordered-subset disintegration, and Markov path induction. The endpoint must quantify all k>=1 and all real rules, not encode the conjecture as an assumed averaged matrix identity. No numerical certificates or graph enumeration are needed. Bounded Pi implementation would await a separate root task; no execution here. Allowed eventual axioms only propext, Classical.choice, Quot.sound. This plan is dormant and does not remove any qualification gate.

## 366145: general acyclic flow attempt, sustained and parked

The literal endpoint is aggregate total arc flow x in the convex hull of unsplittable totals y within coordinatewise x +/- dmax, for every acyclic single-source instance. Commodity marginals need not be preserved individually. Both available arXiv versions state this Conjecture 1. Latest source Theorem 2 proves it on series-parallel digraphs, even with multiple sources. Its final proof invokes Lemma 8's tighter bound and the preceding recursive convex decomposition; dummy commodities with zero weights handle missing local fractional commodities. We read that actual proof, not only the abstract.

First route: split each commodity into a probability distribution on source-sink paths and round independently. This preserves expected aggregate x. It fails the support requirement: several large demands can simultaneously choose the same arc, so deviations add. An expectation argument cannot turn a positive probability of a bad assignment into a convex decomposition supported entirely on good assignments.

Second route: use dependent continuous rounding. Vary path weights preserving commodity masses and aggregate expectations until a boundary is hit. To prove convex-hull membership by separation, it would suffice to find, for every arc cost vector c, a good unsplittable y with c.y >= c.x. But maintaining all arc slabs during rounding may create an extreme point with unresolved commodity choices. No dimension count guarantees an allowable perturbation in a general DAG. Source's series-parallel component tree controls at most two fractional commodities locally; arbitrary crossing supports have no such tree. Simply importing that induction would silently add a graph restriction.

Third route: manufacture a small discrepancy obstruction by encoding arbitrary binary set-system choices as commodity path pairs. A shared source with merging paths permits recombination and extra routes, so a proposed abstract discrepancy obstruction need not be an actual network obstruction. No explicit in-scope graph plus separating cost proof survived this semantic check. No solver plan, finite sweep or numerical search was performed. Missing lemma is a simultaneous bounded rounding/separation theorem for arbitrary acyclic single-source flows, or a genuine finite network whose good unsplittable totals exclude x. Parked; no generic formalization architecture offered as progress.

## 365000: disconnected free-group shapes, sustained and parked

Read filling closure Definition 3, finite-filling Definition 5, translation/conjugation Lemma 6 and its proof, and full Section 8.1 proof. The fill move adds the missing site of a translate gS when all other |S|-1 sites are occupied. Finite filling means every finite initial pattern has finite filling closure; it does not mean the closure of one fixed seed is finite. Theorem 8.1 handles connected S by counting differently positioned labelled edges crossing an empty half-tree boundary.

First extension attempt: replace disconnected S by its finite geodesic hull. A move requiring |S|-1 occupied original sites does not require hull-interior vertices to be occupied. Thus an S-move is not in general a legal hull-shape move. Monotonicity in the initial pattern does not supply monotonicity under changing the shape. The connected theorem cannot be applied this way.

Second extension attempt: attach to each newly filled site a charge on an edge separating the finite initial hull from a virgin half-tree. For connected S the proof forces a sequence of distinct edges of S to cross the boundary, bounding penetration unless S is a generator interval. For disconnected S, missing segments are virtual hull edges, and successive translated components may cross without distinct occupied-edge witnesses. Reuse of a virtual segment is not ruled out. No injective charging lemma or decreasing finite potential was proved.

Third extension attempt: pass to the subgroup generated by differences of elements of S and choose a different free basis. Translation/conjugation changes the cyclic-coset description lawfully, but does not make every finite shape connected in a Cayley tree; generating sets need not contain their intermediate geodesic vertices in any asserted basis. The example pattern {1,a^2,b^2} already warns against treating ambient connectivity as intrinsic subgroup generation. A new basis theorem is missing, not a semantic Lean helper.

Literal singleton issue: Theorem 8.1 explicitly includes a singleton finite-filling exception, while Conjecture 2 does not state one. The filling/corner conventions need reconciliation before making any degenerate literal claim. This tension supplies no qualified result and is not used as a new refutation. The nondegenerate arbitrary disconnected-shape theorem remains unproved. No Pi task.

## 357735: already public exact finite counterexample

Latest source Definitions 2-4 count canonical pairs (A,B) with A+B=C, |C|=|A||B| and min B=0 in dimension one. v1 formulates a maximum-over-alpha variant; latest v2 is the fixed-alpha literal target. ProbXiv publicly posted the following complete fixed-alpha refutation August 17, 2026. Its machine judgement is not used as proof; the object and residue-chain argument are independently checkable.

C={0,...,28} minus {1,14,16}, cardinality 26. Take A_r={0,r}, with
B_3={0,2,4,6,8,10,12,17,18,19,23,24,25},
B_5={0,2,3,4,6,10,12,13,19,20,21,22,23},
B_15={0,2,3,4,5,6,7,8,9,10,11,12,13}.
Each displayed B has 13 elements, starts at zero, and its translate by r is disjoint from B and supplies exactly the other 13 elements of C. Distinct gaps give distinct canonical tilings. This verification is ordinary inspection, not an executed enumeration.

For I={0,...,25}, any canonical two-point tile is {0,r}. In each residue chain modulo r, the bottom point must be in B, membership alternates, and the top point cannot be in B because its r-translate would leave I. Every chain length is even. Write 26=qr+t, 0<=t<r. If t>0, both q and q+1 occur as chain lengths (including length-one cases when q=0), impossible; hence t=0 and q is even. Thus r=1 or 13, and alternation fixes B uniquely in each case. Translation of I to [26] preserves the count. Therefore three versus two refutes the exact literal conjecture. This is public prior resolution, zero credit; no need for a new certificate or Pi execution.

The fixed assignment contains twenty, with the three sustained mechanisms above and this separate public-resolution bridge. Per-ID results.json contains the remaining sixteen compact gaps. No root status changed; no nearby theorem was substituted for any literal answer.
