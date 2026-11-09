# MathDB 336276: personal second review and generic proof

Credit 0. No Lean or mathematical program was run. Root alone adjudicates.

## Audit of the first reconstruction

I read the complete supplied review-r1-PROOF.md before the author proposal. Its forest/copy-matching equivalence, Hall deficiency, threshold lower bound, suffix-maxima envelope, telescoping, finite-grid variance estimate, measurability and ordered limits are sound. The strict-comparison km error is harmless and unnecessary with weak comparisons. No ordinary mathematical error was found. This is verification of a disclosed argument, not a claim of independent invention.

The following simpler construction changes the significance assessment. It pays chronology without controlling arbitrary chronological Hall cuts.

## Generic nested-neighborhood lemma

Let A be a multiset of a real supply marks r, each with k copies, and B a multiset of a real demand marks l. Join a supply to a demand exactly when r<=l. The minimum unmatched demand count is

 d(A,B)=max(0, sup_t [#{l in B:l<=t}-k#{r in A:r<=t}]).                 (1)

Proof: Hall deficiency is max_S(|S|-|N(S)|), including the empty set. For a nonempty S choose t=max_{l in S} l. Then N(S) consists exactly of all supply copies with r<=t. Enlarging S to all demands with l<=t leaves this neighborhood unchanged: an original demand attaining t is present. Thus a maximizing Hall set is a threshold prefix. Conversely a threshold prefix has neighborhood contained in {r<=t}, so its displayed deficit is always a lower bound. Both inequalities prove (1), with all ties and zero neighborhoods allowed. The Hall deficiency identity itself follows by adding d universal dummy supplies and applying Hall; every matching must leave at least the maximum deficit, and Hall gives one leaving at most d.

## Generic iid interval law

Let (L_i,R_i) be iid pairs supported in [0,1]^2 with L_i<R_i almost surely and continuous marginal CDFs F_L,F_R. No independence between L_i and R_i is required. Fix integer k>=1. Let D_n be the minimum number of rooted chronological k-ary trees partitioning the first n intervals, where a parent i of j must satisfy i<j and R_i<=L_j. Put

 c=max_{0<=t<=1}(F_L(t)-kF_R(t)),

which is nonnegative since the value at 0 is zero (continuous marginals and no atom at 0). Then E[D_n]/n -> c. The compact-support/continuity assumptions suffice for the elementary proof below; no arbitrary-atom extension is asserted.

The primary source is Balogh et al., On the Heapability of Finite Partial Orders, DMTCS22:1(2020)#17, Definitions1-3 and5, Theorem1/Corollaries1-2, pp3-4,6-7. Its matching representation applies to the finite poset with order i<j and R_i<=L_j. This relation is transitive because L_j<R_j. A copy-matching gives indegree<=1/outdegree<=k and strict time forbids cycles. Its components are rooted chronological k-ary trees; each ancestry comparison holds by transitivity. Conversely assign the children of each parent injectively to its k copies. Consequently D_n=n-nu. Unique bijections are unnecessary; cardinality correspondence suffices.

Lower bound: the global Hall set S_t={i:L_i<=t} has neighbors contained in {i:R_i<=t}. Therefore
 E[D_n]/n >= F_L(t)-kF_R(t), hence >=c.                         (2)

Upper bound: choose m>=1 and n>=m. Write n=ma+r, a=floor(n/m), 0<=r<m. Use m consecutive time blocks B_1,...,B_m of size a and leave the r terminal observations as singleton roots. For q=1,...,m-1, use only edges from supplies in B_q to demands in B_{q+1}, and choose a maximum matching in this nested-neighborhood graph. Let d_q be its unmatched demand count. Its exact value is (1).

The UNION of these m-1 matchings is a valid matching in the chronological copy graph: demand copies of B_q occur only in the preceding pair, supply copies of B_q occur only in the following pair, and these are distinct bipartite vertices. A vertex may receive a parent AND have children, as the definition permits. No supply capacity or demand capacity is shared between two chosen matchings. Every edge goes to a strictly later block. Thus this union has sum_q(a-d_q) edges and

 D_n <= a+r+sum_{q=1}^{m-1} d_q.                                (3)

Let delta_q^L,delta_q^R be the sup-norm empirical-CDF errors in block q. From (1), simultaneously for all thresholds,
 d_q/a <= c+delta_{q+1}^L+k delta_q^R.                            (4)

It is immaterial that different block-pair matchings are probabilistically dependent: (3) is deterministic and only linearity of expectation is used. Let e_a bound the expected empirical error for either marginal, with e_a->0. Then

 E[D_n]/n <= [a+r+(m-1)ac]/n + [(m-1)a/n](k+1)e_a.              (5)

At fixed m, n->infinity gives limsup<=c+(1-c)/m. Let m->infinity and combine with (2). All k are fixed; no limit uniform in k is asserted.

For completeness, e_a->0 needs no imported empirical-process theorem. On the h-subdivision mesh, monotonicity yields delta<=omega_F(1/h)+max_mesh|F_a-F|. Continuous F on a compact interval is uniformly continuous, so its modulus tends to zero. Each mesh mean has variance<=1/(4a). Cauchy-Schwarz and max squares<=sum squares give expected maximum<=sqrt((h+1)/(4a)). First a->infinity, then h->infinity. For the literal marginals omega<=2/h, hence e_a<=2/h+sqrt((h+1)/(4a)). All counts and optima are finite measurable functions of endpoint comparisons; sup errors are measurable through rational thresholds. They are bounded, so all expectations used exist.

## Literal specialization and set version

Independent uniform U_i,V_i give L=min(U,V), R=max(U,V), with F_L(t)=2t-t^2 and F_R(t)=t^2. Thus
 F_L(t)-kF_R(t)=1/(k+1)-(k+1)(t-1/(k+1))^2.
The maximizing threshold lies in [0,1] for every integer k>=1. Consequently c=1/(k+1)>0, proving both clauses of the exact fixed-k>=2 literal. Ordered iid endpoint pairs, the rooted-tree convention, ancestor order, integrability and normalization have all been bridged.

For the unordered set the same source matching representation and the same threshold argument give the exact finite identity
 D_n^set=max(0,sup_t[#{L_i<=t}-k#{R_i<=t}]).                     (6)
For any nonempty demand set its largest L determines its entire neighborhood; no interval can be its own parent because R_i>L_i, and interval order prevents directed cycles. Uniform empirical convergence in (6) gives the same c directly. Alternatively D_n^set<=D_n and (2) squeeze its expectation. These are one family, with no additional credit.

For k=1 this yields 1/2, consistent with intervals covering 1/2 giving an antichain of expected size n/2. Source p4/p21's square-root width prose is erroneous under its actual definitions; companion p8 calls the cited square-root statistic LIS. This correction earns zero credit and is not the basis of exclusion.

## What is nonroutine?

The finite matching/forest theorem is already printed in the source. The optimizer is one line. Nested neighborhoods reduce Hall to thresholds by a maximum element, and adjacent-block union pays chronology at the cost of one initial block. Finite-grid empirical convergence is elementary. I identify no remaining mathematically nonroutine step in this reduction. The argument neither assumes a stationary Hammersley process nor identifies chronological cuts with global thresholds. The first review correctly warns against the latter error, but constructing a large submatching avoids it altogether.

This is a complete routine-application case, not an authenticated earlier verbatim solution or a worldwide novelty claim. The generic lemma/law here is reviewer-authored and personally checked, not represented as a named earlier theorem. The relevant authenticated earlier theorem is the source's own finite matching representation. Its application, with the explicit elementary construction above, is the basis of my EXCLUDE AS ROUTINE OR KNOWN recommendation (routine branch only).
