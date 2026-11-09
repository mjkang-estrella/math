# Ordinary mechanisms and exact gaps

No numerical, enumeration, solver or Lean execution was used. None of these routes is a completed candidate. Closed special cases are not offered as separate results.

## 328300: Eulerian transform

Let A(n,k) use the source convention (k minus one descents). The required difference is
D_n = sum_(i,j) [A(n-1,i)A(n+1,j) - A(n,i)A(n,j)] x_i x_j.
A proof of coefficientwise nonnegativity after setting x_i=q^i only sums the bracket along i+j=m; it does not control the individual weights x_i x_(m-i). Thus substituting an arbitrary log-convex input into the known q-log-convexity theorem is an invalid deduction.

A sharper mechanism is Abel summation on each diagonal m. Define alpha_k by grouping the ordered bracket terms with {i,j}={k,m-k}, with the diagonal counted once. Then D_n=sum_m sum_(0<=k<=floor(m/2)) alpha_k x_k x_(m-k). For a positive log-convex input, w_k=x_k x_(m-k) is nonincreasing until the middle: w_(k+1)/w_k=(x_(k+1)/x_k)/(x_(m-k)/x_(m-k-1))<=1. If every prefix S_j=sum_(k<=j)alpha_k is nonnegative, then sum alpha_k w_k=S_last w_last+sum_(j<last) S_j(w_j-w_(j+1))>=0. This is a concrete sufficient finite Eulerian coefficient inequality for each n,m, not a solver plan.

Missing lemma: all those prefix inequalities, or another signed-pair transport giving the same weighted inequality. Strong q-log-convexity controls only S_last. No proof of the prefixes was found; they are not asserted true. Boundary zero inputs would require an additional limiting argument, for example perturbation by epsilon times R^k on each finite prefix with a justified preservation of log-convexity, not an unproved blanket continuity assertion.

A second route tried Zhu1609.01544 Theorem1.2. The Eulerian recurrence is A(n,k)=k A(n-1,k)+(n-k+1) A(n-1,k-1). The second coefficient decreases in k. The theorem requires nonnegative increasing functions in its separated recurrence, so its hypotheses fail. Reversing the row does not simply fix both coefficients. Proposition4.11 proves stability of polynomial differences, not the desired transform. Parked with full source/citing/journal clearance outstanding.

## 326977: logistic odds and integer facet slack

Source definitions give strictly graphical positive integer D and positive odds r_i with d_i=sum_(j!=i) r_i r_j/(1+r_i r_j). Put theta_i=log r_i. Monotonicity gives d_i<=d_j iff theta_i<=theta_j for n>=3: after cancelling the shared ij term, each remaining logistic term is increasing. The target is a single constant C bounding every |theta_i| by C log n, uniformly over D.

A proposed facet mechanism uses sorted theta, the threshold pattern theta_i+theta_j>0, and the strict integer Erdos-Gallai slack. Each positive integral slack is at least one. If all logistic edge probabilities were uniformly extremely close to one threshold graph, its facet slack would be too small. This explains why near-facet concentration should force a moderately sized theta_i+theta_j somewhere. It does NOT bound each theta_i: large positive and negative coordinates can cancel. Propagating control along pairs risks losses along a chain growing with n. No dimension-independent propagation lemma was established, and no O(log n) bound is claimed from generic convexity.

A second route uses source Lemma3.8/Remark3.15. Under d_max^2 < M/2, the paper already obtains r_max<=n^2 and r_min>=n^-3, hence |log r_i|<=3log n. This is a complete source-classical special case, zero new credit, and does not remove the density hypothesis. Complementing degrees interchanges r_i with 1/r_i, giving another already equivalent regime; it leaves mixed high/low degrees uncontrolled. Required next lemma is a uniform bound in this mixed regime, not the source sparse estimate again. v1/v2/v3 target passages agree; no complete latest-journal/citing review.

## 330592: heavy-subset families and compression

For fixed n,k,d, the objective is the number of k-subsets I with sum_(i in I) a_i>d divided by binom(n,k). There is an attained maximum despite the strict inequality: the realized objective values form a nonempty subset of the finite set {0,1,...,binom(n,k)}/binom(n,k). This elementary observation settles only existence of an optimizer and says nothing about equal positive weights; it earns zero credit.

Within any chamber defined by the subset thresholds, small perturbations preserve the heavy family. This suggests moving toward lower-dimensional faces. But a chamber boundary can hit sum_I a_i=d before a coordinate reaches zero or two unequal positive coordinates coalesce. With strict >d, a heavy subset can then be lost. Consequently a face/vertex argument alone does not force the equal-support form.

For two coordinates u,v, k-subsets containing both or neither are unchanged under (a_u,a_v)->(a_u+t,a_v-t). Subsets containing exactly one have threshold tests t>d-a_u-sum_J a_j and t<a_v+sum_J a_j-d, where |J|=k-1 and J avoids u,v. These opposing step functions need not improve under equalization. Missing lemma: choose a pair and a direction maintaining at least the optimal heavy count until an equal-support reduction occurs, with all equality thresholds treated literally. No such lemma or exact counterexample was obtained.

Reconciliation: r142 already investigated the accumulation-game sibling360433; r165 parked refined330593. Their earlier computations were read as historical notes, not rerun or claimed as proofs. Published caching-game counterexamples vary the game and do not by themselves refute this objective. The modern general source/citing classification remains incomplete, so this is not a Pi task.

## Source resolutions and semantic traps

371515: the original conjecture is not an immediate corollary of the original strict-streak theorem. The later soft-streak paper supplies the missing cluster proof: weights depend only on the first letter; Proposition3.3 yields a convolution; its generating function Phi(x) is explicitly solved and decomposed at the k-th roots of unity; Proposition3.7 sums first-letter weights; Theorem3.9 gives f(z). Theorem4.2 evaluates at z=1/n using the prior radius-of-convergence theorem. Both exact displayed formulas are already public. Definitions and printed k=4 examples were read. An independent useful convergence check is that disjoint blocks equal to one constant letter occur with probability n^-k, giving a geometric tail bound for waiting time; this does not create a new result.

319189: Angel-Holroyd Corollary2 lists exactly the four source words. Its proof uses E[N_middle]=9/4 from Theorem1 and the two possible middle-swap counts, 3 for the distinguished four and 2 for the others. Thus E=2+P(X), so P(X)=1/4. Theorem1 is proved via stationarity and Polya-urn exchangeability (Lemmas6/7). No novel bridge exists.

322860: absent an explicit pairwise-distinct condition, take a nonempty point (a,b) in S and repeat it four times with c=f=b,e=a. This tautological reading is not a significant solution. The source also says four elements without an explicit inequality; conventional distinctness may be intended. No intended distinct configuration theorem is proved here.
