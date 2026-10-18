# T022BA43 continuation: graph admissibility does not pay the energy budget

Disposition: unresolved, no nomination, no contribution count. The unchanged full target is frozen-scope.md, byte-identical to r43. In particular ordinary numerator coprimality, every badly approximable shift, arbitrary support and bare totient-weighted divergence remain required. The disproved uniform pairwise quasi-independence estimate is not revived. The following is a bounded continuation of two genuinely different proof routes, not a proof or disproof of the target.

## Route 1: normalize the additional ordinary-coprime sieve

Consider a squarefree product q of odd primes at which the source's model exclusion and ordinary coprimality exclude distinct residue classes. Write

R(q)=∏(1−1/p), D(q)=∏(1−2/p), h(q)=R(q)/D(q)=∏(p−1)/(p−2).

Uniform CRT averaging is over residues modulo q. A nonnegative weight w supported on the simultaneous survivors, with mean R(q), satisfies by Cauchy–Schwarz

(Ew)² ≤ D(q) Ew², hence Ew² ≥ R(q)h(q).

Equality holds precisely for the constant surviving weight w=h(q). More generally, restoring a fraction λ of the ordinary-coprime mass forces Ew²/Ew ≥ λh(q). This obstruction applies to every reweighting on that support, not just a constant multiplier. Over increasing odd primorials h(q) is unbounded: h(q)R(q)=∏[1+1/(p(p−2))] has a finite positive limit, whereas R(q) tends to zero by Euler's divergent prime reciprocal product. All local residue calculations are exact; no equidistribution claim about actual selected source rows is imported.

The source's table variance budget (tables.tex, proof surrounding tab:variance-budget, lines 468–542) charges discarded mass using the fixed raw cap N0, and bounds terminal square energy by N0W. The normalized local weight is eventually above any fixed N0. Clipping it to N0 preserves only min(1,N0/h(q)) of the intended mean. Splitting it into colocated labelled portions does not change the square of their total class mass. Raising the cap to N0h(q) changes the purported uniform energy constant. The above inequality shows a nonconstant redistribution cannot restore the same mean with uniformly bounded second/first ratio either.

This is a failure of the proposed normalization interface. It does not prove that every actual source selection encounters these residues, nor exclude a new selection or energy argument that avoids or separately pays them. The prime 2 need not be considered: odd conflict primes already force the unbounded loss.

## Route 2: arithmetic graph absorption and sparse block stratification

The local factors h_p=(p−1)/(p−2), p odd, and h_2=1 are bounded, tend to one, and satisfy ar:h-moments for every fixed real m>0. Indeed h_p^m−1=O_m(1/p), so the logarithm of the product is O_m(∑p^−2). Thus this h is an admissible inflation function for ar:lcm. This observation alone is insufficient.

The exact source edge interface is e(v,w)≤f(v)g(w) h(v/(v,w))h(w/(v,w)), with f≤φ and g≤φ. It is not h(v)h(w). For squarefree v,w, normalized whole rows contribute an additional h(d)², d=(v,w), from shared conflict primes. No cancellation of that factor has been derived.

Even fixing a common squarefree divisor d coprime to stripped rows does not repair the estimate by ordinary scaling. Stripping d changes vertex capacities by φ(d), the lcm cutoff Z by d, and the edge multiplier by φ(d)²h(d)². At exponent 1/2<u<1, restoring the source estimate costs

h(d)² [φ(d)/d]^{2(1−u)}.

Since h(d)R(d) is bounded above and below on odd squarefree d, this is comparable to R(d)^{−2u}, which is unbounded. This computation concerns the attempted common-divisor use of the exact ar:lcm contract, not an assertion that no stronger graph theorem exists.

Exact overlap separation also does not bound these common primes. From r43, for q=gm, r=gn with (m,n)=1, overlap requires

g² ≤ cγ^−1 |r−q|(rψ(q)+qψ(r)).

Substitution cancels g² and leaves

1 ≤ cγ^−1 |n−m|(nψ(q)+mψ(r)).

Thus the necessary condition has no independent control of the common multiplier g. It cannot bound h(g) by itself. This is a necessary-condition observation, not a construction of overlaps for every g.

Finally, partitioning selected rows into dyadic h-buckets does not recover bare divergence. If bucket mass is W_j and the cap repair retains O(2^−jW_j), ΣW_j=∞ does not imply Σ2^−jW_j=∞; W_j=1/j is an explicit numerical counterexample. Nor must a single bucket have infinite mass. This is an obstruction to inference from divergence alone, not a claimed realizable assignment of denominator masses satisfying all source constraints. The dense-window estimate from r43 still counts ambient rows, whereas the required theorem measures arbitrary selected rows by φ(q)ψ(q)/q. No selected-support estimate bridging this discrepancy has been proved.

## What remains unpaid

A proof would need a selection or aggregate mechanism controlling simultaneous conflict primes without losing arbitrary totient-weighted divergent mass, or a replacement for the fixed-cap energy budget. The admissible inflation function, fixed-gcd stripping, exact necessary separation, and dyadic bucketing do not supply it. No monotonicity, density, restricted shift or extra-divergence surrogate is offered.

Chronology correction: an exploratory progress message initially said the graph estimate absorbs h. A later message corrected this before sealing: the moment hypothesis holds, but the actual edge interface omits shared-prime inflation. This report incorporates the exact corrected conclusion.
