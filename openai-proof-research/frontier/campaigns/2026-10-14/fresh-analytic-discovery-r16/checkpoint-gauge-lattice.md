# Screening checkpoint: a lattice obstruction for the moment gauge

This is a proved deterministic observation, not a substantial nomination or an independent review. Family230 source truth is stipulated. No full discovery target has been frozen.

Let 0<kappa<8 and suppose 4/kappa is rational. Write 4/kappa=A/B in lowest terms. The qualitative source defines a=2/kappa, integer ell_n, and radii r_ni=exp(-n^2-2a(i-1)(ell_n+n)). Thus all -log(r_ni) belong to B^(-1) Z. Put delta=1/B and d=1+kappa/8.

Claim: its full gauge h cannot be regularly varying of index d at zero. In particular h(r) cannot be asymptotic to c r^d (log log(1/r))^((2-d)/2) for any 0<c<infinity.

Proof. On each open interval j delta<t<(j+1)delta, every radius knot exp(-t_ni) lies outside the interval. Therefore the full infimum defining f(t)=h(exp(-t)) is

f(t)=min(U_j,V_j exp(-2t)),

where U_j is the infimum of b_ni exp(-d t_ni) over knots t_ni<=j delta, and V_j is the infimum of b_ni exp((2-d)t_ni) over knots t_ni>j delta. Empty sets have infimum infinity. Positivity of h makes the relevant infima positive; at most one crossing occurs. Consequently log f is affine with slope either 0 or -2 except at at most one downward switch inside this interval.

Suppose h is regularly varying of index d. With epsilon=delta/8, at each of the three fixed interior locations t_j=j delta+delta/8, j delta+3delta/8, j delta+5delta/8, regular variation implies

log f(t_j+epsilon)-log f(t_j) -> -d epsilon.

These three disjoint subintervals cannot all contain the single switch. On at least two the increment is exactly 0 or -2 epsilon. The distance of either possibility from -d epsilon is at least epsilon min(d,2-d)>0, contradicting convergence at all three locations. This proves the claim. No moment asymptotic, estimate for ell_n, or numerical test is used.

This does NOT disprove two-sided comparability of the two gauges, equality/proportionality of their induced Hausdorff measures, or regular variation for irrational 4/kappa. The source already cautions that the moment gauge need not have regular asymptotics. The short lattice-envelope argument is technical and should not be counted as a substantial result.

Read dependencies: qualitative gauge.tex in full (definition, radii, finite-exclusion proposition); coefficients.tex in full (ell_n depends on integer moment cutoffs); qualitative introduction.tex lines1-100 and onepoint.tex parameter declaration; explicit introduction.tex in full. Identities are in inputs/source-identities.json. One oversized display of explicit local-laws.tex was truncated; no full reading of that file is claimed and it is not used above.
