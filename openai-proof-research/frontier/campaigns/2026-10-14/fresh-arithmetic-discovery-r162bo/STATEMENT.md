# Frozen author statement: sharp entropy bound for interval variance energy

For every Borel probability measure rho on the real line that is concentrated on a finite or countably infinite set, write p_x=rho({x}) for its positive atom masses and assume its discrete Shannon entropy in natural logarithms is finite:

 H(rho) = sum_{x:p_x>0} p_x log(1/p_x) < infinity.

For every half-open bounded interval I=[a,a+r), r>0, define

 F_rho(I) = inf_{c in R} integral_I (x-c)^2 d rho(x),
 V_rho(r) = (4/r^3) integral_{a in R} F_rho([a,a+r)) da,
 E(rho) = integral_0^infinity V_rho(r) dr/r.

A zero-mass interval contributes zero. All integrals defining E are nonnegative Lebesgue integrals, initially allowed to be infinite; no moment of rho, boundedness of its support, discreteness of its topological support, positive minimum atom mass, or positive minimum inter-atom spacing is assumed.

Then

 E(rho) <= H(rho)/3 < infinity.

The universal coefficient 1/3 is optimal: if U_N is the uniform probability on {1,...,N}, then

 lim_{N->infinity} E(U_N)/H(U_N) = 1/3.

The same measure rho occurs in every quantity. The statement concerns actual atom masses after coincident locations have been merged, and does not substitute entropy of any symbolic presentation. All logarithms, the factor 4, both integration ranges, and the ordinary integer limit N->infinity are part of the frozen statement. No dimension formula, absolute continuity, higher-dimensional energy, effective algorithm, or claim about the optimal constant in additive entropy loss is included.

This is an author-proof nominee. Independent correctness and substantial-contribution reviews, all gates, and campaign counts belong to the parent.
