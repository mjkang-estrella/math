# A different vertical lattice: uniformly bounded full Gaussian mass

This is a positive replacement of the source's vertical weight module, not a full covering theorem. It avoids the zero-atom obstruction and retains ALL nearby lattice points rather than a binary suffix pattern.

For D>=1 set h^2=2pi^2/log(16D), Lambda_v=h Z^D, and

 Theta(y)=h^D sum_(l in Z^D) gamma_D(y-hl).

The Fourier coefficients of the one-dimensional periodization are the Gaussian transform exp(-2pi^2 k^2/h^2). Absolute convergence justifies its Fourier series. Writing t=1/(16D),

 |h sum_l gamma_1(y-hl)-1| <=2 sum_(k>=1)t^(k^2)<=2t/(1-t)<=1/(7D).

Taking products proves, uniformly in y,

 6/7 <= (1-1/(7D))^D <= Theta(y) <=(1+1/(7D))^D<=exp(1/7).

The first inequality is Bernoulli's inequality. Every single normalized atom is at most

 A_D=h^D gamma_D(0)=(pi/log(16D))^(D/2).

This tends to zero faster than exp(-cD) for every fixed c. In particular this full lattice has no hidden zero-atom spike.

## Truncating to a controlled geometric radius

For R=2sqrt(D), Gaussian exponential tilting gives

 h^D sum_(|y-hl|>R) gamma_D(y-hl)
 <=exp(-R^2/4) 2^(D/2) Theta_(h/sqrt2)(y/sqrt2)
 <=exp(1/7) exp(-(1-(log2)/2)D).

The last periodization has Fourier parameter t^2, hence obeys the same upper bound. For all sufficiently large D this tail is at most1/7. Therefore the pattern of ALL l with |y-hl|<=2sqrt(D) has normalized total weight >=5/7 and maximum atom <=A_D. No auxiliary pattern selection is required. A bounding cube gives cardinality at most

 (2R/h+2)^D <=(C sqrt(D log(16D)))^D=exp(O(D log(D+2))).

Modulo hZ^D, the raw indices belong to a fixed finite integer alphabet of size O(sqrt(D log(D+2))) per coordinate. At an exceptional sphere boundary include all equality points; all estimates remain valid.

## Compatibility with the source section-load scales

Take D=ceil(4 loglog n), for n sufficiently large, and rho=C_*n log n. Then D and R lie within the source Gaussian-section preparation range. The new vertical covolume is h^D. With D_h=vol(K)/(rho h^D), the source inner section labels have loads u_l comparable to rho h^D gamma_D(y-hl). Consequently their total load is >=c rho, while

 max_l u_l/n <=C log n A_D ->0.

Indeed log A_D=-(D/2)log(log(16D)/pi), whose ratio to loglog n tends to minus infinity. The number of pattern points is exp(O(D log D))=n^o(1); deleting loads below sqrt(n-D) loses at most n^(1/2+o(1))=o(rho). The source common-horizontal-lattice lemma can therefore still be applied to the retained labels. These numerical conclusions use the actual source constants and do not change its horizontal theorem.

## Precisely what is not supplied

These patterns have many integer choices per coordinate, not the binary-suffix property. The source simultaneous-shear lemma therefore DOES NOT apply. The convex-section counterexample shows that a naive q-fold product expectation is false even with exponentially small holes. This module does not produce a successful common shear or exact coverage.

Moreover Theta controls Gaussian weights and, through inner labels, the lower covering load. It does not yet control the FULL periodized section volumes outside the Gaussian core, nor the essential maximum of each horizontal lattice section. A full thin-covering proof requires both those upper controls in addition to a new multibranch coverage mechanism. No supporting module is nominated as the full target.
