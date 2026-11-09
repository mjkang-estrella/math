# Full section volumes under the dense vertical architecture

This removes the far-vertical-section debt identified in dense-gaussian-vertical.md. It controls horizontal AVERAGES, not pointwise overlap or coverage. The full frozen target is unchanged.

## Lemma

Let f be a log-concave probability density on R^D, with its canonical section-density version when relevant. Suppose

 (1/2) gamma_D(y) <= f(y) <=2 gamma_D(y) for |y|<=R,
 R=100sqrt(D).

Let h^2=2pi^2/log(16D) as in dense-gaussian-vertical.md. Then uniformly in y,

 h^D sum_(l in Z^D) f(y-hl) <=4,

and sup_y f(y)<=2gamma_D(0). For all sufficiently large D, the periodized density is also bounded below by5/14, using only terms with |y-hl|<=2sqrt(D).

## Proof of the far-field bound

Put g0=(2pi)^(-D/2). For r>=R and a unit theta, concavity of log f on the segment from0 to rtheta gives

 log f(rtheta) <=(r/R)log f(Rtheta)−(r/R−1)log f(0)
 <=log(g0/2)+(r/R)(log4−R^2/2)
 <=log(2g0)−Rr/3.

If f(rtheta)=0 the bound is automatic. This proves the global maximum assertion as well. The inequality is valid at support endpoints by radial continuity of section volumes: convex interpolation of the endpoint section with any interior section gives the required lower semicontinuity along the ray, and compactness gives upper semicontinuity. Thus boundary-only exceptional density values are not inserted.

To sum the tail, let v_l=y-hl and partition space into side-h cubes Q_l centered at v_l. Their circumradius delta=h sqrt(D)/2 is at most R/4 for every D>=1. If |v_l|>R and z in Q_l, then |z|>=3R/4 and |z|<=3|v_l|/2. Hence

 exp(−R|v_l|/3) <=exp(−2R|z|/9)
 <=exp(−R^2/12) exp(−R|z|/9).

Multiplying the value at v_l by h^D and integrating this pointwise bound over Q_l, then summing, yields

 h^D sum_(|v_l|>R) f(v_l)
 <=2g0 exp(−R^2/12) integral_R^D exp(−R|z|/9) dz
 <=2 exp(−R^2/12) [18sqrt(D)/(sqrt(2pi)R)]^D <1.

The last integral bound follows from |z|>=|z|_1/sqrt(D) and tensor integration. The core sum is at most2h^D sum gamma_D(v_l)<=2exp(1/7)<3, so the full sum is<4. The lower bound follows from the earlier Gaussian truncated-mass estimate5/7 and f>=gamma_D/2 inside that truncation radius.

## Application to the actual convex body sections

For the source Gaussian-marginal normalization, let f(y)=vol_m(K_y)/vol_n(K). Brunn--Minkowski makes f^(1/m) concave on its support, hence f log-concave. The actual Eldan--Klartag input stated in source preliminaries.tex is TWO-SIDED on |y|<=n^beta, though the source only uses the lower half. With D=ceil(4loglog n), R=100sqrt(D)<n^beta eventually and the relative error is<1/2. Horizontal section translations in the source affine preparation do not change f. Therefore the lemma applies to the ACTUAL full sections, not merely the inner labels.

For Gamma={(a+Zl,hl):a in Lambda_h,l in Z^D}, D_h=vol(K)/(rho h^D), horizontal averaging gives, at every height y,

 E_(x mod Lambda_h) m_K,Gamma(x,y)
 =D_h^(-1) sum_l vol_m(K_(y-hl))
 =rho h^D sum_l f(y-hl) <=4rho.

The sum is finite at fixed y because K is compact. Its lower bound is at least(5/14)rho for all sufficiently large n. Every individual section has normalized load at most2rho A_D, with A_D=(pi/log(16D))^(D/2), so even unselected sections have no large-load spike.

This eliminates the prior vertical mean obstruction, including tails. It does NOT turn an average into essential maximum: the missing problem is to choose the common horizontal lattice and shear with pointwise upper counts O(rho), while simultaneously eliminating holes. The convex strip counterexample still forbids a naive q-fold independent intersection estimate. No full target theorem follows yet.
