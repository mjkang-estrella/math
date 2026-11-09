# Frozen statement: quantitative rigidity of critical inverse-square affine laws

Arithmetic162f chronology alias; owned research root r162h. Source072 only.

Let H={z in C: Im z>0}, and let K be all injective holomorphic F:H->C with F(i)=0 and F'(i)=1, equipped with the topology of locally uniform convergence. Set Q_F=1/F' and
  (T_(x+iy)F)(w)=[F(x+yw)-F(x+iy)]/[y F'(x+iy)].
Let beta be any number in [3/4,1]. Let P be any Borel probability measure on K satisfying, for every x in R, every y>0, and every nonnegative Borel Phi:K->[0,infinity],
  integral_K |Q_F(x+iy)|^2 Phi(T_(x+iy)F) dP(F)
       = y^(-beta) integral_K Phi(F).
These are exact covariance hypotheses; no finite-scale or approximate-law hypothesis is substituted.

For a in R define
  F_a(z)=[(z-a)^2-(i-a)^2]/[2(i-a)],
and put F_infinity(z)=z-i. The parameter space R union {infinity} has its one-point compactification topology.

Claim A (uniform quantitative rigidity). There is a Borel map A:K->R union {infinity}, independent of P, beta, compact sets and derivative orders, such that for every nonempty compact E subset H and every integer m>=0 there exists a finite constant C_(E,m), independent of P and beta, with
  integral_K [ max_(0<=j<=m) sup_(z in E)
                    |F^(j)(z)-F_(A(F))^(j)(z)| ]^2 dP(F)
       <= C_(E,m) (1-beta)^(1/4).
Here F^(0)=F; no boundary smoothness, bounded image, finite-type restriction, or parameter-support condition is imposed.

Claim B (complete critical law). At beta=1 there is exactly one such probability measure. It is the pushforward of da/[pi(1+a^2)] on R by a->F_a. In particular it gives no mass to the affine limit F_infinity. This measure satisfies the displayed covariance for every nonnegative Borel test.

This is the entire proposed theorem. No best exponent or explicit numerical value for C_(E,m) is asserted. Claims A and B will be developed together without changing these bytes. This file is a statement freeze, not a correctness, contribution, acceptance or count decision. Parent alone requests those independent reviews.
