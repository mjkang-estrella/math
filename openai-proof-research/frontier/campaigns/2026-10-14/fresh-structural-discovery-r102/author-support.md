# Intermediate-deficit support, not a nomination

This is author assistance to the unchanged full target in analytic r100. No independent review, scope weakening, or theorem nomination. The all-deficit target remains unresolved. Calculations below isolate two tempting approaches, rather than prove general factor extraction.

## Uniform simplices do not give a growing-distance counterfamily

Put n=m+1>=2, H=1-perp in R^n, P its orthogonal projection, and let E have n independent mean-one exponential coordinates. Write S=sum E_i and D=E/S. Elementary change of variables in the product exponential density gives S independent of D, S~Gamma(n,1), and D uniform on the standard simplex. Put c=sqrt(n(n+1)) and X=c(D-1/n). Then X is isotropic on H; indeed Cov(D)=P/[n(n+1)]. Let W=P(E-1)=S PD. Both X and W have covariance I_H, and the same coupling gives

 a_n=E|X-W|^2=((c-n)^2+n)(n-1)/(n(n+1))<1,

since 0<c-n<1/2. This is an exact calculation using independence and E|PD|²=(n-1)/(n(n+1)).

Choose an orthogonal map O taking u=1/sqrt(n) to e_n by the rotation on span(u,e_n) and the identity on its orthogonal complement. Let R consist of its first n-1 rows and J=[I_(n-1),0]. Then RP=R, RR*=I, and tr(RJ*)=n-2+1/sqrt(n). Thus E|R(E-1)-J(E-1)|²=2(1-1/sqrt(n))<2. J(E-1) is the required m-fold centered product exponential. Minkowski yields

 W2²(Law(RX),Law(J(E-1))) <= (sqrt(a_n)+sqrt(2(1-1/sqrt(n))))² < (1+sqrt(2))² <6.

The entropy follows from the Euclidean volume sqrt(n)/(n-1)! of the standard simplex:

 delta_n=log(sqrt(n)[n(n+1)]^((n-1)/2)/(n-1)!)-(n-1)
        =0.5log n+0.5(n-1)log(n(n+1))-log Gamma(n)-(n-1).

Stirling gives delta_n -> 3/2-(log(2pi))/2, a positive constant. This is enough to rule out this family as a delta=o(W2²) example: numerator is uniformly bounded and the positive limit bounds the denominator below for large n. No exact optimal transport distance or sharp stability constant is claimed. Products of such blocks likewise have transport cost at most6 per block and additive deficits; this operation does not generate an unbounded ratio.

## Symmetric star: spectral deletion alone loses too much

Index coordinates 0,1,...,d. Set T_0ii=T_i0i=T_ii0=1/sqrt(2) for 1<=i<=d and all other entries zero. T is fully symmetric. Its slices satisfy

 B=sum_r X_r²=diag(d/2,1,...,1).

For P onto the last d coordinates and Q onto coordinate0,

 sum_r ||P X_r Q||F²=d/2,

whereas the source scalar slack is Omega(B)=omega(d/2)=O(sqrt(d)). Thus bad rank1 and full tensor symmetry do not imply mixed-block energy O(Omega). Deleting one bad direction is not a justified compression of q(L). This is only an algebraic obstruction to that inference; the pencil is not known to arise from the source transport normalization.

## Jacobian compatibility excludes the star at energy order d

The following argument was derived in parallel by this author and the parent; the parent's compact bump test is used below. It is author assistance, not independent review.

Let x=(x0,z) standard Gaussian, r=|z|, a=x0/sqrt(2), t=r/sqrt(2). The star pencil is

 L=[[0,z*/sqrt(2)],[z/sqrt(2),a I_d]], K=q(L).

On z-perp its eigenvalue is a. On span(e0,z/r), it has matrix M=[[0,t],[t,a]], eigenvalues lambda_±=(a±sqrt(a²+4t²))/2. Consequently

 sum_i K_ii=(d-1)q(a)+q(M)_22,
 sum_i z_i K_0i=r q(M)_12,
 q(M)_12=t(q(lambda_+)-q(lambda_-))/sqrt(a²+4t²).

The formulas hold by continuity also at r=0. From 0<q'<1, q(s)<=q(0)+|s|, q(s)/s->1 as s->+infinity, and q(s)->0 as s->-infinity, uniformly for x0 in a fixed compact interval,

 |q(M)_22|<=C+r,
 r q(M)_12/d ->1/(2sqrt(2)) in L1 as d->infinity.

For the second assertion, r²/d->1 in L2; on each fixed compact interval of a, q(M)_12/t->1/2 as r->infinity. Domination follows from |q(M)_12|<=t, the scalar divided-difference bound q'<=1. This gives uniform integrability r t/d and proves the assertion, including small-r events.

Choose a nonnegative nonzero smooth compactly supported h(x0), with support close enough to0 that q'(x0/sqrt(2))>1/2 there; q'(0)=2/pi>1/2. Define the Gaussian distributional curl test

 F_d(K)=E[(x0 h-h') sum_i K_ii - h sum_i z_i K_0i].

Gaussian integration by parts and the displayed formulas give

 F_d(K)/d -> c_h=(1/sqrt(2)) E[h(x0)(q'(x0/sqrt(2))-1/2)]>0.

The exceptional diagonal contributes O(sqrt(d))/d, since h and h' have compact support. For every matrix Jacobian J_ij=partial_i F_j with finite Gaussian L2 norm, commuting weak derivatives gives F_d(J)=0. The test coefficient matrix has squared Gaussian Frobenius norm exactly

 d E[(x0h-h')²]+d E[h²]=d C_h.

Thus ||K-J||²_L2,F >= F_d(K)²/(d C_h)>=c_h² d/(4C_h) for all sufficiently large d. The noncompact z test can be justified by smooth Gaussian radial cutoffs; integrability of J and its coefficient test lets the boundary terms vanish. No differentiability of J beyond its being a weak Jacobian is needed.

If this exact star L were the source's degree-one part and J=q(A), Frobenius functional-calculus Lipschitzness gives ||K-J||²<=||L-A||²=||Y||². The source remainder gives ||Y||²<=1000 delta. Therefore such a transport has delta>=c d. The star cannot occupy the missing delta=o(m) regime.

## Remaining debt

This rank-two calculation does not establish a general mixed-block coercivity estimate. An arbitrary pencil can have many noncommuting exceptional directions and no common scalar good-block eigenvalue. A usable theorem would control the transport cost of their removal by both Omega(B) and dist(q(L),Jacobians)², without Bop-dependent constants, and then retain enough near-exponential factors. Neither this note nor rank counting proves that theorem. General cones and other log-concave families remain open tests.

## Radial orthant cone models also have uniformly bounded cost

Here is a larger exact counterfamily screen. Let n>=2 and let Z in the positive orthant have density proportional to exp(-V(sum_i z_i)), where V is continuously differentiable and convex on [0,infinity), and the radial integration by parts below is valid (in particular it holds for V(r)=c r^p, c>0, p>=1). Assume nondegenerate covariance. Let X be the centered isotropization of Z. Then its distance squared to a rotated n-fold centered product exponential is at most10. This is a dimension-free upper bound for a family, not the target stability estimate C delta.

Write R=sum Z_i and D=Z/R. Changing variables gives D uniform on the simplex, independent of R, with radial density proportional to r^(n-1) exp(-V(r)). Integration by parts gives

 E[R V'(R)]=n,  E[R² V'(R)]=(n+1)ER.

Under the probability tilted by R/ER, the covariance of R and the increasing function V'(R) is nonnegative. (Its twice-covariance formula is E[(R-R')(V'(R)-V'(R'))]>=0.) Substitution gives

 (n+1)(ER)² >= n ER².                         (C)

For V=c r^p the boundary terms vanish at0 and infinity, so this proof is entirely elementary. We make no assertion here about arbitrary nonsmooth extended-valued V without supplying its approximation step.

On H=1-perp, Cov(PZ)=ER²/[n(n+1)] I_H. Cov(PZ,R)=0, so the tangent coordinates of the full isotropization are

 X_H=c R PD/sqrt(ER²), c=sqrt(n(n+1)).

Choose an independent S~Gamma(n,1), independent of (R,D). Then E=S D has n independent exponential coordinates. The same-direction coupling gives

 E|X_H-P(E-1)|²
 =2(n-1)[1-sqrt(n/(n+1)) ER/sqrt(ER²)]
 <=2(n-1)/(n+1)<2,                           (C1)

using(C). Map H isometrically to R^(n-1) with the rotation R_map from the simplex calculation. Its discrepancy from the first n-1 coordinates of E-1 has mean square less than2. Minkowski therefore gives a coupling of the n-1 tangent coordinates of X to n-1 independent centered exponentials at cost less than8. Append an independent centered exponential to the remaining, centered variance-one radial coordinate of X. Its cost is exactly2. Orthogonality gives total cost less than10. Independence of the appended exponential ensures the target is a full product; the actual radial coordinate of X need not be independent of its tangential coordinates.

For n=1 the elementary independent coupling costs2. Hence these smooth radial orthant models, including the entire p>=1 power family, cannot provide an intermediate-deficit counterexample with delta bounded below and W2²/delta diverging. They remain potential tests of small-deficit constants; this note proves no lower bound for their deficits and no bound proportional to a deficit tending to0.
