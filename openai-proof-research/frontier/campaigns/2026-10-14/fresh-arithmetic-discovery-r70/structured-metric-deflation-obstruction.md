# Structured unital metric deflation can increase both residuals

This is an author method obstruction for the unchanged T101G69 target. It is not a counterexample to that target and is not a nominee. Unlike the earlier ordinary-deflation obstruction, it includes the prescribed unit-preserving metric correction. Unlike an arbitrary unital algebra, the example is an actual compressed product of an HS-orthonormal family of symmetric matrices containing the physical identity, with row Gram below the identity. Its projected multiplication slices are noncommuting even though its representing matrices happen to be diagonal.

Write beta2(T)=||B(T)-I||F^2 and C(T)=sum_{i<j}||[X_i,X_j]||F^2, with unnormalized norms. There is a five-dimensional symmetric cubic T with B(T)<=I and an exact unit for which EVERY global-maximizer metric deflation described in r69/unital-metric-deflation.md increases both beta2 and C. Consequently no positive linear combination a beta2+b C is a decreasing one-step potential for that operation, even within its structured ambient class.

## 1. Exact ambient realization

Inside real diagonal 6-by-6 matrices take the following HS-orthonormal basis:

 Y0=diag(1,1,1,1,1,1)/sqrt(6),
 Y1=diag(2,-1,-1,0,0,0)/sqrt(6),
 Y2=diag(0,1,-1,0,0,0)/sqrt(2),
 Y3=diag(0,0,0,2,-1,-1)/sqrt(6),
 Y4=diag(0,0,0,0,1,-1)/sqrt(2).

Let W be their span and define T_ijk=tr(Yi Yj Yk). Equivalently its polynomial, in coordinates (x,y,z,u,v), is

 T(q,q,q)=b[x^3+3x(y^2+z^2+u^2+v^2)+y^3-3yz^2+u^3-3uv^2], b=1/sqrt(6). (1)

Direct diagonal multiplication gives sum_i Yi^2=(5/6)I6. The physical identity lies in W and corresponds to the exact unit e=sqrt(6)e_x. Thus ||e||^2=6, dim W=5, and the physical/cubic dimension difference is just one. This example has none of the large-unit or missing-matrix-representation qualifications of a generic unital construction.

The slice Gram and residuals are

 B(T)=diag(5/6,2/3,2/3,2/3,2/3),
 beta2(T)=17/36, C(T)=1/3. (2)

For the commutator calculation, X0=b I5 commutes with everything. Within either harmonic pair, the commutator norm squared is 2b^4. Each of the four cross-pair commutators also has norm squared 2b^4. Thus six pairs contribute 12b^4=1/3. In particular the cubic slices do not commute.

## 2. All global maxima

Write r1=sqrt(y^2+z^2), r2=sqrt(u^2+v^2), r=sqrt(r1^2+r2^2). The harmonic terms are at most r1^3 and r2^3. Reflecting x to be nonnegative increases (1). Since r1^3+r2^3<=r^3,

 T(q,q,q)<=b(x^3+3xr^2+r^3), x^2+r^2=1, x>=0.

For r>0 put t=x/r. The derivative of (t^3+3t+1)/(1+t^2)^(3/2) is

 3(1-t-t^2)/(1+t^2)^(5/2).

It changes sign once, at tau=(sqrt(5)-1)/2. The endpoint values at t=0 and infinity are 1, strictly below the interior maximum. Equality in r1^3+r2^3<=r^3 requires one r_i to vanish; equality in the remaining harmonic term requires its angle to be a multiple of 2pi/3. These six choices are related by orthogonal symmetries of (1).

Set a=sqrt(1+tau^2)=sqrt(2-tau). A representative global maximizer and its coefficient are

 v0=(tau,1,0,0,0)/a,
 lambda=b*5tau/a^3, lambda^2=(5+sqrt(5))/12. (3)

## 3. The actual metric correction

An orthonormal tangent basis is w=(1,-tau,0,0,0)/a together with e_z,e_u,e_v. In that order L_v0 restricted to the tangent space is diagonal. The correction metric G=I-L_v0/lambda is

 G=diag(1,gz,gu,gu),
 gz=(1+tau)/a^2=(5+3sqrt(5))/10,
 gu=1/a^2=(5+sqrt(5))/10. (4)

These identities follow by substituting tau^2=1-tau; the w eigenvalue of L_v0 is zero. Let S be the ordinary orthogonal compression and S'=S(G^(-1/2).,G^(-1/2).,G^(-1/2).). This is precisely the r69 unit-preserving operation, without omitting its nonorthogonal change of metric.

Before correction the coefficients of w^3,w z^2,w u^2,w v^2 are respectively p,p gz,p gu,p gu, where p=b a. The remaining harmonic cubic is b(u^3-3uv^2). Applying G^(-1/2) therefore gives exactly

 S'(w,z,u,v)=p[w^3+3w(z^2+u^2+v^2)]+d(u^3-3uv^2),
 p=b a, d=b a^3. (5)

This tensor has exact unit e_w/p, which is the projection of the original unit to v0-perp as required. Its residuals can be computed without irrational square roots of p or d by setting

 P=p^2=(5-sqrt(5))/12,
 Q=d^2=(25-10sqrt(5))/6.

The Gram is diag(4P,2P,2P+2Q,2P+2Q), and

 beta2(S')=(4P-1)^2+(2P-1)^2+2(2P+2Q-1)^2
           =(4627-2065sqrt(5))/18,
 C(S')=4P^2+2(P-2Q)^2=(8345-3715sqrt(5))/36. (6)

The commutator formula follows because the w slice is p I4; the z-u and z-v pairs each contribute 2p^4, while the u-v pair contributes 2(p^2-2d^2)^2. Orthogonal symmetry makes these same values apply at every global maximizer.

## 4. Strict signs and exact consequence

Subtracting (2) from (6),

 beta2(S')-beta2(T)=(9237-4130sqrt(5))/36>0,
 C(S')-C(T)=(8333-3715sqrt(5))/36>0. (7)

No floating-point sign decision is needed: all integer coefficients are positive and

 9237^2-5*4130^2=37669>0,
 8333^2-5*3715^2=432764>0.

Thus every a,b>0 gives a beta2(S')+b C(S')>a beta2(T)+b C(T). Any proposed one-step accounting that additionally pays a nonnegative extraction cost fails as well. Appending any number of orthogonal exact unit factors leaves the two residuals unchanged; extracting those exact factors first costs nothing and eventually reaches this obstruction. Hence the obstruction persists at arbitrarily small residual per dimension. It does not imply small operator density, which is a different hypothesis.

## 5. Limits

This disproves monotonicity of the specified residual potentials for the specified metric-deflation operation, including in the structured matrix-product setting. It does not exclude a potential with additional variables, a grouped or amortized procedure allowing some increases, a different decomposition, or the full T101G69 estimate. The exact full target is still open. No independent review, novelty award, publication, or campaign count change is claimed. The proof above is direct finite-dimensional algebra; the attached exact checker is a reproducibility diagnostic, not a replacement for the universal proof.
