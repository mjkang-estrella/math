# Exact unit-preserving metric deflation

Author continuation of the SAME full global target. This is an exact constructive operation on the unital ambient cubic from unital-ambient-full-reduction.md. It is not a completed trace-paid correction and supplies no independent nomination.

Let T be a fully symmetric cubic on a positive-dimensional Euclidean space, with product xy and an exact unit e: L_e=I. No bound on ||e|| is assumed. Choose a global maximizer v of T(v,v,v) on the unit sphere and let lambda=T(v,v,v). Oddness and the existence of a unit imply lambda>0. Stationarity gives vv=lambda v. Diagonalize L_v on v-perp, writing its eigenvalues as mu_i, and let S be the ordinary orthogonal compression of T to v-perp.

## 1. Exact construction

The maximum second derivative along each tangent direction gives mu_i<=lambda/2. Write e=a v+e_perp. The identity L_v e=v gives

    a=1/lambda,   diag(mu) e_perp=0.                  (1)

For a tangent vector x, compressing e x=x and using (1) gives

    L^S_(e_perp)=G:=I-diag(mu)/lambda >=I/2.           (2)

Thus ordinary compression is generally NOT unital with e_perp. Correct its metric instead: set

    P=G^(-1/2),   S'=P^tensor3 S.

The unit of S' is P^(-1)e_perp, because its multiplication matrix at that vector is P L^S_(e_perp) P=I. But (1) also gives G e_perp=e_perp, so in fact

    P^(-1)e_perp=e_perp.

The new unit is exactly e_perp, in the original Euclidean coordinates on the smaller space. In particular

    ||e_new||²=||e||²-1/lambda².                     (3)

Everything is finite dimensional and constructive: maximize the cubic, diagonalize one selfadjoint multiplication operator, and apply the positive square root of G. There is no division by a small singular value of G, since G>=I/2.

Iterating until the zero-dimensional space therefore gives the exact identity

    sum_j 1/lambda_j²=||e_initial||².                (4)

Here lambda_j is the maximum of the METRIC-CORRECTED product at step j. It is not the maximum of repeated ordinary orthogonal compressions. For the ambient matrix product the right side equals its physical matrix size m. Equation(4) has no hidden factor from a homotopy involving the unit.

## 2. Uniform one-step metric bounds

There is also an elementary lower bound mu_i>=-lambda, with no external tensor norm theorem needed. For a unit tangent eigenvector w, average the cubic on the two unit vectors v/2 plus or minus sqrt(3)w/2. The odd-in-w terms cancel; stationarity eliminates T(v,v,w). The average is

    (lambda+9mu_i)/8.

Each cubic value is at least -lambda by oddness and the global maximum. Hence mu_i>=-lambda. Therefore

    I/2<=G<=2I,  I/sqrt(2)<=P<=sqrt(2)I.              (5)

If M=sum_i mu_i², scalar differentiation on t in [-1,1/2] gives

    ||P-I||F <=sqrt(2) sqrt(M)/lambda.                (6)

Suppose B(T)<=bI at this step. Compression gives B(S)<=bI. Telescoping the three mode actions, using (5), yields

    ||S'-S||HS <=(2+sqrt(2)+1)sqrt(b)||P-I||F
                  <=5sqrt(2b) sqrt(M)/lambda.        (7)

The tensor coefficients removed by ordinary deflation, other than lambda v^tensor3, have squared norm exactly3M. Thus

    ||T-(lambda v^tensor3 + S')||HS²
          <=3M+50b M/lambda².                        (8)

The two terms are orthogonal here: the first has at least one v index, while the metric change is entirely tangent. Replacing the removed coefficient lambda by1 adds the orthogonal cost (lambda-1)².

For comparison with associators, in the stationary basis

    X_v=diag(lambda,diag(mu)),
    X_i=[[0,mu_i e_i^t],[mu_i e_i,S_i]].

The commutators with X_v alone give

    C(T)>=2 sum_i mu_i²(lambda-mu_i)²
          >=(lambda²/2)M.                            (9)

This is useful only with an adequate lower bound on lambda; it does not uniformly pay the M/lambda² term in (8).

## 3. Precise remaining accounting problem

This construction removes the previous approximate-unit obstacle. It also differs from the disproved naive Lyapunov argument: every step now includes a specific nonorthogonal metric correction, and ordinary-compression defect identities cannot be reused as if that correction were absent.

It does NOT prove the needed total cost bound. In particular:

* (4) controls inverse squared maxima by the initial unit size, not by the defect R. An O(m) budget is insufficient when R is much smaller than m.
* Although every P has condition number at most2, repeated changes act on nested spaces. Their distortions cannot be multiplied indefinitely and called dimension independent.
* The one-step Gram bound is B(S')<=8bI. No trace-paid invariant preventing growth over many steps has been proved.
* Corrections in successive remaining spaces overlap. Their squared Frobenius costs cannot simply be added as orthogonal errors; only the removed-index contribution at a single step in (8) is orthogonal.
* The lower bound (9) does not justify replacing M/lambda² by a uniform multiple of C when lambda is small.

A successful use of this exact operation must control the evolving Gram/associator energy and accumulated metric changes, or group the small-lambda steps into a defect-paid block. No such estimate is asserted here. The all-error global target remains open. This note uses direct calculations and the previous ambient reduction, not a new primary theorem or independent review.
