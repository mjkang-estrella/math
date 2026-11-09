# Noncommuting Schur reduction: exact interface and transport debt

Live author work following the completed small-deficit and commuting-pencil notes. The full frozen all-deficit target is unchanged. The PSD trace interface is r102 author assistance, checked below; it is not an independent gate.

## 1. The controlled Schur block

Let Q be the constant spectral projection of B onto eigenvalues outside [1/2,2], P=I-Q, k=rank Q, and Omega=sum omega(lambda(B)). The explicit source omega implies a finite absolute c with

 k+tr(Q sqrt B)<=c Omega.

Indeed (1+sqrt lambda)/omega(lambda) is bounded on this closed complement: omega has its only zero at1 and is asymptotic to a positive constant times sqrt lambda at infinity. For K=q(L) and the actual positive Hessian J, put epsilon²=E||J-K||F². The scalar bound q(t)<=q(0)+|t| and operator concavity of square root give

 E tr(QJ)<=q(0)k+tr(Q E|L|)+sqrt(k)epsilon
          <=q(0)k+tr(Q sqrt B)+sqrt(k)epsilon
          <=C Omega+epsilon²/2.                         (1)

This applies to source J with Omega<=2000delta and epsilon²<=1000delta. Gaussian integrability follows from the source L2 estimates. For SPD J, its Schur complement gives pointwise

 J_QP J_PP^(-1) J_PQ <= J_QQ,
 E tr[J_QP J_PP^(-1) J_PQ]<=C delta.                    (2)

All inverses here are of the GOOD block. Formula (2) is not a trace bound for J_PQ J_QQ^(-1) J_QP: the latter is a good-dimensional matrix and is bounded by J_PP, whose expected trace can scale with the good dimension.

## 2. What the exact partial Legendre transform supplies

Write coordinates (u,v) in the bad and good spaces and J=D²phi. Where the good-gradient map is inverted, SPD gives a smooth local inverse and the following partial Legendre identities. If global existence of each fiber optimizer is additionally available, the same identities hold for the global transform; no global optimizer assertion is needed below:

 psi(u,y)=sup_v {y·v-phi(u,v)},  y=partial_v phi(u,v).

At its optimizer v=v(u,y), differentiation gives

 partial_y psi=v,   partial_u psi=-partial_u phi,
 D_y²psi=J_PP^(-1),
 D_u v=-J_PP^(-1)J_PQ,
 -D_u²psi=J_QQ-J_QP J_PP^(-1)J_PQ >=0.                (3)

Thus (2) controls the squared derivative of the inverse fiber map in the metric J_PP:

 sum_a (partial_(u_a)v)^t J_PP (partial_(u_a)v)
      =tr[J_QP J_PP^(-1)J_PQ].                         (4)

Equivalently, for the forward fiber maps v->F_P(u,v), the velocity partial_u F_P=J_PQ has squared norm in the inverse metric J_PP^(-1) bounded in expectation. The averaging in (2) is with respect to the ORIGINAL Gaussian (u,v), or equivalently its pushforward in (u,y); it is not integration against a product Gaussian in (u,y).

This is a genuine variational reduction, but neither (3) nor (4) yet controls Euclidean W2 between the good-output fiber laws. The Euclidean forward velocity has squared norm tr(J_QP J_PQ), which needs an additional J_PP factor. An upper operator bound on J_PP would supply that factor, but is unavailable uniformly for the source class. Nor may one apply Gaussian Poincare to (u,y) as if those coordinates remained independent Gaussian.

## 3. A precise failure of the bare Schur-to-Euclidean inference

Even for smooth quadratic convex potentials the weighted energy in (2) alone does not bound Euclidean good-fiber fluctuation with a universal coefficient. For one bad and one good coordinate take

 phi_M(u,v)=u²+sqrt(M)uv+(M/2)v²,  M>0.

Its Hessian is [[2,sqrt M],[sqrt M,M]], positive definite with determinant M. The Schur mixed energy is (sqrt M)²/M=1, while

 E|F_P(u,v)-E_u F_P(u,v)|²=M

under independent standard Gaussian u,v. The partial Legendre transform is psi_M(u,y)=(y-sqrt M u)²/(2M)-u², so (3)-(4) also verify directly. This example refutes only a generic metric conversion from (2), not the entropy target or an estimate using covariance normalization and spectral slack. In particular its good-output variance M²+M is not isotropic, and the retained W/covariance normalization could suppress it. It is not a source-compatible counterexample.

The remaining task is to use that normalization or the full q(L)+Y structure to control good-fiber changes in the OUTPUT metric relevant to the original isotropic law. A bare Schur inequality or partial Legendre transform does not do so. No partial-factor law or full-target conclusion is asserted.

## 4. Exact Euclidean decoupling criterion and what it would buy

Let F_P(u,v) be the good-output projection and define barF_P(v)=E_u F_P(u,v), with Gaussian conditional expectation. Gaussian Poincare in u, integrated over v, gives the exact sufficient estimate

 E|F_P-barF_P|²<=E||J_PQ||F²
               <=2E||P q(L)Q||F²+2epsilon².             (5)

The averaged map is a gradient of a convex potential in v: its weak derivative is E_u J_PP, positive semidefinite. Centering is inherited. Under the constant output weight W_P, the corresponding squared cost is at most (40/37) times (5). Thus an O(delta) bound on the first term on the right would remove bad-input dependence at the required cost, with no upper operator bound on J_PP.

There is a real structural distinction between (2) and (5). Source goodness PBP<=2P implies

 E P q(L)² P <=2q(0)²P+2PBP<= [2q(0)²+4]P,             (6)

by scalar functional calculus before compression. This is an EXPECTED operator bound, not a pointwise bound and not independence from the Schur velocity. Multiplying it by a random velocity and taking expectations is invalid. Its trace can scale with rank P, so (6) alone does not give the O(delta) mixed bound in (5).

Even if (5) is established, one must not apply the source entropy theorem to the law of barF_P merely because it is a convex gradient image of Gaussian measure: such an image is not automatically log-concave. A valid continuation would identify barF_P with, or approximate it by, a good-dimensional pencil primitive having the residuals needed for the algebraic argument, or prove another legitimate product-factor statement. Finally the existing partial-factor-lifting lemma pays only 2k for the removed output dimensions, with k=O(delta). These are separate steps; neither is inferred from convexity of the averaged potential.
