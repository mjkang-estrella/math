# Candidate: arbitrary-dimensional disk rigidity for attained complete polynomial equality

Status: **complete proposed analytical proof, not independently reviewed or accepted**. The exact assigned nondisk-equality target is resolved affirmatively if the proof below passes independent review: no finite-dimensional nondisk example exists. No scalar coefficient compression is asserted. R019 is consistent with the proof, including its rank-two norming pair.

## 1. Exact claim

For every finite n,m>=1, every complex n by n matrix A and every finite m by m matrix polynomial F(z), put M=max_{z in W(A)}||F(z)||, in Euclidean operator norms, with base-first evaluation F[A]=sum A^k tensor C_k. If M>0 and ||F[A]||=2M, then W(A) is a nondegenerate closed disk.

A stronger intermediate conclusion is useful. On any unitarily irreducible reducing block B for which ||F[B]||=2M, after normalizing M=1, there exist fixed coefficient subspaces E,G of equal positive dimension r, constant isometries U:C^r->E and V:C^r->G, and an r by r polynomial

    J(z)=V* F(z) U,

such that J is unitary at every point of the boundary of W(B), det J is nonconstant, and

    {z: |det J(z)|<1}=int W(B),
    {z: |det J(z)|=1}=boundary W(B).

The exterior inverse J(z)^-1 is rational, analytic off W(B), continuous up to its boundary, and vanishes at infinity. These are determinant and matrix-channel conclusions, not constant scalar-channel conclusions.

## 2. Credited inputs and the new bridge

All OpenAI mathematics at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb is stipulated true. The actual pinned direct proof is read: the original mass-two resolvent, Faber coefficient inequalities, both ordered multiplier tests, and the residual identity. The already reviewed R016/I245 exterior-limit argument is used in its dimension-independent scope, detailed below. The new steps are retention of the **Jensen defect** in the optimal diagonal test, its vanishing through outer approximation without a uniform strict-contraction constant, and conversion of the resulting constant diagonal fields into a fixed polynomial unitary channel with a rational exterior inverse.

The external geometric input is Jin, *Rigidity at the Extremal Crouzeix Constant*, v2, Proposition 6 (circle criterion), not Jin's scalar equality theorem. Its exact hypotheses are checked in Section 8. Jin's Lemma 8 supplies a curved analytic exposed arc, independently of top-eigenvalue multiplicity. Both actual statements and proofs were read. This proof never asserts a scalar extremizer for B.

## 3. Interior spectrum and the inherited outer-limit system

Normalize M=1. Choose a unitarily irreducible reducing block B with ||F[B]||=2. The complete bound and W(B) subset W(A) imply max_{W(B)}||F||=1. A scalar block cannot attain 2. K=W(B) has interior: empty interior would make an affine rotation of B Hermitian, contradicting irreducibility. A boundary eigenvector is also an adjoint eigenvector, since its quadratic form vanishes for a positive supporting Hermitian slack; thus it supplies a reducing line. Consequently spec B lies strictly inside K.

Fix unit singular vectors x=vec(X), y=vec(Y) of F[B], with X,Y d by m, ||X||_HS=||Y||_HS=1 and F[B]x=2y, F[B]*y=2x. Take analytic convex outer domains Omega_j shrinking to K, normalized exterior maps h_j(lambda)=c_j lambda+c_0j+O(lambda^-1), c_j>0, q_j=lambda h_j', and Faber polynomials b_kj. Set

    R_j=q_j(h_j I-B)^-1, H_j=R_j+R_j*,
    A_j=X*R_jX, B_j=Y*R_jY,
    M_j=Y*R_jX, L_j=X*R_jY,
    S=X*X, T=Y*Y.

To avoid a naming collision, write t_j=max_{Omega_j}||F|| and gamma_j=2/t_j. All source tests below use F/t_j.

Here are the precise inherited dimension-independent facts from the full I245 proof Sections 1–5. Choose rDbar subset K subset Omega_j subset RD after translation. The convex exterior Herglotz formula gives

    log(h_j'/c_j)=2 integral log(1-xi/lambda) dmu_j(xi),
    r<=c_j<=R, |h_j'|<=4R.

The logarithms have uniformly square-summable Fourier tails. Subsequences therefore give strong boundary L2 convergence h_j'->h' and q_j->q, together with uniform boundary convergence h_j->h, where h maps the exterior disk conformally onto C\K and extends as a boundary homeomorphism. The limiting logarithm is finite a.e.; hence q is nonzero a.e. Also q is an outward normal to K a.e. (pass the supporting inequalities at a.e. convergent derivative points). The interior spectrum and uniform boundary convergence give

    R_j->R=q(hI-B)^-1 and H_j->H=R+R* in L2,

with uniform L-infinity bounds. These facts do not use a simple-support arc or a restriction on d. Fourier coefficients of each compressed field consequently converge strongly in ell2.

Put a_j^2=||M_j||_L2(HS)^2. It converges to a^2=||M||_L2(HS)^2. With D_Xj=||A_j+A_j*||_L2^2 and D_Yj defined similarly, the exact nonnegative residual system is

    E_Xj=4a_j^2/gamma_j^2-D_Xj,
    E_Yj=4a_j^2/gamma_j^2-D_Yj,
    E_Bj=D_Xj+D_Yj-2||M_j+L_j*||_L2^2,
    Rres_j=3||Y*X||_HS^2+sum_{k>=1}||X*b_kj(B)Y||_HS^2,
    E_Xj+E_Yj+E_Bj+2Rres_j
       =2(4/gamma_j^2-1)a_j^2 ->0.

Thus every residual tends to zero. In particular Y*X=0, L=0, and the limiting compressed positive field

    Delta=[ A+A*  M* ; M  B+B* ]

satisfies Delta J0 Delta=0 a.e., J0=diag(I_m,-I_m). Indeed the integrated nonnegative quantity tr(Delta J0 Delta J0) is the limit of E_Bj; it is the squared HS norm of the Hermitian matrix Delta^(1/2)J0Delta^(1/2). Quadratic passage uses strong L2, as in I245, not convergence of square roots. Also a>0, since a_j^2/gamma_j^2 >= ||S||_HS^2>0.

## 4. The strict Jensen defect survives outer approximation

For each j let K_j(lambda,mu) be the actual nonnegative Markov kernel of the pinned direct proof:

    K_j(lambda,mu)=2 Re(q_j(lambda)/(h_j(lambda)-h_j(mu)))

off the diagonal. Its continuous diagonal extension is used at equal points. Both angular marginals are one. Write T_j u(mu)=integral K_j(lambda,mu)u(lambda) d tau(lambda), with normalized Haar measure and finite-dimensional HS-valued functions. It is an L2 contraction.

Let A_kj=X*b_kj(B)X. Define the positive Fourier function

    u_j(lambda)=(1/2) sum_{k>=1} overline(A_kj) lambda^k,
    d_j=||S||_HS^2+(1/2)sum_{k>=1}||A_kj||_HS^2=D_Xj/4,
    delta_j=||u_j||_2^2-||T_j u_j||_2^2 >=0.

The bars are entrywise conjugation. The optimal finite diagonal dual tests have coefficients C_0=overline S, C_k=overline(A_kj)/2 for 1<=k<=N. For such a test G_jN, the pinned Faber boundary decomposition gives exactly

    ||G_jN||_boundary^2=d_jN-delta_jN,

where d_jN is the truncated d_j and delta_jN is the analogous contraction defect. Retain this equality in the ordered-test chain rather than replacing it by d_jN. The first ordered test then gives

    gamma_j d_jN <= a_j ||G_jN||_boundary,
    gamma_j^2 d_jN^2 <= a_j^2(d_jN-delta_jN).

All tests here are finite polynomials. Let N tend to infinity at fixed j; contraction of T_j makes delta_jN->delta_j. Therefore

    0<=delta_j <= d_j-gamma_j^2 d_j^2/a_j^2 ->0,

since E_Xj->0 gives d_j->a^2/4 and gamma_j->2. Strong L2 convergence of A_j gives strong L2 convergence u_j->u, where u=(1/2)overline(A-S).

For any Hilbert-space-valued u_j the two Markov normalizations give the exact variance formula

    2delta_j = triple integral K_j(lambda,mu) K_j(nu,mu)
                              ||u_j(lambda)-u_j(nu)||_HS^2
                              d tau(lambda)d tau(nu)d tau(mu).

Choose a subsequence on which q_j and u_j converge a.e. Uniform convergence of h_j and injectivity of h on the circle show, away from the null diagonals, that

    K_j(lambda,mu)->K(lambda,mu)
      =2 Re(q(lambda)/(h(lambda)-h(mu))).

Fatou's lemma applied to the nonnegative triple integrand gives

    K(lambda,mu)K(nu,mu)||u(lambda)-u(nu)||_HS^2=0

for almost every triple. No convergence of the Markov kernels in operator norm, no limit marginal identity, and no uniform positive spectral gap are being assumed.

By Jin Lemma 8, K has a nonempty open curved regular analytic exposed boundary arc. Its preimage I under h is a nonempty open circle interval and has positive Haar measure. A point h(mu) on that arc lies in no nontrivial boundary segment. For every mu in I and almost every lambda different from mu, q(lambda) is a nonzero outward normal at h(lambda), and its supporting line cannot contain h(mu). Otherwise the segment joining those distinct boundary points would be a boundary segment containing h(mu). Consequently K(lambda,mu)>0. Fubini now makes u(lambda)=u(nu) for almost every pair lambda,nu. Thus u is constant, and its zero mean makes u=0. Hence

    X*R(lambda)X=S a.e.

Repeat the same argument with the other ordered test and Y to obtain

    Y*R(lambda)Y=T a.e.                                      (1)

This step is the rank-free bridge. It works for the disk kernel K=1 as well; it does not force r=1 and does not contradict R019.

## 5. Rationalizing the original cross channel

Define rational matrix/scalar functions in the physical variable z:

    C(z)=Y*(zI-B)^-1X,
    r(z)=tr[X*(zI-B)^-1X].

Since tr S=||X||_HS^2=1, (1) implies q(lambda)r(h(lambda))=1 a.e. The same identity holds holomorphically in the exterior: X*R X-S is an exterior Hardy function with zero boundary values, so it vanishes identically; alternatively apply uniqueness coefficientwise in the reciprocal disk. In particular

    q(lambda)=1/r(h(lambda)),
    M(lambda)=C(h(lambda))/r(h(lambda)).                    (2)

The function r has no zero outside K. To prove this, separate z from K by a unit nu with Re(bar nu(z-w))>0 for all w in K. The matrix D=bar nu(zI-B) has strictly positive Hermitian part; its inverse does too, by Re(D^-1)=D^-* Re(D) D^-1. Hence

    Re[nu r(z)]=tr(XX* Re(D^-1))>0.

At the boundary spec B is absent, so r is continuous there. The a.e. identity q r=1 and |q|<=4R give |r|>=1/(4R) a.e. on the boundary, hence everywhere there by continuity and the boundary homeomorphism. Therefore

    mathcal M(z):=C(z)/r(z)

is rational, analytic on C\K and a neighborhood of its boundary, and continuous up to it. Since Y*X=0, C(z)=O(z^-2), whereas r(z)=z^-1+O(z^-2). Thus mathcal M(z)=O(z^-1) at infinity. Its boundary pullback is M.

Now (1) gives Delta=[2S,M*;M,2T]. The identity Delta J0 Delta=0 yields

    M*M=4S^2, MM*=4T^2, MS=TM                       (3)

a.e. In particular S,T have the same positive eigenvalues, and their ranks are the same positive integer r. The kernel and range of M are fixed: ker M=ker S and ran M=ran T.

## 6. A fixed polynomial unitary coefficient channel

Put s=||S||_HS>0. The vanished positive diagonal moments and E_Xj->0 imply a=2s. Consider the constant polynomial G=overline S in the first ordered identity. If U_k are the finite Faber coefficients of F(z)overline S for the limiting h, its positive Fourier coefficients, the source pairing and its limits give

    2s^2=sum_{k>=0}(M_k)_{ij}(U_k)_{ij}
       <=a (sum||U_k||_HS^2)^(1/2)
       <=a ||F(h)overline S||_L2(HS)
       <=a s=2s^2.                                      (4)

The sum is finite in U; the M array is square summable. The limiting Faber coefficients exist because they are precisely the nonnegative Laurent coefficients of the finite polynomial F(h(lambda))overline S. They follow equally by the triangular finite-basis limit b_kj->b_k. The pairing follows by taking the finite source expansion limit; the lower coefficient inequality follows by Parseval, and the last inequality follows from ||F||<=1 on K.

Equality in the first Cauchy–Schwarz step, including its positive real phase, gives U_k=overline(M_k)/2 for every k, with M_k=0 above deg F. Equality in the Parseval lower bound says the negative Fourier part of F(h)overline S is zero. As M_0=0, this proves the **pointwise boundary identity**

    F(h(lambda))overline S=(1/2)overline(M(lambda)) a.e.    (5)

The factor 1/2, conjugation and multiplication order are essential. The analogous second ordered test gives overline T F(h)=(1/2)overline M, though only (5) is needed below.

Take E=ran overline S and G=ran overline T, and constant isometries U:C^r->E, V:C^r->G. By (3),(5), F(h) maps E into G and is an isometry there. Indeed

    (F overline S)*(F overline S)=overline S^2.

The unwanted component (I-VV*)F(z)U is a polynomial vanishing at almost every boundary point, so it vanishes identically. Thus

    J(z)=V*F(z)U

is an r by r polynomial, unitary on the boundary (first a.e., then everywhere by continuity). These subspaces are fixed ranges of the constant Gram matrices, not varying fiber subspaces. Set S_E=U*overline S U>0. Taking the adjoint of (5) after this restriction gives

    J(z)*=(1/2)S_E^-1 U*mathcal M(z)^T V

on the boundary. Define the rational right-hand side to be Q(z). It is analytic outside K, continuous at the boundary, and Q(infinity)=0. Since J is unitary there, JQ=I there. Rational identity uniqueness on infinitely many boundary points gives

    J(z)Q(z)=I                                             (6)

identically as rational functions. Thus Q=J^-1 wherever defined. This also independently shows why this construction need not scalarize F: r can exceed one.

## 7. Paying the full-lemniscate and regularity hypotheses

By the maximum principle in the exterior domain, applied after inversion to scalar matrix elements, ||Q(z)||<1 for every z outside K. It has boundary norm one and value zero at infinity; equality at an interior exterior point for any norming scalar matrix element would contradict the scalar maximum principle and its zero value at infinity.

Let f(z)=det J(z). Identity (6) and Q(infinity)=0 show f is a nonconstant polynomial. In the interior of K, ||J||<=1 by the maximum principle and hence |f|<=1, with strict inequality by the scalar maximum principle and nonconstancy. On the boundary |f|=1. Outside K, Q=J^-1 and ||Q||<1 imply |f|>1. Therefore

    {z:|f(z)|<1}=int K, {z:|f(z)|=1}=boundary K.            (7)

This rules out extra lemniscate components and interior holes explicitly; boundary determinant norm alone would not do so.

For completeness, f' cannot vanish at a boundary level point z0. If f(z)-f(z0)=(z-z0)^k g(z), k>=2, choose alpha so Re(conj(f(z0))alpha^k g(z0))<0. For small positive t, all k points z0+t alpha exp(2pi i j/k) have |f|<1 and hence lie in int K by (7). Their average is z0, contradicting convexity. Thus f' is nonzero on the entire boundary; the implicit-function theorem makes it smooth real analytic. It contains no nontrivial segment: the real polynomial |f(z0+t xi)|^2-1 would vanish identically on the supporting line, contradicting the compact full-level identity. Hence K is strictly convex.

## 8. The exact geometric circle interface

Jin v2 Proposition 6 assumes: (a) K is a compact convex body; (b) boundary K is the **full** level |U/V|=1 for coprime polynomials with deg U>deg V; (c) K is strictly convex; (d) (U/V)' is nonzero on that boundary; and (e) all tangents to some open boundary arc lie in det(sI+u H+v L)=0 for Hermitian H,L, in line coordinates s+uX+vY=0.

Here choose U=f, V=1. Sections 3 and 7 verify (a)–(d). For (e), take H=Re B, L=Im B. Every tangent to the now smooth convex boundary is a support line. Orient it so sI+uH+vL is positive semidefinite. A unit vector realizing the support point has zero quadratic form for this matrix, so lies in its kernel. Its determinant is therefore zero. This verifies the actual Hermitian hyperbolicity interface; convex polynomial lemniscates alone do **not** force circles. Proposition 6 gives that boundary K is a circle, so K is a nondegenerate disk.

The geometric Proposition 6 includes its own projective-dual contact count (Proposition 5) and circular points at infinity. Those are credited external geometric results, not new deductions of this note and not silently inferred from the scalar equality theorem.

## 9. Restoring all reducing summands

Write K=a+rho Dbar, rho>0. The nonconstant polynomial f has modulus one on its circle, so f(a+rho z)=eta z^k, |eta|=1, k>=1. An elementary proof: the reciprocal-polynomial identity from constant boundary modulus prevents a nonzero root, and all roots are inside the disk by (7); equivalently, a polynomial finite Blaschke product is a monomial.

For every z in the full W(A), ||J(z)||=||V*F(z)U||<=1, so |f(z)|<=1. The monomial identity forces W(A) subset a+rho Dbar. The opposite inclusion follows from W(B) subset W(A). Thus the full W(A), not merely the active block's numerical range, is this disk. Rescaling F restores arbitrary M>0.

## 10. Validation, exact checks, formalization and contribution limits

The proof uses no sampled numerical evidence or finite search. Its finite matrix identities can be verified algebraically in arbitrary coefficient rank: Delta J0 Delta=0 gives (3), restriction of (5) gives the displayed Q with an ordinary transpose, and JQ=I follows by a rational identity. A dedicated exact R019 compatibility check is provided separately to challenge the factor/conjugation/order and rank-r interface. This is supporting verification, not an independent proof review.

A formalization would need: (i) HS-valued Markov variance/Jensen identity and its Fatou limiting argument; (ii) the inherited exterior conformal convergence theorem; (iii) rational accretive-resolvent separation; (iv) fixed-subspace Gram restriction and determinant/exterior maximum principles; (v) the credited Jin Proposition 6. No Lean full-theorem certificate is claimed; no axiom merely restating this new theorem is introduced. The determinant extraction is finite algebra suitable for Lean, but proving only that algebra would not certify the analytical result.

Old R016 scalarizes the specified witness through dimension four; the parent extends its technical dimension boundary to five. Old R019 disproves arbitrary-dimensional constant scalar-channel extraction and already realizes rank two. Neither is recounted. The proposed increment is full attained-polynomial **disk** rigidity in all finite dimensions, proved through a determinant channel that permits entanglement. No rational/holomorphic witness theorem, nonattained complete-supremum rigidity, uniform strict gap, near-equality modulus, complete classification, or worldwide priority claim follows automatically.

The direct source already contains the Markov kernel and all non-strict coefficient bounds; it does not state the strict-defect equality mechanism used here. The geometric circle theorem is wholly credited to Jin. Independent adversarial proof and primary-literature contribution gates remain required before any campaign acceptance or publication claim.
