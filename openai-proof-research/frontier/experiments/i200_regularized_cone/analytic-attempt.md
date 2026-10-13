# I200 analytic record: positive quadratic regularization

2026-10-12. **UNRESOLVED; no substantial nomination.** Eight findings remain accepted, two remain. All source theorems and lower operations at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are accepted. The results below distinguish exact auxiliary deductions from the unpaid small-positive-parameter liftability question. No research programs, numerical experiments, tests, historical replay or subordinate agents were used.

## 1. Fixed data and exact question

Fix one choice of the source's data, including its basis matrix U; changing the basis changes the meaning of the added identity and is not done here. Let H=R[x_0,...,x_7]_2 with its monomial Euclidean coordinates, dim H=36, m=330, N>10*36^2, r=20N-1, and n=r+1. The source's rank-20 Hankel seed and separation construction give a unit w, an r-dimensional U in w-perp, and a separation constant eta>0 such that

    G(y)=I_N tensor Y(y),
    g=eta^(-2) P_(w-perp)-ww^T,
    Q(y)=U^T G(y)gG(y)U >=0  for every y in R^m.

Here eta is the source's separation constant; delta below is a different parameter. The entire cone K_0 has no finite affine semidefinite lift by `prop:no-lift`. Define, for each fixed real delta>0,

    Q_delta(y)=Q(y)+delta ||y||^2 I_r,
    p_delta(X,Z,y)=det((det X) Z-Phi_(delta,y)(adj X)),

where Phi is the source's displayed linear operator with Q_delta substituted. Let K_delta be the closed hyperbolicity cone in direction (I_n,I_n,0). The accepted `prop:hyperbolic` applies because Q_delta is positive semidefinite-valued, with the same degree n(n+1). The accepted `prop:epigraph` gives the exact section/projection

    E_delta={(A,t,y): A>=0, ran Q_delta(y) subset ran A,
                         t>=tr(A^dagger Q_delta(y))}.

For y!=0, Q_delta(y)>0, so E_delta requires A>0. For y=0 it consists of all A>=0,t>=0. These are exact statements including the singular boundary.

The unresolved target is whether there is delta_0>0 such that every 0<delta<delta_0 has K_delta without any finite affine semidefinite lift. It is stronger than nonexistence of a joint linear Gram factor. No assertion below identifies those two properties.

## 2. Route A: a new feasible polynomial patch, and why its obstruction fails

### 2.1 Why a bounded singular repair is impossible

On the source ball Omega_0, put A_0(s)=M(s)M(s)^T, rank M(s)=N, and y(s)=y_s, evaluation at (1,s). Its constant coordinate is 1, so ||y_s||>=1. Q(y_s) is supported on ran A_0(s), while Q_delta(y_s) has rank r. Thus the source patch fails the range condition for every positive delta.

Fix h>0 and put A_h(s)=A_0(s)+hI. If lambda_1(s),...,lambda_N(s)>0 are the positive eigenvalues of A_0(s), then

    tr(A_h(s)^(-1))=(r-N)/h+sum_i 1/(lambda_i(s)+h).

Every feasible t over (A_h(s),y_s) satisfies

    t>=delta ||y_s||^2 (r-N)/h.

For a fixed delta>0 a bounded t therefore prevents h from tending to zero. More generally, any sequence of positive-definite A tending to a singular A_* with y tending to y_*!=0 has tr(A^(-1)Q_delta(y)) tending to infinity, since it is at least delta||y||^2/lambda_min(A). This is an energy obstruction, not merely failure of a chosen formula.

### 2.2 Exact polynomial full-rank repair

The most economical graph repair has rational t. Homogeneity clears its denominator without leaving E_delta. Set

    D_h(s)=det A_h(s)>0,
    R_(delta,h)(s)=tr(adj(A_h(s)) Q_delta(y_s)),
    p_(delta,h)(s)=(D_h(s) A_h(s), R_(delta,h)(s), D_h(s)y_s).

All coordinates are polynomial of degree at most 4r+4. Indeed A_h has degree at most four, y_s degree at most four, and Q_delta(y_s) degree at most eight. For every s in Omega_0,

    tr((D_h A_h)^(-1) Q_delta(D_h y_s))
       =D_h tr(A_h^(-1)Q_delta(y_s))=R_(delta,h).

Thus p_(delta,h)(Omega_0) lies exactly on the boundary of E_delta and is a feasible polynomial patch. This is a genuinely new patch, not the invalid rank-N patch with a coefficient replaced. Its finite degree permits the source's finite positive extension and analytic-selection lemmas to be applied for any fixed delta,h. The issue is the sign of its moment residual.

### 2.3 Curvature calculation

On A>0 define

    f_delta(A,y)=tr(A^(-1)Q_delta(y))
               =f_0(A,y)+delta g_0(A,y),
    g_0(A,y)=||y||^2 tr(A^(-1)).

The source's convexity and epigraph propositions imply convexity of f_0 on A>0. We use that accepted consequence; we do not audit it. For a symmetric H and z in R^m, differentiating inverse matrices gives

    (1/2) D^2 g_0(A,y)[(H,z),(H,z)]
      =sum_j ||A^(-1/2)(z_j I-y_j H A^(-1))||_F^2.       (A1)

Expansion of the right side gives ||z||^2 tr(A^(-1))-2(y dot z)tr(A^(-1)HA^(-1))+||y||^2 tr(A^(-1)HA^(-1)HA^(-1)), agreeing with the derivative. At y!=0, choose j with y_j!=0. Vanishing in (A1) gives H A^(-1)=(z_j/y_j)I and then z_i=(z_j/y_j)y_i for every i. Hence the kernel is exactly the radial line R(A,y).

Since D^2 f_0 is positive semidefinite, D^2 f_delta is positive on every nonradial direction. Conversely homogeneity of degree one gives D^2 f_delta(A,y)(A,y)=0. Its kernel is exactly R(A,y). This is strict curvature transverse to scaling, for each fixed positive delta.

Let q_h(s)=(A_h(s),y_s) and qbar_h(s)=D_h(s)q_h(s). No nonzero parameter derivative of q_h is radial: the derivative of the constant coordinate of y_s is zero, whereas that coordinate of y_s is 1, and the seven linear coordinates in y_s recover the parameter derivative. The same holds for qbar_h, because multiplication by the positive scalar D_h only adds a radial derivative. Therefore the seven-by-seven matrix

    H_(delta,h,c)=(D qbar_h(c))^T
                   D^2 f_delta(qbar_h(c)) D qbar_h(c)

is positive definite for every c in Omega_0. All constants here may depend on delta,h,c and on the fixed source data.

### 2.4 The moment residual has the opposite sign

Let Lambda(1)=1 be positive definite on affine squares, with mean mu_i=Lambda(s_i) and covariance Sigma_ij=Lambda(s_i s_j)-mu_i mu_j. Its covariance is positive definite: apply strict positivity to every nonzero affine polynomial a dot(s-mu). Extend Lambda to the finite degree needed for p_(delta,h), using the accepted positive extension lemma if necessary. No representing measure is required.

Write (A_e,t_e,y_e)=Lambda_s p_(delta,h)(c+epsilon s). Because the patch is polynomial these are defined exactly, and A_e is positive definite for small epsilon. Taylor expansion through order two and the identity t=f_delta(A,y) on the patch give

    t_e-f_delta(A_e,y_e)
      =(epsilon^2/2) sum_ij Sigma_ij (H_(delta,h,c))_ij
            +O_(delta,h,c,Lambda)(epsilon^3).            (A2)

For completeness, the terms involving the second derivative of qbar_h cancel: they occur as (1/2) grad f dot Lambda(D^2 qbar_h[s,s]) both in Lambda(f(qbar_h)) and in f(Lambda(qbar_h)). The remaining terms are (1/2)Lambda(D^2 f[J s,J s])-(1/2)D^2 f[J mu,J mu], exactly the covariance contraction displayed in (A2). Two positive-definite matrices have strictly positive trace product. Thus the tested point is actually feasible for every sufficiently small positive epsilon. The moment defect starts at positive order two; it cannot yield the source's negative order-four contradiction.

This proves a precise failure of the repaired-patch route. It does not prove liftability, and does not prohibit every more singular construction. It also handles an arbitrary polynomial boundary patch with a nonradial immersed base at a point with y!=0. A patch with nonzero slack at its center instead has an immediately positive constant residual.

### 2.5 Quantifier and singular-center gaps

The source selects an open analytic lift patch after fixing a finite lift and a polynomial patch, then fixes c there, then sends epsilon to zero. To use a family h=h(epsilon), one would need one controlled selection on the extended parameter space reaching h=0. For fixed delta>0, y_s!=0 and bounded t preclude that boundary by §2.1. Scaling by D_h clears denominators and gives a polynomial patch, but its h=0 limit lies at y=0 and degenerates; an analytic selection on h>0 need not extend across that stratum.

A different approach might seek an obstruction supported at y=0 and singular A, where several eigenvalues vanish together. The accepted selection lemma need not give any center on that lower-dimensional stratum. Nor does the existing Hankel residual identify a negative leading form there after the delta term is included. The missing assertion is a new feasible singular family with a negative leading moment defect on an open set of valid centers, or a different obstruction theorem controlling those singular centers. Merely permitting h,delta,c or the lift to vary with epsilon does not supply it.

## 3. Route B: exact joint-Gram lift range, and the unresolved gap below it

### 3.1 Explicit coefficient construction

Let e_i be the fixed Euclidean coordinate vectors of R^m, G_i=G(e_i), and form the real matrix

    L=[G_1 U | ... | G_m U] of size 36N by mr,
    P=eta^(-2) L^T P_(w-perp) L >=0,
    v=L^T w,
    C=L^T g L=P-vv^T.

Then, for a in R^r and y in R^m,

    a^T Q_delta(y)a=(y tensor a)^T (C+delta I_(mr))(y tensor a).  (B1)

Set sigma=-lambda_min(C). One has

    0<sigma<=||v||^2<infinity.                              (B2)

Indeed C has at most one negative eigenvalue, since its restriction to v-perp is positive semidefinite, and C>=-||v||^2 I. If C were positive semidefinite, (B1) at delta=0 would give a joint linear Gram factor for Q, and the block construction below would make K_0 spectrahedral, contradicting the accepted no-lift theorem. Therefore its unique negative eigenvalue exists. In particular v!=0.

For every delta>=sigma, factor C+delta I=R^T R with k<=mr rows, and split each row into m blocks of length r. These blocks define k linear vector maps b_j(y) in R^r with

    Q_delta(y)=sum_(j=1)^k b_j(y)b_j(y)^T.

Define B_j(y)=[[0,b_j(y)^T],[-b_j(y),0]] in Sym-skew_n and stack them vertically into B(y). Then the single homogeneous pencil

    L_delta(X,Z,y)=[[I_k tensor X, B(y)],
                   [B(y)^T,       Z   ]]                   (B3)

has size n(k+1)<=n(mr+1), and its positive semidefinite locus is **exactly K_delta**, with no projection, closure, or auxiliary variables required.

To check the singular boundary, the generalized Schur complement says (B3)>=0 iff X>=0, ran B_j(y) subset ran X for all j, and

    Z>=sum_j B_j(y)^T X^dagger B_j(y)=Phi_(delta,y)(X^dagger).

These conditions depend on Q_delta, not its Gram factorization. In particular the range condition is equivalent to Phi_(delta,y)(P_ker X)=0, since that matrix is a sum of Gram squares. They therefore agree with the source's pointwise n-column Gram characterization, even when k differs from n and X is singular. This proves the equality. It is unnecessary, and generally false, to claim that the determinant of (B3) is the source's p_delta when k!=n.

For a formula avoiding even a spectral threshold, delta>=||L^T w||^2 suffices, by C+delta I=P+(delta I-vv^T)>=0. The smaller sigma is also the unique positive root of

    v^T(P+sigma I)^(-1)v=1.

The equivalence follows by congruence of P+delta I-vv^T with I-zz^T, z=(P+delta I)^(-1/2)v. The left side strictly decreases for delta>0; the negative eigenvalue established above guarantees the crossing. All statements are symbolic; no eigenvalues or coefficients were numerically computed.

### 3.2 Exact threshold for this method, not for arbitrary lifts

Let S be the cone of quadratic matrix maps with a joint linear Gram factor, equivalently those whose biform a^T Q(y)a is a sum of squares of bilinear forms in a,y. Define

    delta_SOS=min{delta>=0: Q_delta belongs to S}.

This minimum exists and obeys 0<delta_SOS<=sigma. Here is a complete compactness justification in the fixed coefficient space. Write z=y tensor a. If C_j>=0 are Gram matrices of convergent biforms b_j, integrate z^T C_j z over the product of unit spheres with normalized measures. The integral is tr(C_j)/(mr), so their traces remain bounded. Positive semidefinite matrices with bounded trace form a compact set. A subsequence converges to a positive semidefinite Gram matrix for the limit. Thus S is closed. It follows that the intersection of the ray Q+delta||y||^2I with S is closed. It is nonempty by §3.1, and it is upward closed since (delta'-delta)||y||^2||a||^2 is a bilinear SOS. Since Q is outside S, closedness makes its first intersection positive. Consequently

    Q_delta has a joint linear Gram factor iff delta>=delta_SOS;
    K_delta is spectrahedral for every delta>=delta_SOS.

The first equivalence does **not** become an equivalence between membership in S and existence of arbitrary finite affine lifts. No conclusion about K_delta's liftability is proved for 0<delta<delta_SOS. The compactness argument only concerns Gram matrices of the fixed mr bilinear monomials. It supplies neither a bound on arbitrary lift sizes nor common analytic-selection constants for varying lifts.

### 3.3 Why the more flexible constructive variants remain unpaid

For y!=0 the positive square root Q_delta(y)^(1/2) is analytic and semialgebraic locally. Inserting it in a Schur block is a nonlinear description, not a finite affine lift. Likewise a positivity certificate for a polynomial matrix, even one valid on finitely many semialgebraic pieces, need not represent the joint cone by affine pencils.

The exact-lift companion for the 23-variable Choi-Lam cone avoids this problem with `lem:matching`: bounded-degree angular test functions have a fixed Gram matrix and an exact mixed-pairing identity for every symmetric test matrix S, including indefinite S. Its `prop:lift` turns those identities into all range and Schur inequalities for arbitrary feasible functionals. The Hankel Q_delta has no such established identity here. Replacing the identity by uniform approximation on a sphere still leaves errors multiplied by arbitrarily ill-conditioned X^dagger near the y=0 boundary. No positive delta-only margin controls those errors there. Proving an exact bounded-degree matching or a uniformly valid replacement would be a substantive missing construction.

## 4. Why smooth approximation does not decide this family

Q_delta's positive definiteness does not make the entire K_delta Nash-smooth. At y=0, its exact section is

    {(X,Z,0): X>=0,Z>=0}.

Indeed the pointwise Gram vectors can all be chosen zero. Choose a nonzero point X_*=diag(0,0,1,...,1), Z_*=I_n, y=0. Both linear functionals X_11 and X_22 are nonnegative on K_delta and vanish at this point; their supporting hyperplanes are distinct. The cone is full dimensional (the source determinant at e is positive, equivalently its pointwise block there is positive definite). A full-dimensional closed convex set with a smooth local defining inequality has a unique supporting hyperplane at a smooth boundary point. Thus this point is not even C^1 smooth, and in particular not Nash-smooth, for every delta>0.

One can also see exactly where regularization helps: for y!=0 the Gram vectors span R^r. The range of all skew B_j then spans R^n, forcing X>0. The matrix Phi_(delta,y)(X^(-1)) is positive definite, because B_j u=0 for every j forces u=0. Therefore Z>0 too. At the E_delta level all y!=0 boundary points lie on the graph treated in §2.3. The residual singular strata at y=0 are not removed.

Netzer-Sanyal's smooth-boundary theorem and approximation argument, and Scheiderer's Nash-smooth theorem, therefore neither prove nor disprove liftability here. They do invalidate any general inference that every smoothing of a nonliftable cone stays nonliftable. Details and reading limits are in the literature record.

## 5. Contribution and final verdict

The explicit range delta>=sigma (and the exact joint-Gram threshold delta_SOS) gives a meaningful, finite, data-dependent lift range for the requested family. It also rules out nonliftability for all positive delta. Its mechanism is fixed-dimensional coefficient-Gram regularization followed by the already-paid block construction. This is standard finite-dimensional linear algebra and an application of accepted source operations, not a ninth substantial finding.

The denominator-cleared patch is exact and feasible; the order-two positive residual is a useful obstruction to the attempted obstruction. Its role here is diagnostic. It does not settle a new liftability class or the small-delta question. No priority claim for either auxiliary deduction is made.

The two independent routes leave precise gaps: (A) an obstruction at the remaining singular strata, with valid center/selection quantifiers; (B) a genuine exact lift below the joint-Gram threshold, controlling arbitrary singular X rather than only compact well-conditioned pieces. We have neither. The final verdict is **UNRESOLVED; NO SUBSTANTIAL NOMINATION**. Both independent acceptance gates remain with the parent. I198's g+tau I transition and epsilon^12 estimate were not re-nominated or re-proved, and the 23-variable liftable example was never used as a nonliftability premise.
