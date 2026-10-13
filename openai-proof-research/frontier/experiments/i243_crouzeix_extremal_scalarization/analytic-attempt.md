# I243 — early mathematical notes

Work in progress. No claim of a tenth finding.

Let K=W(A) and let psi and psi_cb denote the scalar and complete norms of polynomial evaluation on K. The stipulated pinned theorem gives psi<=psi_cb<=2 in every finite dimension. The question is the equality implication psi_cb(A)=2 => psi(A)=2, initially with A in M_4 and an attained matrix polynomial P of degree at most two. Normalize K by its smallest enclosing disk and impose r Dbar subset K for a fixed r>0.

The scalar-output nilpotent argument is unavailable: the supplied weighted-chain example has norm two at matrix level without a reducing nilpotent block in P[A]. Any successful argument must extract information about the base matrix or scalar functional calculus, not the Jordan form of P[A].

A first exact reduction: a norm-attaining pair in C^4 tensor C^m has left and right coefficient supports of dimension at most four each. Rectangular compression retains the pairing, gives a 4-by-4 rectangular witness, and same-space compression gives coefficient size at most eight. The stipulated bound forces the compressed boundary supremum to remain one at equality. This is finite reduction only, not scalarization.

The structural companion attains a metric for a strictly enclosing analytic domain. Equality for K cannot be inserted into such a domain without paying the domain enlargement. A separate limiting argument is required before using extremal eigenspaces for the exact K problem. With spectrum strictly in the interior, a conformal coordinate and a compact limit of normalized metrics appear available; boundary eigenvalues must first be removed as reducing scalar summands.

The actual ACV sections 5 and 7 will be read next. Their stated dimension count leaves precisely a 2-by-2 rectangular obstruction in dimension four. Minimal-polynomial degree and base dimension must not be conflated: a small generated algebra does not alone give an orthogonal decomposition into small matrices.

## Paid lemma: quadratic columns scalarize in every finite base dimension

Assume the scalar-tuple square-function theorem of Åhag–Czyż–Virtanen (ACV), Theorem 1.3, as read in its primary statement and its quotient consequence Lemma 7.1. Let A be any finite matrix, K=W(A) with nonempty interior, and let p_1,...,p_q be scalar polynomials of degree at most two such that sum_j |p_j(z)|^2 <= 1 on K. If the column (p_j(A)) has norm two, there is a scalar polynomial p of degree at most two with sup_K |p|<=1 and ||p(A)||=2.

Proof. Choose a unit norming vector xi. Put T_j=p_j(A). The square-function estimate at tau=1/2 gives T_i T_j xi=0 for every i,j, since its degree-zero and degree-one terms already sum to two. Let M=C[A]xi and let m be its monic annihilator, of degree k. The map C[z]/(m) -> M, [q] -> q(A)xi, is an isomorphism. In particular m divides p_j^2 for every j. If k>4, every p_j vanishes identically, a contradiction. For k<=4 write m=product_lambda (z-lambda)^{r_lambda}, and g=product_lambda (z-lambda)^{ceil(r_lambda/2)}. Then g divides every p_j. The space of their residue classes modulo m has dimension at most one: for k=1 it is zero; for k=2 it is at most one by direct consideration of the partitions 2 and 1+1; for k=3 or 4, deg(g)>=2, so the degree-at-most-two multiples of g span at most one dimension. Therefore T_j xi=alpha_j v for a unit vector v. Here sum|alpha_j|^2=4. Set c_j=conjugate(alpha_j)/2 and p=sum c_j p_j. The coefficient vector c has Euclidean norm one, sup_K|p|<=1, and p(A)xi=2v. The stipulated scalar bound gives ||p(A)||=2. The row version follows by applying the column version to A* and the conjugate-coefficient polynomials. QED.

This proof uses no decomposition of P[A], and no inverse polynomial. It does not show that an arbitrary matrix witness has a column norming vector. In the scalar conclusion the boundary norm equals one automatically, by the stipulated bound.

## Paid algebraic extension for arbitrary analytic columns

Write m_A(z)=product_lambda (z-lambda)^{r_A(lambda)}, and define nu(A)=sum_lambda floor(r_A(lambda)/2). The ideal J of square-zero elements in C[z]/(m_A) consists exactly of the multiples of product_lambda (z-lambda)^{ceil(r_A(lambda)/2)} and has dimension nu(A). (Every element of this ideal has square zero; products of two such elements also vanish.)

If nu(A)<=1, every norm-two column or row in the quotient functional calculus scalarizes, without a degree bound. On the cyclic module C[A]xi the annihilator divides m_A, so its square-zero ideal has dimension at most one. Apply the previous norming-vector argument there. With quotient entries, take a unit scalar linear combination in the quotient; its norm is at most one. Thus psi(A)=2, even if no prescribed polynomial degree is retained. This is a consequence of ACV's tuple theorem and elementary one-variable local algebra; it is not yet a full complete-equality theorem for that Jordan class.

## New route under verification: positive-block rank, not output rigidity

For an exact quadratic witness in base dimension four, ACV's first variation makes the input/output base Schmidt supports orthogonal. Quadratic column scalarization deals with a one-dimensional support. Otherwise both supports have dimension two, and after rectangular coefficient compression X,Y are 4-by-2 full-rank matrices with X*Y=0. Thus Z=[X Y] is invertible.

The direct pinned proof's positive-block slack is the integral of tr(Delta J Delta J), where Delta=Z*(R+R*)Z >=0 and J=diag(I_2,-I_2). If this trace vanishes, range(Delta) is J-isotropic, and hence rank(Delta)<=2. At a smooth supporting point z with simple top supporting eigenvalue, R+R* has rank three. Invertibility of Z would make the slack strictly positive. This is a route to excluding every simple supporting direction, without claiming anything about the Jordan form of P[A].

The limiting issue can be paid by a uniform exterior-derivative estimate. For an analytic convex enclosing domain with exterior map h(zeta)=c zeta+..., c>0, convexity gives Re(1+zeta h''/h')>=0 outside the circle. The exterior Herglotz representation integrates to

log(h'(zeta)/c)=2 integral_T log(1-u/zeta) dmu(u),  mu(T)=1,

so |h'|<=4c for |zeta|>=1. With sigma(A) strictly inside K, the boundary resolvents of all shrinking enclosing domains are uniformly bounded. Hence the direct proof's a_j^2 stays bounded, and its positive-block slack tends to zero at exact equality. A positive-length interval of simple support directions gives a uniform positive lower bound for that same slack, a contradiction.

Boundary eigenvalues are reducing scalar summands. Removing one leaves base dimension at most three. Applying the coefficient-preserving first-variation compression to the remaining equality witness, followed by the quadratic column lemma, gives a scalar witness bounded on the original K. One must preserve this original-K bound; merely invoking disk rigidity of the smaller block would not suffice if the removed scalar enlarged K.

If no supporting direction has a simple top eigenvalue, applying the same statement at the opposite direction gives repeated bottom eigenvalues too. Every traceless Hermitian pencil of size four therefore has eigenvalues +s,+s,-s,-s and squares to a scalar. Its two generators form a two-generator Clifford relation. Elementary block diagonalization then makes A unitarily equivalent to B direct-sum B for a 2-by-2 B. That proper reducing decomposition again yields a scalar quadratic witness.

This would prove exact degree-at-most-two scalarization for every A in M_4, with no boundary smoothness, inradius, inverse-polynomial, or metric-eigenspace hypothesis. Full details, especially the limiting slack estimate and the first-variation use with the original uniform algebra, are being checked before the conclusion is finalized.

# Completed proof: complete scalarization in base dimension four

The chronological notes above are superseded by the statements and proof below. All pinned inputs are stipulated true. No assertion below applies the scalar square-function theorem to a matrix-valued output.

## Statements and conventions

For a compact convex K and a matrix B with W(B) subset K, let psi_K(B) and psi_cb,K(B) be the norms of scalar and matrix polynomial evaluation, with the supremum norm on K. Write psi(B), psi_cb(B) when K=W(B). The empty-interior case is normal and both constants equal one. All tensor products below put the base space first; rectangular matrices are padded by zero rows/columns when applying a square-matrix statement.

**Theorem 4 (unrestricted exact scalarization).** For every A in M_4(C),

    psi_cb(A)=2  if and only if  psi(A)=2.

Consequently psi_cb(A)=2 forces W(A) to be a nondegenerate closed disk. No attainment by a polynomial, degree bound, Jordan hypothesis, smooth-boundary assumption, positive-inradius bound, or eigenvalue separation hypothesis is imposed in this statement. The same implication in dimensions at most three is ACV's prior result.

**Theorem 4Q (degree-preserving quadratic witness).** Let A in M_4(C), let m>=1, and let P(z)=B_0+B_1 z+B_2 z^2 with B_j in M_m(C). If

    max_{z in W(A)} ||P(z)||=1,       ||P[A]||=2,

then there is a scalar polynomial p of degree at most two such that

    max_{z in W(A)} |p(z)|=1,         ||p(A)||=2.

By ACV Theorem 11.2, there are a in C, rho>0, c!=0 and k in {1,2} such that

    p(z)=c(z-a)^k,
    A is unitarily similar to a I + rho (C_k direct-sum B),    w(B)<=1.

Here C_1=[[0,2],[0,0]], C_2 has its two superdiagonal entries sqrt(2), and the complement has size 4-(k+1). This scalar-witness classification is existing literature; the new assertion is obtaining a scalar witness from complete extremality in dimension four.

In particular Theorem 4Q applies to every fixed r in (0,1] under the question's normalization r Dbar subset W(A) subset Dbar with minimal enclosing disk Dbar. It gives W(A)=Dbar exactly. It does not give a quantitative deficit exponent.

## 1. Source inputs, precisely separated

(P) The pinned direct theorem gives ||F[B]||<=2 sup_K||F|| for every finite rectangular polynomial whenever W(B) subset K; padding gives the rectangular formulation. Uniform approximation extends this to A(K). The pinned direct proof also gives the three boundary inequalities reproduced in section 3 below. Its analytic convex outer-approximation lemma supplies the domains used there.

(V) ACV Sections 2 and 5 give finite-dimensional quotient attainment and the first-variation rectangular reduction. These are general operator-algebra statements, and may be applied to evaluation on any compact convex K containing W(B), not only K=W(B). In particular, if psi_cb,K(B)=2, there are r,s>=1, a quotient element F of norm one, and unit vectors x,y with

    F[B]x=2y,       F[B]*y=2x,       r+s<=dim B.

Choose r+s minimal. The input and output coefficient Schmidt ranks are r,s. Their base Schmidt spaces are orthogonal. In base-first notation, x=vec(X), y=vec(Y), where X is d-by-r, Y is d-by-s, both have full column rank, their Hilbert--Schmidt norms are one, and X*Y=0. The quotient has image alg(B), dimension deg(m_B), as in ACV Proposition 2.1.

For a *given* polynomial extremal no quotient attainment is needed: ACV Lemma 5.2 applies directly, since evaluation at every matrix level is bounded by two. It makes the base Schmidt spaces of any norming pair orthogonal. Rectangular coefficient compression preserves the selected pairing, the evaluation norm two, the pointwise bound one, and the degree. Thus the same ranks obey r+s<=d. Minimality is not needed for this last observation: compress to the actual Schmidt supports.

The first variation is not degree-preserving as a deformation: its ball automorphisms are rational. This is legitimate because (P) bounds the full functional calculus. The *compression of the original extremal* preserves its degree. These operations are distinct.

(S) ACV Theorem 1.3 and Lemma 7.1 give scalar-tuple square functions, including for quotient columns by approximate lifts. The only use of (S) below is to scalarize columns/rows, never a general matrix output.

(G) Jin's scalar disk theorem, as stated and used in ACV Section 11, gives psi(A)=2 => W(A) is a nondegenerate disk. ACV Theorem 11.2 gives the asserted scalar polynomial classification.

## 2. Quotient lifts and two scalarization facts

The quotient reduction in (V) has polynomial lifts with *exact* evaluation. To see this, start with A(K) lifts of quotient norm at most 1+epsilon. Uniform polynomial approximation changes both the boundary norm and the evaluated matrix by arbitrarily small amounts. Fix a linear right inverse to polynomial evaluation onto alg(B), obtained from any polynomial basis of that finite-dimensional algebra. Subtract the right inverse of the evaluation error entrywise. Its supremum norm tends to zero. Thus a fixed rectangular quotient element F has polynomials F_j with F_j[B]=F[B] and sup_K||F_j|| down to ||F||. This is an existence argument, not a computation of the lifts. It applies also when B has boundary eigenvalues: boundedness of evaluation comes from (P).

If a minimal extremal has r=s=1, it is a scalar quotient element of norm one evaluated to norm two, so psi_K(B)=2. This conclusion concerns a supremum; no scalar polynomial attainment is asserted.

For use with a proper reducing summand of dimension at most three, we need the following slight strengthening of ACV's column argument. Let

    m_B(z)=product_lambda (z-lambda)^{r_lambda},
    nu(B)=sum_lambda floor(r_lambda/2).

If nu(B)<=1, every quotient column or row of norm at most one whose evaluation has norm two implies psi_K(B)=2. Indeed, for a norming input xi the scalar-tuple square function gives T_i T_j xi=0 for all entries T_i. On the cyclic module C[B]xi, the annihilator m_xi divides m_B. A square-zero element of C[z]/(m_xi) is divisible by

    g_xi(z)=product_lambda (z-lambda)^{ceil(r_xi(lambda)/2)}.

These elements form an ideal of dimension sum_lambda floor(r_xi(lambda)/2)<=nu(B)<=1. Therefore all T_j xi are collinear. If T_j xi=alpha_j v, ||v||=1, then sum|alpha_j|^2=4. The unit scalar combination with coefficients conjugate(alpha_j)/2 has quotient norm at most one and evaluated norm two. Rows follow by adjoints. For d<=3, nu(B)<=1 automatically. Thus

    d<=3 and psi_cb,K(B)=2  =>  psi_K(B)=2.             (2.1)

This preserves the *original* K. It is not inferred merely from psi(B)=2 for a smaller numerical range.

For actual polynomial columns of degree at most two, the same scalarization holds in every base dimension and preserves degree. The proof is the paid quadratic-column lemma above: m_xi divides every p_j^2; if deg(m_xi)>4 all entries vanish, while if deg(m_xi)<=4 the degree-at-most-two square-zero residues span at most one dimension. Hence a unit scalar combination of the column entries attains two. In particular every actual quadratic complete extremal in base dimension at most three has a scalar quadratic witness bounded on the same K.

## 3. The direct proof's exact residual and its uniform bound

Let sigma(A) subset int K, where K=W(A), and suppose fixed unit x=vec(X), y=vec(Y) norm a rectangular matrix polynomial evaluation F[A] with norm gamma>0. Let Omega be an analytic convex domain containing K, let h be its exterior map, and put

    q(zeta)=zeta h'(zeta),
    R(zeta)=q(zeta)(h(zeta)I-A)^(-1).

Take sup_{Omega}||F||=1. In the notation of the direct source define

    P_0(zeta)=X*R(zeta)X,     Q_0(zeta)=Y*R(zeta)Y,
    M(zeta)=Y*R(zeta)X,       L(zeta)=X*R(zeta)Y,
    a^2=sum_{k>=0} ||Y*b_k(A)X||_HS^2.

The subscript on P_0,Q_0 here only distinguishes these functions from the polynomial F; it does not indicate their Fourier coefficient. Put

    D_X=integral ||P_0+P_0*||_HS^2,
    D_Y=integral ||Q_0+Q_0*||_HS^2,
    C=integral ||M+L*||_HS^2.

All integrals use dt/(2 pi). The source proves

    D_X,D_Y <= 4 a^2/gamma^2,
    C = a^2 + Remainder,
    Remainder = 3||Y*X||_HS^2 + sum_{k>=1}||X*b_k(A)Y||_HS^2 >=0,
    E_B:=D_X+D_Y-2C >=0.

Consequently, with E_X=4a^2/gamma^2-D_X and E_Y defined similarly,

    E_X+E_Y+E_B+2 Remainder = 2(4/gamma^2-1)a^2.       (3.1)

Moreover, for Z=[X Y] and J=diag(I_r,-I_s),

    Delta(zeta)=Z*(R+R*)Z >=0,
    E_B=integral tr(Delta J Delta J).                  (3.2)

The rectangular identities follow by zero padding in the source's square formulation; removing the zero rows and columns preserves every displayed Hilbert--Schmidt norm.

The new limiting observation is that a^2 is uniformly bounded over all small convex outer approximations, for fixed A with spectrum in int K and fixed unit X,Y. Here is a full proof.

**Exterior derivative bound.** Normalize h(zeta)=c zeta+c_0+..., c>0. For a regular analytic convex boundary, the derivative of the tangent angle is nonnegative, so

    Re(1+zeta h''(zeta)/h'(zeta))>=0       (|zeta|=1).

The real part is harmonic outside the circle and has value one at infinity, so it stays nonnegative there. The Poisson formula, or its Fourier series, represents the analytic function by

    1+zeta h''/h' = integral_T (zeta+u)/(zeta-u) dmu(u),

where dmu is the nonnegative boundary real part times normalized angular measure and mu(T)=1. Integrating with the normalization h'(infinity)=c gives

    log(h'(zeta)/c)=2 integral_T log(1-u/zeta) dmu(u).

The branch is fixed at infinity; h' is nonzero in the exterior collar. Thus

    |h'(zeta)| <= c(1+1/|zeta|)^2 <= 4c       (|zeta|>=1).       (3.3)

The boundary assertion follows by continuity. No convergence of boundary derivatives across different domains is needed.

If all enclosing domains lie in {|z|<=R_*}, the Fourier coefficient formula for c gives c<=R_*. Since sigma(A) is a compact subset of int K, the resolvents (zI-A)^(-1) are uniformly bounded, say by M_*, for all z on boundaries of these domains. Therefore Parseval and ||X||_HS=||Y||_HS=1 give

    a^2 = integral ||Y*R X||_HS^2 <= 16 R_*^2 M_*^2.           (3.4)

This bound is independent of the degree and of the polynomial's coefficients. It is also independent of the number of outer approximations used.

Now let F be an attained quotient extremal as in (V), so F[A]x=2y and F[A]*y=2x. Choose exact polynomial lifts F_j with sup_K||F_j||<=1+epsilon_j, epsilon_j down to zero. Choose analytic convex Omega_j containing K, Hausdorff-converging to K, sufficiently close that M_j:=sup_{Omega_j}||F_j||<=1+2epsilon_j. The quotient norm forces M_j>=1. Apply (3.1)--(3.4) to F_j/M_j, with the *same* X,Y and gamma_j=2/M_j. They prove

    integral tr(Delta_j J Delta_j J) = E_{B,j} --> 0.          (3.5)

This is an absolute convergence to zero, not just a normalized residual. The uniform a_j bound is essential.

For a fixed actual polynomial extremal the same conclusion follows simply by using that polynomial on shrinking domains. No quotient lifts are then needed, and its degree is unchanged.

## 4. A simple supporting eigenvalue is incompatible with a nonscalar extremal

Assume n=4, sigma(A) subset int K, and use the extremal from (V). Suppose max(r,s)>1. Its base spaces are orthogonal, so Z=[X Y] has full column rank k=r+s.

For every positive semidefinite k-by-k matrix D, tr(D J D J) is nonnegative: it equals tr((D^(1/2) J D^(1/2))^2). If this trace is zero, then D^(1/2) J D^(1/2)=0. Hence range(D^(1/2)) is a totally isotropic subspace for the nondegenerate Hermitian form J of signature (r,s), and

    rank(D)<=min(r,s).                                  (4.1)

For completeness, the dimension bound follows because projection of a totally isotropic subspace to either positive or negative coordinate space is injective: a vector lying wholly in either space cannot be nonzero and isotropic.

Suppose H_theta=Re(e^(-i theta)A) has a simple top eigenvalue at theta_0. It remains simple on a small interval I. Its support value h_K(theta) and unique support point z(theta) vary continuously (indeed analytically) there. The support point cannot be constant throughout any open subinterval. Otherwise choose a unit vector with numerical value equal to that constant point. It attains the supporting quadratic form at two nonparallel normals; positivity then makes it an eigenvector of both corresponding Hermitian parts, hence an eigenvector of A at that boundary point. This contradicts sigma(A) subset int K. Choose a closed subinterval [alpha,beta] inside I with z(alpha)!=z(beta).

Write nu=e^(i theta), and define

    B(z,nu)=nu(zI-A)^(-1)+conjugate(nu)(zI-A)^(-*).

At z=z(theta), congruence by zI-A gives

    (zI-A)* B(z,nu) (zI-A)
       =2(h_K(theta)I-H_theta).

Thus B(z(theta),nu)>=0 has rank three. Since Z has k independent columns,

    rank(Z*B(z(theta),nu)Z) >= k-1 > min(r,s),

where the last inequality is precisely max(r,s)>1. Equation (4.1) shows that

    d(theta):=tr((Z*B(z(theta),nu)Z) J (Z*B(z(theta),nu)Z) J)>0.

Continuity and compactness give a positive minimum d_0 on [alpha,beta].

Let z_j(theta) be the support point of the analytic convex Omega_j with normal nu. These points converge uniformly to z(theta) on [alpha,beta]. A direct proof uses compactness: any contrary subsequence has theta_j tending to theta and a limiting point in K on its support line; uniqueness makes that point z(theta). The Hausdorff convergence also makes the support values converge. Therefore, for all large j,

    tr((Z*B(z_j(theta),nu)Z) J (Z*B(z_j(theta),nu)Z) J)>=d_0/2.

On the corresponding boundary arc of Omega_j, R_j+R_j*=|q_j| B(z_j,nu). The arc length L_j is at least |z_j(beta)-z_j(alpha)| and is bounded below by some L_*>0. The analytic convex boundary has no straight segment, so its normal traverses this interval once; zero-curvature points do not affect the arclength identity. Cauchy--Schwarz with normalized circle measure gives

    integral_arc |q_j|^2 dt/(2 pi) >= L_j^2/(4 pi^2).

Using (3.2), the whole nonnegative integral is therefore at least

    (d_0/2) L_*^2/(4 pi^2)>0,

contradicting (3.5). We have proved:

**Support multiplicity conclusion.** In base dimension four, an interior-spectrum complete quotient extremal with max(r,s)>1 forces the top eigenvalue of Re(e^(-i theta)A) to have multiplicity at least two for *every* theta.

The argument applies without changes to any actual polynomial extremal with such Schmidt ranks. It does not assert that the entire output F[A] has a reducing nilpotent block.

## 5. Elementary four-dimensional pencil classification

Suppose the support multiplicity conclusion holds. Replacing theta by theta+pi proves that the bottom eigenvalue also has multiplicity at least two. Every nonscalar supporting Hermitian matrix of order four therefore has exactly two eigenvalues, each double.

Write A=aI+B+iC, with B,C traceless Hermitian and a=tr(A)/4. For each real t, B+tC has eigenvalues +s(t),+s(t),-s(t),-s(t), with the scalar zero case included. Hence

    (B+tC)^2 = tr((B+tC)^2) I/4.

Comparing coefficients gives

    B^2=b^2 I,    C^2=c^2 I,    BC+CB=2d I,

where b^2=tr(B^2)/4, c^2=tr(C^2)/4, d=tr(BC)/4 are real and b,c>=0. After rotating A by a unimodular scalar if necessary, b>0 unless W(A) is a point. In an orthonormal basis,

    B=b diag(I_2,-I_2),
    C=[[ (d/b)I_2, V ], [ V*, -(d/b)I_2 ]],
    VV*=V*V=(c^2-d^2/b^2)I_2.

If the last scalar is zero, B and C are proportional and W(A) is a segment, contrary to nonempty interior. Otherwise V=kU with k>0 and U unitary. Conjugating by diag(U,I_2), followed by a permutation of the basis, exhibits

    A unitarily equivalent to B_2 direct-sum B_2                 (5.1)

for one 2-by-2 matrix B_2. This is a direct proof; no assertion of the general Kippenhahn conjecture is used. The repeated-block conclusion is *derived from complete extremality*, not an initial restriction to known direct sums or ellipses.

## 6. Completion of Theorem 4

The implication psi(A)=2 => psi_cb(A)=2 follows from the stipulated bound and psi<=psi_cb. Assume psi_cb(A)=2. Empty interior is impossible, since after an affine rotation A is Hermitian and its polynomial calculus is completely contractive.

First suppose A has a boundary eigenvalue lambda. A unit eigenvector v also satisfies A*v=conjugate(lambda)v: take a supporting line at lambda and use positivity of its supporting Hermitian slack. Thus Cv reduces A. Remove all such one-dimensional reducing summands to obtain

    A=A_0 direct-sum D,

where D is diagonal and A_0 has size at most three. Evaluation on D, with the original K=W(A), has complete norm at most one. Orthogonal direct sums and the finite maximum therefore give psi_cb,K(A_0)=2. Equation (2.1) gives psi_K(A_0)=2. Scalar functions approaching that norm, still bounded on the original K, show psi(A)=2.

Now suppose sigma(A) subset int K. Choose a minimal quotient extremal as in (V). If r=s=1, its scalar quotient norm gives psi(A)=2 immediately. Otherwise section 4 gives repeated support eigenvalues in every direction, and section 5 gives A=B_2 direct-sum B_2. Here K=W(B_2), so psi_cb(B_2)=2. Applying (2.1) in dimension two gives psi(B_2)=2, and hence psi(A)=2. This proves the equivalence. The scalar disk theorem (G) gives the geometric conclusion. QED.

## 7. Completion of Theorem 4Q

Start with the given actual quadratic P and a unit norming pair. If there is a boundary eigenvalue, remove it as in section 6; one remaining block A_0 of size at most three still satisfies ||P[A_0]||=2. Apply coefficient-preserving first-variation compression to P evaluated at A_0 on the original K. Since r+s<=3, at least one side has dimension one. The quadratic column/row lemma in section 2 supplies a scalar quadratic p bounded on K with ||p(A_0)||=2, so ||p(A)||=2.

If sigma(A) subset int K, coefficient compression of the given P gives r+s<=4. If one side has dimension one, use the same quadratic column/row lemma. The only other case is r=s=2. Sections 3--5 apply to the fixed P and show A=B_2 direct-sum B_2. Apply the first variation and coefficient compression to P[B_2]: in base dimension two the two Schmidt ranks must both equal one. The resulting scalar entry p is a constant left/right coefficient compression of P. It has degree at most two, sup_K|p|<=1 and ||p(B_2)||=2. Thus it norms A as required. The stipulated scalar bound forces sup_K|p|=1. Applying (G) proves the displayed classification. QED.

## 8. Analytic checks, counterexamples, and limits

1. The bounded a_j estimate pays the potentially divergent exterior normalization. It uses only spectrum strictly inside K; boundary spectrum is removed *before* it is invoked. Merely discarding the direct proof's nonnegative terms would not pay this step.
2. No exchange of an infinite Faber sum with a nonsmooth limiting boundary occurs. Each source calculation is on its own analytic Omega_j, and the limit uses a uniform bound plus geometric arclength. Boundary derivatives h_j' never need to converge.
3. For the unrestricted theorem, quotient attainment is not polynomial attainment. Exact-evaluation polynomial lifts allow one fixed singular pair to be used at every step. Approximate extremals with changing vectors are not silently substituted.
4. The weighted-chain example remains active: A=[[0,2],[0,0]], P(z)=[[0,z],[1,0]] gives ||P[A]||=2 and an irreducible chain with weights (1,2,1). It has no reducing norm-two nilpotent block. Here the base Schmidt ranks of the maximal singular pair are both one, so the scalar extraction is immediate (p(z)=z). Embedding A as A direct-sum 0_2 gives an order-four instance. The proof handles it and never draws the refuted conclusion about P[A].
5. Polynomial attainment at degree at most two is genuinely stronger than psi_cb=2. The four-dimensional Crabb matrix C_3 has W(C_3)=Dbar and ||C_3^3||=2. Its Jordan form is one size-four block. By Theorem 4Q and the existing scalar polynomial classification, no matrix polynomial of degree at most two can attain two at C_3: such a scalar witness would force a reducing C_1 or C_2 block. This is an exact counterexample to reducing arbitrary complete extremality to attained quadratic extremality. It does not counter Theorem 4.
6. The argument does not require or assert that every matrix with disk numerical range is extremal. The scalar disk implication is used in its stated direction only.
7. Affine nonconstant changes of A, unitary similarity and coefficient-space unitaries preserve all ratios. Theorems 4 and 4Q allow repeated eigenvalues. They supply no base-dimension-five conclusion, no numerical exponent near equality, and no dimension-uniform stability estimate.
8. The support-multiplicity argument for a rectangular extremal yields in general that, along a positive-length arc whose supporting slack has kernel dimension ell, one must have ell>=max(r,s). In dimension four, any nonscalar minimal extremal would force ell>=2; the elementary pencil classification is special to this dimension. No higher-dimensional Kippenhahn claim is made.
