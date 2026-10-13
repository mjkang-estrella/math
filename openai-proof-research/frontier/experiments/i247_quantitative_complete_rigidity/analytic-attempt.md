# I247 — quantitative complete rigidity: partial notes

Status: work in progress, 2026-10-12. Only the permitted finished R016/I242/I245/I246 chain is used. The target is now twenty accepted substantial findings; this note does not change the count of ten.

## Early candidate bridge

Normalize max_W(A)||P||=1 and let gamma=||P[A]||>=2-epsilon. Fix a maximal singular pair x=vec X, y=vec Y, with ||X||_HS=||Y||_HS=1. The exact direct-source residual, passed to W(A) with interior spectrum as in the finished equality proof, should give

    integral ||H^(1/2)(XX*-YY*)H^(1/2)||_HS^2 <= S,
    ||X*Y||_HS^2 <= S/6,
    S = 2(4/gamma^2-1) integral ||Y*R X||_HS^2.

At a point where H has rank d-1 and least positive eigenvalue at least h, its range compression of D=XX*-YY* has norm <=sqrt(slack)/h. Interlacing gives lambda_2(D)<=eta and lambda_{d-1}(D)>=-eta. A quantitative replacement for exact inertia is needed, since X*Y is only small, not zero.

Proposed elementary estimate: if a_2 is the second eigenvalue of XX* and kappa=||X*Y||op, then lambda_2(D)>=a_2-kappa^2/a_2. Indeed on the top two-dimensional spectral subspace of XX*, ||Y* w||^2<=kappa^2/a_2. Therefore a_2<=eta+kappa; the analogous bound holds for YY*. Hence both Schmidt squared tails are at most (d-1)(eta+kappa), i.e. O(sqrt(epsilon)) with controlled field energy and arc. Product-vector distances are O(epsilon^(1/4)).

Stationarity of a maximal singular pair may improve scalar evaluation loss to O(sqrt(epsilon)), rather than merely the Lipschitz O(epsilon^(1/4)) loss. This is to be proved explicitly. Quantitative disk geometry after scalarization is not yet paid and will not be claimed by invoking qualitative R016 or compactness.

# Completed quantitative scalarization theorem

The following supersedes the early proposed estimates. The disk-stability extension remains separate and unresolved below.

## Exact statement, including uniform parameters

Let d>=2 and R,delta,g,ell>0. Let A be a complex d by d matrix, with K=W(A) having interior and K contained in R Dbar. Assume:

1. dist(sigma(A),partial K)>=delta (Euclidean distance of sets; no eigenvector conditioning or separation between distinct eigenvalues is assumed).
2. partial K contains a regular real-analytic arc Gamma of arclength at least ell. At each point of Gamma, with outward normal nu, the largest eigenvalue of Re(conj(nu)A) is simple and differs from its second largest eigenvalue by at least g.

No irreducibility assumption is needed beyond these explicit geometric hypotheses. Write

    K0=(3R)^(d-1)/delta^d,
    C0=8(d-1) R K0 [9 pi R^2/(g ell)+1/sqrt(6)].             (Q1)

For every finite m>=1, every finite-degree M_m-valued polynomial P with max_K||P||=1, and every 0<=epsilon<=1/2 such that

    gamma=||P[A]||>=2-epsilon,

every unit maximal singular pair x=vec X, y=vec Y (P[A]x=gamma y, P[A]*y=gamma x) satisfies

    t_X:=1-||X||op^2 <= min(1,C0 sqrt(epsilon)),
    t_Y:=1-||Y||op^2 <= min(1,C0 sqrt(epsilon)).             (Q2)

There are unit xi,eta in C^d and unit u,v in C^m with

    ||x-xi tensor u|| <= sqrt(2 C0) epsilon^(1/4),
    ||y-eta tensor v|| <= sqrt(2 C0) epsilon^(1/4),          (Q3)

after choices of phase, and the specific scalar compression p(z)=v*P(z)u obeys

    max_K |p|<=1,
    ||p(A)|| >= gamma[1-t_X-t_Y-sqrt(t_X t_Y)]
             >= 2-epsilon-6 C0 sqrt(epsilon).             (Q4)

When the last bound is positive, p is nonzero and its scalar ratio ||p(A)||/max_K|p| is at least the same bound. Rescale P by M=max_K||P|| for the unnormalized version. Dependence on m, degree and coefficient magnitudes is exactly absent. Thus fixed degree and coefficient bounds may be imposed without changing C0. Dependence on boundary spectral distance is delta^(-d), and the controlled support arc costs (g ell)^(-1).

For d=4 and R=1 this is a normalized class with

    C0=648 [9 pi/(g ell)+1/sqrt(6)]/delta^4.

This equals 8*3*27[9pi/(g ell)+1/sqrt6]/delta^4.

## 1. Boundary residual with an explicit energy bound

Translate the origin only temporarily to apply the convex-exterior limit from finished I242 Sections 1–2 / I245 Sections 2–5. Let h map the exterior unit disk onto C\K with positive leading coefficient, q(z)=z h'(z), and use normalized measure d tau=dt/(2pi). The already-paid convex Herglotz argument gives |q|<=4 cap(K)<=4R almost everywhere. The bound cap(K)<=R is unaffected by a temporary translation. Define

    R_A=q(hI-A)^(-1), H=R_A+R_A*, D=XX*-YY*.

Since K subset R Dbar, ||A||<=2R: write A=Re A+i Im A and use ||Re A||,||Im A||<=R. At z in partial K, ||zI-A||<=3R and |det(zI-A)|>=delta^d. If s_1>=...>=s_d>0 are its singular values, then

    ||(zI-A)^(-1)||= product_{j<d}s_j / |det(zI-A)| <= K0.

Consequently ||R_A||<=4RK0 and

    a^2=integral ||Y*R_A X||_HS^2 d tau <=16 R^2 K0^2.     (Q5)

The HS estimate uses ||Y||op<=1 and ||X||HS=1 and is independent of m. Boundary regularity is required only on Gamma, not on the rest of partial K.

For completeness, the outer-domain passage uses the same fixed pair x,y for F_j=P/M_j, where M_j=max_{closure Omega_j}||P|| decreases to 1 along convex analytic approximation (convergence suffices; monotonicity of the domains is not needed). Its singular value is gamma_j=gamma/M_j. Strong L2 convergence of R_j and H_j from the finished source chain passes the nonnegative terms and the quadratic trace to the limit. Thus the exact identity and nonnegativity give

    E_B:=integral ||H^(1/2) D H^(1/2)||_HS^2 <= S,
    6 ||X*Y||_HS^2 <= S,
    S=2(4/gamma^2-1)a^2.                                  (Q6)

Here E_B is the positive-block slack; the factor 6 is twice the source's coefficient 3. For 0<=epsilon<=1/2 and gamma>=2-epsilon,

    2(4/gamma^2-1)<=4epsilon,
    sqrt(S)<=8 R K0 sqrt(epsilon).                        (Q7)

Indeed 2(4-(2-epsilon)^2)/(2-epsilon)^2<=4epsilon is equivalent for epsilon>0 to 0<=4-7epsilon+2epsilon^2, valid on [0,1/2]. The epsilon=0 case follows directly. No polynomial coefficient convergence or uniform exterior collar is invoked.

## 2. Extracting a hyperplane estimate without a lower conformal-derivative bound

At w=h(e^{it}) on Gamma let S_w=Re(conj(nu)(wI-A)). This positive matrix has nullity one and every nonzero eigenvalue at least g. With C=wI-A,

    C* H C=2 |q| S_w.

The least positive eigenvalue of H is at least 2 |q| g/(3R)^2. This follows by applying the singular-value minmax inequality to S_w^(1/2) C^(-1); its least nonzero singular value is at least sqrt(g)/||C||. Let Pi_t be the orthogonal projection onto ran H, a hyperplane. On that hyperplane invert H^(1/2). Therefore

    ||Pi_t D Pi_t||op
       <= (3R)^2/(2g|q|) ||H^(1/2) D H^(1/2)||HS.         (Q8)

Let I=h^(-1)(Gamma), an open interval or a union of intervals on the circle (a single connected arc has a single interval). Because h is reflected conformally on Gamma, |q|>0 on I and

    integral_I |q| d tau = length(Gamma)/(2pi)>=ell/(2pi).

Cauchy–Schwarz and tau(I)<=1 give integral_I |q|^2 d tau>=ell^2/(4pi^2). Weighted averaging of the squared slack now gives a point t in I with

    ||H^(1/2) D H^(1/2)||HS / |q|
          <= 2pi sqrt(S)/ell.

If the infimum is not attained, use a sequence of points and take the numerical bound as a limit; D is fixed. Inserting in Q8 produces a hyperplane compression satisfying, to arbitrarily small error,

    ||Pi D Pi||op <= eta0 := 9pi R^2 sqrt(S)/(g ell).       (Q9)

This is the useful refinement: no lower bound for |h'|, harmonic measure of the arc, or global curvature is assumed. Arclength and the supporting spectral gap suffice.

## 3. Quantitative replacement for the isotropic-inertia argument

Order Hermitian eigenvalues decreasingly. Interlacing for compression to a hyperplane gives

    lambda_2(D)<=eta0, lambda_{d-1}(D)>=-eta0.              (Q10)

Put kappa=||X*Y||op<=sqrt(S/6), A_X=XX*, A_Y=YY*. Let a2=lambda_2(A_X). If a2=0 there is nothing to prove. Otherwise let E be a two-dimensional spectral subspace for the two largest eigenvalues of A_X. For every unit w in E write w=Xz using the minimal-norm right inverse on E, with ||z||<=a2^(-1/2). Then

    ||Y*w||<=||Y*X||op/sqrt(a2)=kappa/sqrt(a2),
    w*D w>=a2-kappa^2/a2.

The minmax principle and Q10 yield a2-kappa^2/a2<=eta0. Hence

    a2 <= (eta0+sqrt(eta0^2+4kappa^2))/2 <= eta0+kappa.

Apply the same argument to -D and exchange X,Y. Since each positive semidefinite matrix has trace 1,

    t_X,t_Y <=(d-1)(eta0+kappa)
             <=(d-1)[9pi R^2/(g ell)+1/sqrt6]sqrt(S)
             <=C0 sqrt(epsilon).

This closes Q2. It does not round X and Y by pretending their ranges are orthogonal. The kappa term is necessary in this argument.

## 4. Product approximation and quadratic loss of the scalar channel

Choose best unit rank-one approximations x0=xi tensor u, y0=eta tensor v, with <x,x0>=a=sqrt(1-t_X), <y,y0>=b=sqrt(1-t_Y) nonnegative. The Schmidt decomposition gives ||x-x0||^2=2(1-a)<=2t_X, and likewise for y. This proves Q3, including the base-first convention X0=xi u^T.

Write x0=a x+e and y0=b y+f, where e perpendicular x, f perpendicular y, ||e||=sqrt(t_X), ||f||=sqrt(t_Y). For T=P[A], the singular equations make both mixed terms vanish exactly:

    y0*T x0=gamma ab+f*T e.

Thus its real part is at least gamma[ab-sqrt(t_X t_Y)]. Since sqrt((1-t_X)(1-t_Y))>=(1-t_X)(1-t_Y)>=1-t_X-t_Y, Q4 follows. In particular the loss is quadratic in product-vector distances; a mere Lipschitz replacement would lose epsilon^(1/4). This uses no gap at the top singular value and works for every maximal singular pair.

Finally y0*T x0=eta* p(A) xi with p=v*P u, while |p|<=||P|| pointwise. This is coefficient-input scalarization of the original polynomial, not a reducing-block statement about T. All inequalities are explicit and remain valid if their right-hand norm lower bound is negative.

## 5. A genuine dimension-four class, nonempty at equality

Let

    B = [[0,sqrt2,0,0],[0,0,1,0],[0,0,0,sqrt2],[0,0,0,0]].

Diagonal phase unitaries conjugate Re(e^(-i theta)B) to Re B. In the symmetric/antisymmetric reflection bases, Re B has eigenvalues 1,1/2,-1/2,-1. Hence W(B)=Dbar; its full boundary is analytic with support gap 1/2, spectrum {0}, and boundary spectral distance 1. Also B^3=2 e1 e4*, so P(z)=z^3 is an exact extremizer. B is unitarily irreducible: a reducing projection commutes with B and B*, hence preserves ker B=span(e1), and the nonzero weighted chain recursively forces it to be 0 or I.

The theorem therefore applies to a nonempty four-dimensional extremal stratum, including all coefficient sizes and all degrees, and to matrices satisfying fixed quantitative perturbations of its gap, spectral-distance and arc conditions. One can take R=2, delta=1/2, g=1/4 and a fixed positive-length arc in a sufficiently small neighborhood of B; eigenvalue continuity supplies the gap, and continuity of the boundary together with sigma(A) near zero supplies delta. This example is an analytic nonvacuity check, not a numerical experiment.

## 6. Reducible extension with the correct full-range normalization

The same conclusion about existence of p holds if A is a direct sum and a reducing block B of size d satisfies the geometric hypotheses above and ||P[B]||=||P[A]||>=2-epsilon, while max_{W(A)}||P||=1. Run the proof on B. Its local maximum M_B is at most 1. If it is below 1, the direct residual follows by normalization with M_B and gives

    2(4 M_B^2/gamma^2-1)a^2 <=2(4/gamma^2-1)a^2,

so all displayed upper estimates still hold. The scalar compression remains bounded by 1 on the full W(A), and ||p(A)||>=||p(B)||. This does not by itself confine the other summands geometrically; exact confinement in R016 used a monomial identity unavailable at positive deficit.

## 7. Counterexample attacks and what is not uniform

**Support-gap collapse gives entangled maximal pairs, with all other elementary data bounded.** Let N=[[0,2],[0,0]], 0<t<=1/2, and

    A_t=(N+(t/2)I) direct-sum (N-(t/2)I),
    P_t(z)=diag((z+t/2)/(1+t),(z-t/2)/(1+t)).

The numerical range is the stadium conv((t/2+Dbar) union (-t/2+Dbar)), contained in (1+t/2)Dbar and containing Dbar. Its spectrum is +/-t/2, at distance at least 1 from the boundary. The polynomial has degree one, and both coefficient norms are bounded by 1. The maximum of ||P_t|| on the stadium is exactly 1, attained at its real endpoints. Evaluating on the four base/coefficient block combinations gives N/(1+t) twice and (N+/-tI)/(1+t) once each. Direct computation of the eigenvalues of (N+tI)*(N+tI) yields

    gamma_t=||P_t[A_t]||=(1+sqrt(1+t^2))/(1+t),
    epsilon_t=2-gamma_t=(1+2t-sqrt(1+t^2))/(1+t) ->0.

The two extremal channels lie in different orthogonal base blocks and different coefficient coordinates. Equal superpositions of their unit right and left singular vectors form a maximal singular pair with both Schmidt squared tails exactly 1/2. On the right circular arc with normal angle |theta|<pi/3, the supporting spectral gap is t cos(theta)>=t/2 and its length is 2pi/3. Thus no estimate t_X<=C epsilon^alpha with alpha>0 can hold for every maximal pair with C depending only on inball/outradius, boundary spectral distance, degree and coefficient norms while omitting the support gap. The family gives the quantitative necessary blow-up C_t>=(1/2)epsilon_t^(-alpha). At t=0 it is the doubled disk block, and entangled maximal pairs already occur at exact equality.

This does not refute the existence of some scalar compression in the degenerate class: such a compression exists in each displayed channel. It refutes uniform recovery of **every** maximal pair, precisely the stronger content of Q2. It does not establish optimal dependence of Q1 on g, nor is this elementary degeneration nominated as an independent substantial finding.

**Disk-contained reducing blocks.** An active good block can coexist with arbitrary other blocks inside its disk. The block version above extracts p bounded on the full numerical range; it does not classify all of A, nor require all blocks to satisfy delta>0. A boundary eigenvalue on an inactive summand can make the full-matrix delta vanish while leaving the active block's estimate intact. This is why the active-block formulation is included.

**Weighted chain.** For A=N and P(z)=[[0,z],[1,0]], the exact matrix evaluation is, after tensor permutation, the nilpotent weighted chain (1,2,1). Its top right singular vector has nonzero second iterate of norm 2. Consequently no scalar-style reducing square-zero norm-two output block can be inferred. Q2–Q4 say only that the top input/output tensor factors scalarize, and indeed u=e2,v=e1 gives p(z)=z. The example satisfies the d=2 geometric hypotheses and is fully consistent with the theorem.

**Whole coefficient polynomial cannot be rank one.** Unused channels such as P(z)=diag(z,1) at N retain exact equality. The nonconstant and constant coefficient matrices are linearly independent and cannot both be replaced by one rank-one channel with zero error at epsilon=0. The theorem only identifies a near-norming scalar compression, not approximation of the entire P.

**Degree and eigenvalue collisions.** Coefficient matrices and degrees never enter Q5 or the local matrix argument. Large coefficients in a polynomial vanishing at A do not invalidate Q2–Q4. Conversely, quotienting by the minimal polynomial does not preserve the boundary norm and is not used. Distinct eigenvalues may collide: the adjugate estimate remains valid with algebraic multiplicity and only separation from the boundary. An extra pairwise eigenvalue gap is unnecessary here.

## 8. Disk geometry: precise unpaid bridge

The completed theorem controls coefficient scalarization, not d_H(K,a+rho Dbar). Applying qualitative Jin or R016 to a near-extremizer would be invalid. The known scalar output estimate (ACV v3 Corollary 9.9) would give closeness of p(A) to a two-dimensional nilpotent block of order O(epsilon^(1/4)) after Q4, but inversion to A is unavailable: p'(lambda) may vanish and distinct spectral points can have the same image. The weighted-chain example blocks applying even that scalar output conclusion before Q4.

A sufficient remaining scalar bridge, not proved here, is: for the normalized class K subset R Dbar, rDbar subset K, dist(sigma A,partial K)>=delta, controlled simple-support arc (g,ell), degree p<=D, coefficient norm sum<=L, max_K|p|<=1, and ||p(A)||>=2-eta, prove explicit beta>0 and C(R,r,delta,g,ell,D,L) with

    inf_{a in C,rho>0} d_H(K,a+rho Dbar) <= C eta^beta.

Even this must account for the whole numerical range and inactive outer blocks; a disk conclusion for only the active compression is not enough. There is no inverse-polynomial assumption in this target.

The full Jin argument explains why this is nontrivial. Its Proposition 3 first obtains the exact rational identity C_A f=2D_A, where C_A=y*adj(zI-A)x and D_A=x*adj(zI-A)x, from a boundary-kernel equality for an inner extremizer f. Proposition 4 uses exact cancellation to show that the **entire** rational unit lemniscate is the boundary. Propositions 5–6 use exact divisibility, irreducibility and hyperbolicity to force a conic and then a circle. Small residual is not exact divisibility; common factors can nearly cancel, and a remote lemniscate component need not be controlled by local arc smallness. No bound controlling these three operations has been proved in this attempt.

The following shortcuts are explicitly rejected:

- Compactness followed by unnamed modulus: no exponent and not the requested discovery.
- Effective semialgebraic or Lojasiewicz transfer used as an unproved black box: would require a full quantitative encoding, and would not establish this geometric mechanism.
- Applying scalar output rigidity to P[A]: false by the weighted chain.
- Assuming p has a polynomial inverse or a lower derivative bound: excludes genuine degree-three equality at the four-dimensional Crabb block.
- Presenting the exact simple-support general-dimensional result as new: already implicit in R016's Lemma S.

## 9. Disposition

The explicit positive-deficit theorem Q1–Q4 is a completed candidate for independent proof and contribution gates. Its new proposed contribution is robust recovery of the coefficient channel, with an arclength-weighted estimate avoiding conformal-derivative lower bounds, and with square-root scalar loss instead of the naive fourth-root loss. It is not just a nonattained supremum extension and is not a compactness modulus.

The full requested quantitative disk-rigidity program remains **unresolved**. No finding is accepted or counted here. Independent reviewers should decide whether Q1–Q4 alone clear the substantiality standard; if they require quantitative disk geometry as part of this finding, this attempt remains technical progress rather than a completed substantial discovery.
