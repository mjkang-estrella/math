# I251 — independent proof review of quantitative scalarization

**Verdict: PASS.** Reviewed exact input: `frontier/experiments/i247_quantitative_complete_rigidity/analytic-attempt.md`, SHA256 `7d8b629513741abab53339c19bb05c9f611ecbd0af1b6ace3246dff8af0eae8b`. No mathematical repair or extra hypothesis is required for completed Q1–Q4 or the stated existence-only active-block extension. This is a mathematical correctness verdict relative to the stipulated pinned results. It neither accepts a finding nor evaluates its significance.

The initial working notes, written before the source check was complete, identified the residual normalization, boundary passage, and tensor convention as the main checks. The complete argument below resolves those checks. Geometry remains unproved and outside the positive verdict.

## 1. Exact claim and scope

Let d>=2, let R,delta,g,ell>0, and let A in M_d(C). Assume K=W(A) has interior, K subset R Dbar, dist(sigma(A),partial K)>=delta, and a regular real-analytic boundary arc Gamma of length at least ell has simple top support eigenvalue with gap at least g at every point. Put

    K0=(3R)^(d-1)/delta^d,
    C0=8(d-1)R K0 [9pi R^2/(g ell)+1/sqrt(6)].

For any finite m>=1 and finite-degree M_m-valued polynomial P with max_K||P||=1, suppose gamma=||P[A]||>=2-epsilon, 0<=epsilon<=1/2. For every associated unit maximal singular pair x=vec X,y=vec Y, both squared Schmidt tails t_X=1-||X||op² and t_Y=1-||Y||op² are <=min(1,C0 sqrt(epsilon)). Best unit product approximants x0=xi tensor u,y0=eta tensor v satisfy Q3. The corresponding scalar polynomial p=v*P u has max_K|p|<=1 and

    ||p(A)||>=gamma[1-t_X-t_Y-sqrt(t_X t_Y)]
             >=2-epsilon-6C0 sqrt(epsilon).

The theorem concerns each pair's extracted channel; it does not select one channel working for all pairs. No degree, coefficient norm, or coefficient-size bound is needed. The parameters concern distance to the boundary, not mutual eigenvalue separation. The local arc is supplied as a hypothesis, so no general-dimensional theorem asserting existence of that arc is required.

## 2. Source contract and exact residual, independently reconstructed

The direct pinned source uses base-first evaluation sum A^k tensor C_k, unnormalized Hilbert–Schmidt norm, and circle probability measure d tau=dt/(2pi). Its fully read Sections 2–3 give the Faber coefficient inequalities, original-matrix field R=q(hI-A)^(-1), H=R+R*>=0, both ordered multiplier tests, and their reciprocal diagonal weights. The bound ||P[A]||<=2 max_K||P|| is stipulated true. No claim here audits that upstream theorem.

At one analytic enclosing domain, fix the maximal singular pair of the normalized F. Define

    a²=integral ||Y*R X||HS²,
    D_X=integral ||X*H X||HS²,
    D_Y=integral ||Y*H Y||HS²,
    C=integral ||Y*H X||HS².

The two multiplier orders FG and GF, using both singular equations, give D_X,D_Y<=4a²/gamma². The source's explicit cross-field Parseval identity is

    C=4||Y*X||HS²+sum_{k>=1}(||Y*b_k(A)X||HS²+||X*b_k(A)Y||HS²)
     =a²+T,
    T=3||Y*X||HS²+sum_{k>=1}||X*b_k(A)Y||HS².

Consequently E_X=4a²/gamma²-D_X, E_Y=4a²/gamma²-D_Y and E_B=D_X+D_Y-2C are all nonnegative and satisfy the exact algebraic identity

    E_X+E_Y+E_B+2T=2(4/gamma²-1)a².

Indeed the left side is 8a²/gamma²-2C+2(C-a²). This checks the normalization without relying on a previous review's verdict. In particular the overlap term is 6||X*Y||HS², as claimed, and not 3||X*Y||HS².

For D=XX*-YY*, W=[X Y] and J=diag(I_m,-I_m), the positive-block slack is pointwise

    tr((W*H W)J(W*H W)J)=tr(H D H D)
                        =||H^(1/2)D H^(1/2)||HS².

The original H has mass 2I. A mass-one density after similarity from the companion is neither needed nor substituted here.

## 3. Boundary limiting argument at fixed near-extremal vectors

Read the entire relevant I242 exterior-limit proof and I245's detailed verification, then checked its application at positive deficit. Start with analytic convex outer domains Omega_j supplied by the actual pinned approximation lemma. For fixed P, M_j=max_closure(Omega_j)||P|| tends to 1 by uniform continuity on a fixed compact neighborhood. Monotone domains or a monotone sequence M_j are unnecessary. The same x,y are maximal singular vectors of F_j=P/M_j, with gamma_j=gamma/M_j>0; there is no reselection or limiting sequence of vectors.

For completeness, the exterior convergence argument is as follows. Temporarily translate an interior point to zero, enclose the domains in a fixed disk and put a fixed disk inside K. Their exterior maps h_j=c_j z+c_0j+O(z^-1) have positive leading coefficient bounded above and below. Convexity gives Re(1+z h_j''/h_j')>=0. Its exterior Herglotz representation yields

    log(h_j'/c_j)=2 integral log(1-xi/z) d mu_j(xi),
    |h_j'|<=4c_j.

The sign follows by differentiating log(1-xi/z): z times its derivative is xi/(z-xi). Along a weakly convergent subsequence of probability measures mu_j, the logarithms converge strongly in circle L², because the kth Fourier coefficient is -2 muhat_j(k)/k and squared tails are bounded by 4 sum_{k>N} k^-2. Exponentiation is 4-Lipschitz on the half-plane Re z<=log4, by integration along a segment; therefore q_j=z h_j' converges strongly in L². The boundary maps are equi-Lipschitz. Exterior inverse normal families identify their uniform limit with the normalized exterior map h of K, and derivative Fourier coefficients identify the L² limit with z h'. This is strong convergence, not an illicit quadratic limit through weak convergence.

The spectrum is inside K with positive boundary distance. Resolvents along h_j converge uniformly to the resolvent along h on the circle: their arguments lie in a compact set separated from the fixed spectrum. It follows that R_j converges strongly in L² to R, and H_j to H. An almost-everywhere convergent subsequence preserves H>=0. The fixed X,Y give a_j² -> a² and E_B,j -> E_B: expand the difference of tr(H_j D H_j D) and use L² Cauchy–Schwarz. Since E_B,j and 6||X*Y||HS² are each bounded above by 2(4/gamma_j²-1)a_j², passing to the limit gives separately

    E_B<=S, 6||X*Y||HS²<=S,
    S=2(4/gamma²-1)a².

No limit of Faber collars or individual coefficient arrays is required. Corners, flat portions and nonsmooth points away from Gamma do not affect this L² argument. On Gamma, reflection of the conformal map and its inverse gives nonzero derivative and identifies q/|q| with the outward unit normal. Convex K has Jordan boundary; its exterior boundary map is a homeomorphism. Thus the arc has the appropriate circle interval preimage. Endpoint choices have measure zero.

## 4. Explicit energy and deficit constants

The original disk bound gives ||Re A||,||Im A||<=R, hence ||A||<=2R. For w in partial K, ||wI-A||<=3R. Since all eigenvalues of A lie in K, the spectral-distance assumption gives |det(wI-A)|=product |w-lambda_j|>=delta^d, including repeated eigenvalues with algebraic multiplicity. The singular values therefore imply

    ||(wI-A)^(-1)||<= (3R)^(d-1)/delta^d=K0.

This does not assume normality or a resolvent bound delta^(-1). The preceding exterior argument yields |q|<=4 cap(K), and capacity monotonicity, or the exterior inverse Schwarz bound, gives cap(K)<=R in the original coordinates. Translation changes neither capacity nor q; the final constant is the original R. Thus ||R||<=4R K0 almost everywhere. Because ||Y||op<=1 and ||X||HS=1, a²<=16R²K0² independently of m.

The stipulated complete bound also gives gamma<=2. For gamma>=2-epsilon and epsilon<=1/2,

    0<=2(4/gamma²-1)<=4epsilon.

For epsilon>0 the upper inequality reduces to 4-7epsilon+2epsilon²>=0; it is decreasing and still 1 at epsilon=1/2. At epsilon=0 it holds directly. Therefore sqrt(S)<=8R K0 sqrt(epsilon), including both endpoints. These computations verify Q5–Q7 and the 8 in C0.

## 5. Congruence with a kernel and arclength weighting

At a regular point w on Gamma put C=wI-A and S_w=Re(conj(nu)(wI-A)). The support hypothesis gives S_w>=0 with nullity one and other eigenvalues >=g. Direct multiplication gives

    C* H C=2|q| S_w,
    H=2|q|(S_w^(1/2)C^(-1))*(S_w^(1/2)C^(-1)).

For Z=S_w^(1/2)C^(-1), the singular-value product inequality gives s_(d-1)(Z)>=s_(d-1)(S_w^(1/2))/||C||>=sqrt(g)/(3R). One can check it directly by applying s_k(ZC)<=||C||s_k(Z). Thus the least POSITIVE eigenvalue of H is >=2|q|g/(9R²); its zero eigenvalue is never inverted. For Pi the orthogonal projection onto ran H, inversion of H^(1/2) only on that range gives

    ||Pi D Pi||op <= 9R²/(2g|q|) ||H^(1/2)D H^(1/2)||HS.

Let f be the Hilbert–Schmidt quantity. If I is the circle preimage of Gamma, arclength gives integral_I |q| d tau=length(Gamma)/(2pi)>=ell/(2pi). Since tau(I)<=1, integral_I |q|² d tau>=ell²/(4pi²). Weighted averaging of f²/|q|² against |q|² d tau and integral f²<=S yields an infimum <=(2pi sqrt(S)/ell)². Therefore there are arc points with compression norm arbitrarily close to

    eta0=9pi R² sqrt(S)/(g ell).

No positive lower bound for |q| is needed. If the infimum is at an endpoint or not attained, apply each ensuing interlacing inequality along an approximating sequence and take scalar limits. This avoids assuming an endpoint's smoothness or asserting that a particular open-arc point attains the infimum. It checks Q8–Q9 with the stated constants.

## 6. Quantitative inertia and every dimension d>=2

Hyperplane interlacing gives lambda_2(D)<=eta0 and lambda_(d-1)(D)>=-eta0. The second inequality is equivalently lambda_2(-D)<=eta0. It remains valid for d=2, where these are the bottom and top eigenvalues respectively; there is no missing d>=3 hypothesis.

Let A_X=XX*, A_Y=YY*, kappa=||X*Y||op<=sqrt(S/6), and a2=lambda_2(A_X). If a2=0 the desired second-eigenvalue bound is immediate. Otherwise take a two-dimensional top spectral subspace E of A_X. Every unit w in E has w=Xz with minimal-norm z=X* A_X^dagger w and ||z||²=w* A_X^dagger w<=1/a2. Hence

    ||Y*w||<=kappa/sqrt(a2),
    w*D w>=a2-kappa²/a2.

Minmax then gives a2-kappa²/a2<=lambda_2(D)<=eta0, so

    a2<=(eta0+sqrt(eta0²+4kappa²))/2<=eta0+kappa.

Interchange X,Y and D,-D for the same bound on lambda_2(A_Y). Since both A_X and A_Y have trace 1, summing at most d-1 smaller eigenvalues yields

    t_X,t_Y<=(d-1)(eta0+kappa)
             <=8(d-1)R K0[9pi R²/(g ell)+1/sqrt(6)]sqrt(epsilon).

Their trivial bound <=1 supplies the stated minimum. This argument retains the overlap error; it does not falsely treat ran X and ran Y as orthogonal at positive deficit. It is unaffected by multiplicity of their top eigenvalues or by reducibility of A. Q2 is proved.

## 7. Product vectors, stationarity and conjugations

Best unit rank-one products exist for every finite coefficient size. Choose phases so that <x,x0>=a=sqrt(1-t_X) and <y,y0>=b=sqrt(1-t_Y) are nonnegative. The distance identity ||x-x0||²=2(1-a)<=2t_X proves Q3. For m=1 both tails are already zero and the argument still applies.

Decompose x0=a x+e and y0=b y+f with e perpendicular x and f perpendicular y; ||e||²=t_X and ||f||²=t_Y. With T=P[A], Tx=gamma y and T*y=gamma x, both linear terms vanish:

    y0*T x0=gamma ab+f*T e.

Thus its real part is >=gamma(ab-sqrt(t_X t_Y)). Since ab>=1-t_X-t_Y, the first lower bound in Q4 follows. It remains valid when negative. The last lower bound follows from gamma>=2-epsilon, gamma<=2 and t_X+t_Y+sqrt(t_X t_Y)<=3C0 sqrt(epsilon). This verifies the factor 6. No spectral gap at the top singular value is used, so arbitrary maximal singular pairs, including all pairs in a multiple top singular subspace, are covered.

For the source's vectorization x=sum_i Xe_i tensor e_i, a product x0=xi tensor u corresponds to X0=xi u^T, not xi u*. If an SVD is written xi a*, then u=conj(a). Likewise Y0=eta v^T. Expanding base-first evaluation gives

    y0*P[A]x0=sum_k(eta*A^k xi)(v*C_k u)=eta* p(A)xi,
    p(z)=v*P(z)u.

Hence ||p(A)|| is at least the above real part, and |p(z)|<=||P(z)|| on K. If the final lower bound is positive, p is nonzero and division by its positive maximum, which is <=1, can only improve that positive bound. This completes Q1–Q4 with exactly the stated quantifiers.

## 8. Active reducing block and limiting cases

For A=B direct-sum A' and an active B with ||P[B]||=||P[A]||=gamma>=2-epsilon, assume the geometric hypotheses for B and normalize max_W(A)||P||=1. Its local maximum M_B satisfies gamma/2<=M_B<=1 by the stipulated bound; in particular it cannot vanish. Applying the residual to P/M_B on B gives

    S_B=2(4M_B²/gamma²-1)a_B²
       <=2(4/gamma²-1)a_B².

All remaining estimates are therefore valid with B's d,R,delta,g,ell. The resulting p is bounded by 1 on the full W(A), and ||p(A)||>=||p(B)||. This proves the stated existence conclusion. It makes no every-pair assertion for the full A when there are several active blocks; such a strengthening would be false in doubled-block examples. An inactive summand with a boundary eigenvalue may violate the full-A delta hypothesis without affecting this extension.

At epsilon=0 the residual gives S=0, hence kappa=eta0=0, rank X=rank Y=1 and ||p(A)||=2, consistently with equality. For positive epsilon with C0 sqrt(epsilon)>=1, the tail bound is simply vacuous beyond its trivial minimum; no assertion of a nonzero p is made unless the displayed scalar lower bound is positive. Finite but arbitrarily large polynomial degrees are legitimate: the analytic-domain source proof handles each finite polynomial, its maximum M_j tends to 1 for that fixed P, and the final estimates contain no degree or coefficient constants. Eigenvalue collisions and singular-vector multiplicities do not introduce any denominator used by this proof.

## 9. Independent counterexample and nonvacuity calculations

### Crabb chain

For B with upper weights (sqrt(2),1,sqrt(2)), diagonal phase conjugation makes every Re(e^(-i theta)B) unitarily equivalent to Re B. In the symmetric reflection basis its block is [[0,1/sqrt(2)],[1/sqrt(2),1/2]], with eigenvalues 1,-1/2; the antisymmetric block changes the second diagonal to -1/2, with eigenvalues 1/2,-1. Thus the support is constantly 1 and its gap is 1/2. The spectrum of B is {0}, and B³=2e1e4*, so z³ attains equality. A reducing projection preserves ker B=span(e1); successively commuting with B* along the nonzero weights forces it to be 0 or I. This verifies the supplied example without a numerical computation. Small perturbations preserve a simple gapped support branch uniformly in theta; its positive curvature also persists by differentiation of the simple spectral projection. Together with spectral and support continuity, this justifies the stated neighborhoods with relaxed R,delta,g and a fixed regular arc.

### Shifted doubled disk / stadium

Let N=[[0,2],[0,0]], A_t=(N+tI/2) direct-sum (N-tI/2) and P_t=diag(z+t/2,z-t/2)/(1+t). The two shifted disk ranges give the stadium segment[-t/2,t/2]+Dbar. It contains Dbar and is inside (1+t/2)Dbar. The eigenvalues +/-t/2 have boundary distance 1. For each scalar diagonal channel, the maximal modulus of its numerator on that stadium is 1+t, attained at the appropriate real endpoint, so max||P_t||=1. Both its constant and linear coefficient norms are <=1.

Evaluation yields N twice and N+tI,N-tI once each, all divided by 1+t. The Gram matrix of N+tI is [[t²,2t],[2t,4+t²]], whose eigenvalues are (sqrt(1+t²)+/-1)². Thus gamma_t=(1+sqrt(1+t²))/(1+t)>2/(1+t), and the two distinct shifted channels are maximal. They belong to orthogonal base blocks and different coefficient coordinates. Equal superpositions of their right vectors, and of their matching left vectors, have Schmidt coefficients exactly (1/sqrt(2),1/sqrt(2)). Both tails are 1/2, while epsilon_t=(1+2t-sqrt(1+t²))/(1+t)>0 tends to zero. For the theorem's epsilon<=1/2 range one may restrict to 0<t<=1/4; the obstruction only needs t tending to zero.

The support eigenvalues within the right and left blocks are +/-1 +/- (t/2)cos(theta). On |theta|<pi/3, the largest is 1+(t/2)cos(theta) and the next is 1-(t/2)cos(theta), giving gap t cos(theta)>=t/2; this circular arc has length 2pi/3. Hence every-pair estimates omitting g genuinely fail, with necessary constants >=(1/2)epsilon_t^(-alpha) for a power alpha>0. This is consistent with, and not a counterexample to, Q1–Q4. At t=0 the top support multiplicity is two. Existence of some scalar channel can still hold there.

### Output and whole-polynomial obstructions

For P(z)=[[0,z],[1,0]] at N, the base-first T maps e2 tensor e1 to e2 tensor e2, then to 2e1 tensor e1, then to 2e1 tensor e2, then to zero. Its chain weights are (1,2,1). The unique top right vector e2 tensor e2 has ||T x||=||T²x||=2. It cannot belong to a reducing square-zero norm-two block, whereas its input/output coefficient factors extract p(z)=z as asserted. This separates the valid input scalarization from invalid scalar-style output rigidity.

For P(z)=diag(z,1), the two coefficient matrices E11 and E22 are linearly independent, so the full polynomial cannot equal one fixed rank-one coefficient channel times a scalar polynomial at epsilon=0. Unused coefficient channels are unconstrained by Q1–Q4. Reducing blocks contained in an active disk likewise impose no classification of the whole matrix. None of these examples refutes the actual result.

## 10. Verdict and limits

PASS, no repairs. The detailed checks establish the candidate's explicit coefficient-scalarization theorem and its correctly normalized active-block extension. No counterexample within its hypotheses was found by the exact analytic attacks above. This is not a numerical certificate or formal-machine proof.

Disk proximity, quantitative versions of Jin's algebraic argument, optimal exponents or constants, whole-P rank-one approximation, every-pair bounds without the support gap, and a global classification of reducing summands are excluded. External Jin/ACV results are not mathematical dependencies of this verdict and have not been newly audited. Their discussion in I247 remains context only. The supplied count of ten out of twenty is unchanged; the independent contribution gate remains separate.
