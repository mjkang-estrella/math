# T096N126: centered Gaussian noise stability at a universal positive correlation

Author research proof for independent review. This is the full theorem in `FROZEN.md`, whose bytes are unchanged. No correctness, contribution, acceptance or count verdict is assigned here. All constants below are absolute; their construction uses the absolute historical calibration constant C_0. The proof does not assert an effective numerical value for the correlation threshold.

## 1. Definitions and the precise inherited input

Let gamma_d be standard Gaussian measure, and let Pi_m be orthogonal projection onto total Hermite degree m. The Gaussian conditional expectation operator T_rho has eigenvalue rho^m on that subspace. Write z(f)=integral x f(x) dgamma_d(x); thus ||Pi_1 f||_2=|z(f)|. For an array use the sum-of-squares Hilbert norm. All functions used are bounded; Hermite series converge in L2 and their nonnegative energy series converge by Parseval.

Put B=3/(2 sqrt(2pi)). A score array t has three nonzero entries t_1,t_2,t_3 in a plane, forming a centered equilateral triangle with |t_i|=1/sqrt(3), and all other entries zero, allowing any three labels. Thus ||t||=1 and |t_i-t_j|=1 for distinct active labels. Its winning-score partition P has three120-degree sectors, no inactive mass, and z(1_Pi)=B t_i. Write T for the compact set of such arrays for fixed finite d,k. Define

    F(A)=sum_i|z(1_Ai)|²,  Delta(A)=B²-F(A),
    J_t(A)=integral [max_i <t_i,x>-<t_(A(x)),x>] dgamma_d
          =B-<t,Z_A>,

where Z_A=(z(1_Ai))_i. The expression for J follows by the Gaussian sector integral, and all integrands are nonnegative.

The pinned source096 theorem gives Delta>=0 for every partition. The stronger operational input from accepted R012 is the following precise form of I38(6.10),(7.1),(7.2): there is C_0<infinity such that, whenever F(A)>0, every maximizing t of <t,Z_A> satisfies

    J_t(A)<=C_0 Delta(A),
    epsilon(A,P):=gamma_d{A(x)!=P(x)}<=6 sqrt(J_t(A)).       (1)

A maximizer exists since T is a finite union of compact frame orbits. I38 obtains C_0=B^(-1)+(2c_V)^(-1) from uniform score stability. Its countable compactification, equality classification, uniform extra-score activation, triangle estimate and squared-pairing calibration are credited wholesale. They are NOT new claims of this proof. The factor6 follows from the historical three-boundary margin calculation J>=epsilon²/36. That bound is unchanged by additional empty labels. The complete historical author argument and review records are retained privately for dependency inspection.

The new argument below uses (1), not merely the weaker distance-to-orbit headline. The only outside mathematical inputs beyond this historical theorem and the stipulated source are elementary Gaussian/Hilbert-space facts proved or explicitly calculated below. In particular no primary small-noise optimizer theorem is assumed.

## 2. A weight on the propeller plane and a uniform smoothing estimate

Fix any such P and identify R^d=L x L^perp, with u in L=R² and y in R^(d-2). Let L_1,L_2,L_3 be the three full lines containing its boundary rays. Set

    w(u)=min_j dist(u,L_j),  v(u)=w(u)/(1+|u|).

Thus 0<=v<=1, and v>0 off a Gaussian-null union of three lines. The full lines are used only as a lower weight, not asserted to be the actual cell boundaries everywhere.

**Lemma2.1.** There are C<infinity and a function e(R)->0 as R->infinity such that for every d>=2, every measurable scalar f with |f|<=1, and 0<rho<=q:=1/4,

    sum_(m>=2) rho^m ||Pi_m f||² <= C rho² integral v|f|;   (2)

if f=0 on {|u|<=R}, then additionally

    |z(f)|² <= e(R) integral v|f|.                        (3)

Both statements allow arbitrary dependence on y, with constants independent of d.

*Proof.* Put a=1/10, W(t)=exp(a t²), l(t)=|t|/(1+|t|). There is finite K such that for every lambda>0,

    integral_{l/W<=lambda} W dgamma_1 <= K lambda.         (4)

On |t|<=1, l>=|t|/2 and W<=exp(a), so the integrand's support is in |t|<=2exp(a)lambda; bounded Gaussian density bounds its integral by C lambda. On |t|>1, l>=1/2. On the displayed sublevel set this implies W<=2lambda W², and integral W²<infinity because 2a<1/2. This proves (4). If the integral is restricted to |t|>T>=1, the same argument gives (4) with K_T=2 integral_(|t|>T) W² dgamma_1, which tends to zero.

For 0<=h<=1, split at this sublevel set. On its complement W<l/lambda. Therefore

    integral Wh <= K lambda+lambda^(-1) integral l h,
    (integral Wh)² <=4K integral l h.                    (5)

The latter follows by minimizing in lambda; if the right-hand integral vanishes use lambda down to0. If h is supported on |t|>T, replace K by K_T.

For a planar 0<=h<=1, split into three disjoint measurable pieces according to a nearest L_j, breaking ties by index. In coordinates (t,s) normal/tangent to the selected line, w=|t| on this piece and

    v=|t|/(1+sqrt(t²+s²)) >= l(t)/(1+|s|).                (6)

For each fixed s apply (5) to that piece, writing b(s)=integral l(t)h(t,s) dgamma_1(t). Cauchy–Schwarz in s gives

    [integral exp(a|u|²)h(u) dgamma_2]²
       <= 4K [integral (1+|s|)exp(2as²) dgamma_1(s)]
                    [integral b(s)/(1+|s|) dgamma_1(s)]
       <= C integral v h.                               (7)

The outer integral is finite. Summing the three pieces, using (sum_j I_j)²<=3sum_j I_j², preserves an absolute C.

If h is supported on |u|>R, split each piece further, disjointly, into |t|>R/sqrt(2) and its complement, on which |s|>R/sqrt(2). In the first part the constant K in (7) is replaced by K_(R/sqrt(2))->0. In the second part the outer Gaussian integral in (7) is restricted to |s|>R/sqrt(2), and tends to0. Summing the six pieces proves (7) with C_tail(R)->0 for R>=sqrt(2). Enlarge it for smaller R if necessary. No truncation of the function's support in the other direction was assumed.

The planar Mehler kernel relative to gamma_2 is positive semidefinite, and its diagonal is

    K_q(u,u)=(1-q²)^(-1) exp(q|u|²/(1+q)).

Its Hermite feature map is (q^(|alpha|/2) H_alpha(u))_alpha. The norm of that vector is sqrt(K_q(u,u))=(1-q²)^(-1/2) exp(a|u|²). The triangle inequality for its integral against f gives

    <f,T_q^(u) f>_(gamma_2)
       <=(1-q²)^(-1) [integral exp(a|u|²)|f| dgamma_2]²
       <=C integral v|f|.                               (8)

One may first project the feature vector to finitely many coordinates and then use monotone convergence; (7) supplies integrable majorants. For support outside the R-ball use C_tail(R) instead. Apply (8) to almost every y-fiber and integrate in gamma_(d-2). For d=2 this factor is a one-point probability space. Product Hermite coefficients c_(alpha,beta) satisfy

    sum_(alpha,beta) q^|alpha| |c_(alpha,beta)|²
       <= C integral v|f|,                              (9)

with the tail constant tending to0 when applicable. Parseval in y and Tonelli justify the identity, including all dependence on y.

For |alpha|+|beta|>=2 and rho<=q,

    rho^(|alpha|+|beta|) <= (rho/q)² q^|alpha|.

For |alpha|>=2 this follows by comparing the remaining powers; for |alpha|=1 use |beta|>=1, and for |alpha|=0 use |beta|>=2. This proves (2) from (9). For total degree1, the coefficient1 is at most q^(-1)q^|alpha|. Thus (9) with its tail constant proves (3). All constants came from two- and one-dimensional integrals. QED.

For later use let f_i=1_Ai-1_Pi. On a mismatch exactly two |f_i| equal1. If the incorrect label is active, the score gap is the distance to its pair boundary line, since |t_i-t_j|=1. If it is inactive, the winning score is at least |u|/(2sqrt(3)). It follows pointwise, and also on every measurable restriction E, that

    sum_i integral_E v|f_i| <= C_v integral_E scoregap,
    C_v=4sqrt(3).                                        (10)

There is no factor k in (2),(3) when summed over labels.

## 3. The exact smoothed scores, including the unbounded planar tails

For active labels put q_i(u)=T_rho1_Pi(u)-1/3; for inactive labels put q_i=0. They do not depend on y. The following are assertions about a fixed reference propeller, not an optimizer regularity argument.

**Lemma3.1.** There are absolute kappa>0, and, for each finite R, C_R<infinity, such that for every 0<rho<=1/4, every u in active winning sector P_i, and every incorrect label j,

    q_i(u)-q_j(u) >= 2kappa rho v(u),                     (11)

and if |u|<=R, with s_ij(u)=<t_i-t_j,u>,

    |q_i(u)-q_j(u)-rho B s_ij(u)|
                   <= C_R rho² s_ij(u).                 (12)

*Proof of(11).* First j is active. Choose orthonormal coordinates (s,b) with s>=0 normal into P_i and b directed along the common boundary ray. Then

    P_i={s>=0,b>=-s/sqrt(3)},
    P_j={s<=0,b>= s/sqrt(3)}.

For u=(s,b) in P_i, b>=-s/sqrt(3). Put sigma=sqrt(1-rho²), mu=rho s>=0. Pair the two reflected integration regions in the Gaussian formula for T_rho. With phi_sigma the N(0,sigma²) density and Phi the standard normal CDF, this gives exactly

    q_i(u)-q_j(u)
      = integral_0^infinity [phi_sigma(x-mu)-phi_sigma(x+mu)]
                     Phi((rho b+x/sqrt(3))/sigma) dx.     (13)

Both factors are nonnegative. On x>=mu, the CDF factor is >=1/2. Hence (13) is at least

    (1/2)[Phi(2mu/sigma)-1/2] >= c min(rho s,1).          (14)

A single positive c works because sigma lies in [sqrt(15)/4,1], the Gaussian density is bounded below on [0,2], and the CDF increment beyond2 is bounded below by its value at2. Since s<=|u| and rho<=1,

    min(rho s,1)>=rho s/(1+|u|)>=rho v(u).

If j is inactive, sum the two active pair differences. Since the three active q's sum to zero,

    q_i=(1/3)sum_(l active,l!=i)(q_i-q_l).

Each pair distance is >=w(u), so (14) gives the same lower bound with a different absolute constant. This proves(11), choosing kappa to include the factor2 for the two mismatch indicators. Boundary ties are harmless and null.

*Proof of(12).* The function (rho,u)->T_rho1_Pi(u) is smooth for |rho|<1: write it as an integral of the density of N(rho u,(1-rho²)Id) over the fixed planar sector. On |rho|<=1/4, |u|<=R, all derivatives needed here have integrable Gaussian-polynomial majorants uniform on this compact parameter set. At rho=0 its value is1/3 and its first rho derivative is z(P_i)·u=B t_i·u. Consequently the u-gradient of the remainder q_i-rho B t_i·u has norm <=C_R rho² on the R-ball, by Taylor's theorem with the mixed derivatives bounded as just described.

For active i,j their remainder difference vanishes identically on the full line s=0, by reflection interchanging the sectors. Integrate its normal derivative from (0,b) to (s,b); this segment remains in the R-ball, and s=s_ij since |t_i-t_j|=1. This proves(12) for active j. For inactive j, the active remainder vanishes at u=0, since a centered isotropic Gaussian places probability1/3 in every sector for every rho. Its absolute value is <=C_R rho²|u|. On P_i, t_i·u>=|u|/(2sqrt(3)), which proves(12) with a larger C_R. QED.

Define

    D(A;P)=sum_i <1_Pi-1_Ai,q_i>
          =integral [q_(P(x))(u)-q_(A(x))(u)] dgamma_d.

For g=f1_(|u|<=R), h=f1_(|u|>R), let J_N be the original score loss on |u|<=R, let D_N,D_T be the two restrictions of D, and put

    U=sum_i integral v|g_i|, V=sum_i integral v|h_i|.

Equations(10)–(12) imply

    U<=C_v J_N,
    |D_N-rho B J_N|<=C_R rho² J_N,
    D_T>=kappa rho V.                                   (15)

This is the step that retains the actual bounded smoothed loss in the tails instead of extrapolating a linear score to infinity.

## 4. Replacing the tails while retaining the centroid alignment

The partition A^N with indicators 1_Pi+g_i is legitimate: it equals A inside the planar ball and P outside it. Let G=Z_(A^N)-Z_P=z(g), H=Z_A-Z_(A^N)=z(h), and write a=||G||, b=||H||. Since Z_P=Bt,

    Delta(A^N)=2B J_N-a².                               (16)

In particular a²<=2B J_N by the stipulated first-moment bound.

**Lemma4.1.** There exist absolute delta_*>0, c_*>0, C_*<infinity such that the following holds. Suppose t maximizes <t,Z_A> over T and

    ||Z_A-Bt||<=delta_*, ||Z_(A^N)-Bt||<=delta_*.

Then

    Delta(A^N)>=c_* J_N-C_* b².                         (17)

*Proof.* Choose t_N maximizing <t_N,Z_(A^N)>. Since minimizing ||Z_(A^N)-Bt'|| over T is equivalent to maximizing this pairing,

    B||t_N-t|| <=2||Z_(A^N)-Bt||.

If two arrays in T have different active label sets, their distance is at least1/sqrt(3), because some label is zero in one and has norm1/sqrt(3) in the other. Choose delta_*<B/(2sqrt(3)), so t_N and t have the same three labels. Their ordered triples can therefore be represented as t=QE and t_N=Q_NE for the same fixed 2-by-3 equilateral matrix E satisfying EE*=I_2/2; Q,Q_N are d-by-2 isometries. All choices of ordering or reflection are included by allowing every isometry Q_N. Other columns are zero.

Let Z_A^head denote the d-by-3 centroid matrix on these labels and M=Z_A^head E*. At Z_A=Bt, M=(B/2)Q. With delta_* sufficiently small, M has smallest singular value at least B/4, because ||(Z_A^head-BQE)E*||_op<=delta_*/sqrt(2). Since Q maximizes the pairing among all frames, it is the polar factor of M, so M=QH_0 with H_0 positive definite and H_0>=B I_2/4. This follows directly from the singular-value decomposition: maximize Tr(Q'^*M) over isometries Q', with equality at the polar factor; full rank makes the maximizer unique.

For any isometry Q', I-sym(Q'^*Q) is positive semidefinite: its quadratic form is |v|²-<Q'v,Qv> >= 0. Thus

    Tr((Q-Q')* M)
      =Tr([I-sym(Q'^*Q)]H_0)
      >=(B/8)||Q-Q'||_F².                              (18)

On the other hand, optimality of Q_N for Z_(A^N) gives

    Tr((Q-Q_N)*M)
       <= <(Q-Q_N)E, Z_A^head-Z_(A^N)^head>
       <= ||Q-Q_N||_F b/sqrt(2).

Combining with(18) shows ||Q-Q_N||_F<=C b, and hence ||t-t_N||<=C b. Also, using optimality of t for Z_A,

    0<=J_t(A^N)-J_(t_N)(A^N)
      =<t_N-t,Z_(A^N)>
      <= |<t_N-t,Z_(A^N)-Z_A>| <= C b².                (19)

The historical calibration applies to A^N: its centroid norm is positive for delta_*<B, and gives J_(t_N)(A^N)<=C_0 Delta(A^N). Since J_t(A^N)=J_N, (19) proves(17) with c_*=1/C_0 and an absolute C_*. No cell-mass condition or bound on d,k was used. QED.

## 5. Uniform global entry and absorption of all errors

Let A be any partition satisfying S_rho(A)>=S_rho(P). It is enough to show that such A is itself a propeller. Parseval gives the exact centered energy representation

    S_rho(A)=sum_(m>=1) rho^m sum_i||Pi_m1_Ai||².

Its full indicator squared-norm budget is sum_i||1_Ai||²=1. Therefore

    rho B² <= S_rho(P) <= S_rho(A) <=rho F(A)+rho²,
    0<=Delta(A)<=rho.                                   (20)

Choose rho<B²/2 so F(A)>0, and choose t maximizing the centroid pairing. The historical calibration gives J_t(A)<=C_0rho and epsilon(A,P)<=6sqrt(C_0rho). First-chaos projection is a contraction, so

    ||Z_A-Bt||² <=sum_i||1_Ai-1_Pi||²=2epsilon(A,P),
    ||Z_(A^N)-Bt||² <=2epsilon(A,P).                     (21)

Consequently one absolute sufficiently small upper bound on rho ensures both hypotheses of Lemma4.1, for EVERY R and every d,k. No maximizer of the noise functional has been assumed to exist; we work directly with an arbitrary contender.

For f_i=1_Ai-1_Pi, the exact quadratic expansion of the centered noise functional is

    S_rho(A)-S_rho(P)=-2D_N-2D_T
           +rho||G+H||²+Q,
    Q=sum_i sum_(m>=2)rho^m||Pi_m f_i||².                (22)

Indeed the linear term is 2sum_i<f_i,(T_rho-Pi_0)1_Pi>=-2D, and the quadratic term splits into first and higher chaos. From Lemma2.1 and(15),

    0<=Q<=C rho²(U+V)<=C' rho²J_N+C rho²V,
    b²<=e(R)V.                                         (23)

Combining(15)–(17),(22),(23), and ||G+H||²<=a²+2ab+b², gives

    S_rho(A)-S_rho(P)
      <= -c_*rho J_N+(C_*+1)rho b²+2rho a b
                    -2kappa rho V+C'_R rho²J_N+C rho²V. (24)

Every sign here comes from the exact identity(16); no tail loss has been replaced by a linear first-moment loss. Since a²<=2B J_N, Young's inequality, with a fixed coefficient depending only on B,c_*, gives

    2ab<= (c_*/4)J_N+C_Y b².

For example use 2ab<=eta a²+eta^(-1)b² with eta=c_*/(8B). Put C_b=C_*+1+C_Y. Choose a single finite R>=sqrt(2) so large that C_b e(R)<=kappa/2. This choice is independent of rho,d,k,A. With(23), (24) becomes

    S_rho(A)-S_rho(P)
      <=-(3c_*/4)rho J_N-(3kappa/2)rho V
                               +C'_R rho²J_N+C rho²V.  (25)

Finally choose rho_0>0 satisfying all the preceding absolute upper bounds, rho_0<=1/4, C'_R rho_0<=c_*/4 and C rho_0<=kappa/2. Shrinking it if necessary retains positivity. Then for every 0<rho<=rho_0,

    S_rho(A)-S_rho(P)<=-(c_*/2)rho J_N-kappa rho V.       (26)

The contender assumption forces J_N=V=0. Original score gaps are strictly positive on every mismatch except the finitely many planar tie lines (and the origin for inactive comparisons). Thus J_N=0 implies A=P almost everywhere inside the ball. Since v>0 almost everywhere, V=0 implies A=P almost everywhere outside it. Hence A belongs to the propeller orbit. Conversely every member of that orbit has the same centered noise energy by orthogonal and label invariance.

If any A had larger energy than a propeller it would be a contender and the preceding conclusion would contradict strict inequality. If it has equal energy it is a propeller. This proves both the frozen inequality and its full equality assertion, for all finite d>=2,k>=3 and arbitrary measurable cells and masses. No scope has been weakened.

## 6. Dependency and contribution boundaries

The proposed full result concerns a fixed interval of POSITIVE correlations and the entire Hermite energy, not the first-moment limit. Its main inheritance is strong: source096 and accepted I38 already supply the uniform first-chaos gap and weighted alignment. Ordinary Mehler expansions, one-dimensional Gaussian integrals, Procrustes geometry, compact-parameter differentiation and Young's inequality are classical. No individual one of those is nominated.

The specific additional compatibility operation supplied in Sections2–5 is the following: the bounded exact smoothed-score loss must absorb an unbounded-dimensional, arbitrarily labeled perturbation without losing the existing optimal centroid alignment. Partial planar smoothing estimates the full Hermite series despite arbitrary orthogonal dependence; the vanishing tail coefficient makes the change in the optimal polar frame affordable; the bounded-ball deficit then combines with the actual tail score loss. This is the author's operation comparison, not a substantiality verdict. Whether these operations are already paid by a stronger compatible primary transfer, or constitute only a technical application of existing stability, remains for independent contribution review.

Primary predecessors and actual reading extents are recorded separately. Heilman's three-label derivative theorem is stronger than its equal-mass introduction and already pays a three-label centered variant; it is credited. No worldwide-priority claim is made. No numerical diagnostic, packet hash or integrity control certifies this analytic proof.
