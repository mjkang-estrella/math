# Author proof of the entire frozen statement S236

This is a research author-proof submission, not a correctness or contribution verdict. The statement is exactly STATEMENT.md, SHA256 ad83c8bcf032a77734228b59ef8e4721215d0c09907e9e504a7df934ab89af1e. Source A and Source B below mean the two authenticated Source361 papers at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Their operative proofs are stipulated true. The additional construction here uses A's exact invariant blocks and its full-period control, not a limit of B's finite-rank examples.

## 1. Paid interfaces and the new operation

Put n=m+1. For every orthogonal complex structure J on R^n, A's link lemma gives

    gamma(a,q,J)=a^2 q^(-1/m)(g_0+(q-1)eta_J^2),
    dvol_gamma=a^m dvol_0,
    A_l(a,q,J)=-Delta_gamma|V_l
      =a^(-2)q^(1/m)[B_l I+(q^(-1)-1)(-D_J^2)],
    B_l=l(l+m-1).                                                (1.1)

The real round spaces V_l are invariant for EVERY J. This is exact, including all multiplicities and the infinite complement of any finite set of degrees. The link-curvature lower bound is

    Ric_gamma >= a^(-2)q^(1/m)
           min{m-1-2(q-1),(m-1)q} gamma.                         (1.2)

We use the following precise finite control interface from A, sections algebra and transmission. For any finite consecutive set 2<=l<=L, the trace-free pulse generators, with both signs of pulse area and both orientations of J allowed, generate the full direct sum of sl(V_l). Proposition `prop:word` consequently gives, at ANY prescribed target in the product of SL(V_l), a finite word and a finite-dimensional parameter slice on which the ideal endpoint map is a local diffeomorphism. The ideal generators have the degree-dependent scalar factors determined by the positive round roots theta_l at a=a_*. These factors are already included in the word. No independent scaling of different degrees is being assumed.

The transmission proof removes the entire following diagonal leg, not just its dwell. If the regular value equation at the pulse exit has slope P_e and pulse value map B, its full-period normalized map is exactly

    D_lj^(-1) T_lj = [I+K_lj(P_e-theta_l I)] B,                  (1.3)
    D_lj=U_lj+theta_l V_lj,
    K_lj=D_lj^(-1)V_lj,       0<=K_lj<=theta_l^(-1) I.

Here U,V are the diagonal scalar solution operators of the whole up-ramp, dwell, down-ramp and final round rest. The factor order in (1.3) is essential. The initial slope may be any slope furnished by the center-regular graph with the stated reset estimate; it need not commute with the leg. Section 5 below verifies the slower radial-tail version of every estimate needed from this interface.

A already permits arbitrary finite targets and finite cyclic selections. B already proves full infinite-tail control and countably many crossing matches for each fixed finite rank, including arbitrary closeness to Euclidean geometry in its stated range. Neither a finite partition nor removal of a finite cutoff by declaration is the new step here. We construct a single schedule handling every degree, then use a signed radial drift to include each critical mean exactly, and finally classify ALL polynomial-growth functions on that metric.

## 2. Targets and one fixed absolute schedule

For each prescribed cycle C=(i_1,...,i_h), let Pi_C e_(i_a)=e_(i_(a+1)) for a<h and Pi_C e_(i_h)=(-1)^(h-1)e_(i_1). Thus det Pi_C=1, including h=1. Their direct sum Pi_l belongs to SL(V_l). The support of each cycle is invariant under both Pi_l and every diagonal matrix in the fixed dwell basis. The signs have absolute value one and do not change any norm or mean.

At level N choose once and for all a finite word from the preceding interface with targets (Pi_2,...,Pi_(N+1)). Restrict its parameters to a compact ball in a finite-dimensional local-diffeomorphism slice. Every word starts and ends at q=1. Its moving pulses use fixed J, and changes of J occur only in open round gaps. The metric profiles can be made smooth and flat at the endpoints. An auxiliary J may be reset across an open round gap even between its two orientation classes: no path between those components is required, because the metric there is exactly independent of J. All earlier target matrices are exactly the same at every level. The words themselves may change completely.

Use the absolute schedule

    T_j=j^6,   L_j=j^7,   t_1=10,
    t_(j+1)=t_j+L_j+4T_j.                                      (2.1)

One period contains a control interval of length T_j, an up-ramp of length T_j, a dwell of length L_j, a down-ramp of length T_j, and a final round rest of length T_j. This is the source schedule. In particular

    t_j=(1/8)j^8+O(j^7),   t_(j+1)-t_j=O(j^7).                  (2.2)

The up/down profiles and J_0 on the whole leg are fixed independently of level. On the control interval the level-N word is realized with q=1+z_N((t-t_j)/T_j,h)/T_j. The function z_N and the orientation changes have finite derivative bounds on the compact parameter ball. Signed pulses can have q slightly below one. No positivity-of-pulse restriction is imposed.

## 3. Radial tail and a safe initial region

Set delta=1/16. Choose a smooth nondecreasing cutoff chi_B, zero on t<=B and one on t>=2B, with derivatives O(B^(-a)) of each fixed order a. Write

    I_B=int_B^infinity chi_B(t)(1+t)^(-1-delta) dt,
    mu=(-log a_*)/I_B>0,
    b(t)=-mu chi_B(t)(1+t)^(-1-delta),
    a(t)=exp(int_(-infinity)^t b(s) ds).                         (3.1)

In (3.1) define b=0 for t<=B and use its displayed formula only for t>B, so no fractional power at t<=-1 is involved. Then a=1 on t<=B, a decreases to a_*, and, for t>=2B,

    log(a(t)/a_*)=A(1+t)^(-delta),       A=mu/delta>0.             (3.2)

Taking B large makes |b|<=1/4. Indeed I_B is bounded above and below by positive constants times B^(-delta), whereas sup chi_B(t)(1+t)^(-1-delta)=O(B^(-1-delta)). Also

    b+b'+b^2
     = -mu chi_B f [1-(1+delta)/(1+t)-mu chi_B f]
       -mu chi_B' f <=0,         f=(1+t)^(-1-delta),             (3.3)

once B is large. Beyond 2B its negative is comparable to mu(1+t)^(-1-delta).

Choose a_bar>a_* so close to a_* that (S1) still holds with a_bar in place of a_*, with a fixed positive margin. By continuity, that margin holds also for q in [1-epsilon_0,q_*], for some epsilon_0>0. Until a<=a_bar and until all initial control thresholds below are satisfied, put q=1. This is a finite prefix of (2.1), and includes a neighborhood of the origin. Later q is the word-plus-leg schedule. Its weak pulses lie in the indicated compact interval once the activation thresholds are large.

Define, with r=exp t,

    g=dr^2+r^2 gamma(a(t),q(t),J(t)).                            (3.4)

On r<=exp B this is precisely Euclidean. Thus no vertex singularity or center boundary problem is left to a limiting argument.

## 4. Uniform regular graphs, including every uncontrolled degree

For u(r,omega) in a fixed V_l, its coefficient vector Y(t) satisfies exactly

    Y''+p(t)Y'-A_l(t)Y=0,      p=m-1+mb.                        (4.1)

The trace of the angular volume derivative is mb; it has no q or J term. In the Euclidean core regular solutions are Y=e^(lt)v. The source's Wronskian/Riccati argument gives a symmetric positive center-regular slope P_l and Y'=P_lY. Here are global bounds independent of all word complexity, so there is no uncontrolled spectral-tail hypothesis.

Since a and q range over fixed compact sets and 0<=-D_J^2<=l^2 I on V_l, there are kappa,K>0 with

    kappa l(l+m-1) I <= A_l(t) <= K l(l+m-1) I                 (4.2)

for all t,J,l>=1. Also 0<p_min<=p<=p_max<infinity. Choose c in (0,1) small enough that c^2<=kappa/4 and p_max c<=kappa/4. At P_l=c l I the right side of

    P_l'=A_l-pP_l-P_l^2                                      (4.3)

is positive definite: (4.2) dominates both p_max c l and c^2 l^2. Choose C>=1 with C^2>K m; at P_l=C l I the right side is negative definite. The matrix eigenvalue barrier argument therefore proves

    c l I<=P_l(t)<=C l I        for every l>=1 and every t.    (4.4)

Symmetry follows either from the vanishing Wronskian of the regular fundamental pair or uniqueness for the symmetric Riccati equation. The barriers prevent finite-time Riccati blow-up. Conversely solving Y'=P_lY from the core gives an invertible fundamental matrix for all finite t and satisfies (4.1), by (4.3). These arguments also prove that all N_l regular solutions extend globally and retain independence, regardless of the choices in any later period.

For each vector solution,

    e^(cl(t-s))||Y(s)|| <= ||Y(t)|| <= e^(Cl(t-s))||Y(s)||
                 (t>=s).                                    (4.5)

This is obtained by differentiating ||Y||^2; it does not require commuting matrices. All V_l are still exact invariant subspaces. For l=0 the only center-regular solution is constant; the other radial solution is singular at the Euclidean center.

Let theta_l>0 solve theta_l^2+(m-1)theta_l=a_*^(-2)B_l. During a round rest, A_l is scalar. Matrix Riccati damping and (3.2) give, for each fixed l,

    ||P_l(t_j)-theta_l I|| <= C_l j^(-1/2)                    (4.6)

for sufficiently large j, uniformly in all earlier words and their parameters. To see the exponent and uniformity explicitly, throughout that rest t is comparable to j^8, so |a-a_*|+|p-(m-1)|<=C j^(-1/2). Subtract theta_l I in (4.3); the linear two-sided damping has a fixed positive lower bound from (4.4). Variation of constants bounds the error at the end by an exponentially decaying initial error plus C_l j^(-1/2). The initial error is bounded by (4.4), independent of the past, and the rest lasts (j-1)^6. This also covers a degree before it is first actively controlled.

## 5. Finite-level control with the modified tail

Fix a level N for this paragraph. All constants may depend arbitrarily on N, its word, compact parameter ball and m,a_*,q_*. Nothing in this paragraph is uniform as N tends to infinity.

On its control interval put eta_j=j^(-1/2)+T_j^(-1). The round coefficient and p differ from their limiting values by O(eta_j), uniformly on the interval; their derivatives are smaller. The initial slope error is O_l(eta_j) by (4.6). The source pulse proof uses an exact scalar baseline v, solving

    v'=a(t)^(-2)B_l-pv-v^2,

and a trace-free first-order response X/T_j, where X is linear in the scaled pulse profile with the degree-dependent generator coefficient. Expanding (1.1) in q-1 gives, uniformly with one parameter derivative, a residual

    ||R|| <= C_N[eta_j/T_j+T_j^(-2)].                          (5.1)

The parameter derivative has the same bound, since all word profiles and their parameter derivatives are bounded on the chosen compact ball. The initial mismatch after subtracting the baseline and the first response is O(C_N eta_j). Damped Riccati variation of constants, exactly as in A equations `eq:pulse-error-equation`--`eq:parameter-error-integrated`, gives

    int_control ||P_l-vI-X/T_j|| dt <= C_N eta_j,               (5.2)

with the same estimate for one parameter derivative. For clarity, the initial O(eta_j) error decays on bounded t scale and contributes O(eta_j), NOT T_j eta_j. The persistent part in (5.1) has integral O(eta_j), since its size is O(eta_j/T_j) and the interval length is T_j. The quadratic error is absorbed by the positive damping for large j. The scalar baseline is kept exact, so its accumulated drift of order T_j|a-a_*| is not falsely treated as a small absolute transfer error.

Integrating the normalized value equation therefore shows C1 convergence of its pulse map to the fixed ideal word, with error O(C_N eta_j). At pulse exit P_e-theta_l I=O(C_N eta_j); its parameter derivative obeys the same estimate. The actual scalar diagonal leg, with initial data y=1,y'=theta_l in each coordinate, has positive solution D_lj. The positivity argument from A is unchanged: U,V solve y''+py'-lambda_i y=0 with lambda_i>0, so U>0,V>=0, U+theta_l V>0 and 0<=V/(U+theta_l V)<=1/theta_l. Thus (1.3), including its derivative, implies that the determinant-normalized FULL-period map

    F_Nj(h)_l = det(D_lj^(-1)T_lj(h))^(-1/N_l)
                     D_lj^(-1)T_lj(h)                        (5.3)

converges in C1 to the same product-SL word. Its determinant is positive, since the center-regular value fundamental matrix and the positive diagonal D have positive determinant. All errors are uniform in the preceding construction by (4.4)--(4.6).

The finite-dimensional local inverse at the prescribed target now gives a parameter h_j in the fixed ball for which, simultaneously for 2<=l<=N+1,

    T_lj=s_lj D_lj Pi_l,        s_lj>0.                       (5.4)

This is an exact equality. Existence follows, for example, by composing the map in coordinates with the inverse ideal word and applying the contraction proof of the inverse function theorem on a smaller ball. Choose the C1 error small enough relative to that fixed ball and inverse derivative bound. It works for every allowed incoming regular graph, so the induction in j is legitimate. Dependence on h is only within this period; no future data enter the selection.

The scalar estimates in the source pulse proof, or the upper and lower value bounds (4.5) on the control interval followed by (1.3), also give

    |log s_lj|<=C_N T_j.                                      (5.5)

There is no uncontrolled exponential from the long dwell: it was removed by D on the left BEFORE using the inverse theorem. The bounded K in (1.3) is what permits this. For l=1, -D_J^2=I for every J and the whole equation is scalar. Put Pi_1=I and define s_1j=T_1j/D_1j. The same normalization and positive scalar bounds give (5.5), with a constant independent of N once the pulse parameters stay in the global compact geometric range. No control of sl(V_1) is asserted or needed.

## 6. Slow activation and a single smooth metric

Collect for level N a finite number M_N>=1 which bounds: its metric pulse-profile derivatives through order N+2 (only the metric, not an auxiliary J reset inside a round gap), its finite constants in (5.1)--(5.5), its inverse derivative bounds and reciprocals of its local-inverse tolerance, and the finitely many additional geometric thresholds needed for that level. Replace M_N by its running maximum if needed. Choose strictly increasing integers J_N with J_(N+1)>J_N so large that, for all j>=J_N,

    M_N<=j^(1/8),
    C_N(j^(-1/2)+j^(-6)) is below the chosen inverse tolerance,

and the bounds below for the Nth word hold. Every such threshold is finite. Define the active level to be N for J_N<=j<J_(N+1). Before J_1 use only round periods. Choose each period's controls by section 5 after constructing the preceding periods. Until a new threshold is reached the preceding level continues to operate, with no waiting region that forgets its previously prescribed targets.

This defines one metric by ordinary induction. There is no finite t accumulation because t_j tends to infinity. Smooth, flat joins on each finite period give a globally smooth metric. For any derivative order a, all sufficiently late levels include the relevant profile bounds, and the scaling by T_j makes the time derivatives of the weak pulse tend to zero; the fixed leg derivatives also tend to zero. This proves the needed all-order local coefficient convergence on annuli without a limit of unrelated metrics.

Each l>=2 has an activation index j_l=J_(l-1). From then onward (5.4) holds at EVERY period for that l with its SAME target Pi_l, even across changes of level. Also for each active l,

    |log s_lj|<=j^(6+1/8),                                    (6.1)

after increasing thresholds to include harmless constants. For l=1 this inequality holds eventually as well. The countably many finite inverse problems do not require a common inverse radius or uniform bound in l.

## 7. Geometry, completeness, volume and cones

Let H=(q'/(2q))(P_J-I/m), where P_J is the Hopf-line projection and primes here mean d/dt. On each moving piece J is fixed; where J changes q is identically one and H=0. The source identities, therefore valid throughout the smooth construction, are

    r^2 Ric_rr=-m(b+b'+b^2)-tr(H^2),
    Ric_(r,tangent)=0,
    r^2 Ric_T^#=Ric_gamma^#-B'-(m(1+b)-1)(I+B),
    B=bI+H.                                                   (7.1)

The mixed identity uses trace H=0 and div H=0 for a Hopf Killing field. During orientation changes the metric is independent of J, so no unaccounted J' term occurs in (7.1).

On the initial round region the tangential coefficient is

    (m-1)(a^(-2)-1)-(2m-1)b-mb^2-b'.

Using (3.3), this is at least (m-1)(a^(-2)-1-2b-b^2)>=0. Radial Ricci is nonnegative there too. There is no need to deform a unit round link while claiming a strict margin it does not have.

On all active periods, a<=a_bar and q is in the fixed compact interval with link margin. Thus Ric_gamma^# >= (m-1+epsilon)I. The remaining difference from (m-1)I in the tangential terms of (7.1) tends uniformly to zero. Indeed b,b' tend to zero, the fixed ramps have q'=O(j^(-6)), q''=O(j^(-12)), and on a weak pulse these derivatives are bounded by M_N/T_j^2 and M_N/T_j^3, respectively. Increasing J_1 and the subsequent thresholds gives positive tangential Ricci.

For the radial component, (3.3) beyond 2B gives a positive buffer comparable to

    (1+t)^(-17/16),

which is comparable to j^(-17/2) on period j. Fixed ramps cost tr(H^2)=O(j^(-12)); weak pulses cost at most O(M_N^2 j^(-24)). These are o(j^(-17/2)), since M_N<=j^(1/8). Round rests and dwells have H=0. Increasing thresholds gives nonnegative radial Ricci everywhere. Together with the zero mixed terms this proves Ric_g>=0, not just separate coordinate tests in a metric with uncontrolled mixed Ricci.

The compact parameter bounds imply global equivalence to the Euclidean polar metric. More directly, the length of any path from o to a point of coordinate r is at least r, and the radial segment has length exactly r. Hence dist_g(o,x)=r. Closed bounded r-balls are compact in the smooth R^n topology, so g is complete. The volume form is exactly

    r^m a(log r)^m dr dvol_0.

Since a tends to a_*, division of its radial integral by omega_n R^n gives normalized AVR=a_*^m. This is one all-radius limit, independent of the partition sequence and not merely a subsequential volume statement.

Take t_j^round in the interior of final rests and t_j^Berger in the interior of dwells. Their distances to the interval boundaries tend to infinity. Under rescaling by exp(-2t_j^round) or exp(-2t_j^Berger), on each fixed compact logarithmic annulus the coefficients converge in every derivative to the constant links gamma(a_*,1,J_0) and gamma(a_*,q_*,J_0), respectively. This follows from the explicit derivatives and local finiteness, not just C0 closeness. The resulting smooth annular limits complete to metric cones. To include the vertex in pointed convergence, use the radial distance and a fixed global upper bound on link diameters: a ball of radius epsilon about the vertex has diameter at most 2epsilon in both spaces, uniformly before passing to the limit. This supplies pointed cone limits including their tips.

The q_*>1 Berger link is nonround: its Hopf-horizontal and horizontal sectional curvatures differ (the source link formula gives q versus 4-3q, up to the common scale, on the appropriate two-plane types). A round sphere has constant sectional curvature. Thus the two compact links are nonisometric, and their vertexed cones are nonisometric. Their vertices are intrinsically distinguished cone tips; equivalently a pointed cone isometry identifies its unit distance spheres. This proves the asserted nonunique tangent cones.

## 8. A signed estimate for the whole diagonal leg

Fix l>=1; all constants in this and the remaining growth sections may depend on l but not on the later active levels or history. The leg uses J_0, so it is diagonal in the frozen dwell basis. Let d_i=d_(l,i)>0, lambda_i^*=d_i(d_i+m-1). On a dwell q=q_*, and (3.2) gives exactly

    lambda_i(t)=lambda_i^* exp[-2A(1+t)^(-delta)],
    p(t)=m-1-m mu(1+t)^(-1-delta).                             (8.1)

Let rho_i(t)>0 solve rho_i^2+p rho_i=lambda_i(t). Taylor expansion of this smooth positive root on a compact positive-coefficient range yields

    rho_i(t)=d_i - (2A lambda_i^*/(2d_i+m-1))(1+t)^(-delta)
                    +O_l((1+t)^(-2delta))
                    +O_l((1+t)^(-1-delta)),                   (8.2)
    |rho_i'(t)|<=C_l(1+t)^(-1-delta).

In particular there are c_l,C_l>0 for which, eventually and for every i,

    d_i-C_l(1+t)^(-delta) <= rho_i(t)
                 <= d_i-c_l(1+t)^(-delta).                    (8.3)

The lower-order error in (8.2) cannot reverse the sign, because the displayed first-order coefficient is strictly positive for every coordinate of this FIXED finite block.

Let y be the positive reference scalar solution defining (D_lj)_ii, with y=1,y'=theta_l at the beginning of the up-ramp. Positivity and scalar Riccati barriers bound w=y'/y above and below by positive constants depending only on l over the whole leg. On the dwell the exact difference z=w-rho_i satisfies

    z'=-(p+w+rho_i)z-rho_i'.                                  (8.4)

The damping coefficient has a fixed positive lower bound. Consequently

    int_dwell |w-rho_i| dt <= C_l[1+L_j t_j^(-1-delta)].        (8.5)

The initial value z at the dwell entrance is bounded, not presumed small. Its integral is bounded because it decays; this is why the ramps do not create an L_j-sized error. On the two ramps and rest, w is bounded, so their total contribution to log y is O_l(T_j). Since t is comparable to j^8 throughout the dwell, (8.3)--(8.5) imply

    log(D_lj)_ii <= L_j d_i-c_l j^(13/2)+C_l(T_j+1),
    log(D_lj)_ii >= L_j d_i-C_l[j^(13/2)+T_j+1].                (8.6)

These estimates are for the ENTIRE leg starting with slope theta_l, including both ramps and rest. The error L_j t_j^(-1-delta) is smaller than a constant for large j. The constants are independent of the pulse word. The growing scalar factor from that word is tracked separately by (6.1).

## 9. Cycling, every-radius endpoint bounds and exact exponents

Fix l>=2 and its activation index j_l. At t_(j_l) let W_(l,C) be the span of the basis vectors with indices in C. Use the invertible center-regular fundamental matrix from section 4 to pull W_(l,C) back to Euclidean-core initial data. Call the resulting space of global harmonic functions E_(l,C). It has dimension |C| and is fixed ONCE. No re-selection of earlier functions occurs at later activations.

For all subsequent endpoints, its value transfer is the product of the monomial matrices s_lj D_lj Pi_l. This product preserves each coordinate cycle. Each starting coordinate follows its exact cyclic itinerary; there is no leakage into another cycle, no commutation approximation, and no accumulation of small off-cycle errors. Within a cycle the resulting vectors stay mutually orthogonal up to their positive diagonal lengths and signs.

For a periodic sequence a_j of period h with mean mu, summation by parts gives

    sum_(j=j_l)^J j^7 a_j = mu sum_(j=j_l)^J j^7 +O_l(J^7).     (9.1)

For completeness, the partial sums of a_j-mu are bounded by a constant depending on its fixed period and amplitudes. Abel summation bounds the left difference by that constant times J^7+sum| (j+1)^7-j^7|=O(J^7). Apply this to each cyclic itinerary with a_j=d_i. The finite starting index changes only constants.

The cumulative positive error from (6.1) is O(J^(57/8)); the cumulative ramp/rest error in (8.6) is O_l(J^7). The negative term in (8.6) sums to at least c_l J^(15/2). Since

    15/2=60/8 > 57/8 > 7,

it absorbs all those errors for sufficiently large J. Also t_(J+1)=sum_(j<=J)L_j+O(J^7), so replacement of sum L_j by time has only the same lower-order cost. Taking the largest or smallest length of the monomial columns gives constants c_l,C_l>0 such that any vector in this cycle obeys, at endpoints and after absorbing its fixed initial norm,

    ||Y(t_(J+1))|| <= C_Y exp[mu_C t_(J+1)-c_l J^(15/2)],
    ||Y(t_(J+1))|| >= c_Y exp[mu_C t_(J+1)-C_l J^(15/2)]       (9.2)

when Y is nonzero. The lower estimate follows from the lower half of (8.6), the absolute bound for log s, and the same weighted-cycle estimate. The constants c_Y are positive because the chosen initial vector is nonzero and the value maps are invertible.

For any t in [t_j,t_(j+1)], (4.5) changes log ||Y|| by at most C_l(t_(j+1)-t_j)=O_l(j^7). Changing mu_C t_j to mu_C t has the same cost. Since j^7=o(j^(15/2)), (9.2) extends to EVERY sufficiently large t, and t is comparable to j^8. Thus

    c_Y exp[mu_C t-C_l t^(15/16)]
       <= ||Y(t)|| <= C_Y exp[mu_C t-c_l t^(15/16)].             (9.3)

All norms on V_l are equivalent. More explicitly, round L2 norm is exactly the coefficient Euclidean norm, it is bounded by sqrt(Vol S^m) times the angular supremum, and the supremum is at most sqrt(N_l/Vol S^m) times that norm by the addition formula (or a finite-basis bound). These constants do not depend on t. Since geodesic radius is r=e^t, (9.3) proves (S4)--(S5), with a smaller c_l if necessary. Boundedness on the remaining compact region supplies the global pointwise O(r^mu_C) endpoint.

For l=1 every equation is scalar, all d_i=d_1 and Pi_1=I. Sections 5--8 and the preceding sums apply without (9.1), since the itinerary is constant. Define E_1 to be its entire regular solution space. This proves the same claims with dimension m+1. No special treatment of a degenerate exceptional eigenvalue is being hidden in the Lie-control argument.

For a sum of several cycles in the same V_l, their endpoint coordinate supports are disjoint, so the squared L2 norm is the sum of their squared norms. Its endpoint logarithmic exponent is the largest present mu_C. Applying (4.5) on incomplete periods proves the same limit at every radius. Across different l, round L2 orthogonality gives the same conclusion, with upper bounds from the finitely many summands. A constant does not change a positive exponent. Thus there is no cancellation loophole at a shared eigenvalue or shared cycle mean.

## 10. The entire infinite spectral tail and exact filtration

Let u be ANY smooth global real harmonic function with pointwise growth at most d>=0. At each radius project u onto V_l using the fixed round measure and orthonormal basis. Because the volume factor a(t)^m is spatially constant and (1.1) is self-adjoint and preserves each V_l, differentiation and integration on each compact sphere show that its coefficient Y_l solves (4.1). This is a statement about each individual projection, so no unjustified exchange of an infinite differential series is needed.

On the Euclidean core, regularity of u implies Y_l=r^l v_l for l>=1; the singular radial solution is excluded by smoothness at o. For l=0 it is constant. Therefore every nonzero projection lies on the center-regular graph already constructed. At any fixed positive radius r_0, the growth bound gives

    ||Y_l(t)|| <= sqrt(Vol S^m) A_u (1+e^t)^d.                  (10.1)

On the other hand (4.5) gives, if Y_l(t_0) is nonzero,

    ||Y_l(t)|| >= ||Y_l(t_0)|| exp[c l(t-t_0)].                 (10.2)

If c l>d these are incompatible as t tends to infinity, regardless of how small the fixed nonzero coefficient is. Hence Y_l is identically zero for every l>d/c. Completeness of the round spherical harmonics in L2 now identifies u at each sphere with the remaining FINITE sum. No finite truncation has been substituted for the infinite spectral tail.

Each remaining V_l is the direct sum of its cycle spaces, by the invertible initial-value map. Section 9 proves that a nonzero finite sum has logarithmic exponent the maximum of its present cycle means. Growth <=d therefore forces all present means <=d. Conversely every cycle with mean <=d satisfies the exact endpoint upper bound and hence the pointwise d bound. Constants are included. This proves the equality (S3), not only its dimension lower bound.

To see directly that its right side is finite, (4.4) and section 9 imply mu_C>=c l, and similarly d_1>=c. Alternatively this follows from (S2) and the compact angular bounds. Independence follows from initial-value invertibility within each V_l and orthogonality between distinct l; it is unaffected by any later stage.

For another fixed basepoint p, the inequalities dist(o,x)<=dist(p,x)+dist(o,p) and its reverse show equivalence of the pointwise polynomial-growth bounds for every d>=0. All dimensions are real; no complex multiplicity has been counted twice. For reference the Euclidean comparison under this convention is h_k(R^n)=binom(n+k-1,n-1)+binom(n+k-2,n-1) for integer k>=0, and h_d=h_floor(d) there. The construction asserts a full real filtration, not a changed normalization of this comparison.

## 11. Compatibility and distinct attainable filtrations

Take m=7, q_*=101/100, a_*^2=9/10. On 1<=q<=101/100 the minimum in (S1) is 1-(q-1)/3, and

    q^(1/7)[1-(q-1)/3] >= 299/300 > 9/10.

Thus the full link constraint holds with strict margin; the parameter regime is nonempty.

For V_2 on S^7, B_2=16. The real charge-square-four subspace has dimension 20 (the complex holomorphic quadratics of dimension 10 paired with their conjugates); the charge-zero component has real dimension 15 (trace-free Hermitian quadratic forms). Their roots satisfy d_low<d_high, since q_*^(-1)-1<0. Leaving all coordinates singleton yields only these two V_2 jumps. Pairing one low and one high vector in a two-cycle yields a two-dimensional jump at

    mu=(d_low+d_high)/2,

strictly between the former values, while reducing the two former jump multiplicities by one each. Leave every other coordinate and every other degree singleton in both prescriptions.

No other degree has a root in that interval. For l=1 the angular eigenvalue is a_*^(-2)q_*^(1/7)(6+q_*^(-1)), smaller than either V_2 eigenvalue. For l>=3,

    B_l+(q_*^(-1)-1)nu >= l(l+6)-l^2/101,

which increases with l and is greater than 26 at l=3. The V_2 bracket is at most 16. The positive-root map is strictly increasing. Thus other singleton degrees cannot supply the newly inserted jump. The two metrics furnished by the theorem have distinct full filtrations. This verifies actual nontrivial prescription freedom under all joint geometric hypotheses; it does not assert freely chosen arbitrary real jump locations.

## 12. Scope reached

The construction proves the entire unchanged S236 statement as an author proof. It uses one metric, exact center-regular value transfers after every block's activation, a strictly negative accumulated correction of order (log r)^(15/16), and a global projection argument for the full spectral tail. It does not use a diagonal limit of separate metrics, a logarithmically weakened endpoint, a conjectural three-dimensional infinite-band extension, or a uniform inverse theorem in unbounded degree. The submission awaits the independent correctness and substantial-contribution reviews required by the campaign; no mathematical grade or acceptance is assigned here.
