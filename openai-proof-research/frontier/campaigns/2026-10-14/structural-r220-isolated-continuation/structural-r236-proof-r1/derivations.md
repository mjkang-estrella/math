# Independent working derivations — S236 correctness review

These calculations concern the submitted unchanged proof, relative to stipulated source truth. They are not a new theorem, a contribution assessment, or a parent verdict. The initial derivations followed full operative Source A/B reading. The scoped primary/history comparisons were completed later, before the final review and seal; see READING-LIMITS.md.

## Scalar baseline and current-parameter derivative

Let p0=m-1, theta^2+p0 theta=a_*^{-2} B_l, kappa_l=a_*^{-2}/(p0+2theta). For a fixed finite word set

X(tau,h)=kappa_l sum_n c_n(h) beta_n(tau) (B_l I/m+D_{J_n}^2).

All sums are finite and bump supports are disjoint with round open gaps. This is exactly Source A's R_l. It is trace free: the round addition tensor sum_a de_a tensor de_a equals B_l N_l/(m Vol S^m) times g_0. Integrating its evaluation on the unit Hopf field gives sum_a ||D_J e_a||_2^2=B_l N_l/m, hence tr D_J^2=-B_l N_l/m. Thus the scalar-looking term in X exactly cancels that trace, as the author states. A's algebra supplies arbitrary product-SL targets and nonsingular parameter slices for these positive degree-dependent factors; different degrees are not independently rescaled by hand.

Choose the exact source baseline v(t_j)=theta and v'=a^{-2}B_l-pv-v^2. On the modified tail, v-theta=O_l(j^{-1/2}) by the scalar damped difference equation, uniformly on the control interval. The expansion is

A_l=a^{-2}B_l I+(p0+2theta)X/T+E_A,
||E_A||_{C^1_h} <= C_N(j^{-1/2}/T+T^{-2}).

For Q=vI+X/T the exact Riccati residual is

rho=A_l-pQ-Q^2-Q' = E_A -[(p-p0)+2(v-theta)]X/T -(X^2+X_tau)/T^2.

Thus ||rho||_{C^1_h}<=C_N eta/T for eta=j^{-1/2}+T^{-1}. For E=P-Q, without commuting any matrices,

E'=rho-(pI+P)E-EQ.

Positive symmetric P,Q and p give a fixed finite-level damping rate. E(t_j)=P(t_j)-theta I=O_l(eta); its current-parameter derivative is zero since the incoming past is held fixed and X vanishes near the endpoint. Hence sup ||E||=O(C_N eta), integral ||E||=O(C_N eta). In particular T eta=j^{11/2}+1 is never small or used as small.

With Q_h=X_h/T, exact differentiation gives

E_h'=rho_h-(pI+P)E_h-E_h P-Q_h E-E Q_h.

The forcing has integral O(C_N eta) and pointwise size O(C_N eta/T). Damping yields integral ||E_h||=O(C_N eta), sup ||E_h||=O(C_N eta/T). These identities are the cited source identities with the new eta substituted into explicit bounds; no extra solvability hypothesis is needed. The normalized value map e^{-int v}B solves F'=(X/T+E)F. Integrated bounds on X/T and its parameter derivative, followed by the ordinary matrix integral inequality, give C1 closeness to the ideal finite word. The possibly large integral of v-theta is retained exactly.

## Whole-leg removal and scalar multiplier

On the diagonal leg the scalar solution maps U,V are positive by (e^{int p}y')'=e^{int p}lambda y and positive Cauchy data. Put D=U+theta V, K=D^{-1}V. Then 0<K<=theta^{-1} I. If B is the pulse value map and P_e the outgoing regular slope,

T=(U+V P_e)B,   D^{-1}T=[I+K(P_e-theta I)]B.

There is no D^{-1} error D conjugation. K is independent of the current parameter and every earlier word. Its derivative in the current parameter is zero. All determinants are positive: det B and det T are exponentials of trace integrals of P, and D is positive diagonal. Smooth determinant normalization near the fixed compact ideal-word image gives a C1-small perturbation of the ideal map. Source A's contraction-in-a-chart proof therefore supplies exact normalized target Pi uniformly over every incoming graph allowed by the barriers/reset, even if that history used other finite words.

At the selected parameter, T=s D Pi exactly with s=det(D^{-1}T)^{1/N_l}>0. Since e^{-int v}D^{-1}T is in a fixed compact positive-determinant neighborhood, log s=int v+O_N(1)=O_N(T). The leg's condition number never occurs. For l=1 the whole equation is scalar. Even without a small exit error, (U+VP_e)/(U+Vtheta) lies between 1 and P_e/theta; the global positive slope barriers bound this ratio above and away from zero. Thus its logarithm is bounded and log s_1=O(T), uniformly in word level after the global geometric range is imposed.

## Barriers, reset, and the infinite complement

On the compact positive a,q range, kappa l(l+m-1)I<=A_l<=K l(l+m-1)I for every l>=1, since 0<=-D_J^2<=l^2 I. Also p in [3m/4-1,m-1]. At a contact eigenvector for clI or ClI, P^2 acts by c^2 l^2 or C^2 l^2 without any commutation assumption on A_l. The displayed c choices in the proof give a strictly inward lower derivative. C^2>Km bounds the upper derivative because l(l+m-1)<=m l^2 for l>=1. Core data P=lI are inside the barriers. Symmetric Riccati continuation, followed by the invertible fundamental equation Y'=PY, proves global regularity and c l<=P<=C l independent of all word complexity.

On each final round rest, E0=P-theta I obeys

E0'=f I-(pI+P)E0-E0 theta,
f=a^{-2}B_l-p theta-theta^2=O_l(j^{-1/2}).

The initial E0 is bounded independently of earlier words and the rest is (j-1)^6 long, so E0(t_j)=O_l(j^{-1/2}). The first active period also has an entirely round preceding interval; taking the activation threshold after 2B and far enough in the absolute schedule supplies the same estimate. This includes degrees not previously activated.

For any vector, d||Y||^2/dt=2<Y,PY> gives the two-sided exponential slope bounds. For any global harmonic u of growth d, its individual round projections solve this exact ODE; regularity in the Euclidean core excludes singular powers. A nonzero coefficient at one fixed radius would violate growth d whenever c l>d, irrespective of its size. Each excluded coefficient is identically zero. Round L2 completeness then reconstructs u from finitely many degrees, pointwise by smoothness. No infinite differentiated series or lower bound uniform over coefficients is needed.

## Signed root drift and summation

Set x=(1+t)^(-delta), delta=1/16. On the dwell lambda=lambda_* e^{-2A x}, p=p0-m mu(1+t)^(-1-delta). The positive-root derivatives are rho_lambda=1/(2rho+p)>0 and rho_p=-rho/(2rho+p). Therefore

rho=d-[2A lambda_* /(2d+p0)]x +O_l(x^2)+O_l((1+t)^(-1-delta)).

The contribution from decreasing p is positive, but is strictly lower order. The leading negative coefficient is positive for every coordinate in each fixed degree. All coordinates in that degree have a common positive minimum. Differentiating the implicit equation gives rho'=(lambda'-p' rho)/(2rho+p)=O_l((1+t)^(-1-delta)).

For the scalar reference solution with entrance slope theta, its slope w has positive scalar barriers throughout the ramps, dwell, and rest. z=w-rho obeys z'=-(p+w+rho)z-rho'. Its entrance mismatch is bounded, not necessarily small; damping bounds its integrated contribution by O_l(1+L t_j^{-1-delta}). Here L t_j^{-1-delta}=O(j^{-3/2}), and L t_j^{-delta} is comparable to j^{13/2}. All three non-dwell pieces together contribute O_l(T). These give both halves of (8.6) exactly for the entire reference leg.

For any finite cycle length h, partial sums of its mean-zero dwell roots are bounded. Abel summation against j^7 yields O_l(J^7) discrepancy. The cumulative signed deficit is comparable to sum j^{13/2}, hence J^{15/2}; sum |log s|<=sum j^{49/8}=O(J^{57/8}); cumulative ramp/rest error is O_l(J^7). All positive errors are strictly lower order. Since t~J^8, the signed deficit is t^{15/16}. A partial period costs O_l(J^7) by the global slope bound, so both upper and lower estimates hold at every radius, not only endpoints. Positive c_l survives by choosing a later threshold, with no lower bound uniform in l.

At endpoints, products are monomial: distinct starting coordinates have disjoint images. Minimum-column and maximum-column estimates apply to every nonzero initial vector. Different cycles have disjoint endpoint supports, and different degrees are round-L2 orthogonal. This rules out cancellation even at shared means. The fixed-degree addition formula supplies t-independent L2/sup comparison. The same reasoning treats l=1 with constant itinerary, and l=0 has only the regular constant.

## Geometry checks

S= r^{-1}(I+B), B=bI+H, H=(q'/(2q))(P_J-I/m) gives exactly

r^2 Ric_rr=-m(b+b'+b^2)-tr H^2,
r^2 Ric_T^#=Ric_gamma^#-B'-(m(1+b)-1)(I+B).

The Hopf vector is Killing and constant length for each Berger metric. Its unit normalization has divergence zero and geodesic flow, so div P_J=0 and div H=0. The shape trace is spatially constant; Codazzi gives zero mixed block. Changes of the label J only in open q=1 gaps create no metric derivative. This handles both disconnected orientation classes.

With the late cutoff the radial scale has b>=-1/4 and b+b'+b^2<=0, a=1 on the core and a down to a_*. Before active periods, the round tangential coefficient is bounded below by (m-1)(a^{-2}-1-2b-b^2)>=0. On active periods the strict S1 link margin persists for a<=a_bar and q in [1-epsilon0,q_*]. The radial buffer is j^{-17/2}; ramps cost j^{-12}, weak pulses at most M_N^2 j^{-24}<=j^{-95/4}. Tangential errors go to zero. Full tensor positivity follows because mixed terms vanish.

Closed radial balls are compact and radial distance equals r. The exact density r^m a(log r)^m gives AVR a_*^m. Centers of round rests and Berger dwells have growing distances to interval boundaries, so each bounded logarithmic annulus converges in all orders to the required fixed cone. Inner balls have ambient diameter <=2epsilon, which includes the tips in pointed convergence. Berger Ricci eigenvalues differ by the positive multiple (m+1)(q_*-1); round links are Einstein. Thus nonisometry also follows directly from the read source Ricci formulas, without relying on an unquoted sectional-curvature identity.

## Thresholds and chronology

Each level has finitely many word, derivative, inverse, geometry and scalar constants. A finite J_N can satisfy all its eventual conditions and M_N<=j^{1/8} for all j>=J_N. Strictly increasing J_N ensure every degree activates. The earlier level continues through the interval before J_(N+1), so there are no waiting gaps in old exact targets. Incoming graphs depend only on already constructed periods. No convergence of h_j is needed: the metric is defined on disjoint finite periods with flat joins and no finite-time accumulation. For each derivative order a, eventually N+2>=a and the scaled metric-profile bounds make all required time derivatives small. Spatial Hopf derivatives have uniform bounds because J lies in the compact orthogonal-complex-structure family. Arbitrarily large finite cycle and word constants delay activation; they do not create a degree-uniform inverse requirement.
