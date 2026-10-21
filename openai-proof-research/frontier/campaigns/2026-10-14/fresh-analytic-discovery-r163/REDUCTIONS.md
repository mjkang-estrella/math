# Integrated Vlasov–Maxwell notebook

This is PREFREEZE research, not a frozen theorem, author-proof nominee, or independently reviewed finding. The exact primary and source identities, labels, versions and reading extents are private. S denotes the stipulated pinned SOURCE362 proof; L, R, N and D denote the primary continuation/cone, radiation, nonresonant-smoothing and transport-commutator papers mapped in private/COMPARISON.md. All notation below uses S's one-species normalization, with no background charge. This notebook develops the strongest compatible reduction rather than asserting significance from a change of hypotheses.

Write q(v)=(1+|v|²)^(1/2), u(v)=v/q(v), F=(E,B), K_F=E+u×B, rho_f=integral f dv and j_f=integral u f dv. The system is

    partial_t f + u·grad_x f + K_F·grad_v f = 0,
    partial_t E - curl B = -j_f,    partial_t B + curl E = 0,
    div E = rho_f,                 div B = 0.

## 1. Exact feasibility scope and the important distinction

Consider the class

    0 <= f0 in L1(R6) intersection Linfinity(R6),
    f0(x,v)=0 for |v|>R0, with some finite R0,
    E0,B0 in H1(R3),   div E0=rho_f0,   div B0=0.             (1)

There is no compact spatial-support hypothesis in (1). The particle mass is finite. Because initial momentum is bounded, initial particle energy is finite too. Fields are not required to have pointwise bounds. Every smooth approximation considered below satisfies the EXACT coupled equations and both constraints. No artificial force regularization is being substituted for them.

The construction below gives a uniform finite-time momentum bound for these smooth approximations, a global distributional limit with bounded momentum on every finite slab, its H1 spacetime field regularity, its renormalization and energy identities, and a comparison inequality against a smooth reference. These are compatibility calculations toward evaluating a possible result. They do not assert uniqueness between two arbitrary rough solutions. In particular they do not assert uniqueness among all finite-energy weak solutions without a propagated momentum bound.

The complete original tail notebook already attempted removal of compact initial momentum, including polynomial initial-label growth. That scope is not retried or restricted here. The distinction in (1) is low regularity at a FIXED finite initial momentum radius.

## 2. Radiation on arbitrary eligible time sets

Let X:[0,T]->R3 be C1 and strictly timelike: |X'|<1. For t>0 put

    Y(t,n)=X(t)+tn,   d_+(t,n)=1+n·X'(t),   n in S2.

The map is injective away from its t=0 tip. For t2>t1,

    |X(t2)-X(t1)| < t2-t1,

so the closed balls with centers X(t) and radii t are strictly nested. A fixed y can lie on at most one of their boundaries. Its Jacobian is t² d_+ in dt dn measure. Its image need not be all of R3; bounding its integrals by whole-space integrals is legitimate. Also

    |Y(t,n)-X(0)| <= 2t.                                  (2)

For a vector W solving the free wave equation with data (W0,W1), Kirchhoff gives

    W(t,X(t)) = (4pi)^(-1) integral_S2
        [W0(Y)+t n·grad W0(Y)+t W1(Y)] dn.                 (3)

For measurable A subset [0,T], Cauchy–Schwarz and the Jacobian imply

    integral_A integral_S2 t |G(Y)| dn dt
       <= ||G||2 [integral_A integral_S2 d_+^(-1) dn dt]^(1/2). (4)

For the undifferentiated term in (3), insert t and 1/t in (4). By (2) and the translated Hardy inequality,

    integral_image |W0(y)|²/t(y)² dy
       <= 4 integral_R3 |W0(y)|²/|y-X(0)|² dy
       <= 16 ||grad W0||2².                               (5)

One elementary proof of the last inequality is to integrate div((y-x0)/|y-x0|²)=|y-x0|^(-2) against |W0|², remove a small spherical cutoff, and apply Cauchy–Schwarz. Smooth compact functions give H <=2 sqrt(H)||grad W0||2; density gives the H1 assertion. The estimate is uniform in x0.

If b=|X'|, direct spherical integration gives

    integral_S2 d_+^(-1) dn
      = (2pi/b) log((1+b)/(1-b)),                           (6)

with continuous value 4pi at b=0. If q_X=(1-b²)^(-1/2)<=8w on A, (6) is at most C log(2+w). For A contained in an interval of length I, (3)–(6) yield

    integral_A |W(t,X(t))|dt
      <= C sqrt(I log(2+w)) (||grad W0||2+||W1||2).         (7)

This is an absolute-value bound. It controls vector impulses and bounded time-dependent projections as well. It is valid if X leaves the w-band outside A. The change of variables uses the whole timelike curve but the angular integral uses only A. No acceleration norm occurs.

Apply (7) to S's homogeneous electric and magnetic waves, whose initial velocities are curl B0 and -curl E0. They need not form a vacuum Maxwell pair; no such assertion is used. Consequently

    integral_A (|E_fr|+|B_fr|)(t,X(t))dt
        <= C ||F0||H1 sqrt(I log(2+w)).                    (8)

S's initial-particle boundary contribution is bounded pointwise by C(R0,||f0||infinity) t. Its signed initial-cone boundary has the same dependence after its initial-label change of variables. Both therefore cost C_T I.

This calculation refines the presentation of primary R's radiation estimate by using Hardy for the zeroth-order term and retaining the logarithm already present in primary L's moving-cone proof. The underlying primary operations are compatible and actually read. The better-looking displayed exponent is not itself evidence of substantial contribution.

## 3. Uniform substitution through the entire signed proof

Fix a finite T. Work first with any smooth admissible datum whose initial momentum radius, f0 supremum, total particle mass, total energy and field H1 norm have common upper bounds. The initial spatial radius and all higher derivatives may vary.

In S, P is dyadic and at least 1024 times the largest current supported energy; w is a dyadic receiver energy. Put L=log(2+P) and S_w=P²L/w. On eligible measurable times in an interval of upper length I<=(w/P)², (8) satisfies

    ||F0||H1 sqrt(I log(2+w)) + C_T I <= C P sqrt(I),       (9)

since 1<=w<=P and I<=1. The constant C depends only on the common initial bounds and T.

Here is the downstream compatibility, including the places where a formally plausible substitution could fail.

(a) The retarded representation remains an identity for each smooth approximate solution. Its phase-label Jacobian, total energy, cone energy and phase-volume preservation use no derivative bound of f0 in their final estimates. Bounds used solely to remove the cone-tip cutoff are allowed to depend on that one smooth compact interval.

(b) The occupation proof uses total particle mass/energy and f0 supremum. Its stable-cell length still comes from the SAME common-P signed bootstrap. We do not change P, remove high-source bins, or substitute a label-dependent cap. The joint energy budgets and angular partitions remain exactly those of S.

(c) S's baseline direct proof uses the data force only through its integral over the eligible set. Replace its final pointwise-data estimate by (9). All near/far balances, deficit estimates, radius sums and angular sums remain available. The result is still

    direct baseline <= C[P sqrt(I)+(M+sqrt(A)) I S_w],
    integral |K| <= C sqrt(w)[P sqrt(I)+(M+sqrt(A)) I S_w].  (10)

(d) In S's first use of signed cancellation, the direction first-exit intervals have disjoint interiors. Their ramp weights and bounded projections are summed BEFORE using (9). Their union has measure at most I, so there is ONE sqrt(I) cost. Summing sqrt(length) separately over the intervals would be an unjustified loss. The moving projection contributes a coefficient multiplying the full |K|, already covered by (10). The initial-cone boundary remains C_T I. Therefore the direction-count estimate and its improved-occupation window are unchanged.

(e) The second signed selection uses the same three occupation bounds and the same summable weight. Its selected receiver coefficient is at most C/sqrt(w). Multiplying by the full absolute-force bound in (10) cancels sqrt(w), exactly as in S. The time-weight, spatial-transition and source-cutoff errors retain the original parameter dependence. Radiation is not inserted into the source-acceleration identity as an independently transported species.

(f) Endpoint recovery uses only the signed bootstrap. It gives

    |Delta V| <= (C_eta+2M sqrt(eta)) P sqrt(I)
                  + [C_eta(M+sqrt(A))+2A eta] I S_w.       (11)

Choose eta, then M, then A, then the large-P threshold as in S. All choices can be made uniformly from the common bounds. For each fixed smooth solution, the compact-slab force bound initializes and propagates the bootstrap by continuity. It may be large and depend on high derivatives, but it does NOT enter the choices in (11). This is why the eventual cap is uniform despite approximation derivatives diverging.

For intervals longer than (w/P)², the band restriction gives |Delta V|<=16w, whereas P sqrt(I)>w. Choosing M>=16 handles those intervals directly. Thus no concatenation loss is needed to recover the full interval statement.

Thus the full source increment inequality survives with constants M,A,P_* depending only on T and the common initial quantities just stated. The proof does not assert uniform estimates for arbitrary momenta in a rough weak solution before constructing that solution.

## 4. Quantified finite-horizon momentum cap

Let Q(t)=max_(initial supported labels) q(V(t)). Choose a common integer n0 so that 2^n0 exceeds the initial cap and the relevant source threshold. If Q first reaches 2^n at t_n, select a maximizing label and its last earlier time s_n with q=2^(n-1). Then s_n>=t_(n-1) and the label stays in that energy band on [s_n,t_n]. Put Delta_n=t_n-s_n.

With P=1024*2^n, w=2^n and q 1-Lipschitz, the uniform increment inequality gives

    1/2 <= 1024 M sqrt(Delta_n)
                 + 1024² A Delta_n log(2+1024*2^n).        (12)

At least one term is >=1/4. Hence, for common positive c and c0,

    t_n-t_(n-1) >= Delta_n >= c/(n+c0).                    (13)

If level 2^N is reached by T, sum (13) to obtain

    T >= c log((N+c0+1)/(n0+c0+1)).                        (14)

There is therefore a common finite number Q_T controlling all supported momenta up to T. The common bound excludes arbitrarily high levels before T, rather than merely excluding finite-time blow-up for each approximation separately. Constants c,n0 are allowed to depend on the prescribed T; (14) is not advertised as a horizon-independent growth rate.

## 5. Constraint-compatible approximation of (1)

Choose smooth spatial cutoffs 0<=chi_R<=1 tending to one, and write

    f0,R=chi_R f0,   sigma_R=rho_f0-rho_f0,R.

The density rho_f0 belongs to L1 intersection Linfinity, hence to L2. Therefore sigma_R tends to zero in L1 and L2, and by interpolation in L^(6/5). The Coulomb operator

    C[sigma]=-grad(-Delta)^(-1)sigma

has div C[sigma]=sigma and obeys

    ||C[sigma]||2 <= C ||sigma||_(6/5),
    ||grad C[sigma]||2 <= C ||sigma||2.                    (15)

The first bound is Sobolev duality: solve -Delta phi=sigma in the homogeneous H1 space, test by phi and use ||phi||6<=C||grad phi||2. The second is the bounded Fourier multiplier for the Hessian of (-Delta)^(-1). These arguments include nonzero total charge.

Set E0,R=E0-C[sigma_R], B0,R=B0. Then the constraints match f0,R and the fields converge to F0 in H1. Smooth f0,R by compact unit-mass nonnegative convolutions in x and v. Smooth the fields with the SAME spatial kernel. Since integrating the velocity kernel gives one,

    div(E0,R * eta_x) = integral (f0,R * eta_x * eta_v) dv. (16)

The magnetic constraint is preserved too. Choose radii of velocity mollification <=1 and tending to zero. Every approximate datum has particle momentum <=R0+1, phase-space density supremum <=||f0||infinity, mass <=||f0||1, bounded energy and uniformly bounded H1 fields. Field convolutions have bounded derivatives of every order by L2–L2 convolution bounds, so they lie in S's admissible class. Particle data are smooth and compactly supported in phase space. We may choose a diagonal approximation with f0,n->f0 in L1 and L2 and F0,n->F0 in H1.

The source produces exact global classical solutions (f_n,F_n). Sections 2–4 give Q_T independent of n. Spatial support radii need not be uniform, but finite particle speed gives the uniform tail estimate

    integral_(|x|>R+T) f_n(t,x,v) dx dv
       <= integral_(|x|>R) f0,n(x,v) dx dv.                (17)

This tends to zero uniformly in n after discarding finitely many initial n and then letting R grow. The finitely many remaining approximations have the same tightness. This is sufficient for global mass bookkeeping.

## 6. Nonlinear compactness using the actual nonresonant operation

Energy and bounded momentum give, on [0,T],

    ||f_n||_(L2_t,x,v)² <= T ||f0||infinity ||f0||1,
    ||F_n||_(L2_t,x)² <= 2T H_bound,
    ||K_(F_n) f_n||_(L2_t,x,v)
        <= C(Q_T) ||f0||infinity ||F_n||_(L2_t,x).         (18)

These are the precise hypotheses for the compact-momentum instance of primary N. It is useful to spell out its proof because it avoids asking for derivatives of f_n or F_n in the right-hand side.

Let U_n(t,x,v) be the zero-data wave solution of Box U_n=f_n. Put g_n=-K_(F_n)f_n, so T_v^+ f_n=div_v g_n, with T_v^+=partial_t+u(v)·grad_x. Let h_n solve Box h_n=g_n with zero data, and let h_n^I solve the homogeneous wave equation with initial value zero and initial velocity f0,n. Then

    T_v^+ U_n = div_v h_n + h_n^I.                        (19)

Choose chi(v) smooth compactly supported and equal to one on |v|<=Q_T, enlarged slightly, and choose lambda strictly between max_supp(chi)|u(v)|² and 1. With T_v^-=partial_t-u(v)·grad_x, define

    Q_lambda,v = lambda Box - T_v^- T_v^+.

Its Fourier symbol is

    (1-lambda) tau² + lambda |xi|² - (u(v)·xi)²,

bounded below by c(Q_T)(tau²+|xi|²). At frequencies of norm at least one, its reciprocal and all finitely many required v derivatives have the corresponding order-minus-two bounds. At low frequency use the L2 wave-energy bound for U_n; equivalently invert 1+Q_lambda,v and retain U_n as an additional L2 right-hand term. Applying this elliptic operator to U_n, using (19), and moving v derivatives by integration by parts onto the cutoff and inverse symbol shows

    integral chi(v) U_n(t,x,v) dv is bounded in H2_loc(t,x), (20)

uniformly in n. The same holds with chi u_i in place of chi. Wave energy bounds on U_n,h_n,h_n^I use only the L2 quantities in (18) and ||f0,n||2. Commutators with a time cutoff are first order and hence controlled by those wave energy bounds. No f_n derivative is used.

There is no hidden initial-time regularity assumption in this use. Extend f_n and g_n by zero to t<0, and use retarded U_n,h_n. Extend h_n^I by zero to t<0; it is continuous at zero with locally square-integrable first derivatives and solves Box h_n^I=delta_0 f0,n. The distributional identity (19) holds across zero. Thus the same cutoff-and-Fourier proof works in a time neighborhood of [0,T], with a harmless later cutoff. It supplies an H2 bound for the averages up to time zero. Since all L2 estimates are global in x, one can use a time cutoff alone and obtain the corresponding global spatial norm; local spatial cutoffs also suffice for compactness.

The fields are the homogeneous initial-data waves plus the first derivatives of the two averages in (20). The homogeneous waves have H1 spacetime bounds from F0,n in H1 and curl F0,n in L2. Therefore F_n is uniformly bounded in H1 on each compact spacetime box, including boxes meeting t=0. This is precisely the primary smoothing mechanism, not a new regularity assertion inferred from weak convergence alone.

By Rellich compactness and a diagonal extraction, F_n->F strongly in L2 on compact spacetime sets. Extract f_n weak-* in Linfinity and in the bounded L1/energy classes. Positivity, the Q_T momentum bound, and (17) persist. For any compact test function in phase space,

    integral (F_n-F) f_n test ->0,
    integral F (f_n-f) test ->0.                          (21)

The first follows from strong L2 fields and the uniform f_n bound on the finite v domain; the second follows by weak-* convergence against the fixed L1 test F times the test function. This passes the nonlinear Vlasov term. Maxwell's equations and Gauss constraints pass linearly. Initial terms pass because the approximations converge strongly to (1). We have a global distributional solution with bounded momentum on every finite slab. Extraction on increasing integer horizons gives ONE global solution, not unrelated solutions for different T.

## 7. Renormalization, initial traces, and exact energy

The limit has F in H1_loc of spacetime and f bounded with bounded momentum on each finite slab. Its phase vector field b=(u,K_F) lies in L1_t W1,1_loc(x,v), and div_(x,v)b=0. Primary D's commutator applies locally. In direct form,

    (b·grad f)*eta_eps - b·grad(f*eta_eps) ->0 in L1_loc.   (22)

The bound before taking the limit is C||f||infinity||grad b||L1 on a slightly enlarged compact set. Approximate b by smooth fields to get convergence; the divergence correction cancels the smooth limiting term. This is the actual primary regularization argument.

Consequently beta(f) solves the transport equation for C1 beta with beta(0)=0 and bounded derivative on the attained range. Initial traces are included by extending b=0, f=f0 for t<0. The initial weak formulation makes the extended equation distributionally valid across zero, and (22) gives the renormalized trace there. Smooth x cutoffs remove spatial boundaries because |u|<=1 and beta(f) is bounded by C f. Momentum cutoffs can be chosen outside Q_T, where f vanishes. Thus mass and every finite Lp norm are conserved, and f has the corresponding strong Lp time representative for finite p. This does not claim uniqueness of a nonlinear system merely from uniqueness of transport by a GIVEN b.

The finite momentum cap gives j_f in Linfinity_t L2_x: by Cauchy–Schwarz in v,

    ||j_f||2 <= |B_(Q_T)|^(1/2) ||f||2.                   (23)

The first-order Maxwell group and Duhamel formula therefore give F in C_t L2_x with the prescribed initial trace. Its energy identity is valid with current in L1_t L2_x. Testing Vlasov by q(v) times momentum and spatial cutoffs gives

    d/dt integral q f = integral E·j_f,
    d/dt (||E||2²+||B||2²)/2 = -integral E·j_f.            (24)

The product in (24) is integrable by (23); magnetic work is zero. Spatial cutoff errors vanish using finite total energy and |u|<=1. Because q is bounded on the propagated support and the initial trace is present, (24) recovers the exact initial particle energy, with no unidentified initial defect. Thus total energy is conserved for the constructed limit. A lower-semicontinuity inequality alone would not prove this equality.

## 8. Full finite-time comparison against a smooth source solution

Let (f_bar,F_bar) be any fixed smooth source solution on [0,T], and (f,F) a solution of the constructed class. Assume both momentum supports lie in |v|<=Q on this slab; Q may be the maximum of their finite caps. Put g=f-f_bar and deltaF=F-F_bar. Their difference equation, using b from the rough solution, is

    (partial_t+b·grad)g
       = -(deltaE+u×deltaB)·grad_v f_bar = h.              (25)

Let A_T= sup_(t,x) (integral |grad_v f_bar(t,x,v)|² dv)^(1/2), which is finite because the reference is smooth and compact in phase space. Then

    ||h||2 <= C A_T ||deltaF||2,
    ||delta j||2 <= |B_Q|^(1/2) ||g||2.                  (26)

The source version of (22), actually allowed in primary D, justifies the L2 energy identity for (25). Spatial cutoffs have only the bounded u flux; momentum boundary terms vanish outside the common cap. Combining transport and Maxwell energies gives

    D(t) <= D(0) + C(A_T+|B_Q|^(1/2)) integral_0^t D(s) ds,
    D(t)=||g(t)||2²+||deltaF(t)||2².                       (27)

Therefore

    sup_(t<=T) D(t) <= D(0) exp(C_T T).                   (28)

This is an actual nonlinear comparison: the different force in the rough transport operator was retained, and its mismatch appears in h. For equal smooth initial data it gives equality with the global source solution inside this bounded-momentum, renormalized class. It also gives finite-horizon L2 stability for rough perturbations of a smooth source solution, with constants depending on the common initial bounds and the reference, rather than on the perturbations' derivatives.

The source's own uniqueness-energy proof already contains the smooth version of (25)–(28); the primary commutator supplies its rough justification. Thus (28) is another paid compatible composition, not automatically a substantial stability discovery.

## 9. Precisely what the stronger uniqueness inference would require

There are two distinct stronger questions which the preceding calculations do not settle, and neither is frozen as a candidate.

First, take two arbitrary rough solutions with compact momentum. Using one as the reference in (25) would require a usable norm of grad_v f_bar. H1 regularity of the fields does not provide that derivative of f_bar. Linear transport uniqueness for a fixed b is insufficient because the two solutions generate different b. Primary R contains a published strong-weak uniqueness corollary with its own compatibility/class assumptions; this notebook does not silently widen that statement to a different class or replace the coupled estimate with a citation to linear uniqueness. No broad refutation of that published corollary is made.

Second, take a finite-energy weak solution with the SAME smooth initial data as S but with no propagated momentum cap. The signed proof uses source trajectories and smooth approximation identities; it has not been transferred to every such weak solution. Equation (23), needed for the simple Maxwell comparison, also loses its finite velocity-volume constant.

A concrete algebraic diagnostic explains why energy alone does not fill that gap. Let a_R=R^(-4/3), let phi be a nonnegative smooth bump in the unit spatial ball, and let psi be a nonnegative smooth momentum bump supported in 1<|v|<2 with v_1/|v|>3/4. Set

    f_R(x,v)=phi(x/a_R) psi(v/R),   R>=2.                 (29)

The sup norm is fixed, mass is comparable to R^(-1), and total particle energy is comparable to one. The first current component is bounded below by c R³ phi(x/a_R), so

    ||j_R||2 >= c R³ a_R^(3/2) = cR,
    ||f_R||2 is comparable to R^(-1/2).                   (30)

These examples can obey Gauss with B_R=0 and E_R=C[rho_R]. Since rho_R=R³ c_psi phi(x/a_R), Coulomb scaling gives

    ||E_R||2² = C R^6 a_R^5 = C R^(-2/3).                (31)

Thus even the Gauss-compatible field-plus-particle energy and phase-space density supremum do not give the required current L2 bound. These are smooth diagnostic data with varying initial momentum, NOT nonunique solutions or counterexamples at a common compact initial datum.

For a hypothetical unrestricted weak–strong comparison, one would need an actual propagated tail/density estimate sufficient to close the Maxwell-current term, or a different modulated quantity with a closed inequality. For example, a weighted L2 comparison would need enough weight to integrate its reciprocal in v (power greater than three), plus propagation of that weighted quantity under the rough force. The basic energy bound controls only one particle moment and does not supply this. If fields are separately H1, the relation div(deltaE)=delta rho replaces the lost tail current bound only by a derivative of deltaE, which is not present in (27); differentiating Maxwell then calls for derivatives of g. No such closed coupled inequality was established here.

## 10. Discovery disposition

The sustained construction reaches uniform radiation control, the full source signed bootstrap with approximation-uniform constants, an actual constraint-compatible rough-data limit, nonresonant field regularity, renormalization/energy, and smooth-comparator stability. Its operations are explicitly supplied by S and the actual primary mechanisms after ordinary localization, convolution and compactness. This notebook has not identified an additional fully paid nonroutine operation supporting a substantial nominee. It therefore remains PREFREEZE/no nominee; it does not assign itself a correctness or contribution grade.

The stronger coupled rough-rough comparison or unrestricted finite-energy weak–strong comparison is unproved here. They are recorded as precise limits of the construction, not as findings, not as necessarily substantial once solved, and not as worldwide open-problem certifications. No old frozen scope or verdict is changed, no tail target is renamed, and no formal/manuscript/release work is authorized by this notebook.
