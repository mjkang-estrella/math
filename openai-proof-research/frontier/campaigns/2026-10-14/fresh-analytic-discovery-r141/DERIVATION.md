# PREFREEZE feasibility notebook: forced-fluid computation under perturbations

Codex / GPT-6 Astra / high / default service tier. One family: Source376 forced incompressible computation, including its control/robustness interface. No theorem frozen, nominee, or self-assigned gate. Pin and operative proofs stipulated true.

## Starting interface, read before these calculations

The eventually stationary companion (ES), main.tex thm:main, constructs U(t)=alpha(t)W on the fixed flat T^3, alpha=1 for t>=1, W smooth divergence-free and mean-zero. It computes the finite force formula F=U_t+(U.grad)U-nu Delta U and optionally its Leray projection; zero initial data and uniqueness follow from lem:realization. Fixed particle P=(1/4,1/4,0) enters O={1/32<Y<1/8} iff the input machine halts. The proof's autonomous-suspension and steady-ramp operations, finite-time tube estimate, force formula, mean and uniqueness were read. No full compiler reading is claimed yet. The exact source says no uniform infinite-time tolerance is supplied.

I80 already develops compact Euclidean velocity/pressure/solenoidal force and rapidly vanishing derivatives using balanced rotation gates. That full scope is not reopened or nominated. Its shrinking signal is not a positive precision margin. I20 already warned against identifying finite-time tubes with robust computation. Source ES instead has a positive geometric detector separation along the exact nonhalting computation; exponential amplification of coordinate errors still matters.

## Strongest compatible time-dependent construction (working derivation)

The right baseline is not a scalar Gronwall estimate. The following integrates volume preservation, local solenoidal kicks, transport by the exact drift, residual forcing and pressure projection. It is supporting feasibility mathematics, not proposed new-to-literature content.

Normalize vol(T^3)=1. Fix a smooth autonomous mean-zero divergence-free W, nu>0, a finite mixed derivative order m, and any epsilon>0. Write Phi_s for its flow, 0<=s<=1. Choose a fixed small chart radius rho<1/16 and a smooth radial cutoff chi=1 on B_{rho/2}, supported in B_rho. For x in T^3 and a small vector a, define in the translated chart

    B_{x,a}(x+y) = curl_y [ (1/2) chi(y) (a cross y) ].

Periodize by zero extension. Since curl(a cross y)=2a, this equals a near x. It is divergence-free, mean-zero (a periodic curl), and ||B_{x,a}||_{C^k} <= C_k |a| for every fixed k, uniformly in x. If |a|<rho/4, its time-one trajectory from x is x+a and stays in the plateau.

Choose eta>=0 smooth supported in (1/4,3/4), integral eta=1. On a unit interval starting at an integer j>=2 put

    w(j+s,z)=eta(s) D Phi_s(Phi_{-s}z) B_{x,a}(Phi_{-s}z).

Thus w=eta(s)(Phi_s)_*B_{x,a}. In moving coordinates z=Phi_s(y), the equation z'=W(z)+w(j+s,z) is exactly y'=eta(s)B_{x,a}(y), so starting at x it ends at Phi_1(x+a). This is an exact correction formula, not a perturbed-flow approximation. Divergence-free follows from volume preservation. Mean-zero also holds: a zero-flux divergence-free field corresponds to an exact two-form i_B(dx1 wedge dx2 wedge dx3); pushforward by the isotopy Phi_s preserves exactness. Equivalently integrate the transported field's evolution partial_s B_s=[B_s,W]; the integral of both divergence-form commutator terms vanishes. Its initial mean is zero.

For each fixed k, all mixed derivatives of w up to k are bounded by C_k(W,eta,chi)|a| on this unit interval. The constants use only finite spatial derivatives of W and its unit-time flow/inverse. The absolute start j and later number of intervals do not occur. Pulse collars make arbitrary finite concatenations globally smooth, with the same supremum bounds.

## Reachability pays long-time amplification without shadowing

Fix 0<r<rho/4, allow every |a|<r on each interval, and put R_0={p},

    R_{n+1}=Phi_1(N_r(R_n)).

Every point of this set is realized by a finite list of the preceding smooth solenoidal kicks. Phi_1 preserves volume, hence |R_{n+1}|=|N_r(R_n)|. This does NOT assert the sets R_n are nested; only their volumes are nondecreasing. For n>=1 they are nonempty open sets.

If N_r(R_n) is not all of T^3, there exists q with dist(q,R_n)>=r. Along a path from a point of R_n to q, continuity of the distance supplies z with dist(z,R_n)=r/2. Then B_{r/4}(z) lies in N_r(R_n) minus closure(R_n). Consequently

    |R_{n+1}| >= |R_n| + v_3 (r/4)^3

whenever N_r(R_n) is not the whole torus. This elementary estimate needs no smooth boundary of the reachable set, PDE front regularity, isoperimetric theorem, or uniform drift smallness. After at most floor(1/[v_3(r/4)^3])+2 intervals the whole torus is reachable; otherwise repeated volume increases exceed one. Exact constants are deliberately a crude supporting bound. Choosing a target in the interior of any nonempty open detector produces finite entry.

There is no inference that the original trajectory is close to the controlled one for the entire time. Long times permit accumulation of arbitrarily small admissible changes; volume growth replaces that invalid inference.

## Force compatibility, including mean and pressure

Leave the source U unchanged until time 2; subsequently U=W. For a finite concatenation of the above kicks set U_tilde=U+w. It starts from the same zero datum. The unprojected force difference is exactly

    G = partial_t w + (W.grad)w + (w.grad)W
        + (w.grad)w - nu Delta w.

Every term has zero spatial mean: w and its derivative/Laplacian do, and the transport terms integrate to zero by solenoidality. Let P be the periodic Leray projector. If the reference force is solenoidal, use delta f=P G and adjust pressure by the complementary gradient. The prescribed velocity U_tilde then satisfies the full Navier--Stokes equation. ES lem:realization's difference-energy argument supplies uniqueness on each finite interval. This is an explicit global smooth solution, not a general global wellposedness claim.

For a fixed finite mixed order m, the source projection proof bounds C^m(PG) by finitely higher spatial derivatives of G (five extra suffice in its displayed Fourier estimate). Thus, using enough fixed derivatives of W,

    ||delta f||_{C^m_{t,x}} <= C_{m,W,nu}(r+r^2).

The constant is independent of the number of kicks. Choose r sufficiently small to make this <epsilon. Since there are finitely many pulse intervals, w and delta f are compactly supported in time after 2; the force returns exactly to the original stationary force afterward. The first transient is generally later than time one. This is NOT a perturbation that is itself stationary for every t>=1.

For every prescribed finite derivative order and every positive error tolerance, time-dependent smooth mean-zero solenoidal force errors can therefore steer the designated particle into the detector in finite time. A basic neighborhood in the C-infinity topology constrains finitely many such seminorms, so the same construction fits a supplied basic neighborhood. It does not establish one perturbation small in every order with arbitrarily preassigned infinitely many bounds; it does not estimate a time-integrated perturbation norm, a stationary perturbation norm, or a stochastic probability. No generic 'noise destroys universality' claim is made outside this quantifier set.

## What this does and does not settle

Within the just-described time-dependent error class, no nonhalting path can exclude the detector under all small errors. This is a direct compatible classical control/residual composition. It is not evidence for a substantial nominee merely because the errors are solenoidal or small in a finite smooth topology. Primary and historical comparison must be completed before any further claim.

The potentially different question keeps the perturbation stationary after the same initialization time (or replaces W by a nearby autonomous field). Our construction does not pay that constraint. The time-indexed kicks prescribe different values near recurrent locations; turning them into one autonomous field can create incompatible jets. Disjoint thin tubes may avoid value conflicts but their derivatives cost powers of inverse tube radius, and no estimate independent of the recurrence geometry has been obtained. A C1 conservative connecting theorem alone would not control the second and higher velocity derivatives needed for small force in C^m. These are precise compatibility issues to investigate, not a frozen target or an assertion of worldwide openness.

## Primary comparison and late compatible improvements

The explicit derivation above was recorded before the later full readings listed here. ES main.tex was subsequently completed through all 1017 lines. Prefix Instructions (PI), autonomous.tex 1-338, supplies a second actual autonomous Hamiltonian suspension, with a quiet phase-window detector and a slow onto clock. It does not add a new independent time coordinate to T^3: the third coordinate is already the repeating phase of the original processor. Encoding a different perturbation on each successive unit interval requires a nonrepeating index or a new construction; simply setting t=Z mod1 repeats the same perturbation. Slowing that clock or adding a fourth coordinate would change the exact problem, not pay this obligation.

The October6 Incompressible Box Transport (IB) analysis.tex 1-282 gives a stronger projection estimate than the five-derivative bound first used above:

    ||P G||_{C^r} <= S_1 ||G||_{H^{r+2}},
    S_1=(1+52/(2pi)^4)^(1/2),

with explicit finite spatial-derivative control of the Sobolev norm. The operator commutes with time differentiation. This reduces the excess regularity spent on projection; there remains a Laplacian in G. The source improvement is credited, not offered as a new bound. All source proof operations are stipulated true, not truth-audited.

Burago--Ivanov--Novikov, 1605.01702v2, actual mathematical body lines117-785, proves global controllability for bounded locally Lipschitz incompressible fields on R^d with uniformly vanishing mean drift. A mean-zero periodic lift meets that hypothesis: split a large cube into unit cells plus O(L^(d-1)) boundary cells; the normalized remainder is O(||W||infinity/L). Rescale the field to allow any fixed positive control speed. Their compact-set time bound and global Lipschitz argument already supply finite travel times. Their proof treats accessible-set boundary cones, flux, and isoperimetric/coarea growth. No direct claim about Navier--Stokes forcing derivatives follows from a merely measurable additive control. The transported smooth kicks above pay that compatibility by elementary fixed-scale localization and exact drift conjugation. The older control theorem and the source residual operation are thus compatible, not competing failed routes.

Kryzhevich--Stepanov, 1801.06200v2, actual prop_trans1 and its proof, th_control1 and the preceding th_Pugh0 proof were read in the ranges recorded separately. Their compact recurrent-set argument gives another route: local control makes the reachable set open, recurrence supplies invariance/closure, and connectedness leaves no proper clopen reachable component. Their noncompact Newtonian corrector is explicitly not generally divergence-free; its small divergence is not zero divergence. We do not apply it as a solenoidal force perturbation. Their later C1 closing step is not a C2-small force construction.

Bessa, published 2008 note, Theorem1.1 and Sections2-4, is an actual conservative C1 connecting/mixing comparison. Section4.1 constructs transverse exact forms and a Whitney extension in injective flowboxes; Section4.2 invokes topological towers to avoid overlapping supports; Section4.3 treats the dimension-three elliptic complication. The note itself supplies guidelines and cites Bonatti--Crovisier and Pugh--Robinson for substantial transitive proofs. These were not all freshly read. Its C1 closeness, generic orbit assertions, and ambient divergence-free class cannot silently be replaced by a prescribed-particle, zero-flux, C^{m+2}-small realization. No full proof of the proposed stationary extension is inferred from that comparison.

Cardona--Miranda--Peralta-Salas, 2111.03559v3, Section6.1 lines979-1079, gives robust tape-bounded simulation on a compact subset of T^3 only up to first exit. It permits trajectories to return later without maintaining the decoding assertion. Its unforced viscous variant uses nonzero Beltrami initial data and finite accumulated orbit time M/(nu lambda^2). It therefore does not give the fixed-zero-data, infinite-time robust event considered here. It is a strong credited finite-computation operation, not a counterexample to the time-dependent error calculation. The paper's transitive reference to Bournez--Graca--Hainry was sought; raw CiteSeer retrieval failed404 and repository/author web access was blocked. No BGH proof is claimed read. Generic statements about all robustness notions are not imported from its abstract.

## Testing the stationary shortcut at the correct norm

For a stationary replacement W+w, the same fixed source ramp gives the exact mean-zero projected force change

    delta f(t)=P[alpha'(t)w
                 +alpha(t)^2((W.grad)w+(w.grad)W+(w.grad)w)
                 -nu alpha(t) Delta w].

This genuinely preserves stationarity for t>=1 and the zero initial datum. Thus the analytic realization is paid IF an appropriate stationary velocity perturbation with controlled derivatives and the required event is supplied. For example, small C^{m+4} spatial norm of w is a sufficient input for small C^m mixed norm of delta f by the IB projection estimate and the fixed ramp. This sufficient norm is not claimed necessary.

A precise derivative test shows why C1 closeness alone is not that input. On T^3 take

    w_N(x)=N^(-3/2) sin(2pi N x_2) e_1.

It is smooth, divergence-free, and mean-zero; its convection is zero. Its C1 norm tends to zero, but ||Delta w_N||infinity=4pi^2 N^(1/2). For W=0 and t>=1, P leaves this shear invariant and the exact stationary force is -nu Delta w_N. Hence the force sup norm tends to infinity. This is a counterexample only to the implication 'C1-small velocity necessarily gives C0-small residual force.' It is not a counterexample to the possibility of choosing better perturbations, to a solution-specific connecting operation, or to robust/unrobust computation for the particular source.

One also cannot turn the time-dependent construction into an autonomous field just by drawing its trajectory. Prescribed values at repeated spatial points must agree; nearby returns must satisfy the selected derivative bounds. A tube of radius d carrying a correction of amplitude a typically spends derivatives a d^(-k). Ensuring the force norm at order m then spends still higher derivatives. This dimensional estimate describes the missing bound for that route; it is not a theorem ruling out all stationary implementations. The available source finite-rectangle Hamiltonian extension establishes existence with derivatives depending on clearance, not perturbative smallness near this already fixed processor over arbitrary recurrence times.

## Precise stopping point

No nonroutine full theorem has closed and no statement is frozen. The completed time-dependent control reduction is supporting work only. The unresolved operation is a stationary, mean-zero, divergence-free perturbation construction for the actual ES processor, preserving the fixed ramp and viscosity, that changes the prescribed-particle infinite-time detector event while controlling the displayed force residual in an arbitrarily prescribed finite smooth norm; alternatively one would need a proof of a specific robust stationary behavior with those same constraints. Neither direction is proved here. We do not assert that this is an independent worldwide-open problem or that every nonhalting processor admits the perturbation.

The comparison does not ask for a new grade on C80, on a restricted old full target, or on a renamed scalar-clock corollary. It does not change the old arbitrary-core pressure-completion gap. No broader family exhaustion, full primary review, correctness review, contribution assessment, acceptance or count follows.

For an open detector and computably supplied W, the finite time-dependent construction can also be searched effectively: use rational vectors strictly inside the kick ball, simulate the explicitly prescribed smooth velocities on finite intervals with derivative bounds, and enumerate certificates of entry into a rational ball compactly contained in the detector. Continuity and the existence argument guarantee that some finite rational kick list succeeds. This is not an execution-free stationary compiler or a decision algorithm for the original event; the altered flow can enter even for a nonhalting input. No effectiveness claim is needed for exact arrival at an arbitrary noncomputable prescribed point.
