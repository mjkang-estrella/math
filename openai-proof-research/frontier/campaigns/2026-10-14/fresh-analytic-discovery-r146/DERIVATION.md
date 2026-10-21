# Separated cores in the Source371 defocusing equation

PREFREEZE / no nominee. These are integrated feasibility calculations, not a frozen theorem, full author-proof submission, independent correctness judgment, or contribution grade. The investigation stays within one developed family. All source statements and operative proofs at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true.

## 1. Question and actual inherited operations

The initial question was simultaneous self-similar blowup at an arbitrary finite prescribed set of points of the standard T^12, with no additional point singularities. A stronger question, considered after the finite-core reduction below, is whether the synchronized solutions form a C1 physical H^K submanifold of the expected codimension N−1 when centers, phases and common time are allowed to vary. Neither question is frozen. The stronger question is not presented as an established frontier conjecture, a known open problem, or a result.

Fix one admissible large odd p from Source371, a=1/(p−1), its nonvanishing radial profile Q, and its logarithmic phase frequency b. Choose the source's finite integer high order K sufficiently large; its actual condition is

    K > max(8, 6−2a+2B0+1),     B0=p ||Q||_infty^(p−1).

Further increasing the finite K is allowed by the operative proof: all fixed-order symbol estimates are available, and its spectral top-derivative criterion applies. We need no uniformity in p or K. Write s0=6−a. The spaces are exactly

    Y = dot H^(s0)(R^12) ∩ dot H^K(R^12),
    ||v||_(Y_L)^2 = (2πL)^12 Σ_n [(L^(−2)+|n/L|²)^s0+|n/L|^(2K)] |v_n|².

The periodic low-frequency regularizer is retained. In particular a constant z has norm (2π)^6 L^a |z|. We do not impose L² integrability on Q, whose tail is |y|^(−2a+2ib) times a full symbol expansion.

Source labels used in the calculation are `profile:existence`, `profile:symbol-expansion`, `profile:time-symbol`; `lin:spatial`, `lin:compact-error`, `lin:observation`, `linear:decay`, `linear:torus`; and `nl:residual-formula`, `nl:step`, `nl:graph`, `nl:parameter-expansion`. The complete linear and nonlinear proofs were read. Their significant content includes actual stable semigroup decay, retention of norm that escapes a local limit, and exact normalized spectral coordinates. The full free/core/spectral construction was not reread; these remain stipulated source dependencies with stated reading limits.

For the fixed profile, let E have columns

    iQ, ∂_1 Q,...,∂_12 Q, (a−ib+D/2)Q,
    Λ=diag(0,1/2,...,1/2,1).

There is bounded π:Y→R^14, with πE=I, πS(s)=exp(sΛ)π, and exponentially decaying S(s) on ker π. This is an actual evolution estimate, not an inference from eigenvalues alone.

The actual antecedent chain matters. Buck–Carballeira–Gómez-Serrano–Shi, arXiv:2609.23685v1, §4.2–4.3, supplies compact-error spectral splitting and a Lyapunov–Perron graph followed by finite-dimensional localization. Its radial Euclidean power/dimension pairs differ from ours. Fan, arXiv:1510.00961v3, supplies multipoint synchronization, prescribed points and nested-cutoff propagation of exterior regularity for focusing mass-critical NLS in dimensions one and two. Li, arXiv:2304.02078v2, §6.3, supplies symmetry matching by Brouwer and explicitly handles rough perturbations continuously. These methods are credited even where their theorem statements do not directly apply in dimension twelve.

Actual completed project history includes the full C66 author proof, its I68 full-scope TECHNICAL ONLY disposition and phase-slice reduction, and r122's arbitrary-manifold feasibility calculation. C66's original proof PASS remains unchanged. Neither changing a slowly varying factor nor moving to a curved metric is a fresh target here.

## 2. Put all cores in one global evolution

Let N be fixed and finite, and let x_1,...,x_N be distinct points of T^12. Choose a fixed physical radius ρ>0 so that the coordinate balls B(x_j,2ρ) are pairwise disjoint and lie in flat injectivity neighborhoods. All constants below may depend on N,ρ and the fixed configuration. They are not uniform as points collide or N tends to infinity.

Let χ be a smooth nonnegative cutoff equal to one on B(0,1/2), supported in B(0,1). For a proposed common time T put τ=T−t, s=log(T/τ), L_s=τ^(−1/2), and use a single expanding torus T^(12)_(L_s). Its moving centers are c_j(s)=L_s x_j modulo the expanding lattice. Near the jth center let z_j=y−c_j(s), and put

    Ψ_s(y)=Σ_j exp(iθ_j) χ(z_j/(ρL_s)) Q(z_j).             (2.1)

The fixed phases θ_j are optional profile parameters. Since c_j'=c_j/2,

    (∂_s+y·∇/2)z_j=z_j/2,
    (∂_s+y·∇/2)χ(z_j/(ρL_s))=0.                        (2.2)

The identities are independent of the periodic lift, just as in the source's one-core computation. We are not postulating a collection of independent physical equations.

At every point, at most one summand of Ψ_s is nonzero. Hence for N(z)=|z|^(p−1)z,

    N(Ψ_s)=Σ_j N(exp(iθ_j)χ_j Q_j),
    DN(Ψ_s)=Σ_j DN(exp(iθ_j)χ_j Q_j).                    (2.3)

The first identity removes all nonlinear cross terms of the approximate profile EXACTLY. The second uses DN(0)=0. It does not make the actual Schrödinger propagator a direct sum: perturbations still move through the entire torus.

Each profile has precisely the source cutoff defect, translated and phase rotated:

    R_j=exp(iθ_j)[2∇χ_j·∇Q_j+(Δχ_j)Q_j+(χ_j−χ_j^p)N(Q_j)].

Its derivatives on the transition annulus obey |∇^m R_j|≤C_(m,ρ) L_s^(−2−2a−m). The low-order symbol norm contributes L_s^a, and the K norm is smaller. Therefore

    ||Σ_j R_j||_(Y_(L_s)) ≤ C_(N,ρ) L_s^(−2−a).         (2.4)

This includes the regularized zero-frequency contribution. The Ψ_s norms are uniformly bounded by finite summation of source symbol bounds. No exponentially decaying profile tail has been assumed.

A sum of *uncut* profiles would instead produce slowly decaying core interactions. That failed variant does not obstruct (2.1)–(2.4).

## 3. Finite observations retain the global norm

Let V_s=DN(Ψ_s) and evolve

    (∂_s+y·∇/2)v=iΔv−av+ibv−iV_s v.                   (3.1)

Because the cutoffs have disjoint support, the pointwise real operator norm of V_s is at most the same B0 as for one core. It is not N B0. The derivative constants in lower terms can depend on N and ρ, which is harmless for a fixed configuration.

Apply the source's compact-error argument separately around each moving center. Translation and multiplication by a constant phase preserve the defining Fourier norms. The dyadic tail estimates remain summable; for example, the fractional product tail has the source exponent −2+a−a²≤−7/4. In each fixed-radius ball use the same local interpolation between L² and H^K. Sum finitely many terms, choosing the per-core small coefficient after N is fixed. The resulting estimate has the form

    ||V_s v||_(s0,L_s)+||[∇^K,V_s]v||_2
      ≤ ε ||v||_(Y_(L_s)) + C_ε Σ_j ||v||_(L²(B(c_j(s),R_ε))).  (3.2)

The high-order leading multiplication term remains bounded by B0 independently of K, with all derivative combinatorics in (3.2). The exact squared free-norm rates are −a and 6−K−2a. The same energy calculation therefore gives

    d/ds ||v||² ≤ −c ||v||²+C Σ_j ||v||²_(L²(B(c_j(s),R))).     (3.3)

This is the finite-observation version of the source inequality, derived by the same local estimates. It is not an operator-norm approximation of the global propagator by N free-space propagators.

Choose localized coordinate maps J_(j,L)v centered at Lx_j, undo the fixed phase, and cut off on radius ρL. They map Y_L boundedly into Y by the source's discrete-to-continuous Fourier proof; the fixed radius factor changes only constants. Let E_L^N have the N blocks exp(iθ_j)χ_j E(z_j), and set

    raw π_L^N = (π J_(1,L),...,π J_(N,L)),
    C_L=raw π_L^N E_L^N,
    π_L^N=C_L^(−1) raw π_L^N,     P_L^N=E_L^N π_L^N.    (3.4)

The off-diagonal blocks of C_L vanish because of disjoint cutoffs. Each diagonal block tends to I_14 by symbol-tail convergence. Thus (3.4) is well defined for large L and gives exact π_L^N E_L^N=I_(14N), with uniformly bounded maps for the fixed configuration.

For a bounded sequence of initial data with L→∞, look in each moving coordinate z_j. On every fixed slab and ball, (3.1) has the same bounded drift as the one-core equation; the other core potentials vanish there for large L. A finite diagonal subsequence has local limits v_j(s). The source weak-local-limit and free-adjoint argument identify

    v_j(s)=S(s)v_j(0),
    ||v_j(0)||_Y≤C_J liminf ||v_L(0)||_(Y_L).             (3.5)

All N observations must be kept. For initial vectors in ker π_L^N, each πv_j(0)=0. Integrating (3.3) BEFORE taking a local limit consequently gives

    limsup ||F_L^(M)v_L(0)||²
       ≤ exp(−cM)+C_N ∫_0^M exp(−c(M−s))exp(−2ηs) ds.   (3.6)

This tends to zero as M grows. Finite-dimensional coordinate convergence similarly gives

    ||π_(L')^N F_L^(M)−D_N π_L^N||→0,
    D_N=diag(exp(MΛ),...,exp(MΛ)),   L'=L exp(M/2).       (3.7)

First choose M sufficiently large, then L. After projection at the final scale the stable step norm can be made ≤1/8. The order of choices matters; neither a local zero limit nor disjoint support alone would control escaped norm. Equations (3.2)–(3.7) explain the strongest compatible transfer, rather than leaving it as an unnamed gluing obstacle. They have not undergone an independent review.

## 4. What the graph mechanism would already supply

For fixed N, points, phases and T, polynomiality, uniform algebra bounds and (2.4) give the source nonlinear step estimates with constants depending on this fixed configuration. With

    v_n=w_n+E_n^N u_n,    w_n∈ker π_n^N,

there are exactly the source forward/backward recursions, now in 14N finite coordinates. Use sup_n 2^n(||w_n||+A|u_n|). The phase coordinates have multiplier one but the forcing and sequences decay exponentially, so the backward sums converge. No new phase-resonance obstruction appears. Choose A after the fixed slab bound, then a small sequence ball, then L large enough for the coordinate defect. Require 2exp(−(2+a)M/2)<1 for the cutoff forcing.

This is a finite-copy Lyapunov–Perron calculation, not evidence of a new graph method. It yields the expected fixed-parameter graph mechanism with

    ||v(s)||_(Y_(L_s)) ≤ C exp(−δs),    δ=log(2)/M>0,    (4.1)

and a small initial nonstable correction. In physical variables the common-time reconstruction is

    u(t,x)=τ^(−a)(τ/T)^(ib)[Ψ_s(x/√τ)+v(s,x/√τ)].        (4.2)

At x_j only its own cutoff core survives, so (4.1) implies τ^a|u(t,x_j)|→|Q(0)|. In particular, existence with a fixed prescribed T and centers is not defeated by a lack of N independent exact time symmetries: the graph can select N time-mode coefficients in the initial datum. An attempt to make *every* nearby datum synchronized has a different parameter problem.

The source alone already contains one core, Gaussian full support and higher-dimensional product-fiber examples. These are not being nominated again. Nor is this section a frozen assertion of a full multipoint theorem; it records the compatible construction and checks which supposed obstacles survive it.

## 5. Exterior regularity: use the actual Fan operation

A decaying rescaled remainder does not immediately give a bounded physical remainder. In fact the direct bound is τ^(−a+δ), which can still diverge. But it is enough to start a nested-cutoff argument; stopping at that direct bound would miss a compatible operation.

Take any compact exterior region away from the prescribed points. The source full slow-tail expansion makes the physical approximate field uniformly smooth there as τ→0: the powers in

    τ^(−a)(τ/T)^(ib) (|x−x_j|/√τ)^(−2a+2ib)

cancel exactly, and further profile terms carry positive integer powers of τ. From (4.1), on a slightly larger exterior region,

    ||u(t)||_infty ≤ C(1+τ^(−a+δ)),
    ||u(t)||_infty^(p−1) ≤ C τ^(−1+κ),
    κ=min(δ/a,1)>0,                                   (5.1)

for 0<τ≤min(T,1). This nonlinear coefficient is integrable up to T.

The global high-order bound supplied by (4.2) and the bounded rescaled norm is

    ||u(t)||_(H^K) ≤ C τ^(−B),    B=K/2+a−3.            (5.2)

Indeed ∂_x^K contributes τ^(−K/2), volume contributes τ^3, and amplitude contributes τ^(−a). Lower physical norms are controlled by the same upper bound, using interpolation and mass. The defocusing conserved mass and energy give a uniform H^1 bound on every classical interval before T. This use of conservation is legitimate in H^K, K>8, and does not claim control at the scaling-critical index.

Let ζ and χ be nested smooth exterior cutoffs with ζ=1 on a neighborhood of supp χ. Suppose ||ζu||_(H^r) is uniformly bounded, initially r=1. Interpolation with (5.2) gives, for r≤q≤K,

    ||ζu||_(H^q) ≤ C τ^(−B(q−r)/(K−r)).                (5.3)

The equation for χu is the ordinary physical Schrödinger equation with sources χN(ζu) and the first-order cutoff commutator. By the standard polynomial tame product estimate,

    ||χN(ζu)||_(H^q)
       ≤ C ||ζu||_infty^(p−1)||ζu||_(H^q),
    ||[Δ,χ]u||_(H^q) ≤ C ||ζu||_(H^(q+1)).             (5.4)

The fractional H^q product estimate can be obtained by telescoping polynomial low-frequency approximations and summing dyadic high-frequency tails; it is the usual Moser/paraproduct operation, not a new nonlinear estimate. It is also precisely the type of product estimate in Fan's actual nested-cutoff proof. No Euclidean dispersive estimate is needed here: on the torus the free group is unitary on every H^q, so L¹_t H^q forcing suffices.

Put q=r+h. Equations (5.1)–(5.4) make both sources integrable if

    B(h+1)/(K−r)<1,           Bh/(K−r)<κ.               (5.5)

Consequently χu remains bounded in H^(r+h), and its Duhamel integral converges there as t→T. A positive increment exists whenever

    r<K−B=K/2+3−a.                                    (5.6)

To make the finite iteration explicit, choose q_* with 6<q_*<K−B, possible after choosing the finite K large enough. On 1≤r≤q_* take a positive h smaller than half each of

    (K−q_*)/B−1,        κ(K−q_*)/B,        1.

Choose finitely many nested cutoffs and stop the last increment at q_*. Every step satisfies (5.5). The endpoint H^(q_*) bound, with q_*>6, implies a bounded continuous exterior representative and convergence in a slightly lower still-embedding Sobolev norm (indeed the displayed L¹ forcing also yields convergence at each attained exponent).

This pays the exterior-regularity feasibility calculation, conditional only on the fixed-core graph package in §§3–4. It is not justified to retain 'infinite propagation' as an unpaid obstruction after this calculation. The mechanism is an adaptation of Fan's interpolation operation, using the source's small positive δ and defocusing energy for the starting H^1 bound. Fan's mass-critical, low-dimensional theorem is not invoked as if it already stated the dimension-twelve result.

The calculation proves neither smoothness of a synchronization *set of initial data* nor a new-to-literature assertion. It also does not imply arbitrary high exterior smoothness from one fixed finite K: the explicit ceiling in (5.6) is retained.

## 6. Synchronization geometry is a different claim

For fixed positions, phases and T, the graph removes 14N coordinates. If N centers (12N variables), N limiting phases and a single common time are freed, dimension counting suggests

    14N−(12N+N+1)=N−1                              (6.1)

remaining relative-time conditions. This is useful bookkeeping, not an implicit-function theorem. At the decoupled reference the N time eigenvalues are one; only their common-time combination is an exact global time symmetry. Independent local time variations alter the initial datum and must be controlled by an actual construction.

There are two distinct questions which must not be conflated:

* Finite-core existence with fixed common T: the backward graph can tune all time coordinates, as in §4. No physical open-set claim follows or is needed.
* A C1 codimension-(N−1) physical synchronization stratum, with local uniqueness/rank and continuous differential in the SAME H^K topology: a joint parameter-dependent mismatch functional and a constant-rank argument are required. These have not been established here.

The source's parameter proof differentiates the smooth reference only. It treats the arbitrary H^K perturbation by strong continuity under translation/rescaling and applies degree. Li's actual §6.3 likewise uses Brouwer, even though its one-core limiting asymptotics identify parameters uniquely. Fan proves the continuity needed for its finite-parameter endpoint map and uses topology; it does not give the proposed H^K differentiability statement in our setting.

A tempting inference fails: the translation action h↦h(·+z) is strongly continuous on H^K but its z derivative is ∂h, not a bounded H^K-valued operation for arbitrary h∈H^K. On a Fourier mode with H^K norm one, the difference quotient has size comparable to its frequency. Likewise differentiation of a free step with respect to its time coefficient introduces Δ. Smoothness of the graph for fixed parameters therefore does not, by itself, establish smoothness of the graph after parameters act on all physical data.

These observations refute only the naive Banach implicit-function inference. They do not rule out a suitable mismatch functional. A promising stronger compatible operation is to use finite-coordinate adjoints: derivatives can fall on smooth localized adjoint test functions instead of on the arbitrary datum. At the linear level πJ is finite dimensional; elliptic regularity for adjoint eigenfunctions is potentially relevant. At the nonlinear level one needs differentiable dependence of the backward dual evolution and summable bounds for its parameter derivatives, uniformly over the allowed H^K ball and all similarity slabs. No such weighted dual/parameter theorem is supplied by the bounded maps and strong continuity already used in (3.4)–(3.7).

The concrete unpaid interface is thus a jointly C1 physical mismatch map F(q,h) with h in a genuine H^K-open ball, whose zero set is the synchronized family and whose differential has rank N−1 after the 13N+1 phase/center/common-time parameters have been eliminated. A proof must show the needed uniform adjoint regularity or another way to handle derivative loss, the convergence of differentiated infinite graph sums, and local uniqueness/rank. A formal count, a degree zero, a smooth-reference-only calculation, or an assertion in a stronger H^(K+2) topology does not pay that interface at H^K.

Even closing that interface would not automatically establish substantial contribution. Smooth invariant-manifold and modulation methods might already pay it once their exact hypotheses are verified. This round has not demonstrated otherwise and makes no nonroutine-evidence claim from an unproved bridge.

## 7. Phase slicing does not create a spurious obstruction

I68's completed C66 reduction must be credited: a nonlinear slice removes its single neutral phase because the FULL equation is exactly equivariant under one constant phase. No logarithmic forcing or neutral-sum claim from that technical result is revived here.

For N separated cores one may prescribe N approximate phases, but only their common rotation is an exact global gauge symmetry. A spatial multiplier exp(iΣ_j θ_j χ_j(x)) produces gradient and Laplacian commutators in the transition regions. The first-order term acts on the perturbation, so its apparent small coefficient does not make it a bounded H^K→H^K perturbation. This prevents copying N independent exact-gauge reconstructions verbatim. It is not an impossibility argument: conjugated energy norms, bounded finite-coordinate tests or a modulation system can be compatible alternatives. Moreover the exponential graph in §4 already handles all N neutral coordinates without slicing. Thus phase slicing supplies neither a new obstruction to finite-core existence nor a complete proof of the stronger smooth-stratum claim.

## 8. Stopping point

The strongest integrated reduction is substantial in length but not established as a substantial contribution: disjoint physical cutoffs, finitely many local observations retaining escaping norm, normalized block coordinates, the source graph, and Fan-style exterior interpolation. Those are compatible known/source operations. The calculation rules out several premature gap claims; it does not nominate their composition as a supporting result.

A smooth physical synchronization stratum remains unproved, and its contribution case has not closed. No exact new theorem is frozen. No current-open, worldwide-priority, exhaustion or impossibility conclusion is inferred. Source371's old scopes, C66, r122, the required r145 Coulomb targets, H138/T185R144 and every other supplied old disposition remain unchanged. Parent alone integrates, reviews and counts.
