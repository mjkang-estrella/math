# Thermal depletion: a pre-freeze interface, not a theorem

Myeongjin Kang, no affiliation. Original prose CC BY 4.0.

No target is frozen and no candidate is nominated. This screen does not reopen I153's connected zero-temperature structure-factor target or the spin-wave fluctuation target of analytic r19. Family267 is a developed family; the operation inspected here is thermal occupation identification at the interaction-energy scale. Its feasibility and eligibility have not been established.

## The proposed full statement being tested

Fix a hard-sphere exclusion distance/scattering length a>0, and use the exact symmetric Dirichlet hard-core Hamiltonian on the three-torus, with kinetic energy -Delta and units hbar²/(2m)=k_B=1. For every fixed tau>0 put T=8*pi*rho*a*tau. At each fixed rho, first take every thermodynamic sequence N_j,L_j→infinity with N_j/L_j³→rho, keeping this T fixed. Then take rho↓0. The proposed occupation measure is

    (N_j sqrt(rho a³))^-1 sum_{k≠0} n_{Gamma_T,j}(k) delta_{k/sqrt(8*pi*rho*a)}
      → ((8*pi)^(3/2)/(2*pi)^3) g_tau(p) dp,

against every bounded continuous real test on R³, including the constant test 1, where

    e(p)=|p| sqrt(|p|²+2),
    alpha(p)=(|p|²+1)/e(p),
    v(p)²=(alpha(p)-1)/2,
    g_tau(p)=v(p)²+alpha(p)/(exp(e(p)/tau)-1).

The limit convention would be the source's epsilon/rho_0/thermodynamic-limsup convention, not an asserted unique fixed-density momentum limit. All tau>0 and the entire occupation measure, including infrared tightness and its total mass, remain in this proposed scope. Nothing here proves it, and no restriction to annular tests, very small temperature, or bounded potentials is substituted as a nominee.

Near p=0 the thermal term is tau/(2|p|²)+O(1/|p|), hence integrable in three dimensions. At infinity the vacuum term is O(|p|^-4) and the thermal term decays exponentially. At tau=0 this reduces to the source's established profile. The coefficient (8*pi)^(3/2) follows from k=sqrt(8*pi*rho*a)p and rho sqrt(rho*a³)=(rho*a)^(3/2); this normalization calculation is technical.

## What was actually compared

The positive-temperature hard-core source states condensation at some positive T(a,rho), and its scaled setup imposes 0<T_scaled<=D^-1 with r=alpha/D, alpha fixed. The operative energy section proves entropy bounds and an insertion estimate ending in

    F_j^(-W)-F_(j-1)^(-W) <= C alpha +1+T_scaled log_+(Cj/V).

It makes this uniform by T_scaled<=D^-1 and j/V<=2D. It does not state uniformity for fixed positive T_scaled. This is a limitation of that displayed estimate, not a proof that insertion or condensation fails at a fixed scaled temperature. The bounded-repulsion companion's introduction similarly confines its theorem to physical T<=rho².

The hard-core depletion source's `en:surplus` compares a ground-state upper energy with localized lower forms. In scaled volume V it bounds the retained quasiparticle energy and other nonnegative penalties by C V Q^-1/5. Its `en:observable` then estimates a weighted one-body observable by its quasiparticle vacuum trace, with errors

    C(1+R²) Q_energy + C sqrt((1+R²) Q_energy * vacuum_trace).

The thermal state of the limiting quadratic Hamiltonian has instead

    V^-1 E sum_p e(p)b_p* b_p
      → integral e(p)/(exp(e(p)/tau)-1) dp/(2*pi)^3 >0.

This integral is finite and strictly positive for tau>0. Thus replacing a ground state by a thermal state in the vanishing-surplus proof would discard a leading term. The formula above is an exact effective-model calculation; no physical-gas quasiparticle limit is inferred from it.

The source's infrared proof is separately essential. In `assembly.tex`, distant deletion comparisons control the variance of cell root-mean-squares, a fourth-moment local comparison relates these to arithmetic means, and `asm:infrared` proves occupation of P_R-P_0 is o(V). The positive/negative-parts argument there explicitly uses a ground-space minimization identity. An arbitrary thermal square-root kernel cannot be inserted into that identity. The positive-temperature companion supplies a mixed-kernel positive-overlap construction, but the introduction and energy operations read here do not supply the depletion-scale o(V) estimate at fixed positive scaled temperature.

## Closest primary operations already pay thermal free energy

Haberberger–Hainzl–Schlein–Triay, arXiv:2405.03378v1, Theorem1 and Propositions2–3, give a sharp free-energy upper bound at T<=C rho a for fixed nonnegative radial compactly supported L² interactions. In Section2, formulas(2.19)–(2.26) construct a quadratic thermal state and conjugate it by unitary Weyl, quadratic, and cubic transformations; this preserves entropy. Formula(2.23) explicitly computes the trial occupation profile written above. Thus even this profile calculation is an antecedent, not a new prediction. Their small-periodic-box trial state is transferred to the thermodynamic limit by a boundary collar. This hypothesis does not include an infinite hard core.

Fournais–Junge–Girardot–Morin–Olivieri–Triay, arXiv:2408.14222v1, Theorems1.1 and1.3, give the sharp lower bound for nonnegative radial nonincreasing compactly supported interactions with support radius bounded by a fixed multiple of scattering length, including hard cores. Their Sections2.3–2.9 retain spectral gaps, use coherent zero-mode substitution, diagonalize a quadratic Hamiltonian, control the 3Q term, and take its thermal trace. In particular Corollary2.13 retains the exact Bogoliubov dispersion on low modes; high modes have a weakened positive coefficient. This is an operative antecedent, not just a title comparison. The chemical potential in Theorem2.9 controls zero-mode number and has 10mu<=ell^-2. It is not a theorem for arbitrary signed occupation fields on all nonzero modes.

Consequently deriving scalar thermal pressure from these established operations, or differentiating it in temperature by convex secants, is not proposed as substantial. These reads do not establish a matching hard-core upper free energy at this thermal scale. The pinned zero-temperature hard-core upper energy alone cannot provide its entropy-bearing trial state. No claim of absence in the unread literature is made.

## A finite spectral warning: free energy and the ground state do not identify thermal occupation

On C³ take N=diag(0,1,2), H1=diag(0,E,2E), and H2=diag(0,2E,E), E>0. They have identical spectra, hence identical partition functions at every temperature; both have the same unique ground vector and zero ground occupation. Both obey H_i >= (E/2)N. Nevertheless at beta>0 their Gibbs occupations differ by

    (exp(-beta E)-exp(-2 beta E))/(1+exp(-beta E)+exp(-2 beta E)) >0.

Tensoring M copies makes this difference extensive while preserving equality of every free-energy density and the ground-state occupation. This is not a hard-sphere counterexample. It rules out an abstract inference from scalar free energies, zero-temperature covariance, and a coarse common coercivity bound alone.

## What relative entropy does give on a fixed momentum annulus

This elementary lemma is technical support only. It makes the missing infrared step precise.

Take independent oscillator modes indexed by p in a finite-volume lattice. Let H=sum_p e_p b_p* b_p, e_p>0, and let sigma be its Gibbs state at temperature tau. For each mode choose real u_p,v_p with u_p²-v_p²=1 and set a_p=u_p b_p+v_p b_p*. Let A=sum_p chi_p a_p* a_p, where chi is supported in a fixed annulus delta<=|p|<=J and bounded by one in absolute value. Assume on that annulus e_p is bounded above and below away from zero and u_p,v_p are uniformly bounded; the number of annular modes is O(V). The coefficients may be the Bogoliubov coefficients above.

For |lambda| sufficiently small depending only on this annulus and tau, define

    P_V(lambda)=log Tr exp(-(H-lambda A)/tau).

The modes remain independent even though A need not commute with H. For one mode put alpha=u²+v² and ell=lambda chi. Exact squeezing gives

    E_ell=sqrt(e²-2e alpha ell+ell²),
    H_mode-ell a*a = E_ell c*c + (E_ell-e+ell)/2.

Indeed the coefficient of b*b is e-alpha ell, that of b²+b*² is -uv ell, and alpha²-4u²v²=1. Positivity holds uniformly on the fixed annulus for small |lambda|. Its partition function is therefore

    exp(-(E_ell-e+ell)/(2tau))/(1-exp(-E_ell/tau)).

Uniform boundedness of its first two derivatives on a smaller lambda interval implies

    |P_V(lambda)-P_V(0)-lambda E_sigma A/tau| <= C V lambda².

For any state omega with finite relative entropy D(omega||sigma), the Gibbs variational principle (or relative entropy to the tilted Gibbs state) gives

    lambda(E_omega A-E_sigma A)/tau
        <= D(omega||sigma)+C V lambda².

Applying both signs and then letting lambda↓0 proves that D(omega||sigma)=o(V) implies V^-1(E_omega A-E_sigma A)→0, uniformly for the fixed annulus and bounded chi. Unbounded-observable applications can first use finite particle cutoffs and pass using the two-sided exponential-moment bounds supplied by the same stable tilted oscillator. This is not Pinsker applied to an extensive observable.

Thus a suitable actual relative-entropy comparison could identify annular thermal occupations. It still would not prove the full proposed statement. Nor has that relative-entropy comparison been established for the exact interacting gas in this screen.

## Exact infrared counterexample to the entropy-density shortcut

Even within the quadratic reference model, relative entropy o(V) does not control total nonzero-mode particle occupation. This is a route counterexample, not a counterexample to the proposed physical statement.

Use a torus of side L, V=L³, and a single mode p_L=(2*pi/L,0,0). Put e_L=e(p_L), alpha_L=alpha(p_L); then e_L~sqrt(2)|p_L| and alpha_L~1/(sqrt(2)|p_L|). Replace this mode's reference geometric Gibbs law by its number state |m_L><m_L|, leaving every other mode unchanged, with

    m_L=floor(delta V/alpha_L),  delta>0 fixed.

The relative entropy is exactly

    D_L=(e_L/tau)m_L - log(1-exp(-e_L/tau)).

Since m_L=O(L²), e_L=O(L^-1), D_L=O(L)+O(log L)=o(V). Relative entropy adds under tensor products, so this is the full relative entropy of the altered state. Its physical occupation in this mode is alpha_L m_L+v_L². The reference occupation is alpha_L/(exp(e_L/tau)-1)+v_L²=O(L²). Hence their particle-occupation difference divided by V tends to delta. The added mass is invisible to every fixed annular test and escapes toward p=0.

There is no contradiction with the annular tilt lemma: the stable positive tilt interval for a*a degenerates at low momentum. From E_ell²=e²-2e alpha ell+ell², the first positive instability occurs at

    ell_c=e(alpha-sqrt(alpha²-1)) = |p|².

The equality uses e*alpha=|p|²+1 and e²(alpha²-1)=1.

A common positive occupation tilt over every nonzero mode must therefore vanish like L^-2. Dividing a merely o(V) entropy error by that tilt loses the desired conclusion. Number-conserving hard-core admissibility is not claimed for this Fock-space diagnostic.

## Exact unpaid operations and bounded disposition

A proof of the full thermal occupation law would need at least:

1. A sharp thermal comparison for the exact hard-core Gibbs state that retains occupation information, for example a suitably uniform signed one-body-field free-energy comparison or a local relative-entropy statement. Scalar free energy is not enough. The hard-core thermal upper construction must also be supplied if this route uses matching free energies.
2. A thermal counterpart of the source's long-wavelength deletion/RMS estimate, strong enough to make the mass of P_R-P_0 vanish in the iterated limits. The relative-entropy-density comparison in item1 does not pay it, as the explicit single-mode construction shows.
3. Ultraviolet tightness and passage from local cosine observations to global Fourier observations, with the same arbitrary bounded-continuous tests and no hidden fixed-volume-first limit.

No construction closing these operations was obtained. The effective-model computations delimit the route; they do not establish an obstruction to the actual gas. This remains a pre-freeze, non-counting feasibility screen, with the full proposed thermal law unproved. The all-tau scope was not replaced by an annular or low-temperature surrogate.
