# Approximate neutral atomic states: adaptive conditional comparison

Author: Myeongjin Kang. Original prose: CC BY 4.0. No affiliation.
Status: author proof submitted for independent checking; no gate or count claimed.
Pinned source truth: OpenAI math repository fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, family 263. Source receipts are in `263-source-receipts.json`; source copies are private third-party material. Assistance from the parent on the IMS and neutral tail identities is author-side assistance, not independent review.

## Exact target

Let Z_l and m_l be positive integers, m_l<Z_l, with m_l→∞ and Z_l/m_l→∞. On the fermionic sector ∧^{Z_l}L²(R³;C²), with kinetic convention −Δ/2, let Ψ_l be any normalized form-domain state of

H_{Z,N}=Σ_i(−Δ_i/2−Z/|x_i|)+Σ_{i<j}|x_i−x_j|^{-1}.

Let q_{Z,N} denote the closed Hamiltonian quadratic form; all energies below are form values, without requiring operator-domain membership. Write δ_l=q_{Z_l,Z_l}[Ψ_l]−E_{Z_l}(Z_l)≥0 and assume only δ_l=o(m_l^{7/3}). Denote its ordinary one-particle density by ρ_l, of exact mass Z_l. Then, for every a>0,

m_l^{-1}∫_{|x|>a m_l^{-1/3}}ρ_l(x)dx → (81π²/2)a^{-3}.

Consequently, with R_m(Ψ)=inf{r≥0:∫_{|x|>r}ρ_Ψ≤m},

m_l^{1/3}R_{m_l}(Ψ_l)→(81π²/2)^{1/3}.

There is no eigenstate, spatial symmetry, gap, prescribed speed of the little-o, or relation between the speeds Z/m→∞ and δ/m^{7/3}→0. Fermionic antisymmetry is retained. This is an expected-density statement, not a particle-count law of large numbers. No assertion of novelty to the literature is made.

## Source contracts and notation

F is *Uniform excess charge for Coulomb molecules and the outer radius of neutral atoms*, E is *Generalized ionization energies for full Coulomb atoms*, and R is *Generalized outer-electron radii of neutral Coulomb atoms*. All refer to the pinned September 24, 2026 manuscripts.

F's neutral bounded-offset input (also R §2) gives E_Z(Z)≤E_Z+C, where E_Z=inf_n E_Z(n). Set D=δ+C+1, s=m^{-1/3}, e=Ds^7, λ=Zs³. Thus e→0, λ→∞, and q_{Z,Z}[Ψ]≤E_Z+D. Constants may depend on fixed geometric/accuracy parameters but not on Z,D,r or the particle number.

The following operative source facts are used, rather than a blanket extension of an eigenstate result.

* E §2 `lem:local-field-input`, `eq:annular-count`, and F §4 `screen-local`: for every normalized finite-sector form-domain D-state, a_y=|y|/L, L=10^5, J_y=Z/|y|−Σ_{|x_i−y|≥40a_y}|x_i−y|^{-1},
  (E J_y)_+≤C[max(a_y^{-3},1)+√(Da_y)]/a_y,
  and the raw count in any fixed annulus [c r,C r] has L² norm at most C(max(r^{-3},1)+√(Dr)). The corresponding conditional field estimate for an allowed fresh square cut has the same bound. These are arbitrary-offset form-state estimates, not eigenstate estimates.
* F's global density bound, for n≤3Z: ∫ρ^{5/3}≤C(Z^{7/3}+D).
* F §5, the observation likelihood construction and score estimate: unordered independently blurred arrays at geometrically increasing widths ℓ_j=r_j^{1.01} give, for any event likelihood a(x), |∇a|≤Cℓ_j^{-1}a log^{5/2}(exp(1)/a), also with a replaced by 1−a. The constant is independent of n and the number of arrays. Conditional densities have simultaneous continuous versions and the tower property.
* E §3, the fresh-cut localization, fine-patch energy comparison, Coulomb duality, and two-posterior potential identity. Their only use of the eigenstate property is the preceding event-energy bound. At price zero every core slice and every packet-insertion trial has energy at least E_Z. The actual patch error budget is reproduced below.
* E §4, the weak maximum construction of a positive conditional barrier. Its algebraic open-cover construction only needs the two inverse implications, cap, tower, and a quantified error mass. Those hypotheses will be supplied anew.
* R §4, neutral compactness, positive-barrier transfer, and dilation rigidity. The proof only uses a scaled error mass tending to zero; the particular source bound s³ is dispensable. The one-line modification of that bound is stated below.

The construction below supplies the unpaid interfaces: arbitrary-state event cost, adaptive simultaneous comparison, summable bad-band error from nuclear to observation scale, and an exterior tail estimate allowing D→∞.

## 1. Observation events for a form-domain state

Let A belong to the observations at levels j and above, p=P(A)>0, a(x)=P(A|x), and Ψ_A=√(a/p)Ψ. The likelihood is symmetric, so Ψ_A is antisymmetric. Apply the IMS identity with f=√a and g=√(1−a). Bounded-Lipschitz approximation, followed by the integrable score bounds below, justifies it in the form domain. Since every normalized state in this sector has energy at least E_Z,

p(q_{Z,Z}[Ψ_A]−E_Z)≤D+(1/8)∫ |∇a|²/[a(1−a)] |Ψ|².

For a≤1/2 the score bound makes the integrand ≤Cℓ_j^{-2}a log^5(exp(1)/a). For a≥1/2, the complement bound makes it ≤Cℓ_j^{-2}(1−a)log^5(exp(1)/(1−a))≤Cℓ_j^{-2}a. The endpoints have the limiting interpretation. Finally

E[a log^5(exp(1)/a)]≤C p log^5(exp(1)/p).

For example, under the probability a|Ψ|²/p, P(log(p/a)>t)≤e^{-t}; integrate its fifth moment and use log(exp(1)/a)≤log(exp(1)/p)+(log(p/a))_+. Thus

q_{Z,Z}[Ψ_A]≤E_Z+D/p+Cℓ_j^{-2}log^5(exp(1)/p).                 (1)

The localization term is not divided by p a second time. This is the required replacement for the ground-state multiplier identity. It is uniform in n, Z, D and the number of arrays.

## 2. Adaptive master packets

Fix a sufficiently small universal ε as in E's barrier initialization. Put r_0=εZ^{-1/3}, r_j=2^j r_0, J=max{j:r_j≤s}, and use observation widths ℓ_j=r_j^{1.01} for j<J. Eventually J≥1. The sigma-fields F_j decrease, and F_J is trivial.

Set

A=99/100, b=1/10000, w=1/100000,
T(r)=max(r^w,(Dr^7)^b) for r≤s.

For d_hat=max(|x|,r_0), choose the master width

t_x=c_1 d_hat T(min(d_hat,s)),

with sufficiently small fixed c_1>0. Here T(s)→0. The width is Lipschitz with constant at most Cc_1 T(s), since the logarithmic slopes of the two branches are w and 7b. It has positive minimum c_1r_0T(r_0). It need not be differentiable at the branch transition: Lipschitz regularity is sufficient in all kernel-center tests. Let K_x(y)=g_{t_x}(y−x)² with the source radial normalized g, and

μ_j(y)=E[Σ_iK_{x_i}(y)|F_j],   H_j(y)=Z/|y|−K*μ_j(y).

They have exact mass Z, tower identities, ΔH_j=−4πZδ_0+4πμ_j, and the fixed-system regularity of E §3. On a fixed enlarged annulus r/2≤|y|≤8Mr, r=r_j≤s, a_y∼r, t_y/a_y∼T(r), with fixed comparison factors. In particular

T(r)≥r^w, T(r)≥(Dr^7)^b, T(r)≤C_M T(s)→0.             (2)

The master kernel has approximate mass 1+O(T(s)); its bound and Lipschitz bound are Ct^{-3}, Ct^{-4}. The fine patch width remains a_y^{1.2}. Thus fine width ≪ observation width ≪ master width ≪ a_y uniformly in j. None of these scales assumes a rate for e→0.

## 3. Simultaneous inverse comparison with a weighted failure bound

For any fixed M≥2, positive height band h_l<h_h, and 0<ξ<h_l/16, there is an event G_j∈F_j such that the source inverse implications and universal field cap hold for r≤|y|≤4Mr:

|y|^4H_j≤C_cap;
|y|^6μ_j>k h^{3/2} ⇒ |y|^4H_j≥h−ξ;
|y|^6μ_j<k h^{3/2} ⇒ |y|^4H_j≤h+ξ,

for every h∈[h_l,h_h], k=2^{3/2}/(3π²). Its failure probability is

P(G_j^c)≤C[(Dr^7)^α+r^η],
α=A−15b=1977/2000=0.9885, η=40−15w.                  (3)

This statement holds simultaneously for every j<J in sufficiently far systems. Its threshold may depend on the displayed fixed parameters.

Here are the altered estimates in E §3 proving (3). Write u=Dr^7 and θ=C(u^{1−A}+r^{.02}). Any event of probability p≥u^A+r^{40} has, by (1), tilted offset

D_A a_y^7≤C[u^{1−A}+r^{4.98}log^5(exp(1)/r^{40})]≤θ.       (4)

All appearances of the source shifted and unshifted offsets can therefore be replaced by this same bound at price zero. In particular the tilted annular count is O(r^{-3}) uniformly, and the observed-count argument of E §3 gives a retained event C_j with failure at most u^A+r^{40}, on which

μ_j≤Cr^{-6}T(r)^{-3}, |∇μ_j|≤Cr^{-7}T(r)^{-4}.         (5)

For the universal cap, condition on {|y|^4H_j(y)>C+t}. Radial packet averaging outside the local exclusion ball and the trivial-data screening bound give

C+t≤C_0+C√(u/p)+Cr^{2.49}log^{5/2}(exp(1)/p).

Choose C>C_0+2. Splitting the last two terms shows

p≤C'u/(1+t)²+C'exp(−c r^{-0.996}(1+t)^{2/5}).

Integrating in t≥0 yields E(|y|^4H_j−C)_+≤C(u+r^P) for any fixed P. The source subharmonic mean argument on balls of radius |y|/10 then gives a universal simultaneous cap on the enlarged annulus outside probability C(u+r^{40}). There is no spatial-net loss in this step.

For either fixed-point inverse failure, intersect with C_j and condition if its probability is at least u^A+r^{40}. The fresh square cut of E §3, selected at a radius in [5a_y,6a_y], gives E_Q n_o²≤Ca_y^{-6} and E_Q n_del²≤C a_y^{.2}a_y^{-6}. Its conditional core field envelope has L² norm ≤Ca_y^{-4}, by (4) and the allowed-cut screening estimate. The exact lower/upper energy comparison at price zero is

E_Q[D_C(σ−ρ)+∫W_-σ]
 ≤D_A+C[√β a_y^{-7}+b_f^{-1}a_y^{-3}+b_f^{-2}(a_y^{-4}+a_y^{-3})]
 ≤Ca_y^{-7}θ,                                                   (6)

where β=a_y^{.2}, b_f=a_y^{1.2}, D_C is the Coulomb quadratic form, ρ=k(W_+)^{3/2} is the patch minimizer, and σ is the fine smear of the retained out particles. In particular ∫_{B(y,4a_y)}ρ_tilt^{5/3}≤Ca_y^{-7}. This follows directly from E's `eq:patch-error-budget` with δ'=D_A and P(0)=E_Z, and its kinetic argument. There is no assumption that the conditional core is in the neutral sector; its lower bound is E_Z.

On the event D_C(σ−ρ)≤a_y^{-7}θ^{1/2}, whose Q-complement has probability O(θ^{1/2}), the normalized master-density error is bounded by

C[r^{.01}T^{-4}+r^{.2}T^{-4}+θ^{1/4}T^{-5/2}+T(s)].    (7)

This tends to zero uniformly in j. For the u term the worst exponent is (1−A)/4−5b/2=.00225>0; for the r term it is .02/4−5w/2>0. The first two terms vanish because .01−4w>0. E's patch oscillation proof is unchanged, with T in place of a_y^w. In the high-density case its control of the negative field on the exceptional patch has relative expectation at most

C[θ T^{-3}+T(s)],                                      (8)

which tends to zero since 1−A−3b>0 and .02−3w>0. In the low case the universal patch upper bound suffices.

The exact two-posterior potential identity of E §3 applies to this tilted form state and fresh cut. Its relative expected error is bounded by

C[T(s)^{1/5}+β^{1/5}+√β+θ^{1/2}T^{-1/2}+T(s)²+(T(s)+√3β)^{1/5}],    (9)

which tends to zero. This uses the local raw-density bound just proved and Coulomb duality, with θ in (6). Thus the same fixed positive separation ξ/4 gives a contradiction. Every fixed-point inverse failure intersected with C_j has probability <u^A+r^{40}.

Finally use a spatial net of mesh c r T(r)^5, with O_M(T(r)^{-15}) points, and the fixed source height net. From (5) the normalized density variation is O(T(r)). The source local-potential/harmonic-gradient proof gives for v(y)=|y|^4H_j(y) the variation over that mesh

|v(z)−v(y)|≤C[T(r)²+T(r)^5 v(y)_-].                    (10)

Its upper form preserves high failures even at arbitrarily negative v, and its lower form preserves low failures (where v>0), exactly as in E's final height-net argument. The union bound is

C[u+r^{40}+T(r)^{-15}(u^A+r^{40})]
 ≤C[u^{A−15b}+r^{40−15w}],

using both lower bounds in (2) separately. This proves (3), with no power loss in the number of particle labels.

## 4. Nuclear initialization and the weighted barrier budget

The initial truncated conditional potential is P_0=K*(1_{d<r_0}μ_0). At a fixed point r_0≤|y|≤1.1r_0, condition on P_0(y)>.05Z/r_0 if its probability is at least u_0^A+r_0^{40}, u_0=Dr_0^7. By (4) the tilted offset is o(r_0^{-7}), hence ≤Z^{7/3} eventually for fixed ε. The global density bound and radial packet averaging give

E[P_0(y)|event]≤CZ^{7/5}r_0^{1/5}=Cε^{6/5}Z/r_0,

contradicting the event for the fixed sufficiently small ε of E §4. The minimum packet width gives |∇P_0|≤CZr_0^{-2}T(r_0)^{-2}. A net of spacing c r_0T(r_0)^3 has O(T(r_0)^{-9}) points and relative interpolation error O(T(r_0)). Thus the initial good event G_0 satisfies P_0≤.1Z/r_0 on that annulus and

P(G_0^c)≤C[u_0^{α_0}+r_0^{η_0}],
α_0=A−9b=.9891, η_0=40−9w.                             (11)

The E §4 initialization with μ_in=1_{G_0}1_{d<r_0}μ_0 and p_0=1_{G_0^c}1_{d<r_0}μ_0 is now literal. Choose its fixed B,C_inv,M and unequal shifts. The resulting u_0 has the stated singular offset and barrier inequalities. The subsequent open-cover max construction, retained-branch checks, and conditional forgetting of E §4 are unchanged, using (3) at its fixed parameters. They yield

Δu_j≥−4πZδ_0+4π1_{d<r_j}μ_j−4πp_j+1_{d≥r_j}4πk(u_j)_+^{3/2},
B d^{-4}(1−r_j/(8d))≤u_j≤C_inv d^{-4} for d≥r_j,
supp p_j⊂{d≤r_j}, p_j≥0.

All fixed-system regularity and simultaneous-test arguments survive because the adaptive width still has positive minimum. Price zero introduces no change to the Laplacian, branch comparisons, or Jensen step.

The important new budget is for the integrated gained mass, not a pointwise density estimate. Let M_j=∫_{r_j≤d<2r_j}μ_j. Each contributing packet has center in a fixed comparable raw annulus, so M_j≤E[N_ann|F_j]. Conditional Jensen and the arbitrary-offset count bound give

||M_j||_2≤Cr_j^{-3}(1+√(Dr_j^7))≤Cr_j^{-3}.

The bad-band indicator is the same across the whole annulus. Therefore (3) and Cauchy–Schwarz give

E∫1_bad1_{r_j≤d<2r_j}μ_j
 ≤C[D^{α/2}r_j^{7α/2−3}+r_j^{η/2−3}].                 (12)

Both exponents of r_j are positive; 7α/2−3=.45975. Summing the geometric sequence and preserving expected mass through conditional averaging yields, for every j≤J,

s³E∫p_j≤C[s³Z(u_0^{α_0}+r_0^{η_0})+e^{α/2}+s^{η/2}]=:B_s→0.      (13)

Indeed r_0=εsλ^{-1/3}, u_0=ε^7 e λ^{-7/3}, and
s³Z u_0^{α_0}=ε^{7α_0}e^{α_0}λ^{1−7α_0/3}→0;
s³Z r_0^{η_0}=ε^{η_0}s^{η_0}λ^{1−η_0/3}→0.

The exponents are negative on λ since α_0>3/7 and η_0>3. This proves the budget for arbitrary independent rates e→0 and λ→∞. No unscaled o(1) error mass is asserted or needed.

## 5. Scaling and identification of the profile

For each fixed q≥2 choose j<J with s/(2q)≤r_j≤s/q. Such j exists eventually because r_0/s→0. Apply (3) at this j with band M large enough to cover [r_j,qs], and with a finite height band and accuracy ensuring

|s^6μ_j(sx)−k(s^4H_j(sx))_+^{3/2}|≤q^{-8}|x|^{-6}

for r_j/s≤|x|≤q, together with the universal cap. To obtain the displayed estimate from the inverse implications, choose heights from a small positive lower height to a height exceeding C_cap+1; the low-height implication bounds density where the field is small or negative, and continuity of h↦kh^{3/2} controls the remaining band. For fixed q all parameters are fixed, (3) tends to zero, and all comparison errors (7)–(10) tend to zero. Markov and (13) additionally retain s³∫p_j≤√B_s except on probability √B_s.

A slow deterministic diagonal q=q_s→∞ gives these assertions on events of probability tending to one, with a_s=r_j/s∈[1/(2q_s),1/q_s]. This diagonal does not impose a rate on the input sequences. Define F_s=s^4H_j(s·), σ_s=s^6μ_j(s·), U_s=s^4u_j(s·), P_s=s^6p_j(s·). Then

F_s=λ/|x|−K*σ_s, ∫σ_s=λ, ΔF_s=−4πλδ_0+4πσ_s;
supp P_s⊂B(0,a_s), ∫P_s≤√B_s→0.

The rescaled barrier inequality and positive bounds have exactly the hypotheses used in R §4. For clarity the only change in its proof is the estimate, for fixed x≠0,

(K*P_s)(x)≤2√B_s/|x|→0,

in place of its bound 2s³/|x|. The additional comparison-error density q_s^{-8}|x|^{-6} on a_s≤|x|≤S has mass O(q_s^{-5}) and potential tending to zero at x. Exact neutrality gives nonnegative spherical means of F_s; together with the cap this bounds its full local L¹ norm. Localized Coulomb potentials and harmonic interior estimates give compactness. Subtracting the two Poisson inequalities and the positive Coulomb correction transfers the barrier by the weak positive-part test on B(0,S). Letting S→∞ gives B|x|^{-4}≤F≤C_cap|x|^{-4}. R's nonradial dilation-contact rigidity then gives

F=A_*|x|^{-4}, A_*=81π²/8,
σ_s→ρ_*(x)=kA_*^{3/2}|x|^{-6}

locally uniformly away from zero, uniformly over all retained data. The source proof of uniformity uses a contradictory choice of one datum at each index; it requires no measurable selection.

## 6. Expected annular masses and an arbitrary-offset exterior tail

For a fixed compact annulus the normalized conditional packet mass has uniformly bounded L² norm: it is bounded by s³ times a conditional raw annular count, and the source estimate gives C(1+√(Ds^7))≤C. Thus discarded data have vanishing expected normalized mass by Cauchy–Schwarz. Uniform convergence on retained data implies convergence of the expected packet annular mass to ∫ρ_* there. The relative master width of every packet near a fixed scaled annulus is O(T(s))→0; squeezing between annuli with slightly expanded/contracted boundaries transfers the same assertion to the ordinary density ρ_Ψ. The limiting density has no boundary-sphere mass.

The source's bounded-offset far-tail summation cannot be used when D grows. The replacement is a neutral spherical identity. For the ordinary screened field H(y)=Z/|y|−K*ρ_Ψ(y), neutrality and Newton's spherical average give

r average_{S²} H(rω)=∫_{|x|>r}(1−r/|x|)ρ_Ψ(x)dx≥(1/2)N_out(2r).

No spatial radiality of ρ is assumed. Since H(y)≤E J_y, the arbitrary-offset local-field bound gives, for 0<r≤1,

N_out(2r)≤C(r^{-3}+√(Dr)).                              (14)

All potentials and spherical integrals are legitimate: the global L^{5/3} density bound and finite total mass make the ordinary potential finite and continuous. At r=Rs, for each fixed R,

s³ N_out(2Rs)≤CR^{-3}+C√e R^{1/2}.

Taking limsup along the sequence, then R→∞, proves the required tightness of the normalized outer mass. Combining it with annular convergence gives, for each a>0,

s³N_out(as)→4πkA_*^{3/2}∫_a^∞r^{-4}dr
 =(4π/3)kA_*^{3/2}a^{-3}=(81π²/2)a^{-3}.

Finally take a_-<(81π²/2)^{1/3}<a_+. The limiting masses at these two radii are respectively greater and less than 1. The continuous nonincreasing outer-mass function (ordinary density is integrable) therefore brackets R_m between a_-s and a_+s for all sufficiently far systems. Let a_± tend to the claimed constant. This proves the full stated target.

## Limits of this submission

This is a source-relative proof proposal requiring independent mathematical, novelty/eligibility, and full-scope review. It does not count itself as accepted. The new part is the joint adaptive comparison and weighted nuclear-to-outer barrier closure (1)–(13), with the neutral tail (14); the final profile rigidity is explicitly paid by the source and Solovej. No claim of having independently audited the stipulated source theorems is intended. A separate reading ledger and primary comparison will record the precise operative passages read. No Lean proof has yet been produced.
