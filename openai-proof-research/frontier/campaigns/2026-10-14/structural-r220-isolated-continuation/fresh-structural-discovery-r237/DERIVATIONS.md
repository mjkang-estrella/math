# r237 prefreeze derivations

Authorized provenance: Codex / GPT-6 Astra / xhigh / default service tier. Only Source362 at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb; its operative proofs are stipulated true. No theorem is frozen at this stage. No grades or counts assigned.

## D1. Free-wave trace without pointwise field derivatives

Let X:[0,T]→R³ be C¹ and strictly timelike, a=X', and assume q_X=(1−|a|²)^(-1/2)≤P. For any measurable J⊂[0,T], |J|≤I, define Ψ(t,n)=X(t)+tn. At t>0 it is injective: t−|y−X(t)| is strictly increasing, so a given y has at most one root. Its volume Jacobian is t²D₊, D₊=1+n·a>0. Also |Ψ(t,n)−X(0)|≤2t. For g∈C∞∩H¹, Cauchy–Schwarz, change of variables, and translated Hardy give

∫_J∫S² |g(Ψ)| dn dt
≤ (∫_J∫ D₊|g(Ψ)|² dn dt)^(1/2)(∫_J∫D₊^(-1)dn dt)^(1/2)
≤ 4||∇g||₂ (∫_J∫D₊^(-1)dn dt)^(1/2).

Indeed the first squared factor is ∫image |g(y)|²/t(y)² dy ≤4∫ |g(y)|²/|y−X(0)|²dy ≤16||∇g||₂². Similarly

∫_J∫ t|∇g(Ψ)|dn dt ≤ ||∇g||₂ (∫_J∫D₊^(-1)dn dt)^(1/2).

The angular integral is (2π/|a|) log((1+|a|)/(1−|a|)), with continuous limit 4π at a=0. It is ≤C log(2+P). Kirchhoff's formula therefore gives

∫_J (|Efr(t,X(t))|+|Bfr(t,X(t))|)dt
≤ C sqrt(I log(2+P)) (||∇E₀||₂+||∇B₀||₂).

These are the source's homogeneous *wave* fields with velocities curl B₀ and −curl E₀; they need not jointly solve vacuum Maxwell. This proof handles the t=0 endpoint by the Hardy bound, with no discarded boundary term. The path is arbitrary and may be the self-consistent receiver; no acceleration bound is used. For rough fields the formula defines a trace by approximation on a fixed path, but the argument below only applies it to smooth approximants. No trace of an arbitrary L² representative is presumed.

## D2. Uniform source bootstrap interface

For smooth source-admissible data, retain bounds on initial momentum radius Rv, ||f₀||∞, total energy H₀, and ||∇E₀||₂+||∇B₀||₂. The initial retarded boundary term and the signed initial-cone boundary use only f∞, Rv, T. All subsequent occupation, direct, cancellation, direction, selection, and closure estimates use energy, f∞, these boundary bounds and the data-force contribution. Replace its former CI estimate by C sqrt(I log(2+P))+CI≤C'P sqrt(I) for I≤1. The same estimate holds on arbitrary measurable eligible times and against weights in [0,1], so disjoint direction-cell weights incur no extra cell count. Receiver velocity on eligible times is already controlled by q_X≤P. Thus the same bootstrap scales λ, I_m⁰, angular window, selected weights W, and coefficient U are retained; no exponent is altered. Source's compact-interval constants for cutoff removal and continuity are allowed to depend on the individual approximation and do not enter M,A,P₀.

This yields common M,A,P₀(T) for a family with the four stated data bounds, subject to a final dependency audit of all source equations. The source's doubling proof then yields a common finite momentum radius Q_T: choose N with 2^N above initial q and P₀/1024. Each crossing of 2^(n−1) to 2^n costs at least c_T/(n+1), where c_T depends on M,A but not the family index. Summing gives n+2≤(N+2)exp(T/c_T). A larger integer power of two is a valid common Q_T. This is a finite-horizon bound; c_T,N may depend on T and no uniform long-time rate is asserted.

## D3. Exact admissible rough-data approximation

Consider 0≤f₀∈L∞ with compact phase support and E₀,B₀∈H¹(R³), div E₀=∫f₀dv, div B₀=0 in distributions, without background. Set f₀,ε=ηε^x*ηε^v*f₀, E₀,ε=ηε^x*E₀, B₀,ε=ηε^x*B₀ for nonnegative compactly supported unit-mass mollifiers. Integration in v commutes and removes ηε^v, so Gauss is exact. Every field derivative is bounded by convolution L²–L², fields remain L², and f₀,ε is smooth compactly supported. Initial radii increase by at most one; f∞ and H¹ field norms are uniformly bounded. Particle energy converges by compact support; fields converge strongly in H¹. This avoids an incorrect compact cutoff of a charged electric field. Nonempty examples: any nonnegative bounded compact f₀ has ρ₀∈L¹∩L², its Coulomb field E_C=−∇(−Δ)^(-1)ρ₀ lies in H¹ (low Fourier frequencies use ρ̂∞ and ∫|ξ|^(-2)<∞; high frequencies use ρ₀∈L²), and arbitrary divergence-free H¹ additions are allowed. Nonzero total charge is compatible with finite field energy.

## D4. Compactness route under the common support bound

For smooth approximants, D2 gives fε supported in |x|≤Rx+T+1, |v|≤Q_T. Hence fε is bounded in L∞ and L², jε,ρε in L∞ and L², and Fε in L∞_tL²_x. The force-density product Fε fε is uniformly L² on each finite slab. The kinetic equation has divergence-in-v L² right-hand side; the compact-velocity averaging lemma gives local compactness of ∫ψ(v)fεdv in L²_{t,x}. With a fixed ψ≡1 on the common support and the three ψ=u_j, the actual densities and currents converge strongly in L²_{t,x}; spatial support makes this global in x. Maxwell Duhamel and strong initial L² convergence then give Fε→F strongly in C_tL²_x along the subsequence. Consequently Fεfε→Ff distributionally, using strong×weak. Constraints pass. Positivity and support pass weak-star.

To be completed with the exact primary averaging hypotheses and endpoint argument. Uniform total-energy conservation follows if weak convergence of fε(t) is established at every t and q is tested using compact cutoffs equal to one on the support. The transport equation gives an equicontinuous weak pairing for smooth compact tests, with time modulus controlled by the L² force-density bound. Strong C_tL² field convergence then identifies the limiting energy at every t. This supplies a concrete route beyond merely applying the source separately to truncations.

## D5. Present scope distinction

Cheverry–Ibrahim's published Corollary 4.3 and arXiv Corollary 12 have been read. Their statement invokes condition (1.10), ρ(x)=∫f₀(x,v)dv in a system with a prescribed background, and their local construction/uniqueness discussion is not yet a checked no-background coupled uniqueness input. Setting that background to zero while preserving (1.10) forces f₀=0; it does not furnish our charged rough-data class. Their cited transport theorem concerns a fixed Sobolev vector field; nonlinear self-consistent uniqueness requires a separate comparison. This is a compatibility limitation on importing the corollary, not an audit of Source362.

The free trace is closely related to the moving-cone L² operation already present in Pallard/Luk–Strain. A rough-data existence/compactness consequence may be a classical/source composition. No claim of substantial novelty or new-to-literature status is made. A genuinely new closed stability/uniqueness operation remains to be investigated before any nomination.


## D6. Dependency audit and completion of the compactness reduction

This is a derived reduction, not a nominated theorem or a correctness verdict. The following spells out the strongest construction achieved in the selected family.

The initial quantities needed for a common signed bound can be taken as upper bounds on A₀=||f₀||∞, Rv, H₀ and G₀=||∇E₀||₂+||∇B₀||₂, with fixed horizon T. The total mass is at most H₀ since q≥1. Initial spatial radius Rx is needed for the compactness argument below; the force budgets themselves use conserved energy instead. All statements here concern smooth members of the approximating family until a limit is constructed.

The proof-interface audit is as follows.

* `ret:energy` uses finite total energy and positivity. Its cone flux has the sign U−n·S and particle factor q(1−n·u), unchanged. Phase volume, q≥1 and A₀ give the mass and cap-density bounds.
* `ret:phase-change` has dz=d dy dv and `ret:receiver-time` has dt/ds=d/D. The Jacobian in D1 is instead the *initial free-wave* map, t²(1+n·a). They must not be interchanged. The collision null-set argument may use an individual compact momentum bound while deriving each identity; the uniform estimates do not retain that constant.
* `ret:data-bound` is the sole pointwise free-wave input. Replace it by D1 when integrating the data force. The initial boundary is ≤C(A₀,Rv)t, since d₀ is uniformly positive on the fixed initial momentum ball. The `can:weighted-formula` initial boundary is ≤C(A₀,Rv,T)∫|ψ|. No derivative of f₀ is needed in either bound.
* `occ:stability`, `occ:refined-proposition` and the joint budget use only the assumed signed increments, energy and A₀. The cell length λ=[C₁(P/m)(M/ω+sqrt(AL/ω))]⁻², the actual/deficit split and clipped endpoint cells are unchanged. No limiting rough characteristic is used to justify them: they hold on each smooth approximant.
* Every row of `dir:near-far` and the exceptional deficit estimate is unchanged. The sole replacement is ∫eligible|Kdata|≤C sqrt(I log(2+P))+CI≤CP sqrt(I), because I≤1. Thus `dir:baseline` and `dir:absolute`, including its sqrt(w) factor, retain their original parameter dependence.
* The signed primitive k₀/(rd), residuals R and A, receiver acceleration a_t=(Id−a⊗a)K/q_X, source/geometric cutoff cancellation, varying projection, cone entry and cone-tip remainder remain exactly those of the source. In particular no source-acceleration term is silently discarded.
* Direction-cell weights have disjoint interiors. D1 bounds their union at once. It introduces no factor equal to the number of cells. The same L⁶/δ direction count therefore precedes, rather than presupposes, the improved occupation bound in the p,w≥P^.7 angular window.
* The representative selection, W=(Pθ)^−ε φ^ε h^ε, the unsafe-bin contradiction, U≤w^−1/2 W, the h₀ spatial transition and time-ramp derivative estimates are unmodified. D1 is used only on the data term, so all delicate exponents and constants remain the source's paid operations.
* Choose η,M,A,P₀ in the source order. The individual compact-interval force supremum C_* appears only in its open-and-closed bootstrap argument; it is not part of the chosen M,A,P₀. This explicitly permits smooth approximants with unbounded higher norms.

For clarity the translated Hardy estimate in D1 follows by integration by parts, initially away from the origin: div(y/|y|²)=|y|⁻² in three dimensions, so ∫|g|²/|y|²≤2(∫|g|²/|y|²)^(1/2)||∇g||₂. Cutoff/density gives the H¹ version. The angular logarithm is bounded using 1−|a|≥(2P²)⁻¹. Thus all constants in D1 have the required uniformity and the near-light-speed denominator has not been replaced by a fixed subluminal speed independent of P.

Choose n₀ so that 2^n₀ dominates the initial energy radius and P₀/1024. At a first Q(t)=2^n crossing, use P=1024·2^n and w=2^n. The source inequality gives

1/2 ≤1024 M sqrt(Δ_n)+1024² A Δ_n log(2+1024·2^n).

Hence Δ_n≥min{(4096M)⁻²,[4·1024²A log(2+1024·2^n)]⁻¹}≥c_T/(n+1). The disjoint crossings have total duration ≤T, and the harmonic sum bounds n by (n₀+2)e^(T/c_T). Choosing a larger integer power of two gives a common momentum radius Q_T. There is no assertion that this formula is a uniform-in-T asymptotic estimate: both c_T and n₀ are functions of the prescribed horizon.

Here is the compactness argument with the missing endpoint details supplied. Work first on [0,T], with uniform phase cylinder K_T=B(Rx+T+1)×B(Q_T). For any smooth compact phase test φ,

|〈f_n(t)−f_n(s),φ〉|≤C_φ |t−s| + C_φ∫_s^t ||F_n(τ)||₂ dτ.

This follows from the weak transport identity, |u|≤1, the common phase support and f∞ bound. The field energy gives a uniform Lipschitz modulus for this fixed test. A countable dense set of tests and weak compactness produce f_n→f in C_t(L²-weak) along a subsequence; density extends this to every fixed L² test. In particular f(0)=f₀, not merely an unspecified weak trace.

On [δ,T−δ], multiply the kinetic equation by a smooth time cutoff and apply Rein's exact Lemma 1 (H^(1/4) momentum averages for h,g₀,g₁∈L²). Here h=ζ f_n, g₀=ζ' f_n and g₁=−ζ(E_n+u×B_n)f_n. The negative sign is the one in our transport equation. These quantities are uniformly L². Choose velocity test functions equal to 1 and u_j throughout B(Q_T). Rellich gives strong density/current convergence on interior compact time intervals. The common L∞ bound and finite spatial support make the L² norm of either endpoint strip ≤C sqrt(δ); taking δ→0 gives strong convergence on the entire [0,T]×R³. Thus the zero-extension jump at t=0 is never misrepresented as an L² source.

Maxwell's first-order group U(t) is unitary on L², even for nonzero divergence. Therefore

sup_{t≤T}||F_n(t)−F(t)||₂
≤||F₀,n−F₀||₂+sqrt(T)||j_n−j||_{L²([0,T]×R³)}→0.

The nonlinear force passes because F_n is strong in L² spacetime, f_n weak-star in L∞ on a fixed momentum ball, and the test function's v-derivative is smooth. For the part (F_n−F)f_n use L²–L²; for F(f_n−f) use weak convergence with the resulting L¹ or L² compactly supported test, obtained by density. The continuity equation follows by integrating in v with a cutoff identically one on the common support. Both divergence constraints follow by convergence from their exact initial versions and Maxwell evolution. All these statements are for the self-consistent limit fields, not externally prescribed fields.

Since a compact test equals q(v) on K_T, weak convergence at each time implies convergence of the particle energy. Strong C_tL² convergence of fields and convergence of initial energies then give the exact total energy identity for every time. Particle mass is likewise preserved. This already improves the generic weak-limit energy inequality; the mechanism is compact momentum support and strong Maxwell convergence, not a lower-semicontinuity assertion promoted to equality.

## D7. Nonresonant smoothing, renormalization and strong subsequential convergence

The following is the precise additional classical operation, read in Bouchut–Golse–Pallard 2004, Theorem 1 and its full elliptic-symbol proof, plus its Section 3 kinetic Maxwell representation. It must not be confused with ordinary averaging of f. Let U(t,x,v) solve □U=f with zero wave data. Its transport identity is T_v^+ f=∑_i∂_{v_i}g_i, with g_i=−(E+u×B)_i f∈L². For χ supported in a fixed momentum ball, the nonresonant theorem gives ∫χ(v)U dv∈H²_loc in spacetime. Indeed choose λ=(1+v_M²)/2, v_M=sup_suppχ|u|<1. The symbol

q_v^λ(τ,ξ)=(1−λ)τ²+λ|ξ|²−(u(v)·ξ)²

is ≥(1−v_M²)(τ²+|ξ|²)/2. Its v-derivatives retain order two. Solving wave equations for g_i and for the initial f trace, using their energy estimates, and integrating v derivatives onto χ/q_v^λ gives the H² bound. This is precisely the primary proof's operation; its constants depend on Q_T. They are uniform in n because Q_T is already uniform, not because the nonresonant gap remains positive as Q→∞.

Maxwell fields are first derivatives of the moments with χ=1,u_j on the support, plus the homogeneous wave part. The latter is in H¹ in spacetime on each finite slab for H¹ initial E,B, by the Fourier wave formula. Thus the fields have local H¹ regularity away from the initial time, with uniform bounds for smooth approximants. The nonlinear source is put inside the L² vector g; no smoothness of E or B is asserted for a coefficient of the differential operator ∂_v.

To include t=0 without assuming a nonexistent H¹ trace from an interior-only theorem, use the equation's actual time reversal: f^rev(t,x,v)=f(−t,x,−v), E^rev(t,x)=E(−t,x), B^rev(t,x)=−B(−t,x). The same positive-species equations and constraints result. Apply Source362 and D1–D2 to the reversed smooth data. Each approximant therefore exists on all real times with common compact phase support and energy bounds on [−3T,3T]. Apply the nonresonant estimate first to this reversed solution on [T,2T]; averaging gives a time s_n∈[−2T,−T] for which ||F_n(s_n)||_{H¹} is uniformly bounded. These times may vary with n; this is harmless. Restart the *linear wave representation* at s_n, whose distance from [−T/2,T] is bounded below by T/2. The same nonresonant estimates now give a uniform H¹ bound across t=0. All needed f_n(s_n) L² bounds are supplied by phase-volume preservation. The common finite spatial support of the potential-source part and finite wave speed turn the local spatial bounds into global spatial bounds; the homogeneous part already has global H¹ bounds. Consequently F_n is bounded in H¹ on every finite spacetime slab, with constants depending on that slab. This argument is a regularity estimate, not a new existence/continuation step.

For the limit b(t,x,v)=(u(v),E(t,x)+u(v)×B(t,x)), local H¹ field regularity gives b∈L¹_t W^{1,1}_loc in phase space (in fact local W^{1,2}), and div_{x,v}b=0. The commutator proof in DiPerna–Lions Theorem II.1 applies on every compact phase cylinder. Because f has a common compact phase support on each finite time slab, local renormalization suffices; no global growth hypothesis for b on all unbounded momenta is silently assumed. If f_ε is its phase mollification, the equation has a commutator r_ε→0 in L¹_tL¹_loc. Integrating β(f_ε) against a cutoff equal to one on the slightly enlarged support, and letting ε→0, yields

∂_t β(f)+div_{x,v}(b β(f))=0

for C¹ β with β(0)=0, with derivative bounded on the range 0≤f≤A₀. The initial trace is β(f₀): integrate the mollified identity from 0 using f_ε(0)=η_ε*f₀, then use commutator convergence on a slab containing 0. This explicitly addresses the trace, rather than deriving it from weak convergence of β(f_n).

Take β(s)=s² on [0,A₀]. It gives ||f(t)||₂=||f₀||₂ at every t after choosing the weakly continuous representative. Weak continuity and conservation of this Hilbert norm imply strong L² continuity. The same cutoff argument yields every bounded-range Casimir and all finite Lp norms, with strong C_tLp continuity by interpolation and common support. These are properties of each subsequential solution, not a comparison between two different self-consistent fields.

For a sequence of admissible rough data converging strongly in L¹ with a common L∞ bound and common phase support, and fields converging in H¹ with exact constraints, mollification plus the preceding bounds gives subsequential compactness. For the constructed smooth approximants, strong L² convergence of f₀,n follows from L¹ convergence and the common L∞ bound. Weak convergence f_n(t)⇀f(t) is uniform in t when tested against any fixed L² function. The compact set f([0,T])⊂L² has a finite ε-net, so that convergence is also uniform against the moving test f(t). The polarization identity and equality of the f_n and f L² norms then prove

sup_{t≤T}||f_n(t)−f(t)||₂→0.

Interpolation gives the same conclusion for each finite p, and the already proved field convergence is in C_tL². This is a strong *subsequential* compactness conclusion, not an approximation-independent solution map. No subsequence has been promoted to the whole sequence by invoking fixed-field transport uniqueness.

## D8. Attempts to close a coupled quantitative comparison

For two smooth solutions, g=f₁−f₂ and ΔF=F₁−F₂ satisfy

T₁g=−(ΔE+u×ΔB)·∇_v f₂,

and Maxwell energy is forced by Δj. At common momentum radius Q, ||Δj||₂≤C_Q||g||₂. Pairing with g gives

d/dt (||g||₂²+||ΔF||₂²)
≤C_Q(1+||∇_v f₂||∞)(||g||₂²+||ΔF||₂²).

This is valid with its displayed coefficient, and it yields uniqueness/stability against a smooth reference. It is not uniform in the admitted rough-data family. The failure of that inference is concrete: choose nonnegative smooth compact a(x), a smooth compact b(v) strictly positive on a smaller ball, and φ supported in that smaller ball. Set h_k(v)=∂_{v₁}[k⁻¹φ(v)sin(kv₁)]. Its v integral is exactly zero, ||h_k||∞ is uniformly bounded, and ||∇_v h_k||∞ grows along a sequence like k. For a fixed sufficiently small ε>0, f₀,k=a(x)(b(v)+ε h_k(v)) is nonnegative with common phase support, bounded f∞ and energy. Every datum has exactly the same density a∫b, so the same Coulomb E₀ and B₀=0 meet Gauss and have a common H¹ bound. Thus no hidden charge constraint controls the missing kinetic derivative. This is a test of a proposed estimate, not an example of nonuniqueness.

Integrating the right-hand side by parts in v only transfers the missing derivative to g. Changing to a negative Sobolev norm introduces commutators with the field; H¹ spatial regularity alone does not supply a Lipschitz coefficient for those commutators. The linear DiPerna–Lions theorem compares solutions for one prescribed b, and consequently cannot remove the inhomogeneous term generated by ΔF.

A characteristic comparison was also carried through its available bounds. For a smooth common initial density, let Z_i=(X_i,V_i) be the two measure-preserving flows and put

D_δ(t)=∫ f₀(z) log(1+|Z₁(t,z)−Z₂(t,z)|/δ) dz.

On a common compact phase region, the Sobolev maximal-function estimate and change of variables in each flow give

D_δ(t)≤C∫₀ᵗ(1+||F₁(s)||_{H¹})ds + C δ⁻¹∫₀ᵗ||ΔF(s)||₂ds,

when the initial flows agree. The constants use f∞, the phase support and mass. The first term comes from |b₁(Z₁)−b₁(Z₂)| divided by δ+|Z₁−Z₂|; the second uses bounded spatial density of the second flow and Cauchy–Schwarz. For identical prescribed fields, letting δ→0 gives the familiar uniqueness mechanism. For coupled fields, Maxwell gives only ||ΔF(t)||₂≤||ΔF₀||₂+∫₀ᵗ||Δj(s)||₂ds. No estimate proved here closes these two displays with an Osgood modulus.

The missing current comparison is not an automatic consequence of a small transport distance. Choose a compact spatial bump a and a compact momentum profile b with nonzero mean current. Define f_k=a(x)(1+εsin(kx₁))b(v), and let g_k be its spatial translate by π/k. The translation is a coupling with mean squared displacement O(k⁻²), whereas ||j_{f_k}−j_{g_k}||₂ stays bounded below along large k (the bump-translation error tends to zero; the oscillatory sine term has nonzero L² limit). Both are nonnegative and have common support bounds. Their Coulomb initial fields satisfy the exact constraints and have uniformly bounded H¹ norms. Thus a universal instantaneous current-L² modulus based only on transport distance and the admitted norm bounds cannot be used. Spacetime nonresonant averaging may improve this, so this example is not an impossibility theorem for a stronger coupled argument.

Interpolation is another concrete available route, but the elementary version does not reach uniqueness. For any s>5/2, transport distance controls Δj in H^{−s}_x against C¹ tests, while the actual averaging lemma gives a uniform H^{1/4}_{t,x} bound away from endpoints. Interpolating produces a fractional power, with exponent θ=1/(4s+1), in an L² spacetime current estimate. It does not give an Osgood modulus: replacing a linear quantity by its θ-power, 0<θ<1, leads to a differential comparison whose reciprocal modulus is integrable at zero. This diagnoses precisely what this interpolation route loses; it does not rule out a different use of the signed or nonresonant structure.

## D9. Strongest-reduction comparison and remaining scope

D1 is an endpoint H¹, short-measurable-time version of the moving-cone method. Its ingredients are not unaccounted-for primary operations: Luk–Strain Proposition 5.2 proves the logarithmic cone-Jacobian estimate; Cheverry–Ibrahim arXiv Lemma 18 / published Lemma 4.9 executes the free-field trace for W^{1,p}, p>3/2; Hardy handles the undifferentiated initial-field term here. Their p<2 formula has P^(4/p−2) I^(2−3/p) behavior near the initial endpoint, rather than the sqrt(I log P) behavior used above. Substituting that lower-regularity exponent into the source's sqrt(I) bootstrap is not justified. We did not claim a W^{1,p}, p<2 extension or change the source's stable-cell lengths to conceal this issue.

D2–D7 integrate those primary operations with *all* the source's internal estimates, and then with Rein averaging, Bouchut–Golse–Pallard nonresonant smoothing and the DiPerna–Lions commutator. They provide a durable route to global rough solutions with bounded phase support on every finite slab, exact energy/Casimir conservation and strong subsequential compactness. Those deductions have not received independent review and are not being submitted as a substantial-contribution nominee. They do not provide an approximation-independent solution map, a closed nonlinear uniqueness proof, a uniform quantitative comparison for the entire rough class, or a long-time asymptotic theorem.

The investigated stronger objective is global well-posedness/quantitative stability in the no-background class 0≤f₀∈L∞ with compact phase support and E₀,B₀∈H¹ satisfying Gauss. It remains prefreeze: no exact theorem statement was frozen, and no weaker scope has been substituted for a frozen target. The currently unpaid operation is a coupled comparison that controls the force/current feedback without kinetic derivatives and without assuming the fields already coincide. It must distinguish strong subsequential compactness from whole-sequence stability and must use the actual nonresonant/retarded structure with uniform finite-horizon momentum control. Neither an old open-problem statement nor an inaccessible reference is used as evidence of novelty. No exhaustion, worldwide-priority, correctness, contribution, acceptance or count claim is made.
