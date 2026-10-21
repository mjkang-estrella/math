# r171 prefreeze calculations: full cones and finite-group realization

PREFREEZE. No theorem nominee is frozen in this file. These are durable feasibility calculations and source/primary compositions, not an author-proof submission. Source301 and every operative upstream proof at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true. Provenance: Codex / GPT-6 Astra / high / default service tier. Only the parent integrates or assigns dispositions and counts.

## 1. The interface actually supplied by Source301

Write P=A⊗W⊗K and Q=B⊗W⊗K for separable nuclear complex C*-algebras A,B. T(P) means all extended lower-semicontinuous tracial weights, including zero, weights finite only on proper ideals, and purely infinite-valued ideal weights. It is not the bounded trace space or the cone of densely defined traces. The topology is the cut topology: for a≥0 and ε>0, convergence imposes

    limsup_i τ_i((a−ε)+) ≤ τ(a) ≤ liminf_i τ_i(a).

The source's prescribed map is F:T(Q)→T(P), continuous, additive, positively homogeneous, and a cone homeomorphism. It is contravariant: a realizing Φ:P→Q satisfies T(Φ)(τ)=τ∘Φ=F(τ). Its Cuntz-semigroup map G:Cu(P)→Cu(Q) satisfies

    d_τ(G(x)) = d_{F(τ)}(x).

The realification identification uses Robert's L(T), with its increasing, rapidly approximable functions and finite-locus continuity; arbitrary lower-semicontinuous functions are not substituted. Scalar limits of weights recover finite-domain and kernel ideals. Infinite weights therefore carry structural information even when bounded traces see nothing. A cone isomorphism transports this information and the full ideal lattice, including quotients with no finite traces. These are already source conclusions.

The source's full proof was read, not just its abstract. Its mechanisms matter to the following applications:

* Compact ideal controllers: V≪U has a controller b_(V,U), and the finite tested elements compactly supported in V are dominated by finite multiples of that controller. Multiplicities can grow with the stage; coordinates are delayed after the relevant multiplicities and cuts have been fixed.
* Sequence models take values in Q∞=ℓ∞(Q)/c₀(Q). A regularized limit weight is ρ(x)=sup_(ε>0) lim_ω τ_n((x_n−ε)+). The trace sequences can themselves be unbounded or infinite. The model equalities quantify over these weights, not just constant bounded traces.
* A fixed cut a≼(b−δ)+ has a comparison witness with squared norm at most (||a||+η)/δ. This uniformity, rather than a bound on changing matrix sizes, makes coordinate comparisons usable. Strict rank comparison in Q∞ is obtained by separation with normalized coordinate weights.
* The local error ideals J(U) are defined using rank errors r_n d_τ(c), where r_n→0 and c is a fixed compact controller. Membership in J(U) is not norm smallness. Such errors disappear for regularized weights densely finite on the relevant ideal, but infinite-weight behavior still needs a separate positive signal.
* The small-stabilizer mechanism takes slowly vanishing UHF fractions, after finite multiplicities and cuts have been selected, and dominates countably many local error coefficients. The no-model version first constructs cone maps using quotient-cone quasidiagonality and positive plateau witnesses. It does not assume an already existing model to prove existence of that model.
* Norm uniqueness first aligns finitely many weights on compact trace caps. The bounded-rank cut estimate makes the needed evaluations continuous; barycenters and rational normalized averages turn separation into local J-errors. Ideal-related absorption and multiplier stable uniqueness absorb these errors using a spare model. Splitting the original models into two UHF halves supplies the spare. The conclusion is coordinate multiplier-unitary norm uniqueness, not merely 2-norm agreement.
* Tracial cone correction keeps two distinct requirements: moments on densely finite ideals, and a lower ideal-generation signal. On a quotient where a weight is infinite, positive signal inequalities retain that part of the cone. A typical support estimate bounds d_τ((y−ε)+) by a fixed scalar multiple of a cut rank of the averaged signal; it is independent of the number of matrix summands.
* The Stinespring correction must retain fine ideal labels on the complete projected support. Scaling the cone variable is not fine-label preserving on its own. A second stabilizer dominates the corrected-minus-rough map while keeping the lower signal. Thus agreement on the finite ideal is promoted to agreement on the whole extended weight, with no finite-domain density assumption.
* The point step uses one translation on a line model. In C₀(R)⋊Z, its corner projection p has a finite positive partition with Σ y_i* y_i=p⊗a and Σ y_i y_i*=ζ²⊗a. This proves equality of extended traces even at infinity, without subtracting infinite values. All-pairs late-coordinate uniqueness and a summable conjugacy construction then give an actual map. A two-sided intertwining gives an isomorphism realizing the prescribed F.

The exact labels used here are st:realification, st:ideals, st:controllers, st:folding; seq:regularized, seq:uniform-witness, seq:strict-comparison, seq:sandwich, seq:diagonal; sm:stabilizers, sm:coefficient-domination; un:uniqueness, un:trace-cap, un:barycenter, un:absorption, un:stable-uniqueness, un:spare; and pt:corner, pt:point-model, pt:actual-map, pt:intertwining. The complete local source includes, their hashes, and reading extents are in private/.

In particular, when two actual isomorphisms P→Q have the same pullback on the whole trace cone, their constant sequences are equal-data point models. Source norm uniqueness applies. For a variable coordinate trace sequence, equality is retained on every functional-calculus cut before taking the ultralimit, so this use does not silently weaken the definition of a model.

## 2. Why independently choosing lifts is insufficient by itself

Let G be finite, |G|=m, and prescribe cone automorphisms F_g of T(P) with

    F_1=id,  F_(gh)=F_h∘F_g.

This is the pullback convention for an honest action g↦α_g. Source existence gives automorphisms a_g of P with T(a_g)=F_g, choosing a_1=id. It supplies no equations a_g a_h=a_(gh).

For finite tests one can use source uniqueness to choose multipliers u_(g,h) so that a_g a_h≈Ad(u_(g,h))a_(gh). On sufficiently enlarged tests, the two parenthesizations of a_g a_h a_k differ by the associator

    L=a_g(u_(h,k))u_(g,hk),   R=u_(g,h)u_(gh,k).

The resulting estimate says R*L approximately commutes with the tested image of a_(ghk). It does not say ||R*L−1|| is small, nor that R*L is scalar. Hence an anomalous action with a scalar 3-cocycle cannot be inferred from these implementers on a nonsimple algebra. However, this is not the final obstruction: the following direct construction avoids composing the chosen a_g.

## 3. An exact finite-group inductive system

For each n≥0 put

    C_n = ⊕_(g∈G) M_(m^n)(P).

Label its matrix coordinates by G^n (the zero-fold matrix algebra is C). Use a new leftmost matrix coordinate at each step. Define the injective *-homomorphism φ_n:C_n→C_(n+1) by

    (φ_n(x))_g = diag_(h∈G) a_(g⁻¹h)^(m^n)(x_h).

Here a_r acts entrywise on the old matrix coordinates. The map is a block diagonal *-homomorphism. Its norm is max_h||x_h||, since every a_r is an automorphism. No approximate multiplicativity or group law for a_r is required.

Let λ_k be left translation on ℓ²(G), and define

    (β_k^(n)(x))_g = Ad(λ_k^⊗n)(x_(k⁻¹g)).

This is an honest action on C_n. Direct calculation gives exact equivariance of every connecting map. At outer coordinate g and new diagonal coordinate h, both β_k^(n+1)φ_n(x) and φ_nβ_k^(n)(x) have the old-matrix block

    a_(g⁻¹h)^(m^n)(Ad(λ_k^⊗n)(x_(k⁻¹h))).

For the first expression, this is obtained by replacing g,h by k⁻¹g,k⁻¹h in φ_n; their relative displacement is still g⁻¹h. Entrywise automorphisms commute with permutation matrices. Consequently L=lim(C_n,φ_n) carries an exact action β of G. It is separable and nuclear.

This step is the essential compatibility calculation. It should not be replaced by a claim that approximate lift multiplication automatically corrects to exact multiplication. The construction uses the chosen lifts only on single relative displacements; it never imposes relations on their compositions.

## 4. Recovering the entire trace cone of the limit

Use the unnormalized matrix-trace identification T(C_n)=T(P)^G. If τ=(τ_g), direct evaluation of a positive block gives

    (Tφ_n(τ))_h = Σ_g F_(g⁻¹h)(τ_g)
                  = F_h(Σ_g F_(g⁻¹)(τ_g)).                       (1)

All expressions are finite sums of extended weights; no subtraction or division of infinite values occurs. Multiplication by 1/m is positive scalar multiplication and is defined at infinity.

Define continuous cone maps

    j(σ)_h = F_h(σ),
    r(τ) = (1/m) Σ_g F_(g⁻¹)(τ_g),
    E = j r.

Then rj=id, because F_(g⁻¹)F_g=id and the sum has m identical terms. Thus E²=E. Equation (1) is

    Tφ_n = m E.                                                 (2)

For a compatible inverse-limit sequence (τ_n), equation (2) forces Eτ_n=τ_n at EVERY stage. Write τ_n=j(σ_n), where σ_n=rτ_n. Compatibility becomes σ_n=mσ_(n+1). It follows that

    τ_n = m^(−n) j(σ_0).                                       (3)

Conversely (3) defines a compatible sequence for each σ_0∈T(P). Thus the inverse limit is topologically isomorphic to T(P): one direction is the continuous coordinate formula (3), and the inverse is r at coordinate zero. There is no compactness argument hiding a loss of finite or infinite weights, and no cancellation law for the cone is used.

The continuity interface is Elliott–Robert–Santiago, arXiv:0805.3122v2, Theorem 4.8 and its actual proof: Cu inductive limits give inverse limits of their functional cones. The nuclear exact case identifies these functionals with all extended lsc traces. Source/Robert realification is compatible with this identification. The direct-sum and matrix identifications above can also be checked on positive elements and their cuts, so they respect this topology.

The induced action on cone coordinates satisfies

    (Tβ_k^(n)(τ))_h = τ_(kh),
    Tβ_k^(n)(jσ)_h = F_(kh)(σ)=F_h(F_kσ).

Therefore the identification (3) conjugates Tβ_k to the prescribed F_k. The original cone action is recovered, not averaged away: E projects the product cone onto the twisted diagonal j(T(P)), not onto the fixed cone of G.

## 5. Returning to the prescribed algebra and obtaining Rokhlin towers

Do not assume L itself is W-stable or stable merely because its building blocks are. Instead form

    R = L ⊗ U ⊗ W ⊗ K,
    U = ⊗_(n≥1) M_m,
    μ_k = ⊗_(n≥1) Ad(λ_k).

For the trivial group, take U=C. The full trace cone of U tensoring is canonically unchanged, using its normalized trace and the inverse system of unnormalized finite matrix traces. W tensoring and K stabilization have the full-cone identifications supplied by Source301/Robert. In particular T(R) is naturally isomorphic to T(P). None of these statements is restricted to normalized traces on R.

The product action β⊗μ⊗id_W⊗id_K induces F on this cone. The μ factor has exact Rokhlin towers in successive tensor factors: the rank-one diagonal projections p_h are permuted by λ_k and sum to 1. Move these projections beyond any finite tensor test. In the nonunital product, multiply by a G-invariant approximate unit from the other factors. The resulting positive contractions are central, mutually orthogonal and idempotent modulo the annihilator, and their sum represents the identity in F∞(R). Equivalently this is the tensor permanence argument in Girón Pacheco–Szabó, arXiv:2608.09517v1, Lemma 1.7.

R has the precise form to which Source301 applies. Apply its prescribed-cone isomorphism to R and P, using the identification above (and W/K absorption on P if writing both sides explicitly in stabilized form). Transporting the action along that isomorphism produces an exact finite-group Rokhlin action on P with pullback F_g for every g.

Every compatibility is visible: separability, nuclearity, the contravariant group convention, matrix normalization, inverse-limit topology, arbitrary ideal structure, infinite weights, Rokhlin towers, and the final prescribed invariant. This closes the finite-group realization route explored here. It remains a source/classical inductive-system composition, not a new theorem nominee. It supplies no natural choice of lifts for all cone maps, no global functorial section, no continuous parameter dependence on F, and no exact agreement with a separately prescribed action on an ideal.

## 6. Where this leaves discovery

Section 5 cannot be submitted merely as “equivariant classification” without payment checks. COHERENCE.md performs the existing-action comparison using the strongest primary theorem actually read. RELATIVE.md tests the additional exact relative requirement and shows why the trace cone alone cannot supply it. No old target is weakened or renamed by these calculations, and no general impossibility assertion follows from the relative example.
