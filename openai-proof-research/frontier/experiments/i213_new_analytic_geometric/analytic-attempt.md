# I213 — exact boundary approximation: proofs and remaining estimate

## 1. Target and verdict

Fix a finite exponent p>3 and B=B(0,1) in R³. Let f:cl(B)→cl(B) be a homeomorphism, f|∂B=id, and f|B∈W^{1,p}. Target **B_p** asks for g_j∈Diff∞(cl(B)), g_j|∂B=id, with g_j→f strongly in W^{1,p}(B). Here Diff∞(cl(B)) means smooth up to the boundary, with nonsingular differential there and a smooth inverse up to the boundary. It is stronger than an interior smooth diffeomorphism with a continuous boundary extension.

**Verdict: B_p unresolved in this investigation; no PROVED NOMINATION.** The results below are technical reductions and a precise failure of a proposed method. None disproves B_p. The restriction p>3 is used in the ambient-approximation route for uniform convergence; some technical reductions hold for every finite p≥1.

## 2. Route A: insert an exact collar, then approximate relatively

### A1. Sobolev Alexander compression (technical; full proof)

For every 1≤p<∞ and every f as above, put, for 0<r<1,

F_r(x) = r f(x/r) if |x|<r, and F_r(x)=x if r≤|x|≤1.

Then F_r is a homeomorphism of cl(B), is the identity on the collar r≤|x|≤1, and F_r→f strongly in W^{1,p}(B) as r↑1. Moreover

∫_B |DF_r−I|^p = r³ ∫_B |Df−I|^p,
∫_B |F_r−id|^p = r^{p+3} ∫_B |f−id|^p.

Proof. Let q=f−id. Its zero trace on the smooth sphere implies q∈W_0^{1,p}(B); its zero extension q~ belongs to W^{1,p}(R³). On B, F_r−id=r q~(x/r). Dilations converge strongly to the identity in W^{1,p}: prove this first for compactly supported smooth functions, then use their density and the uniformly bounded dilation operators for r∈[1/2,1]. This gives the claimed convergence and the two changes of variables give the identities. Inside Br, F_r maps Br homeomorphically onto Br and is identity on its boundary; outside it is identity. The inverse is given by the same construction with f^{-1}; therefore the glued map is a homeomorphism. No regularity of the inverse derivative is needed. ∎

This supplies an exact collar **before** smoothing. It supplies no rate depending only on the Sobolev norm and does not itself produce relative smooth approximants.

### A2. Flattening an already smooth boundary-fixing diffeomorphism (technical; full proof)

If g∈Diff∞(cl(B)), g|∂B=id, then for every finite p≥1 it is a W^{1,p} limit of Diff∞(cl(B)) maps equal to id in a neighborhood of ∂B.

Proof. Write t=1−|x| and ω=x/|x| in a fixed thin collar. At t=0, Dg is identity on tangential vectors. In the inward normal direction its components are (b(ω),a(ω)), where a(ω)>0. Thus m=min(1,min a)>0 and a,b and the second derivatives are bounded. Taylor expansion in these coordinates gives

g(x)−x = t(b(ω)+(a(ω)−1)n(ω))+O(t²),

uniformly with the corresponding first derivative remainder. Choose a smooth nondecreasing cutoff θ_ρ(t), zero near t=0 and one for t≥ρ, with 0≤t θ'_ρ(t)≤κ. Such cutoffs exist with arbitrarily small fixed κ>0: take a smooth step in log(t), over a sufficiently long interval [log(ρ)−L,log(ρ)]. Choose κ so κ max|a−1|<m/4 and then choose ρ small. Define

G_ρ(x)=x+θ_ρ(t)(g(x)−x)

in the collar and G_ρ=g outside it. In orthonormal tangential/normal frames its differential has tangential block I+O(ρ), lower left O(ρ), bounded upper right, and lower right

1+(θ_ρ+tθ'_ρ)(a−1)+O(ρ).

The lower right is ≥m−κ max|a−1|−O(ρ); hence det DG_ρ>0 for small ρ. Remainders remain O(ρ) even where θ' is large, because tθ'≤κ. G_ρ is smooth and identity near ∂B. Convexity of B puts its values in B. Its extension to cl(B) is proper with boundary degree one, so the positive local degrees give a diffeomorphism onto B, with the identity supplying smooth boundary invertibility. Finally G_ρ−g is supported in a collar of volume O(ρ), its derivative is bounded by a constant depending on g, and its value is O(ρ). Thus ‖G_ρ−g‖_{W^{1,p}}≤C_{g,p}ρ^{1/p}→0. ∎

No uniform bound in terms of ‖g‖_{W^{1,p}} is claimed: m and the derivative bounds can depend on g.

### A3. Exact reduction of the unpaid problem

Let **C_p** say: every W^{1,p} homeomorphism F of cl(B) that is identity on some open boundary collar can be approximated strongly by smooth diffeomorphisms of cl(B) which are identity on some boundary collar (the output collar may depend on the approximant).

For every finite p≥1, B_p and C_p are equivalent for this class of continuous closed-ball homeomorphisms. C_p⇒B_p follows by A1 and a diagonal choice of approximation errors. B_p⇒C_p follows by applying B_p to F and applying A2 separately to each smooth approximant, with errors tending to zero. This is a **technical reduction**, not a proof of either assertion.

Source check: `sm:relative-pl` keeps a map fixed where it is already PL but supplies no derivative estimate. `hp:opening` preserves the carrier on an eligible closed target set and supplies fine value control, not a general Sobolev estimate. `hp:carrier` protects internally constructed exact cores; it is not stated for an arbitrary externally prescribed collar. The full-range `sm:smoothing` gives strong approximation with a strictly positive continuous value tolerance on the *open* domain. Its stated conclusion does not assert exact agreement on an open collar or smoothness at ∂B. The high-range final assembly uses two smoothing calls and finite cubical corrections; exact prescribed boundary data are not a conclusion. No unsupported relative strengthening of these stipulated operations is inserted here.

## 3. Route B: ambient approximation and controlled collar straightening

Extend F_r from A1 by identity to 2B. It is a W^{1,p} homeomorphism of cl(2B). Apply the stipulated high-range theorem on 2B. Its smooth onto approximants G_j converge strongly in W^{1,p}(2B); for p>3 the bounded smooth-domain embedding also gives uniform convergence on cl(2B), using their continuous Sobolev representatives. On every annulus outside Br, the limit is id.

Choose r<r_-<r_+<1. A sufficient additional statement would construct smooth diffeomorphisms H_j of 2B satisfying

H_j=G_j on B_{r_-},  H_j=id on 2B\B_{r_+},
‖H_j−G_j‖_{W^{1,p}(2B)}→0.                         (CS_p)

Uniform convergence puts G_j(cl(B_{r_-})) inside B_{r_+} eventually, so there is room for an ambient topological correction. What is missing is its derivative cost on the annulus. If CS_p held for such sequences, H_j|B would prove C_p, then B_p. CS_p is stated as a sufficient estimate, not an equivalence or a theorem.

The direct proposal H_j=id+χ(G_j−id), with a fixed scalar collar cutoff χ, does **not** follow from strong smallness. The next construction refutes that method even for a sequence converging to identity. It does not refute adaptive straightening or CS_p.

### B1. Fixed-cutoff folding despite arbitrarily small strong Sobolev error (technical diagnostic; full proof)

There exist a fixed χ∈C∞(R;[0,1]), equal to 1 for t≤0 and 0 for t≥1, and smooth orientation-preserving diffeomorphisms g_s:Q→Q, Q=(−2,2)³, equal to id near ∂Q, such that, as s↓0,

‖g_s−id‖∞→0 and ‖g_s−id‖_{W^{1,p}(Q)}→0 for every finite p≥1,

but h_s(x)=x+χ(x₁)(g_s(x)−x) is not injective.

Choose χ(t)=1−exp(−1/t) for 0<t<t₀, and extend it smoothly with the stated constant ends. Put

d_s=exp(−1/s), δ_s=2s², ε_s=d_s/[2(1−d_s)].

For sufficiently small s, 0<ε_s<1/2. Choose a fixed nonnegative ψ₀∈C_c∞(R) with ψ₀(0)=1, ψ₀'(0)=−1 and ψ₀'≥−1. Here is an existence construction to make all requirements simultaneous. Take a nonnegative smooth b supported in (−1,2), with max b=b(0)=1 and ∫₀^∞b=1. Take a nonnegative a supported in (−4,−2) with ∫a=∫b. Set ψ₀(z)=∫_{−∞}^z(a−b). Its support is compact, it is nonnegative, and it has the required value and slope. Let

ψ_ε(z)=ψ₀((1−ε)z),  u_s(t)=δ_s ψ_{ε_s}((t−s)/δ_s).

Then u_s(s)=δ_s, u_s'(s)=−1+ε_s, u_s'≥−1+ε_s, and u_s is supported on an interval of length O(δ_s). Its amplitude is O(δ_s) and derivative is bounded independently of s. Fix η∈C_c∞((−1,1)²), 0≤η≤1, equal to 1 near (0,0). Define

g_s(t,y,z)=(t+η(y,z)u_s(t),y,z).

Its determinant is 1+ηu_s'≥ε_s>0. Each one-dimensional fiber is strictly increasing and is identity near both endpoints of (−2,2); hence g_s is an onto smooth diffeomorphism of Q, identity near its boundary. The support has volume O(δ_s), so

‖g_s−id‖∞≤Cδ_s,
‖g_s−id‖_{L^p}≤C_pδ_s^{1+1/p},
‖Dg_s−I‖_{L^p}≤C_pδ_s^{1/p}.

At (s,0,0), however, the first derivative of the first coordinate of h_s is

1+χ(s)u_s'(s)+χ'(s)u_s(s)
 = d_s+(1−d_s)ε_s−(d_s/s²)δ_s
 = −d_s/2 <0.

The other coordinates are unchanged. On the line y=z=0 the map is identity near the two endpoints but has negative derivative at s. A continuous injective interval map with those endpoints would be increasing, which is impossible. Thus h_s is not injective. ∎

There is no contradiction with A2: A2 assumes an already boundary-fixing smooth map and chooses a cutoff using its nondegenerate boundary differential and a logarithmic transition. Nor does this refute arbitrary cutoffs tailored to g_s. In this example id itself is an excellent corrected approximant. The diagnostic excludes only the asserted fixed-cutoff implication.

### B2. What fine tolerances really do give (technical direct source consequence)

If H:cl(B)→cl(B) is a W^{1,p} homeomorphism, H|∂B=id, and H is locally bi-Lipschitz in B, then `sm:smoothing` with ξ_j(x)=j^{-1}dist(x,∂B)² gives smooth interior diffeomorphisms g_j:B→B, strongly approaching H, whose continuous extensions to cl(B) fix ∂B pointwise. Indeed the value estimate forces the boundary limit to equal H's; compactness and bijectivity give a homeomorphism of the closures. No boundary derivative is asserted. This does not prove B_p, even in this restricted class, because Diff∞(cl(B)) is a stronger conclusion. It is a direct source corollary, not a contribution nomination.

## 4. Primary comparison and significance limits

Iwaniec–Kovalev–Onninen, arXiv:1009.0286v1, Theorem 1.1(i),(v), already gives zero-trace error and compactly supported modification when the input is smooth outside a compact set, in dimension two. Its full five-stage proof was read. The energy control uses planar coordinatewise p-harmonic replacements into convex targets, followed by smoothing with previously fixed derivative bounds. That is an actual relative energy mechanism; neither its planar injectivity theorem nor its energy control transfers to dimension three by citing topology.

Hencl's survey arXiv:2502.01336v1, read in the existing local extraction, separates ordinary approximation, elastic-energy approximation, incompressible approximation, and weak/strong closure questions. B_p is a boundary-constrained version of the approximation question; it is not a resolution of its inverse-energy or incompressibility questions. No claim that B_p is independently recognized as open throughout the literature is made.

The current Campbell–D'Onofrio–Vítek bibliographic/abstract check confirms an existing smoothing result for a piecewise affine input, not an arbitrary rough Sobolev homeomorphism. For the operative smoothing and relative topology this report relies on the precisely read **pinned** source interfaces, not on importing an unread external proof.

**Next unpaid estimate:** C_p, or the stronger sufficient annular correction CS_p. A valid proof must control strong derivative error while retaining injectivity and exact collar agreement. Fine values, ordinary topology, the valid smooth-boundary flattening lemma, and the fixed-cutoff construction above do not pay that estimate. Even if C_p is ultimately a localization of the complete source construction, that localization must be written and checked before it is asserted. No significant new case has been proved here.
