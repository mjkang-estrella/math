# I74 — Relative symplectic packing: paid local transport and a protected comparison model

Date: 2026-10-09. **RP remains unproved and unrefuted. No substantial finding is nominated.** The accepted count remains eight. All statements and proof operations in `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are premises. I70's deductions are independently checked below; its evidence PASS is not an analytic premise.

This continuation obtains two actual constructions rather than another sufficient lemma named after RP. The transport route produces fixed-capacity Hamiltonian paths for nonlinear shears and for a class specified by a derivative bound. In particular, it proves RP and a slack-independent small-ball threshold for these explicitly described images of one large ball. The direct route constructs a compactly supported Hamiltonian comparison map and a **toric** transfer function for a radial affine surplus, fixing a prescribed outer positive region. It also supplies an exact relative deformation with the horizontal Poisson brackets canceled, and computes the area cost of that deformation. These are restricted, technical deductions. Neither constructs the geometry required by an arbitrary prefix.

The [complete inherited assignment](../sources/i74_relative_symplectic_packing/full-brief.txt), including the original I70 assignment and returned report, is frozen from the parent's task record. [Immutable references](../sources/i74_relative_symplectic_packing/immutable-references.json) hash-reference I70's actual report, scripts, original/final seals, snapshots and failures, without recursively copying them. The [four current ledger snapshots](../sources/i74_relative_symplectic_packing/mutable-ledgers.json) are the only mutable references. AGENTS, the pin, complete tree and catalogue are immutable references. I72 and I73 are independent and unused. No staging, commit, publication, shared-file edit or agent spawning was performed.

## 1. Target and independent audit of I70

Use capacity units

\[
 B(c)=\{z\in\mathbb C^n:\pi|z|^2\le c\},\qquad
 \omega_0=\sum dx_j\wedge dy_j,\qquad \operatorname{vol}B(c)=c^n/n!.
\]

Every embedding is defined on a neighborhood of its closed source, with disjoint compact images in the open target. For every `n≥3`, `R>0`, finite positive lists `a,b`, and every prescribed packing `e` of the a-balls, **RP** asks for a packing of the b-balls in

\[
 U_e=\operatorname{Int}B(R)\setminus\bigcup_j e_j(B(a_j))
\]

provided `Σa_j^n+Σb_i^n<R^n` and every two distinct entries of the combined list have sum `<R`. The original maps e must remain exactly unchanged. No equality case, energy bound, infinite packing, continuous selection in e, or parametrized lifting assertion is included.

Let P denote the pinned *Symplectic Ball Packings in Higher Dimensions*. Its absolute theorem makes the total packing space nonempty. RP requires surjectivity onto **every** prescribed prefix of its forgetful map. This distinction persists throughout this report.

### I: PASS ORIGINAL WITHOUT REPAIRS, within the original hypothesis

For a supplied smooth isotopy `e_t` on fixed enlarged balls with disjoint images, differentiating `e_t*ω₀=ω₀` gives a closed one-form `α_t=e_t*(ι_vω₀)` on each source. The radial homotopy formula

\[
 F_t(z)=\int_0^1\alpha_t(uz)[z],du
\]

satisfies `dF_t=α_t` and depends smoothly on `(t,z)`. With `ι_Xω₀=−dH`, set `H_t∘e_t=−F_t`. Since these domains have full dimension, its differential gives the entire desired vector field, not merely a tangential component. Pull back fixed cutoffs from slightly smaller enlarged balls; extend by zero. Compactness of the closed time interval and strict separation provide common support inside the target. Uniqueness of the Hamiltonian flow gives `χ_t∘e_0=e_t` on the requested balls, including their parameterizations. Transport the other balls by `χ_1`.

Thus the extension proof is valid without a flux assumption on the complement. **The existence of the fixed-capacity path remains GAP for arbitrary e.** Neither its existence nor a uniform Hofer estimate is added by this audit.

### S: PASS ORIGINAL WITHOUT REPAIRS, and already a source operation

For one centered ball of capacity `a≥R/2`, strict admissibility permits a slightly larger rational reserved capacity and slightly enlarged remaining balls. P's `app:large` (`n≥4`) and `six:large` (`n=3`) actually put the latter in the exterior of that reserved central ball. The shell identification `geo:shell` has the original standard form; the six-dimensional cut returns to exactly `H−aE` and keeps the required moment bound. Hence the centered ball is untouched. A compactly supported Hamiltonian image has the same extension property by transporting only the new balls. Prescribed parameterizations need never be replaced. There is no assertion here about arbitrary small centered balls or arbitrary large embedded balls.

### D: PASS ORIGINAL WITHOUT REPAIRS, with its δ dependence retained

For bounded open U and `V=n!vol(U)`, fix `0<δ<V`. I independently checked the covering step: maximal dyadic cubes whose closures lie in an open residual set cover it up to null boundaries; finitely many cover more than half its volume. Quarter-side inscribed closed balls cover a dimension-dependent positive fraction, have strictly separated closures, and leave an open residual. Finitely many rounds therefore produce disjoint compact balls of capacities `c_j`, `j=1,…,J`, with

\[
 C=\sum c_j^n>V-\delta/2.
\]

Choose `ρ≤min_j c_j/4` and `Jρ^n≤δ/4`. Strict next-fit assignment of items `b_i^n≤ρ^n` cannot exhaust these bins when `Σb_i^n≤V−δ`: rejection leaves at most `ρ^n` unused in each bin, so exhaustion would force already assigned volume at least `C−Jρ^n>V−δ`. Each assigned load is strictly below its bin budget and each pair of assigned capacities sums to less than the bin capacity. P packs each bin. Finite compact containment supplies the source neighborhoods. In a prescribed complement, symplectic volume and zero-volume smooth boundaries give `V=R^n−Σa_j^n`.

There is no limiting embedding in this proof. `ρ(U,δ)` depends on both the actual geometry and δ. **The original proof does not establish a positive lower bound as δ decreases to zero.**

### Orbit transfer and curvature: PASS ORIGINAL WITHOUT REPAIRS

For `P(qu)+K(u)−K(qu)≥d`, every q-invariant probability measure must have `∫P≥d`. On a finite permutation orbit, summing proves the upper bound by its orbit mean; the recurrence `K(qu)−K(u)=P(qu)−mean_O P` attains it. For any supplied smooth q,

\[
 K(u)=-\frac1N\sum_{j=1}^{N-1}(N-j)P(q^ju)
\]

makes the comparison exactly `N^{-1}Σ_{j=1}^N P(q^ju)`. Smooth uniform approximation preserves a strict gap when only continuity is initially supplied. This constructs K from a finite-average bound; it does not construct q, make K toric, or supply face compatibility.

For a two-dimensional base and `Ω=ω_V+d(A ds+B dt)`, with `h=B_s−A_t` and `{A,B}=Σ(A_xB_y−A_yB_x)`, expansion gives

\[
 \frac{\Omega^{m+1}}{(m+1)!}
 =\bigl(h-\{A,B\}\bigr)\frac{\omega_V^m}{m!}\wedge ds\wedge dt. \tag{1}
\]

Equivalently, eliminating the vertical block of the skew matrix gives the same scalar. Orientation-compatible symplecticity is `h−{A,B}>0`. I70 correctly distinguishes this condition from mere `h>0`. Its description of P is also correct: P's nontoric part is already handled by **one base covector** after Hamiltonian suspension, and its outside corrections are toric. Nontoric dependence itself is not a source gap.

### Method countermodels: PASS ORIGINAL WITHOUT REPAIRS, with no target refutation

The centered shear `(q,p)↦(q,p+4q−4q³)` is symplectic, maps the Euclidean unit ball strictly inside radius 3 by `1+8/(3√3)<3`, and its Alexander expression at `t=1/2`, `(q,p)=(1,0)`, has squared norm 10. Equal-class, equal-orientation exact forms with signs `(+,+,+)` and `(−,−,+)` have a rank-two midpoint. The affine moment function `p−1/4` has positive mean and outer values, but is negative on the protected region `p≤1/8`; an identity q there cannot satisfy a positive comparison. Coefficients `A=L^{-1}sin(L²x)`, `B=s+L^{-1}sin(L²y)` have curvature `1−L²` at zero despite small coefficient error. Three volume-3/5 items cannot fit in two fixed unit bins.

These refute the stated methods only. The bins are not an ambient obstruction; the shear is not an RP counterexample; same-class interpolation failure does not rule out other paths. The parked Lagrangian dilation and odd-iterate screens are not inputs here. Their historical conclusions remain unchanged: positive fiber dilations lie in one exact Hamiltonian image class, the finite iterate statement is `∀K∃Φ_K`, and normal resonances refute a uniform-small-ε method only. No new full audit or theorem about those unused screens is claimed.

## 2. Stronger companions and primary proof operations

The [fresh searches](../sources/i74_relative_symplectic_packing/searches.json) use the complete fixed 9,340-file corpus and retain sorted line **multisets**. The complete tree has 13,223 entries, 749 manuscript directories and 10,373 blobs; the [tree screen](../sources/i74_relative_symplectic_packing/tree-screen.json) explicitly lists the 1,033 blobs outside the fixed corpus. The corpus is not described as the whole tree, and search hits are not described as a full reading. The three searches have 155, 15 and 316 lines, including irrelevant lexical matches.

I read P's comparison fixed-point/rearrangement argument, relative primitives, one-covector suspension, outer-face Moser conditions, common-complex-structure Kähler interpolation, and both shell transfers. Fresh raw responses for the five corresponding source files reproduce their pinned Git blobs. The higher-dimensional Seshadri manuscript remains about very general point tuples of a **given polarized complex variety**; its embedded surface companion concerns nef exceptional classes, not an arbitrary symplectic blowup with prescribed boundary charts. The newer *Deforming hypersymplectic four-manifolds to hyperkähler triples* supplies a constant-class deformation on **closed real four-manifolds carrying a positive triple**. Its individual-Kähler corollary does not apply to a higher-dimensional ball complement. These are explicit hypothesis mismatches, not upstream objections. W's polar packing corollary remains spent and supplies no fixed-prefix operation.

Seven unversioned primary records were fetched anew, then their latest observed versions were separately fetched: Siegel–Yao **2312.13224v1**, Schlenk **2011.03317v2**, Buse–Hind **1112.1149v1**, Buse–Hind–Opshtein **1404.4183v1**, Entov–Verbitsky **2211.15970v2**, Edtmair **2509.15390v1**, and Cristofaro-Gardiner–Hind **2307.01140v2**. These are dated observations bound to retained responses, not future version claims. Full response bytes, headers, times, extracted texts and read-passage ranges are in the [primary evidence](../sources/i74_relative_symplectic_packing/primary/) and [passage bindings](../sources/i74_relative_symplectic_packing/passages.json).

**Transport.** Siegel–Yao Proposition 2.4 shrinks radii before its local relative Moser argument; Proposition 2.3 allows the blowup sizes, and hence classes, to vary. Schlenk's actual §2.4 proof first shrinks, then uses four-dimensional inflation to return each intermediate blowup form to the endpoint class, and controls the divisor at infinity during blowdown. Removing that inflation step is not a proof. [Siegel–Yao §2.3](https://arxiv.org/html/2312.13224v1), [Schlenk §2.4](https://arxiv.org/html/2011.03317v2).

**A more serious Kähler lead.** Entov–Verbitsky Theorems 3.2 and 3.7 give orbit results for Kähler-type ball embeddings in closed projective space. Their proof normalizes forms near exceptional divisors, blows down, and uses common-complex-structure interpolation and relative Moser on actual neighborhoods. The integrable compatible structure on the entire manifold is essential. Their existence result can avoid a specified complex hyperplane; the general closed-space orbit theorem does not say the resulting symplectomorphism preserves that hyperplane. Nor does P declare its arbitrary packing prefix Kähler-type. Thus neither “both endpoints are Kähler-type” without the required boundary data nor “their blowup classes agree” proves RP. No arbitrary-prefix identification is supplied by these results. [Entov–Verbitsky, §§3.1–3.2, 5.5–5.6](https://arxiv.org/html/2211.15970v2).

**Higher-dimensional filling, strongest version checked.** The 2013 **published** Buse–Hind paper is stronger than arXiv v1: Remark 1.2 upgrades their constructions to actual embeddings of full **open ellipsoids**. Theorem 1.3 gives thin-ellipsoid full fillings of closed rational manifolds; Theorems 4.1 and 4.5 use Donaldson polarizations, disk bundles and induction, with the latter giving a specified thin shape from successive approximately holomorphic hypersurfaces. Their equal-ball stability is published Theorem 1.5. The old v1's smaller-scale arrow convention must not be attributed to these final constructions. The general higher-dimensional principle upgrading arbitrary compact-subset embeddings to an open embedding remains unasserted. Most importantly here, neither published filling construction controls avoidance of prescribed exceptional divisors or proves strong unequal-ball stability for an arbitrary complement. The rationality of a blowup alone does not pay those interfaces. The complete publisher PDF and proof passages were retrieved and checked; the weaker draft comparison is preserved. [Buse–Hind, published §§1, 3–4](https://doi.org/10.1112/S0010437X12000826).

The published Proposition 3.5 also matters: its suspension of a disjoint ellipsoid packing adds the **same new axis c** to every component. Lifting a four-dimensional ball of capacity b therefore produces `E(b,b,c,…)`, not a ball of capacity b in the higher dimension. If all added axes are c>b, the container volume exceeds that ball volume by `(c/b)^(n−2)`; if c<b, its width is too small to contain that ball. This explains why simply suspending four-dimensional unequal-ball stability does not pay a full-volume unequal-ball packing in our dimension. It is a limitation of that direct lift, not an obstruction to other constructions.

**Strong stability and boundaries.** Buse–Hind–Opshtein's unequal-ball theorem is in dimension four and uses controlled ellipsoid/pseudoball pieces and singular inflation. Edtmair's smooth-boundary theorem is also four-dimensional: §8 reduces through Morse levels and the boundary-compatible frusta/cuboid stratification from §9 to tame packings. It supplies full-volume ellipsoid approximation; Remark 1.1 expressly leaves smooth dependence needed for a limiting interior embedding unproved. Combining these four-dimensional tools does not give a higher-dimensional complement theorem. The rough/unbounded-boundary examples of Cristofaro-Gardiner–Hind are not complements of our finite smooth embedded balls. [Buse–Hind–Opshtein §§1, 3](https://arxiv.org/html/1404.4183v1), [Edtmair §§1, 6–9](https://arxiv.org/html/2509.15390v1), [Cristofaro-Gardiner–Hind §1](https://arxiv.org/html/2307.01140v2).

Hind’s actual higher-dimensional nonisotopy examples use polydisks or polylike domains in `B⁴×R^{2n−4}`. Their nonextension-to-a-common-ellipsoid result does not turn them into ball obstacles in a ball; the first four pages were checked directly. [Hind, Theorems 1.3, 1.5 and 1.9](https://academicweb.nd.edu/~rhind/3disotopyv2.pdf).

These are bounded applicability/proof-interface comparisons. No inaccessible page is cited as read. The Buse author-host PDF URL returned 404, retained separately; the publisher PDF succeeded. The Entov–Verbitsky journal landing page corroborates publication, while its proof passages here come from the current arXiv v2. I70's inaccessible AMS response, missing initial search-response archive, indexing failure and duplicate-provenance verifier failure remain preserved in the referenced old evidence.

## 3. Route A: actual fixed-capacity paths on explicit nonlinear classes

### A1. Shear transport, including the failed Alexander example

Let `r=√(a/π)`, `r_R=√(R/π)`, and let

\[
 f(q,p)=(q,p+\nabla F(q))
\]

be defined on a neighborhood of the closed radius-r ball. Suppose `f(B(a))⊂Int B(R)` and `a<R`. Then

\[
 f_t(q,p)=(q,p+t\nabla F(q)),\qquad 0\le t\le1, \tag{2}
\]

is a fixed-capacity symplectic isotopy in `Int B(R)` from the inclusion to f. Indeed, symmetry of `D²F` makes every f_t symplectic and injective, with the displayed inverse shear. For each z, `f_t(z)=(1−t)z+t f(z)`; convexity of the target ball bounds its norm by the larger endpoint norm. Both endpoint compact images are strictly inside. Therefore the whole trace has a uniform positive target margin. Smoothness on a neighborhood permits a fixed slightly larger source ball while retaining this margin for every t. Apply audited I to get a compactly supported Hamiltonian χ with `χ|B(a)=f|B(a)`.

This is a constructed path, not a use of source shrinking. In particular, **I70's shear countermodel is Hamiltonian-standard inside its stated radius-3 target**, even though its particular Alexander path escapes. This repairs the method on this class without changing the old countermodel's verdict.

For `n≥3`, `a≥R/2`, and admissible b, apply S then χ to the b-balls. The prescribed map f itself is retained. The same conclusion holds for any prescribed parameterization whose image is `f(B(a))`, since only disjointness from that image matters. Finite compositions of shears also work when each intermediate closed image stays inside the target: interpolate each stage, with the preceding image as its domain; compactness and convexity again pay the collars and target containment. No bound on Hessians is needed. For example, a small-amplitude shear `p_1↦p_1+ε sin(kq_1)` can have arbitrarily large derivative while (2) still works if `ε<r_R−r`.

**Scope:** one large prescribed ball with this explicit form or a finite controlled shear factorization. A general ball embedding is not known here to admit such a factorization with every intermediate image in the target. An unrestricted factorization in Euclidean space does not pay that condition.

### A2. A derivative criterion for a second, genuinely constructed path

Let e be a symplectic neighborhood embedding of B(a), and put `v=e(0)`. Suppose

\[
 |v|+r\sup_{z\in B(a)}\|De(z)\|<r_R. \tag{3}
\]

Then e is connected to the standard centered inclusion by a fixed-capacity compact isotopy in the target.

Choose `r'>r` and L bounding the derivative on the radius-r' ball such that `|v|+Lr'<r_R`. For `0<t≤1` set

\[
 e_t(z)=v+\frac{e(tz)-v}{t},\qquad e_0(z)=v+De(0)z. \tag{4}
\]

The conjugate source/target dilations cancel their symplectic factors, so every e_t is symplectic. The formula

`(e(tz)−v)/t=∫_0^1 De(stz)z ds`

makes the path smooth through t=0 and gives `|e_t(z)−v|≤L|z|`. Thus it lies in the fixed ball centered at v of radius Lr', which is strictly inside the target.

Write `A=De(0)=UP` in symplectic polar form. Here U is orthogonal symplectic and P is positive symplectic. The identity `PJP=J` implies that every positive real power `P^s` is symplectic. Its eigenvalues occur in reciprocal pairs, so `||P^s||≤max(1,||P||)≤L` for `0≤s≤1`; a symplectic linear map has norm at least one. The path `v+UP^s z` therefore contracts A to U inside the same container. A unitary path contracts U to the identity without increasing radii. Finally translate v to zero; the bound `|v|+r'<r_R` controls this last path. Reparametrize the finitely many stages to be constant near their endpoints and use I. The endpoint equality is equality of maps on B(a), not only images.

Consequently, for `a≥R/2`, (3) gives another explicit class on which RP holds. This is stronger than asserting that some isotopy exists: the test uses e and its derivative only. It is weaker than arbitrary containment and does not apply to every embedding. It is also different from A1: bounded-amplitude high-frequency shears need not satisfy (3).

For several balls the same construction can be performed in disjoint round containers satisfying the corresponding derivative bounds. It connects the prefix to the translated round configuration in those containers. **This does not prove its extendability unless that reference configuration is independently known to extend.** P does not guarantee the desired centers.

### A3. An honest slack-independent consequence on the paid class

For any e covered by A1 or A2 with `a≥R/2`, choose once and for all

\[
 \rho=(R-a)/2>0. \tag{5}
\]

Every finite positive list `b_i≤ρ` with `Σb_i^n<R^n−a^n` embeds in U_e. Indeed, `a+b_i<R`, and `b_i+b_j≤R−a≤R/2<R`; S followed by the constructed χ applies. This threshold is independent of the residual volume slack and of the number of balls. It holds for closed-source neighborhood embeddings and strict total volume. It asserts neither equality nor a continuous selection of packings.

This is a real restricted uniformity result, but it is a direct consequence of S once the explicit paths above are paid. It is **technical**, not a nomination for the general fixed-complement strong stability question.

### A4. What an arbitrary-prefix blowup still costs

The explicit paths above also induce compatible blowups: use each e_t as the collar chart in the cut/gluing construction. Their source capacities stay fixed; exceptional divisors keep their labels and line areas; the outer target collar is untouched by the compact Hamiltonian extension. On a common blowup identified using that extension the pulled-back form is constant. Thus there is no hidden inflation claim for these classes.

For arbitrary e, shrink-and-connect instead gives classes `RH−Σa_j(t)E_j`. The missing global step is a smooth positive correction returning **every** intermediate form to `RH−Σa_jE_j`, with compatible exceptional normal models and unchanged target collar. If a fixed-class path on an already identified manifold were supplied and fixed the collar forms, the relative primitive issue is manageable: neighborhoods of the exceptional divisors retract to `CP^{n−1}`, and the outer target collar retracts to `S^{2n−1}` (a neighborhood of the compactifying infinity divisor instead retracts to `CP^{n−1}`), all with H¹=0. A global primitive of the derivative is locally exact there and can be corrected by disjoint cutoffs to vanish on smaller collars. Relative Moser would then fix those collars pointwise. But producing that positive path and its common normal charts is precisely what the source and the primary shrink argument do not do. Setwise preservation of divisors is insufficient to assert this chart control.

No arbitrary symplectic blowup is silently assigned a common integrable complex structure. The local sign countermodel from §1 still blocks a cohomology-only linear interpolation. This is an exact geometric gap, not a new conditional theorem proposed for acceptance.

## 4. Route B: construct q, keep a positive protected region, and pay curvature

### B1. A protected comparison that actually exists

Let `m≥1`, `0<c`, and choose capacities `9c<C<L`. On `V=B^{2m}(L)` put

\[
 p(z)=\pi|z|^2,\qquad P_0(z)=p(z)-c.
\]

There exist smooth toric K, a Hamiltonian isotopy q_t of V supported in `{p<C}`, and d>0 such that

\[
 P_0(qz)+K(z)-K(qz)\ge d\quad(z\in V),\qquad q=q_1, \tag{6}
\]

with **both K and every generating Hamiltonian zero on a neighborhood of `{p≥C}`**. Thus any protected subset of that region is fixed pointwise. All outer-face moments are preserved because the isotopy is the identity in an outer collar. `P_0` has negative values near zero, so this is not the trivial everywhere-positive comparison.

Here is the construction. Put `r_c=√(c/π)`. Since `√(C/π)>3r_c`, choose a vector w and radii r₀,r₁ such that

\[
 |w|>r_c,\qquad |w|+r_c<r_0<r_1,
 \qquad |w|+r_1<\sqrt{C/\pi}. \tag{7}
\]

Take a smooth h with `h'(I)=1/2` for `I≤πr₀²`, `h'(I)=0` for `I≥πr₁²`, and h=0 on that outer interval. Define the compactly supported Hamiltonian

\[
 Q(z)=h(\pi|z-w|^2).
\]

With our convention its time-t map is

\[
 q_t(z)=w+e^{2\pi i t h'(\pi|z-w|^2)}(z-w). \tag{8}
\]

The distance to w stays constant, so the flow is supported in the radius-r₁ ball about w. On the radius-r₀ ball it is the half-turn `qz=2w−z` at time one.

Choose `π(|w|+r₁)²<C_1<C_2<C`, and a smooth radial cutoff χ(p) equal to one for `p≤C₁` and zero for `p≥C₂`. Set

\[
 K(z)=\tfrac12\chi(p(z))(p(z)-c). \tag{9}
\]

In the support of q, both z and qz lie where χ=1. Consequently the left side of (6) is `(P_0(z)+P_0(qz))/2`. In the half-turn region this equals

\[
 \pi|z-w|^2+\pi|w|^2-c\ge\pi|w|^2-c>0.
\]

In the transition region `|z-w|≥r₀`, every rotated point has norm at least `r₀−|w|>r_c`. Both terms of the average are at least `π(r₀−|w|)²−c>0`. Outside the support of q, q is the identity, K cancels, and the same lower estimate applies because `|z-w|≥r₁`. Thus one may take

\[
 d=\min\{\pi|w|^2-c,\ \pi(r_0-|w|)^2-c\}>0. \tag{10}
\]

All functions extend smoothly past V, with support strictly inside it. This pays the Hamiltonian realization, toric K, protected set and outer moments, not merely a finite orbit surrogate. The same q,K,d work for any P with `P≥P₀`; a uniform perturbation of P₀ of size `<d` retains a positive comparison with the corresponding smaller gap. For the source-shaped affine P₀, concavity, outer positivity and positive mean are automatic: `mean_V P₀=mL/(m+1)−c>0`.

The factor 9 describes this particular protected half-turn construction. Positivity at its center needs `|w|>r_c`, and covering the entire negative ball by the full-rotation region needs `r₀>|w|+r_c`. Fitting the support inside a centered protected threshold then needs radius greater than `2|w|+r_c>3r_c`. This is **not** a lower bound for all permitted q or an RP obstruction.

### B2. A positive relative deformation with exact bracket cancellation

The q just constructed can be suspended without reintroducing unpaid horizontal terms. Let the base be the compact cylinder `[0,1]_s×(R/Z)_t`. Choose smooth bumps η,ζ supported in `(0,1)`, with `0≤η≤1`, and let A be a positive constant with

\[
 A>\|\eta'\|_\infty\|K\|_\infty. \tag{11}
\]

For `λ∈[0,1]` define

\[
 \widehat\Omega_\lambda
 =\omega_V+A\,ds\wedge dt+d(\lambda\eta(s)K\,dt),
 \quad
 D_\lambda(s,t,z)=(s,t,q_{\lambda\zeta(s)}z),
 \quad \Omega_\lambda=D_\lambda^*\widehat\Omega_\lambda. \tag{12}
\]

The unsuspended form has a single base covector and curvature `A+λη'K>0`. D is a diffeomorphism, so every Ωλ is symplectic. More explicitly its horizontal primitive has coefficients

\[
 a_\lambda=\lambda\zeta'(s)Q,
 \qquad b_\lambda=As+\lambda\eta(s)K(q_{\lambda\zeta(s)}z).
\]

Since Q is autonomous and invariant under its own flow,

\[
 \partial_s b_\lambda-\partial_t a_\lambda
 =A+\lambda\eta'K\circ q_{\lambda\zeta}
 +\lambda^2\eta\zeta'\{Q,K\circ q_{\lambda\zeta}\},
\]

whereas

\[
 \{a_\lambda,b_\lambda\}
 =\lambda^2\eta\zeta'\{Q,K\circ q_{\lambda\zeta}\}.
\]

They cancel **at every λ,s,t,z** in (1). This is not a C⁰ approximation. The variation primitive `∂λ(aλ ds+bλ dt)` vanishes near both base boundary circles and near the protected region `p≥C`; it vanishes near every outer face as well. Relative Moser therefore exists on a neighborhood of this compact model and fixes those collars pointwise. This is a constant-class, positive, relative deformation on an actual specified model.

This computation is deliberately compared with P's `surf:one-covector`: the pullback/single-covector device is already a source operation. The additional content here is an explicit protected q and K for a nontrivial surplus, together with the fully written cancellation and boundary restrictions. No originality or substantiality is claimed for Hamiltonian suspension or Moser.

### B3. The area cost is real, and the model is not the arbitrary complement

One cannot use (11) to add area freely in RP. There is a sharp elementary budget for this particular cylinder ansatz. Let η rise monotonically from 0 to 1 and fall monotonically to 0, and let `m_K=min K≤0≤M_K=max K`. Replace A by a positive fiber-independent density κ(s). Positivity for all λ requires

\[
 \kappa(s)>-m_K(\eta')_+(s)+M_K(-\eta')_+(s). \tag{13}
\]

Conversely (13) suffices, since it bounds the worst fiber value of `−λη'K`. Integrating gives

\[
 \int_0^1\kappa(s),ds>M_K-m_K=\operatorname{osc}K. \tag{14}
\]

Smooth positive majorants of the right side of (13) make the total arbitrarily close to `osc K` from above. Thus the infimum required area is exactly `osc K`; the gauge suspension adds no further bracket cost. This is an area statement about (12), **not a Hofer estimate for RP**, and does not restrict P's different handled-base construction.

No map from this cylinder–fiber model into an arbitrary U_e with adequate volume and requested ball-layer sizes has been constructed. Its protected set was placed where P₀ was positive, in a specified outer region. The original arbitrary prefix does not come with such moment coordinates. Conjugating a model to move that prefix into the region would itself require the missing geometric construction. Cutting Q off around an arbitrary obstacle may destroy the half-turn pairing exactly on the negative region; I70's fixed-region counterexample still applies there.

A direct RP construction must therefore produce, inside the **actual** U_e, the base and fiber geometry, the cap supports and positive comparison pairing, while retaining enough integrated area for the requested capacities. If it uses the cylinder ansatz, it must pay (14) from the existing area density, not insert it. If it follows P's more efficient handled-base architecture, it must construct a protected placement compatible with the closed handle one-form and toric outside layers. If it leaves either architecture, it must establish `inf(hλ−{Aλ,Bλ})>0` for its own actual coefficients. This is the remaining geometric estimate; (6) and (12) alone are not RP.

## 5. General complements: what uniformity can actually be added

There is a modest new strengthening of D that does not remove slack. Fix n,R,a and δ with `0<δ<R^n−Σa_j^n`. Let \(\mathcal E\) be any compact family of prescribed neighborhood embeddings in the uniform topology on the disjoint closed balls. Then there is one `ρ(𝓔,δ)>0` for which D holds for **every** e in the family and every finite list with `b_i≤ρ` and `Σb_i^n≤R^n−Σa_j^n−δ`.

To prove this, for each e choose the finite Euclidean bins in the proof of D with total capacity power greater than `V−δ/2`. Their compact union has positive distance from e's compact images. Uniformly nearby maps therefore still avoid the same bins; the bins and their capacities have not moved. The same threshold works throughout that neighborhood. Finitely many such neighborhoods cover \(\mathcal E\); take the minimum of their positive thresholds. Since all prefixes have the same capacities, V is constant. The packing chosen may jump as e varies: no continuous selection, path lifting or parameterized b-map is claimed.

This conclusion is technical and follows from finite compact containment. It does not show that `inf_{δ>0}ρ(𝓔,δ)>0`. Even a family consisting of a single arbitrary smooth prefix does not remove that missing bound. A diagonal sequence of finite constructions supplies neither a uniform positive threshold nor a convergent sequence of embeddings with the needed derivative and collar control.

The closure of U_e is a compact smooth symplectic manifold with outer sphere and finitely many inner sphere boundaries. U_e is connected: a path meeting any removed ball can be rerouted through a collar of its connected boundary, with disjoint collars for finitely many balls. This rules out treating the two-bin combinatorial example as its topology. Neither a disconnected two-bin obstruction, a camel isotopy obstruction in a different ambient domain, a rough-boundary example, nor a non-ball obstacle refutes its packing stability or RP. No actual prescribed-ball counterexample has been found here.

## 6. Reproduction, limitations and handoff

Run from the project root:

```bash
python -B frontier/experiments/i74_relative_symplectic_packing/verify.py
```

The verifier is offline and read-only. It binds every I74 artifact except its own seal and captured output, checks the 229 old/input hash references without refreshing any old seal, replays the unchanged I70 verifier, recognizes exactly four mutable ledgers, checks complete-tree versus fixed-corpus domains and line multisets, verifies fresh pinned responses against Git blobs, and replays HTML extraction, observed current versions, read-passage hashes and the independent diagnostics.

The diagnostics use nine named groups of exact finite checks, not a large repeated test count: the radial primitive, orbit transfer, independent Pfaffian expansions in three fiber dimensions, gauge-bracket cancellation, old method countermodels, strict finite assignments, the constructed protected comparison, and fixed-capacity transport identities are included. They neither compute an arbitrary packing nor certify a universal geometric statement. The first finite run had an incorrect expected orbit minimum: the two-cycle mean is 1, while the three-cycle mean is 4/3. The telescoping identity passed; the expected minimum was corrected to 1. The failed script and diagnosis are retained. The primary-version comparison was strengthened after retrieving the published Buse–Hind PDF; its earlier arXiv-only paragraph is preserved, not silently overwritten. An initial acquisition setup also failed because an optional HTML parser was absent; no request had run, and the retained standard-library extractor is explicitly derived from I70's. See [development failures](../sources/i74_relative_symplectic_packing/development-failures.json).

**Original I70 analytic audit:** I, S, D, orbit transfer, curvature and their method countermodels pass in their original scopes without repairs. **New author deductions:** A1–A3, B1–B3 and compact-family fixed-slack uniformity have the proofs above; these are restricted technical statements awaiting any parent-requested fresh review. **GAP:** arbitrary fixed-capacity prefix transport, adapted arbitrary-complement models, general slack-independent unequal-ball stability, and RP itself. **Counterexample:** none to RP or to strong stability of a fixed smooth prescribed ball complement.

The useful new direct datum is the explicitly permitted q/K with protected positive region and its exact area cost. The useful transport datum is a paid path for concrete nonlinear prefixes, including a repair of the failed Alexander method on its own shear example. Neither supplies the global compatibility missing for arbitrary e, and neither warrants a count increment. Parent integration, fresh independent proof/significance review, commits and publication remain the parent's responsibility.
