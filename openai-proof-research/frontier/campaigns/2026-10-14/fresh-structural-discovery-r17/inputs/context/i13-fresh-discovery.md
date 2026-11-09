# i13 fresh discovery: regular-pattern pinning, projected counts, and nonconventional fluctuations

Research date: 2026-10-08 PDT; retrievals on 2026-10-09 UTC. Corpus pin: `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

**Outcome: no additional substantial positive finding is proposed.** Three distinct hypotheses were developed against actual manuscript statements and current primary literature. The most promising construction, a biregular-pattern extension of the Sidorenko counterexample, meets an exact obstruction to both its original pinning step and a natural sign-averaging repair. The projected-counting proposal meets incompatible-extension and exponential-variance obstructions. A proposed square-root fluctuation upgrade of qualitative multiple mixing is false, with a complete bounded-observable counterexample below. These are research screens, not replacements for the requested findings. No R number or count change is assigned; R006, R008, R009 remain the three accepted findings at this task's input snapshot.

All pinned theorems are accepted, without auditing upstream truth. The proofs below concern new deductions or failures of proposed extensions. The Gaussian construction is a classical long-memory obstruction, not a reopening of the excluded Gaussian-decoupling route.

## 1. Brief, input state, and evidence

The complete unabridged brief is [full-brief.txt](../sources/i13_fresh_discovery/full-brief.txt); the task record is preserved byte-for-byte under `inputs/frontier/iterations/iteration13-fresh-discovery-task.json`. Its operative scope was: seek fresh combinatorial, TCS, dynamical, or mathematical-physics mechanisms; screen at least three genuinely distinct hypotheses against strongest source statements and companions; prove the strongest viable extension; check primary literature early and after formulation; preserve precise contracts, failed steps, reproducible diagnostics, immutable identities and input snapshots; write only this report and the two assigned i13 directories; do not delegate further, stage, commit, change indexes, assign an R number, or increment the count. It excludes active topology/complex-prime-mode work, R009 variants, spent operator, hot-spots, Hodge, Gaussian-decoupling, arithmetic-reservoir, Tingley-ultraproduct, quantum-memory EPnI and Potts-FIID routes.

Read scope controls: `AGENTS.md`, `sources/upstream.json`, the catalogue selectively, `frontier/TEN-FINDINGS.md`, `frontier/README.md`, `frontier/iterations/README.md`, and historical discrete/structural and excluded-route reports. Snapshot copies and initial SHA-256 identities are in [input-snapshots.json](../sources/i13_fresh_discovery/input-snapshots.json). The original complete `sources/preprints-tree.json` was parsed, every entry traversed, and all paths/types/blob identities retained in [complete-inventory-screen.json](../sources/i13_fresh_discovery/complete-inventory-screen.json): **13,223 entries, 10,373 blobs, 2,850 trees, `truncated: false`**. This is full metadata coverage, not a claim to have read every manuscript.

Downloaded 126 TeX/BibTeX files from 15 selected manuscripts/companions. Every download's computed Git blob SHA-1 agrees with the complete pinned tree. [pinned-manifest.json](../sources/i13_fresh_discovery/pinned-manifest.json) records exact pinned raw URL, path, Git blob identity, SHA-256, bytes and retrieval time. [theorem-contracts.json](../sources/i13_fresh_discovery/theorem-contracts.json) retains 251 exact labelled statement blocks with source locations; extraction is evidence storage, not a claim that every stored lemma was used. The deeper reads used below are identified by label.

Six current primary PDFs, their text extractions, version-bearing headers and SHA-256 hashes are retained in [literature/manifest.json](../sources/i13_fresh_discovery/literature/manifest.json). Early and final web-search outputs are preserved separately. Search results included irrelevant hits; only inspected primary papers support mathematical comparisons. Failure to find a duplicate is not evidence of global priority.

## 2. Source contracts and three hypotheses

### A. A biregular **pattern** violating Sidorenko

The target was a connected biregular bipartite pattern, preferably the point/triangle incidence graph of a regular triangulated surface, violating Sidorenko. This would extend family 161 into a structurally restricted class where the source's irregular color-refinement mechanism fails. It is not a request to make the **host** regular: that reduction is already classical. No separate MathDB rank or significance score is asserted. The named problem is the regular-pattern restriction of Sidorenko's inequality after accepting its general disproof.

Read *A counterexample to Sidorenko's conjecture*, `build/sections/introduction.tex`, blob `32890ea14c106eeb0556da93226165ac93739371`, `thm:main`: a fixed incidence graph H of 22 triples on 13 points, with 35 vertices and 66 edges, has a finite simple host G with `t(H,G)<p(G)^66`. Point degrees are 4,5,6; face degrees are 3. `cor:amplification` already gives arbitrarily small normalized density ratios and fixed-density injective deficits. `cor:forcing` already gives a nonconstant graphon matching the edge and H densities. These are excluded duplicates.

The stronger working interface is in `build/sections/kernel.tex`, blob `bbe11be8fffe968012060ec43e6aff597e922831`: `lem:kernel-support` constructs a single negative all-nonempty coefficient; `lem:pinning` isolates the intended type map using vertex and pair scores, assuming color refinement becomes discrete within both parts. The finite-field rank-layer/tail estimates are proved for the specified source complex, not for an arbitrary replacement complex. They are not silently imported into our attempted regular construction.

Primary comparisons: [Coregliano–Razborov, *Biregularity in Sidorenko's Conjecture*, v2](https://arxiv.org/abs/2108.06599v2), Theorem 3.1, concerns regularizing the kernel/host. [Conlon–Lee, *Sidorenko's conjecture for blow-ups*, v3](https://arxiv.org/abs/1809.01259), Corollary 1.3, supplies a sufficiently large one-sided blow-up satisfying Sidorenko. Thus indiscriminate blowing up a violating pattern can destroy the violation. Neither result provides the requested biregular violating pattern. Section 3 develops and blocks the most promising construction rather than asserting this target is impossible.

### B. Count distinct projections of common bases without completion multiplicities

For two rank-R matroids M1,M2 on a finite set E and a retained set A⊆E, define

`P_A={B∩A : B is a common base of M1,M2}`.

The target was a uniform FPRAS for `|P_A|` in the independence-oracle model, with polynomial calls/bit work in `|E|, ε^-1, log δ^-1`, counting each visible configuration once. More generally one could ask for distinct retained-coordinate vectors of common integer polymatroid bases with binary capacities. This is a genuine change of the counted object, not the already-solved full-base problem. No published high-importance designation for this exact projected problem was verified; it cannot pass the significance gate on application language alone.

Read *An FPRAS for Common Integer Polymatroid Bases with Binary Capacities*, `build/sections/introduction.tex`, blob `c74bce3869be3469749091b6f3ab60dbf61a81fa`, `thm:main`: for normalized monotone integral submodular r1,r2 with equal total rank R, count exactly once each nonnegative integer x with `x(E)=R`, `x(S)≤ri(S)` for every S and i. Runtime is polynomial in ground-set size, binary input length, ε^-1 and log δ^-1 on every execution; zero counts are detected exactly. Its matroid and cell-bounded contingency-table companions were checked. The matroid paper's `cor:intersection` already covers all, prescribed-size, and maximum-size common independent sets, including unequal input ranks. Projection is not one of these changes of cardinality.

The early current-literature check found [Chen–Liu, *An FPRAS for Counting Common Bases of Two Matroids*, v1, 5 October 2026](https://arxiv.org/abs/2610.06724v1). Theorems 1.6 and 1.16 treat substantially more general convolution/curvature inputs; Appendix C already covers strong orientations, Euler tours, reliability variants, integer polymatroid intersections, bounded flows, network-matrix vertices, rainbow matchings and degree-constrained forests. These were excluded as fresh routine applications. In particular C.23 uses a **unique** flow completion. This does not justify counting arbitrary projections with many completions. No curvature or log-concavity contract for the required multiplicity-flattened law was established. Section 4 gives exact failures even with ideal completion counts.

### C. Upgrade qualitative multiple mixing to square-root fluctuations

The proposed stronger conclusion was: for every invertible mixing probability system and bounded centered f,g, the laws of

`N^-1/2 Σ_{n=1}^N f(T^n x)g(T^{2n}x)`

are tight, with a possible subsequent CLT or O(N^-1) mean-square error for averages. This would remove quantitative decorrelation hypotheses from a meaningful portion of nonconventional limit theory. It is **false**.

Read family 145, *Rokhlin's multiple-mixing problem for one transformation*, `01-introduction.tex`, blob `49fd4d05cdb48edec0d6e09f4044fe01e340c2a4`, `thm:main`: each fixed finite family of sets asymptotically factors when every pairwise time separation diverges. Its `08-consequences.tex`, `cor:endomorphisms-flows`, already covers forward endomorphisms and strongly L1-continuous flows; these are not discoveries.

Read the strongest family-154 companion, *Pointwise Multiple Ergodic Averages for Mixing Transformations*, introduction blob `a6df9e8a343b9ec676ebac165d69a36af7fca396`, `thm:main`: for every fixed n≥2 and fixed bounded tuple, consecutive multiple averages converge almost surely to the product of means. The exceptional set can depend on the tuple, and no rate is supplied. Its `inputs.tex` says explicitly that its higher-order mixing input is qualitative. Triple and fourfold companions and *Triple ergodic averages with distinct integer slopes* (introduction blob `bf7d99007cd9db871618b274f414105a2ec76350`, `thm:main`) were checked to exclude merely changing slopes or lengths. The last paper's internal smooth-triple input has a broader nonmixing scope than its headline; no quantitative fluctuation conclusion is extracted from it.

[Kifer–Varadhan, *Nonconventional limit theorems in discrete and continuous time via martingales*, v4](https://arxiv.org/abs/1012.2223v4), Section 2, imposes quantitative dependence/approximation conditions. [Dobrushin–Major (1979)](https://www.renyi.hu/~major/articles/non-central.pdf) and [Breuer–Major (1983)](https://www.renyi.hu/~major/articles/breuer.pdf) already distinguish long-memory noncentral scaling from summable-correlation CLTs. The proof in Section 5 is an explicit two-slope bounded-observable obstruction; its mechanism is classical, and it does not count as a corpus-enabled discovery.

## 3. Full obstruction to the proposed regular-pattern construction

### 3.1 Vertex/pair pinning fails for every biregular pattern

Let F=(P⊔Q,L) be finite, with nonempty parts and no isolated vertices, with every P-vertex of degree d and every Q-vertex of degree c. Write p=|P|, q=|Q|, m=|L|, so pd=qc=m. Assume at least one part has more than one vertex. For arbitrary real scores s_a, t_b, u_ab, on all part-preserving maps h define

`Q(h)=Σ_{v∈P}s_{h(v)} + Σ_{w∈Q}t_{h(w)} + Σ_{vw∈L}u_{h(v),h(w)}`.

For an actual edge ab∈L, let k_ab collapse all of P to a and all of Q to b. Then

`(1/m) Σ_{ab∈L} Q(k_ab) = Q(id)`.

Indeed `Q(k_ab)=p s_a+q t_b+m u_ab`; each a occurs in d edges and each b in c. Summing and using pd=qc=m proves the identity. Therefore at least one nonidentity constant map has score at least the identity's. These competitors are genuine homomorphisms, so forbidding nonedge target pairs does not remove them.

This proves that the source's unique-maximizer conclusion cannot hold for a biregular pattern with this score interface, for **any** choice of scores. Color refinement also remains stuck at its two initial part colors. It does not prove every other pinning scheme impossible.

For positive vertex priors π_a, ν_b and positive edge thinning factors λ_ab, the same identity applied to logarithms gives a useful stronger form. Define

`w(h)=∏_{v∈P}π_{h(v)} ∏_{w∈Q}ν_{h(w)} ∏_{vw∈L}λ_{h(v),h(w)}`.

If w*=w(id), then `(∏_{ab∈L}w(k_ab))^(1/m)=w*` and hence `Σ_{ab∈L}w(k_ab)≥m w*`. Normalizing priors does not affect this identity. This is the relevant statement for source type weights.

### 3.2 A parity-conditioned random-sign repair also has the wrong expected sign

This is an exact finite statement about the source's coefficient mechanism. It assumes **no** unproved rank-layer estimate for a replacement complex.

Let K be a finite simplicial complex specified by distinct three-element faces, every point-pair appearing in a face belonging to exactly two faces, and with connected face-neighbor graph. Suppose every point lies in the same positive number d of faces. Its point/face incidence graph F is (d,3)-biregular. Let C be its set of corners, m=|C|=3|faces|. In this setting m≥2. A concrete example is the standard triangular torus on `(Z/4)^2`, with 16 points, 32 faces, m=96, d=6.

For each point-pair e, let U_e be its four incident corners. At a corner κ, the two point-pairs through that corner in its face are e,f. Put `M_κ=U_e∪U_f`, `Γ_κ=U_e△U_f`. Distinct faces share at most one pair, so `|M_κ|=7`, `|Γ_κ|=6`, and `M_κ\Γ_κ={κ}`.

Fix 0<θ<1 and signs σ_κ. The source two-branch activation law at κ is: with probability 1/2 activate M_κ and bias its signs by `1+σ_κ θ χ_{Γ_κ}`; with probability 1/2 activate Γ_κ and bias by `1−σ_κ θ χ_{Γ_κ}`. Each branch is a normalized nonnegative probability law. Define its moment

`A_κ(α,β)=E[1_{α∪β⊆S} χ_{α△β}(ξ)]`.

For nonempty α,β, its entries are exactly:

- if α=β⊆Γ_κ, the value is 1;
- if α=β⊆M_κ and κ∈α, the value is 1/2;
- if `α△β=Γ_κ` and `κ∈α∪β⊆M_κ`, the value is `σ_κ θ/2`;
- all other entries are zero.

This follows by expanding the two branch expectations; if the union is contained in Γ_κ, the two signed contributions cancel. In particular nonempty disjoint labels have zero moment.

For a part-preserving map h from F to itself, set moments at a nonincident image pair to zero and form the all-nonempty coefficient

`C_σ(h)= Σ_{α_e⊆C, α_e≠∅ for every point-pair e} ∏_{κ=(v,j)∈C} A_{h(v),h(j)}(α_{e(κ)},α_{f(κ)})`.

Every sum is finite. This is the formal source coefficient with K substituted for the original complex. Give h the positive weight w(h) of Section 3.1. Choose σ uniformly from the sign vectors with `∏_{κ∈C}σ_κ=−1`.

**Proposition.** For every K, θ and positive weights just specified,

`E_σ Σ_h w(h) C_σ(h) ≥ [63m−|Aut_part(F)|(θ/2)^m]w*`

`≥ m[63−2(θ/2)^m]w* >0`.

Here automorphisms preserve the point/face parts. Thus the parity-conditioned random-sign method cannot prove a negative coefficient by making its expectation negative, regardless of these type weights.

**Proof.** First, for any exponents b_κ,

`E_σ ∏κ σ_κ^{b_κ}`

is 1 if every b_κ is even, −1 if every b_κ is odd, and zero otherwise. One can see this by selecting m−1 independent signs and setting the last equal to minus their product. This includes m≥2 and uses no limiting argument.

Each nonzero local moment is either a positive diagonal number or a positive multiple of a single σ at its target corner. A term in C has exactly m local factors. Its averaged sign can be negative only if it uses every one of the m target signs oddly. Consequently every factor must be signed and each target corner must appear exactly once. The induced corner map is then a bijection. All nonzero target pairs are incidences. Biregularity forces the vertex map to be a bijection as well: at a target point, its d incoming image incidences must be the disjoint union of d incidences for each preimage point, so there is exactly one preimage; the same argument uses degree 3 at a face. Thus every possible negative term comes from a part-preserving automorphism h.

For an automorphism there is exactly one nonzero all-nonempty label assignment, after relabelling coordinates: `α_e=U_{h(e)}`. Here is the support argument, to make this extension explicit. For identity types, `∩_{κ∈U_g}M_κ=U_g`: a coordinate at a corner lies in the supports of all four corners of g exactly when it belongs to U_g. Indeed its available corners lie in its own face and the two opposite faces on its two pairs; two different opposite faces cannot supply both endpoints of a third pair. Thus α_g⊆U_g. At a corner, the two nonempty labels must intersect, because disjoint labels have zero moment. Their containing sets meet only at that corner. Applying this at all four corners of g forces α_g=U_g. The unique product is `(θ/2)^m∏κσ_κ=−(θ/2)^m`. Relabel by h for any automorphism. All automorphisms have weight w*, since they permute each of the vertex and edge sets.

Now fix a constant homomorphism k_ab to a target corner κ=(a,b). No term in its coefficient can have negative averaged sign: it uses at most one of the m sign variables, so its parity pattern cannot be all odd. For each nonempty α⊆Γ_κ, assigning this same α to every source point-pair gives local diagonal moment 1 at every corner. These are 63 distinct terms. Hence `E C_σ(k_ab)≥63`.

Every map other than an automorphism has nonnegative averaged coefficient by the sign classification. Constant maps here are not automorphisms. Summing their contributions and using Section 3.1 gives

`E Σ_h w(h)C_σ(h) ≥63 Σ_{ab∈L}w(k_ab)−|Aut_part(F)|(θ/2)^m w*`

`≥[63m−|Aut_part(F)|(θ/2)^m]w*`.

Finally an automorphism of this complex is determined by the image of one face and the ordering of its three points. Fixing a face pointwise fixes the unique other face along each of its pairs and hence its third point. Connectedness of the face-neighbor graph propagates this to every face and point. Therefore `|Aut_part(F)|≤6|faces|=2m`. The claimed strict bound follows. ∎

**Scope of this obstruction.** It does not prove that every fixed sign choice has nonnegative coefficient. A positive mean does not exclude exceptional negative choices. It also does not identify an average of full kernels with a kernel whose homomorphism density is that average; such an interchange would be invalid. The statement blocks precisely the proposed expectation-based sign repair of this finite coefficient scheme. It is neither a new Sidorenko counterexample nor a proof of Sidorenko for biregular graphs.

**Next concrete target.** Before revisiting geometric rank layers, construct an admissible activation system that retains a negative identity coefficient but suppresses collapsed-map diagonal terms. For this scheme the 63 diagonal terms survive automatically. Source moments are second moments, so `|A(α,β)|²≤A(α,α)A(β,β)`; simply setting the two needed diagonal entries to zero also kills the desired off-diagonal entry. A replacement needs a global constraint excluding constant labelings, not a verbal assertion that higher-order pinning removes them. Alternatively exhibit and analytically control a specific exceptional sign choice. Only after a negative finite coefficient is obtained should the new complex's singular-profile tail estimate be attempted. Neither missing construction was supplied here.

## 4. Full projected-counting obstructions

### 4.1 Projection does not commute with intersection

On E={a,b,c}, let M1 have blocks `{a}`, `{b,c}` and M2 have blocks `{b}`, `{a,c}`, each with rank one on each block. Their base families are respectively `{ab,ac}` and `{ab,bc}`. Their common-base family is `{ab}`. On A={c}, each separate projection is `{∅,{c}}`, while the projection of the intersection is `{∅}`. The two individual completions of `{c}` require different deleted elements.

Thus replacing each rank oracle by an independently projected constraint can admit spurious visible configurations. This small example disproves that reduction, not the existence of another FPRAS.

### 4.2 Visible external fields cannot generally remove multiplicities

Take K4,4 and its two partition matroids, whose common bases are its 24 perfect matchings. Retain the two disjoint diagonal edges (1,1),(2,2). For the four visible masks 00,10,01,11, the completion counts are

`m00=14, m10=m01=4, m11=2`.

Both distinguished edges occur in 2!=2 matchings. Exactly the first occurs in 3!−2!=4, and similarly for the second; subtract from 4! to get 14.

Positive activities x,y on the two visible edges give projected masses proportional to `14,4x,4y,2xy`. They cannot all be equal, since equality of a product-weighted 2×2 table requires `m00 m11=m10 m01`, whereas 28≠16. This only rules out fields on the **retained** coordinates; it does not claim that every weighting of hidden edges or every richer model fails.

### 4.3 Exact inverse-completion sampling can still cost exponentially many samples

Suppose, even ideally, that one can draw a perfectly uniform full common base B and compute its fiber size m(B∩A) exactly. The unbiased estimator `Y=1/m(B∩A)` has `E Y=K/Z`, where K is the number of visible masks and Z the full-base count. Multiplying its sample mean by Z would estimate K.

For one K4,4 block, `E Y=4/24=1/6`, whereas

`E Y²=(1/24)(1/14+1/4+1/4+1/2)=5/112`.

For q disjoint blocks, the full uniform law factors, Y is a product, and

`E Y²/(E Y)²=(45/28)^q`.

Thus its relative variance is `(45/28)^q−1`. With s independent samples the relative mean-square error is exactly this quantity divided by s. It requires exponentially many samples for fixed relative RMS accuracy, even with exact fiber information. This is a limitation of this estimator, not a complexity lower bound for all randomized algorithms or a universal high-probability sample lower bound.

Likewise rejection from the full uniform law with acceptance probability `c/m(mask)` can be uniform on masks only with `c≤min m=2^q`. Its best possible acceptance rate in this class is

`c K/Z≤2^q 4^q/24^q=3^-q`.

The examples use just two explicit partition matroids on 16q elements. Binary-capacity expansion and rank-oracle precision are not the issue.

**Next concrete target.** Produce either a bijective two-polymatroid encoding of the visible masks, or a chain on visible masks with a polynomial conductance/Poincaré bound under its *uniform support law*. An FPRAS for each individual fiber, obtainable from restrictions/contractions of the source problem, does not supply such a bound. Current convolution/curvature theorems would be relevant only after their hypotheses are verified for a representation of that law; those hypotheses are not asserted here. General projected counting remains unresolved in this report.

## 5. Full nonconventional fluctuation counterexample

**Proposition.** There is an invertible probability-preserving system mixing of every finite order, and centered bounded functions f,g taking values in {−1,1}, such that, for

`S_N=Σ_{n=1}^N f(T^n x)g(T^{2n}x)`,

`liminf_{N→∞} P(|S_N|>M√N)≥1/36` for every fixed M>0.

In particular `S_N/√N` is not tight, although `S_N/N→0` almost surely. The source guarantees the latter; it also has an elementary proof in this example.

**Construction and mixing.** Set `r(h)=(1+|h|)^(-1/4)`. This is positive definite on Z because

`r(h)=Γ(1/4)^-1 ∫_0^∞ t^(-3/4)e^-t (e^-t)^|h| dt`.

For each 0<a<1, `a^|h|` is the covariance of a unit-variance stationary Gaussian AR(1) process; nonnegative mixtures preserve positive definiteness. The covariance therefore defines a two-sided stationary centered unit-variance Gaussian sequence A_h. Take an independent copy B_h on the product sequence space, and let T shift both by one. It is invertible and measure preserving.

For any finite collection of time-separated finite coordinate blocks, off-block covariance entries tend to zero. Gaussian characteristic functions consequently converge to those of independent blocks. Cylinder events then factor asymptotically (first for continuity sets, then for all cylinder events by approximation), and approximation in measure by finite-coordinate events proves mixing of every fixed finite order for the full sequence sigma-algebra. No quantitative alpha-mixing claim is being made. Put `f=sgn A_0`, `g=sgn B_0`, assigning either value at zero, a null event. Both means are zero.

**Covariances and the leading bilinear part.** For unit Gaussians X,Y with correlation ρ,

`E[sgn X sgn Y]=(2/π)arcsin ρ`, and `E[X sgn Y]=sqrt(2/π)ρ`.

The first identity follows by rotational symmetry of a two-dimensional standard Gaussian and the angle between the two defining half-planes; the second follows by `E[X|Y]=ρY` and `E|Y|=sqrt(2/π)`. Thus no unproved Hermite estimate is needed.

Write a=sqrt(2/π), `Z_n=sgn A_n sgn B_{2n}`, `W_n=a² A_n B_{2n}`, `D_n=Z_n−W_n`, and c=a^4=(2/π)^2. Independence of A and B gives, for h=|i−j|,

`E Z_i Z_j=c arcsin(r(h)) arcsin(r(2h))`,

`E W_i W_j=E Z_i W_j=E W_i Z_j=c r(h)r(2h)`.

Hence the sums `M_N=ΣW_n`, `R_N=ΣD_n` are orthogonal in L², and

`E D_i D_j=c[arcsin(r(h))arcsin(r(2h))−r(h)r(2h)]`.

For h≥1, both correlations are bounded away from 1. Taylor's formula on the fixed compact interval `[0,2^-1/4]` gives `0≤arcsin u−u≤C u³`. Therefore `0≤E D_iD_j≤C'(1+h)^-1`. At h=0 the variance is finite. It follows by summing the covariance diagonals that

`E R_N²=O(N log(N+1))`.

On the other hand

`V_N=E M_N²=c[N+2Σ_{h=1}^{N−1}(N−h)r(h)r(2h)]`

`~ C0 N^(3/2)`, where `C0=(2/π)^2 (8/3)2^(-1/4)>0`.

For completeness, `h^(1/2)r(h)r(2h)→2^-1/4`; split off any fixed finite initial segment and compare the remainder above and below with fixed multiples of h^-1/2. The elementary Riemann-sum limit is `N^-3/2 Σ(N−h)h^-1/2→∫_0^1(1−u)u^-1/2du=4/3`. The singular endpoint is controlled by `Σ_{h≤εN}h^-1/2≤2√(εN)`. This proves the stated asymptotic and `E R_N²=o(V_N)`.

**Fourth moments give non-tightness; variance divergence alone would not suffice.** Let U=(A_1,…,A_N), V=(B_2,…,B_{2N}), independent Gaussian vectors with covariance matrices P,Q. Then M_N=a² UᵀV. Conditioning on U,

`E M_N^4=3a^8 E(Uᵀ Q U)^2`

`=3a^8[(tr(PQ))²+2tr((P^(1/2)QP^(1/2))²)]≤9 V_N²`.

The middle equality follows by diagonalizing the positive semidefinite quadratic form in independent standard Gaussians and using their second/fourth moments. The last inequality uses `Σλ_i²≤(Σλ_i)²` for nonnegative eigenvalues. Singular covariance matrices are allowed, using their square roots.

Paley–Zygmund applied to M_N² yields

`P(|M_N|≥sqrt(V_N/2))≥1/36`.

Chebyshev and `E R_N²=o(V_N)` show `P(|R_N|>sqrt(V_N/8))=o(1)`. On the intersection of the first event and the complement of the second, `|S_N|≥sqrt(V_N/8)`. This threshold is asymptotic to a positive multiple of N^3/4 and therefore eventually exceeds M√N for every fixed M. The required liminf follows. Taking any tail tolerance less than 1/36 proves failure of tightness.

Finally `E S_N²=O(N^3/2)`. Along N=k³, Chebyshev gives a summable upper bound `O(k^-3/2)` for `P(|S_N|>εN)`. Borel–Cantelli yields `S_{k³}/k³→0` almost surely. Since |Z_n|≤1 and `(k+1)³−k³=O(k²)`, interpolation gives `S_N/N→0` at all integers. This independently verifies compatibility with the stipulated pointwise theorem. ∎

**Next target and limit.** A positive fluctuation theorem must use a quantitative, summable dependence or approximation condition that this example violates. Merely assuming all fixed orders of mixing is insufficient. Establishing such a theorem under a genuinely weaker explicit condition than Kifer–Varadhan would require a new martingale/cumulant estimate; none is derived from the qualitative corpus contracts here. This counterexample is a reason to park the rate-free upgrade, not a new substantial result to count.

## 6. Additional quick threshold screen

The strongest actual family-186 statement is not just the catalogue's monotone threshold bound. The hypergraph manuscript `introduction.tex`, `thm:main`, gives, for each fixed r≥3 and every n≥r, every bias 0<p<1 and every relabeling-invariant Boolean f,

`Var_p(f)≤C_r I_p(f)/(log n)^(r/(r−1))`,

without monotonicity. Its graph companion already has the nonmonotone r=2 analogue. The hypergraph `completion.tex` keeps a favorable bias factor in the high-degree term, but its low-degree term is separate. Retaining only the high-degree bias factor and attaching it to the whole variance is unjustified. Ordinary threshold integration is already `cor:threshold`, so it was not counted as a new estimate.

An extension to general vertex-exchangeable random graphs cannot follow from this product-measure contract. For example fix 0<a<1/4, take latent U uniform on [−a,a], and conditionally sample G(n,p+U), for p∈[a,1−a]. Let f be the increasing invariant property that at least half the possible edges are present. Conditional laws of large numbers and dominated convergence give, for |p−1/2|<a,

`P(f=1)→P(p+U>1/2)=(p−1/2+a)/(2a)`.

At the zero-probability equality value of U, the choice of strict versus nonstrict majority is immaterial. By monotonicity and evaluation at fixed points on either side of the limiting quantiles, the ε-to-(1−ε) width tends to `2a(1−2ε)>0`. Thus the annealed exchangeable model has a broad window despite every conditional sample being an ordinary product graph. This blocks an overbroad annealed extension; it says nothing against a carefully formulated independent inhomogeneous or quenched theorem. No fourth prospective finding is proposed.

## 7. Verification, literature limits, and handoff

Run from this repository:

```sh
python frontier/experiments/i13_fresh_discovery/diagnostics.py
python frontier/experiments/i13_fresh_discovery/verify.py
```

The deterministic diagnostic checks the score identity on all 173 nonempty biregular labelled bipartite graphs with each part size 2–4, for three independent score arrays per graph; verifies an explicit (6,3)-biregular triangular torus; checks all 127² nonempty entries of the local activation matrix against the two-branch law; enumerates all 24 K4,4 perfect matchings and the incompatible-extension example; records exact rational tensor-power variance/rejection factors; and computes the Gaussian covariance sums through N=262144 plus a separate finite-matrix fourth-moment calculation. Integer/rational checks are exact. Floating-point variance asymptotics and matrix checks are diagnostics only. The general proofs are Sections 3–5, not these finite calculations.

The final search tested the exact scopes—biregular **patterns** versus hosts, projected **support** versus weighted marginals, and long-memory nonconventional fluctuations. It did not establish worldwide priority for any obstruction. The classical long-memory comparison is affirmative prior art; the counting paper's October 2026 applications rule out several attractive but already-covered routine targets. This report makes no MathDB score, priority, human-review, or formal-certification claim.

[artifact-manifest.json](../sources/i13_fresh_discovery/artifact-manifest.json) seals this report and every i13 artifact except the manifest itself and its derived verification result. [verification.json](../sources/i13_fresh_discovery/verification.json) records source-blob checks, literature hashes, snapshot equality, and artifact integrity. Concurrent parent changes, if any, are distinguished from preserved snapshot bytes. No source/index write is needed for this handoff.

Recommendation: retain i13 as a negative discovery record. The most concrete genuinely new next construction obligation is a replacement for the Sidorenko activation scheme that eliminates globally collapsed labels without killing required off-diagonal moments, followed by a new singular-tail estimate for the replacement complex. Projected common-base counting needs a new uniform-support representation or mixing estimate; rate-free nonconventional square-root fluctuations should not be pursued. None warrants advancing the accepted count.
