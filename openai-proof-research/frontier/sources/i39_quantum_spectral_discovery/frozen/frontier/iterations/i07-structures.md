# Iteration 07, structural lane: simultaneous parity obstructions in dimension four

Date: 2026-10-08, America/Los_Angeles (retrievals extend into 2026-10-09 UTC).

**Status: one prospective finding, with a proposed proof, submitted for independent proof and contribution reviews. No accepted finding is added. The accepted substantial count remains TWO (R006 and R008).**

The proposed theorem is that, for every integer r ≥ 1, there is a closed connected oriented aspherical topological **four**-manifold M_r and an injection

\[
\iota_r:(\mathbb Z/2)^r\hookrightarrow\operatorname{Out}(\pi_1M_r)
\]

such that **no nonzero element of its image is induced by any homeomorphism of M_r**, including homeomorphisms of infinite order. Thus this is an obstruction to individual representatives, not merely to choosing representatives that form a finite group action. The dimension stays four as r increases. A more precise intermediate statement classifies a family of finite abelian covers by a lattice parity condition.

The proposed new construction uses ports with two labels: a channel and a bit. Along coordinate j, channel j flips and every other channel is preserved. Ordinary independent copies of the source parity gadget fail on mixed odd relations; the explicit failure and its repair are part of the argument below. The geometric extension in Lemma G, especially the passage from the source's globally colored cyclic graph to endpoint-colored general graphs, is the principal review target. It is proved below by specifying and checking the local construction, rather than silently importing a theorem with broader hypotheses than its statement.

This report accepts all theorems at the pinned OpenAI revision as requested. It does not audit their truth. No claims about worldwide priority are made. In particular, the older literature on generalized Nielsen realization is a real comparator, not evidence to be dismissed by a failed search. No external messages, submissions, commits, or shared-index changes were made.

## 1. Scope, screens, and source record

Pin: `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` in `https://github.com/openai/math`.

The headings of all available families in the requested ranges 032–069, 102–142, 155–210, 240–259, and 285–320 were extracted to `../sources/i07_structures/broad-screen-headings.json`. This was a catalogue screen, not a claim to have proved or exhaustively compared all their contents. The complete `sources/preprints-tree.json`, not the truncated root tree, was used to identify manuscript files.

The deeper retrieval contains all 253 TeX/BibTeX files for the selected families 126, 177, 197, 207, 247, 249, 250, 251, 253, 259, 285, 305, 315, and 320. `../sources/i07_structures/retrieval-manifest.json` records the immutable raw URL, upstream path, family, bytes, UTC retrieval time, and SHA-256 of each file. `theorem-contracts.json` stores exact statement text, labels, source line ranges, and hashes. Files were retrieved from raw GitHub at the pin; they are not inferred from catalogue abstracts.

The prior R006/R008 acceptance rules, the failed Frankl constructions, the parked Hodge constructions, the closed multiplier-operator family, and the Gaussian candidate's classical-decoupling demotion were read as scope controls. None is relaunched here.

### Candidate A: robust matching SDP lower bounds — rejected

Family 126, `Exponential-PSD-rank-of-positively-shifted-matching-matrices-October-5-2026/build/source/sections/introduction.tex`, `thm:main`, states: there is an absolute c > 0 such that, for each fixed 0 < ρ < 1, there is n₀(ρ), and for every even n ≥ n₀(ρ),

\[
\operatorname{rank}_{\rm psd} (|M\cap\delta(U)|-1+\rho)_{U,M}\ge 2^{cn}.
\]

Factors are arbitrary real PSD matrices and entries are exact. `cor:exact-lift` already covers unshifted rank and exact affine SDP lifts. The endpoint ρ = 1 has a diagonal factorization of size binomial(n,2).

A tempting extension was robustness under exponentially small arbitrary entrywise perturbation. It is false. Kaniewski–Lee–de Wolf, *Query complexity in expectation*, Theorem 19, give a nonnegative approximation of the unshifted matching slack of PSD rank

\[
2^{O(n^{1/2+\varepsilon}(\log n)^2)}
\]

and entrywise error at most `2^{-(n/2)^{2ε}}`, with exact agreement at small entries. Taking ε = 1/4 gives subexponential rank and error `2^{-sqrt(n/2)}`. Appending a scalar PSD block adds the exact constant ρ to every entry and increases rank by at most one. Thus the same approximation defeats the proposed uniform robustness assertion for the positively shifted matrix. This is a general argument, not a numerical test. Primary manuscript: https://homepages.cwi.nl/~rdewolf/publ/qc/query_expectation-arxiv.pdf . The accepted manuscript itself explicitly flags this comparator.

### Candidate B: a finitely presented ordinary Eilenberg–Ganea counterexample — not obtained

Family 249, `.../build/sections/introduction.tex`, `thm:main`, gives a finitely generated residually finite G with cd_Z G = 2 and gd G = 3. Its seed is the height kernel for an acyclic flag triangulation of the presentation complex

\[
\langle x,y\mid x^2=y^5,\ x^2=(xy^{-1})^3\rangle.
\]

The same introduction explicitly states that G is **not finitely presented**, although it has a finite length-two free resolution. Family 250's strongest companion, `Simple-F-infinity-overgroups-of-groups-with-decidable-word-problem-September-23-2026`, `thm:main`, embeds every finitely generated decidable-word-problem group in a simple group of type F∞. It expressly gives neither torsion-freeness nor finite cohomological dimension.

The needed bridge is an embedding preserving cd ≤ 2. A two-dimensional classifying-space construction cannot contain this G, because its subgroup cover would contradict gd G = 3. The dimension issue cannot be omitted. Leary's primary *Subgroups of almost finitely presented groups*, Theorem 3.4, gives a finitely presented two-generator overgroup with cd at most cd G + 2, not cd G. Its Theorem 3.3 applies to a special HNN extension of a free group, not to arbitrary cd-two inputs. Source: https://d-nb.info/1162825146/34 . No dimension-preserving envelope was constructed; the route is not a result.

### Candidate C: periodic Kazhdan examples — duplicate

The principal family-247 manuscript already has `cor:kazhdan`: its infinite finitely presented periodic Steinberg group has property (T) and is nonamenable. The residual-finiteness companion already gives the infinite finitely presented residually finite 2-group. Combining finite-index inheritance of (T) with these statements is routine. It is not a new substantial deduction.

### Candidate D: puncturing coboundary expanders for quantum codes — insufficient interface

Family 177, `thm:main`, gives, for every fixed d ≥ 3, constants D and ε > 0 and arbitrarily large finite pure d-complexes with at most D top-dimensional faces at each vertex, and

\[
\|\delta_i f\|\ge\varepsilon\operatorname{dist}(f,B^i),\qquad 0\le i<d.
\]

Weights are the top-face incidence probability weights, and coefficients are F₂. In particular every lower-degree cocycle is a coboundary. Puncturing top faces does not by itself supply positive-rate, large-distance logical cohomology. A formerly small coboundary with support in deleted checks can become a short logical word. No new distance or rate estimate was found. Neither the theorem nor this observation solves a quantum-code problem.

### Candidate E: simultaneous four-dimensional realization obstructions — selected

The strongest applicable topology companions are the marked-disk, PD4, and nonhomeomorphic-manifold papers in families 305 and 320. All their TeX/BibTeX files were retrieved. The source already disproves Wall realization, constructs a Borel-counterexample pair, and constructs one unrealizable self-homotopy involution. Merely restating any of those would be a duplicate.

The remaining proposed advance is **unbounded elementary-abelian rank of individually unrealizable homotopy classes while the manifold dimension remains four**, with one common construction and an exact finite-abelian-cover obstruction. This is one construction and, if accepted, at most one finding. We do not count its cover criterion, individual involutions, and rank-r conclusion separately.

## 2. Named problem and bounded novelty assessment

The relevant MathDB entry is [Borel conjecture, 316143](https://mathdb.com/p/316143/borel-conjecture), retrieved through the search index. The observed entry describes the homeomorphism-existence formulation and labels it a conjecture; it supplied no numerical significance score or featured classification for this specialization. **No rank, score, or featured designation is asserted.** Its web status is not used to override the stipulated corpus, which already refutes the general four-dimensional assertion.

Primary prior-art comparisons:

1. Block–Weinberger, *On the generalized Nielsen realization problem*, Comment. Math. Helv. 83 (2008), Problem 1.1 and Theorems 1.5–1.6: obstructions to realizing finite homotopy actions, including a Z/2 example with centerless fundamental group. This is substantial prior art. Failure of a finite-order/group-action lift is weaker than excluding **every** homeomorphism representing a particular outer class. https://math.uchicago.edu/~shmuel/Nielsen.pdf
2. Bartels–Lück, *The Borel conjecture for hyperbolic and CAT(0)-groups*, arXiv:0901.0442v2, main theorem and Proposition 0.3: the dimensional hypotheses matter; the four-dimensional assertion uses a goodness condition. This prevents a casual appeal to a high-dimensional rigidity theorem. https://arxiv.org/abs/0901.0442
3. Davis–Hayden–Huang–Ruberman–Sunukjian, *Exotic aspherical 4-manifolds*, Theorem 1.1: homeomorphic but nondiffeomorphic smooth examples, not the individual topological-homeomorphism obstruction proposed here. The author-hosted file is a 2024 manuscript; the [Annals publication](https://annals.math.princeton.edu/2026/204-2/p06) is 2026. https://people.math.osu.edu/davis.12/papers/dhhrs.pdf
4. Daura Serrano, *Actions of large finite groups on aspherical manifolds*, arXiv:2407.13602, Theorem 1.6 and Proposition 1.11: bounds on actual finite homeomorphism groups under hypotheses on center and outer automorphisms. These concern actual actions and do not furnish the rank-r subgroup in the present statement. https://arxiv.org/abs/2407.13602

The literature directory retains all six primary downloads (including the two rejected-candidate comparators) and text extractions with hashes. Targeted searches covered individual versus finite-order Nielsen realization, elementary abelian outer actions, aspherical four-manifolds, and finite-cover realization. They did not establish an exact duplicate; **that is not a worldwide-priority proof**. A novelty reviewer should test whether a previously known equivariant reflection construction already implements this signed multi-channel constraint in fixed dimension. The finite-group-action and smooth-category distinctions must be maintained.

## 3. Exact accepted interfaces

Abbreviate the pinned family-320 manuscript by **B**, the marked family-305 tensor manuscript by **MT**, and the family-305 PD4 manuscript by **PD**. All paths below are relative to `preprints/`:

- B: `Nonhomeomorphic-closed-aspherical-four-manifolds-with-the-same-homotopy-type-October-4-2026/build/`.
- MT: `A-marked-tensor-obstruction-to-four-dimensional-disk-embedding-September-24-2026/build/`.
- PD: `A-PD4-group-without-an-aspherical-manifold-model-September-24-2026/build/`.

Every displayed contract below is at the pin. Exact TeX and SHA-256 are in the contract JSON. We import no conjectural estimate.

**B, `sections/tensors.tex`, `ten:assignment`.** Let K have characteristic zero and let Γ be a finite loopless multigraph, with a distinguished plus and minus endpoint for each edge. Each edge has a coordinate block h_e of dimension N_e ≥ 0 and algebraic power-series germs F_e,b_e. At each vertex v choose a family L_v of nonempty subsets of incident edges. Put

\[
T_v=K[t_e:e\in E_+(v)]/(t_e^2),\quad
S_v=\sum_{E_+(v)}(F_e+t_eb_e)-\sum_{E_-(v)}F_e.
\]

Suppose formal sections M_v, centered modulo the nilpotent parameters, have injective central tangent maps whose signed edge-difference map is an isomorphism, satisfy S_v(M_v)=0, and, for every L in L_v, satisfy

\[
\left(\prod_{e\in L\cap E_+(v)}t_e\right)
\left(\prod_{e\in L\cap E_-(v)}b_e\right)(M_v)
\in((\partial_hS_v)(M_v)). \tag{SC1}
\]

Then every edge can be assigned to one endpoint so that no prescribed L is assigned wholly to its vertex. The ideal is an actual gradient ideal, not its radical; products of distinct t_e remain. There is no bipartiteness hypothesis and no degree bound.

**B, `sections/reflection.tex`, `refl:input`.** Let D be a compact connected oriented smooth four-manifold with connected boundary S and free fundamental group H, homotopy equivalent to a finite graph with 2k two-spheres. Its full middle module must have a specified framed immersed hyperbolic basis of k planes with zero quadratic self-intersections. Attach three-cells on this basis to obtain a collared oriented PD4 pair (P,S), with P ≃ BH and π₁S → H onto. Reflect P in the dual panels of a finite flag triangulation of S, with an independent Z/2 label per vertex. The resulting Q is finite, oriented, aspherical and four-dimensional. If Q has a closed topological four-manifold model, S has a marked graph-type filling: a compact oriented four-manifold V with boundary S and a homotopy equivalence V → P extending the prescribed boundary map. The CAT(0)/assembly and controlled-filling inputs are included in this accepted interface.

**B, `sections/chambers.tex`.** `ch:four-tip-model` constructs the marked four-tip body with disjoint bodies and only opposite-port cap intersections; `ch:laws` supplies a Brunnian four-slot law with leading word `[[X₁,X₂],[X₃,X₄]]` modulo Γ₅. `ch:exterior-model`, `ch:homotopy-type`, `ch:exterior-duals`, and `ch:poincare-chamber` give the tube-side pushout, the free middle module, algebraic duals, and PD pair. These are geometric, based and framed statements. Color is not a geometric framing. The generalization of the finite body list and of the endpoint labels is proved in Lemma G below, not assumed as the literal scope of `ch:even-filling`.

**B, `sections/formal.tex`.** `for:edge-input` is an input for a single compact connected smooth three-manifold with one torus boundary, with the specified boundary cohomology line. It supplies a based connection slice, its actual curvature/gradient ideal, and marked peripheral holonomies. `for:formal-data` assembles such slices for the source's marked cuts over a cyclic graph. Its proof uses arbitrary incident plus/minus sets and treats each four-slot law separately. We explicitly verify its extension to our graph below. The underlying MT labels are `thm:edge-algebraicity` in `sections/04-algebraicity.tex` and `lem:tensor-nilpotent-correction` in `sections/05-vertices.tex`, as well as its edge-germ inputs. Exact single-cut/marked-algebraicity hypotheses are retained.

**B, `sections/cyclic.tex`, `cyc:criterion`.** For a finite connected aspherical Q with G → Z onto, if its double cover has a closed n-manifold model and all sufficiently large odd cyclic covers have none, the conjugation class of a lift of 1 is not represented by any homeomorphism of a double-cover model. The source proves this without a finite-order assumption on a hypothetical homeomorphism. Lemma A below extends this height argument to Z^r, keeping the non-split group extension rather than assuming commuting lifts in G.

## 4. The new finite constraint and the failed first version

Write bits additively in F₂. Fix r ≥ 1. A plumbing type is

\[
(i,j,c,q),\qquad 1\le i,j\le r,\quad c\in\mathbb F_2,\quad 1\le q\le5.
\]

There are m = 10r² types, each with two distinct ports. Both ports belong to **channel i**. The initial port has bit c and the terminal port has bit

\[
c+s_{ij},\qquad s_{ij}=1-\delta_{ij}\quad\text{in }\mathbb F_2. \tag{4.1}
\]

The plumbing generator of this type will have vector height e_j. Thus ports have equal bits in their own direction and opposite bits in the other directions. At each vertex, the law family contains every four-element subset consisting of two bit-zero and two bit-one ports **of one channel**. No four-slot body uses more than one channel.

Let Λ ≤ Z^r be a finite-index lattice and A_Λ = Z^r/Λ. Assume

\[
e_j\notin\Lambda\quad(1\le j\le r). \tag{NL}
\]

Make a graph on A_Λ with one directed edge of each type `(i,j,c,q)` from v to v+e_j. Direction here only labels its original ports; the plus/minus directions later supplied by the cuts can differ. Retain all parallel edges, including the two distinct lifts when e_j has order two. Condition (NL) makes the graph loopless and makes the incident-edge/port correspondence bijective.

**Lemma C (simultaneous parity constraint).** An endpoint assignment avoiding every law set exists if and only if Λ ⊂ 2Z^r. In that case a cap selection choosing exactly one endpoint at every plumbing is available, with one selected bit per channel at each vertex.

*Proof of necessity.* For a purported assignment, let D_i(v) be the nonempty set of bits for which vertex v receives at most one incident edge of channel i and that bit. It is nonempty because otherwise v receives two edges of each bit and hence an entire prescribed four-set.

Fix i,j and w=v+e_j. For each c there are five parallel edges whose port bits at v,w are c,c+s_ij. If both c ∈ D_i(v) and c+s_ij ∈ D_i(w), at most two of these five edges can be assigned to their endpoints, a contradiction. Hence

\[
D_i(w)\cap(D_i(v)+s_{ij})=\varnothing.
\]

Two nonempty subsets of a two-element set with this property must both be singletons. Denote them by σ_i(v),σ_i(w). Then

\[
\sigma_i(v+e_j)=\sigma_i(v)+\delta_{ij}. \tag{4.2}
\]

The graph is connected because the e_j generate A_Λ. Lift these functions to Z^r. Equation (4.2), also read backwards, gives σ_i(z)=σ_i(0)+z_i mod 2 for every integer vector z. Periodicity under every λ ∈ Λ forces every λ_i even. Thus Λ ⊂ 2Z^r.

*Proof of sufficiency and of the cap assertion.* If Λ is even, choose σ_i(v)=v_i mod 2 and select every port of channel i whose bit is σ_i(v). Along a type `(i,j,c,q)` edge the selected bits change by δ_ij, whereas its two port bits change by 1−δ_ij. Exactly one port is selected. Assign each edge to its **unselected** endpoint. Each vertex then receives no edge whose port bit is its selected bit, so cannot receive a whole law set. ∎

Five is the unchanged multiplicity from the source. Three would suffice for this combinatorial inequality; no sharper geometric theorem is claimed.

**Why r uncoupled cyclic obstructions fail.** Requiring only that channel i flip along direction i allows independent choices transverse to that direction. In `Z/3 × Z/2`, take generator images g₁=(1,1), g₂=(0,1). Both g₁ and g₂ have even order, so the two independent coloring problems are soluble, although the relation 3g₁+3g₂=0 has odd coefficients. Therefore individual coordinate-cycle tests do not imply Λ ⊂ 2Z². The cross-direction, opposite-bit plumbing in (4.1) enforces preservation in all other directions and removes exactly this defect. This is the substantive constraint construction; it cannot be replaced by saying “take r copies.”

## 5. Geometric realization of the constraint

**Lemma G (proposed geometric bridge).** The type table (4.1) can be realized by finite chamber data (D,P,S,H) satisfying `refl:input`, with an epimorphism w:H → Z^r, such that for every finite-index Λ:

1. all the chamber hypotheses lift to `(D_Λ,P_Λ,S_Λ,H_Λ)`, where H_Λ=w⁻¹Λ;
2. if Λ ⊂ 2Z^r, S_Λ has a marked graph-type filling;
3. if (NL) holds and S_Λ has a marked graph-type filling, then Λ ⊂ 2Z^r.

The construction and verification follow. The changes in endpoint colors and law families are part of this lemma, not part of the quoted source statement.

### 5.1. A finite marked construction

Use m=10r² mutually plumbed pairs of distinct cancelling handles and p=9 additional one-handles. The elementary plumbing chart is B's `ch:plumbing-chart`: two product disk-bundle charts whose coordinate core disks intersect once. Its core geometry and framing use no colors. Give its ports the channel/bit labels in (4.1). No handle is plumbed to itself. Different charts are disjoint.

Each channel has 10r ports of each bit. At one block install a four-tip body for every ordered quadruple of distinct ports in that channel of bit pattern `(0,1,0,1)`, every independent choice of the four conjugators from `{1,l₁,…,l₉}`, and every independent sign of each tip. Include all channels, and repeat the same finite list at every lifted block. An explicit list size is

\[
k=r(10r)^2(10r-1)^2\,10^4\,16. \tag{5.1}
\]

Its size is not claimed small. The specification is finite and constructive; no limiting family of handles occurs in any fixed r example.

The proof of B's `ch:four-tip-model` places a finite list by disjoint boundary handlebody thickenings, chosen whiskers, collar separation, and separated parallel copies of port cores. It acts on the four marked tips individually. Apply that construction to the list just specified. Its needed hypotheses are: four distinct ports per body; independent fixed conjugator/sign markings; finitely many bodies; distinct plumbing branches with product framings. All hold here. Changing the *label* on one end of a plumbing changes neither its chart nor this placement. The result still has only opposite-port cap intersections. Deleting the unused mixed-channel quadruples does not change a single retained body's construction. Each law is Brunnian in its four tips and has the leading bracket in `ch:laws`; the proof by the three punctured-torus boundary commutators is unchanged.

Before the body replacements, the plumbed manifold X has the marked graph homotopy type

\[
X\simeq B F(\tau_{i,j,c,q},l_1,\ldots,l_9).
\]

This follows from its tree development by block graphs joined along contractible product balls, just as in `ch:plumbing-group`. In particular it depends on the number and pairing of handles, not on their labels.

Perform the tube-removal and `V_a × S¹` replacements of B's `ch:chamber-definition`, one per installed bottom surface. The marked pushout `ch:exterior-model` applies because each bottom surface is a proper inward push of a disjoint boundary surface with its product trivialization. Each body is nullhomotopic in X, since its two upper branches cap there. Each replacement contributes a normal-circle generator z_a and two sphere summands, by the explicit cofiber of the two branch circles into the longitude/normal torus. Consequently

\[
H=\pi_1D=F(\tau_{i,j,c,q},l_s,z_a),\qquad
D\simeq BH\vee\bigvee^{2k}S^2. \tag{5.2}
\]

Set w(τ_{i,j,c,q})=e_j and w(l_s)=w(z_a)=0. This is a surjection. The replacement pieces have trivial height image: their longitude dies in H and their normal circle has height zero.

### 5.2. Full middle basis, pair duality, and covers

For each body choose one cap on each upper branch, without requiring these arbitrary initial choices to be disjoint. The rim-sphere calculation of `ch:exterior-duals` gives framed representatives u_a,g_a with λ(u_a,g_b)=δ_ab and λ(g_a,g_b)=0. In each remaining cap intersection the two parallel sheets have opposite signs and equal group labels, because their difference is an unused upper-tip loop that still bounds its cap in the exterior. This cancellation is local to that body and the opposing plumbing branch. It is unaffected by channel labels or by the bit at the other end.

The u-u matrix is hermitian with even identity coefficients on the diagonal. As H is free and has no involutions, subtracting triangular halves of g combinations makes it zero. The symmetrization formula for the framed Wall invariant then gives zero quadratic self-intersections. There are 2k classes in the free rank-2k module from (5.2). Their hyperbolic pairings give a one-sided inverse to their basis matrix. Direct finiteness of matrix rings over ZH (via finite quotients of the free group and finite-dimensional regular representations) makes that matrix invertible. They therefore form a basis of the **whole** middle module.

Attach three-cells along this basis. The resulting P has graph homotopy type. The regular-coefficient duality verification in `ch:poincare-chamber` quotients the nonsingular absolute and relative middle summands and restricts cohomology to their annihilators; cap-product naturality descends duality from D to (P,S). This establishes an oriented finite PD4 pair. The same relative low-degree homology argument as `ch:boundary-surjectivity` gives π₁S → H onto. All hypotheses of `refl:input` have now been checked.

For every finite-index Λ, S_Λ is connected by this surjectivity. Since all replacement pieces have height zero, the construction lifts body by body to the cover. Restricting the full free middle module from ZH to ZH_Λ yields the full lifted basis. The group-ring coefficient projection to H_Λ retains inverse pairs and the identity, so zero framed Wall invariants remain zero. The three-cells and orientation lift. This proves assertion 1, with no cyclicity hypothesis on the finite quotient.

### 5.3. Positive filling on every even lattice

If Λ ⊂ 2Z^r, use Lemma C's port selections at every vertex of A_Λ. Every upper torus in a body has one tip of each bit in one channel, so exactly one of its two caps is selected. Compress both upper branches using those caps. Because exactly one end of every plumbing chart is selected, **all** selected cap parallels are disjoint, across all bodies and all channels.

The geometric clause of `ch:exterior-duals` now gives embedded framed sphere pairs with one intersection inside each pair and no other intersections. Their classes form a full hyperbolic basis by the preceding middle-module argument. Remove pairwise disjoint neighborhoods of these pairs, each a punctured S² × S² with boundary S³, and glue a four-ball to each boundary. Denote the resulting manifold by V_Λ. These are interior operations, so its boundary is S_Λ with the original marking.

Van Kampen preserves H_Λ, since the removed neighborhoods, their boundary spheres, and the inserted balls are simply connected. In the universal cover, Mayer–Vietoris says that the sphere-pair contributions exhaust H₂ of the old cover, and the boundary S³ classes exhaust H₃ of the complement. Gluing balls removes the latter without creating H₄. All other reduced homology groups vanish; the new cover is simply connected. It has CW type, so the homological Whitehead theorem makes it contractible. Thus V_Λ ≃ BH_Λ ≃ P_Λ. The group marking is unchanged on the boundary, and the boundary collar homotopy extension property turns this into a homotopy equivalence of pairs equal to identity on S_Λ. This proves assertion 2.

### 5.4. Negative filling: checking the general graph interface

Suppose (NL) and a marked filling of S_Λ is given. Undo all installed law surgeries by attaching the dual two-handles. The normal-circle generators z_a are free factors in the marking and have height zero, so these attachments cancel exactly those graph circles. The resulting W has boundary ∂X_Λ and the graph homotopy type of X_Λ. Its dual cocores are proper disjoint disks bounding the installed law curves.

Let Γ_Λ be the plumbing graph from Section 4; extra l_s loops are not plumbing edges. Repeat the construction of `for:cuts` over the universal **tree of Γ_Λ**, rather than over the universal tree of a cycle. The marked graph map forgets the extra loops. Prescribe it on outside faces, law disks, and join-torus collars. The associated tree bundle has contractible fiber, so these prescriptions extend. Choose the punctures away from these sets, make the map constant near them, smooth over edge interiors, and take regular cuts. The component graph is a tree because its π₁ is a quotient of the cover's group, generated by the named extra loops lying in pieces. The prescribed plumbing tree is its principal subtree. Off-principal branches have trivial stabilizer and finitely many quotient orbits, so merging them into their attaching principal pieces produces connected vertex pieces and one connected cut per prescribed edge. No cyclic valence or global color was used. Each cut has precisely its prescribed torus boundary; each retained law disk remains in its vertex piece.

The formal construction also needs more than the existence of cuts. Its hypotheses transfer as follows.

- `H²(W;C)=H³(W;C)=0` because W has graph homotopy type. Mayer–Vietoris gives an isomorphism in degree two and a surjection in degree one for the edge-difference restrictions. Here `b₁(W)=b₁(Γ_Λ)+9|A_Λ|`; evaluation on the nine extra loops at each vertex identifies the degree-one kernel. This is the exact replacement of the source's `dp` count.
- Half-lives/half-dies for each connected torus-boundary cut, together with the two bounding longitudes and surjectivity, makes its boundary image one of the two original coordinate lines. This chooses plus/minus independently for each edge. It does not use any bit or channel label.
- Use the filled punctured-form complex from the source for topological vertex pieces: functions constant near punctures and positive-degree forms zero there. This computes filled cohomology and permits coefficientwise Stokes. Every cut itself is a compact smooth three-manifold, as required by `for:edge-input`.
- Apply `for:edge-input` to each cut separately. On each vertex use its based cohomological contraction and the same curvature recursion as the source. The signed restriction isomorphism gives the tangent isomorphism, the full-column gradient minor, and the finite residual ideal. A vertex may have arbitrary numbers of plus and minus ends; no step here requires its incident edges to have common labels.
- Choose the same nine adjoint-spanning background matrices over C((σ)) on the extra loops. Graph cycles add free generators, not relations. Recenter in the joint σ-adic ring before passing to Laurent coefficients. Use MT's marked algebraicity and formal comparison separately on each edge.
- For each installed four-set L, independently use all its conjugator/sign versions. Its law is Brunnian with leading nonzero tensor `[[U₁,U₂],[U₃,U₄]]`. Independent adjoints spanning End(sl₂) make the leading tests span all four-coordinate products. If J_L is their product ideal and Q_L the actual law ideal, then `J_L=Q_L+m_v J_L` and `Q_L ⊂ I_v`. Nakayama gives `J_L ⊂ I_v`. This is a calculation for one four-set. It never requires laws for **other** channels' mixed four-sets.
- Replace logarithmic perturbations by the source's quadratic polynomial in the marked holonomy, and apply the nilpotent correction. Its change is identity modulo I_v and retains all mixed nilpotent products. The resulting algebraic edge germs and formal sections satisfy (SC1) for exactly our installed law family, as well as exact potential vanishing and the tangent isomorphism.

These steps reproduce the proof obligations of `for:formal-data` for the changed graph and law list. In particular, the global bit swap at a join has no role in the based holonomy, torus slopes, analytic plus/minus choice, or shared central edge coordinates. Bits determine **which four bodies were installed**, and that is their only use before the final combinatorial step.

Apply the accepted `ten:assignment`. Its hypotheses have just been verified, including looplessness (NL), distinct edges in each law, actual ideals, and common edge germs. The resulting endpoint assignment is impossible by Lemma C unless Λ ⊂ 2Z^r. This proves assertion 3 and completes Lemma G's proposed proof. ∎

## 6. Exact cover classification after reflection

Reflect the chamber P in a finite flag triangulation of S with independent panel labels A₀=(Z/2)^V. Let Q=R_A₀(P), G=π₁Q. The folding map Q → P is identity on each chamber and induces a split surjection G → H. Compose with w:H → Z^r and use w also for this epimorphism. For a lattice Λ define G_Λ=w⁻¹Λ and let Q_Λ be its connected finite cover.

**Theorem F (cover realization).** Q is a finite connected oriented aspherical PD4 complex, and:

- if Λ ⊂ 2Z^r, Q_Λ has a closed connected oriented topological four-manifold model;
- if (NL) holds, Q_Λ has such a model if and only if Λ ⊂ 2Z^r.

*Proof.* The initial conclusions about Q are `refl:input`, using Lemma G. The cover Q_Λ is the pullback of P_Λ along the folding map. It consists of A₀-labeled copies of P_Λ with the original downstairs label reused on each lifted panel.

For even Λ, glue copies of the marked filling V_Λ with these same panel identifications. At every corner, incident lifted panels have distinct downstairs labels, so the local charts are the usual manifold reflection charts. The resulting space M_Λ is a closed connected oriented topological four-manifold. The relative homotopy equivalence V_Λ → P_Λ is identity on all boundary panels and their intersections. Gluing the finite cofibration diagrams gives a homotopy equivalence M_Λ → Q_Λ. Thus M_Λ is aspherical.

Any closed manifold model of the oriented aspherical Q_Λ is orientable: its orientation character is the action on the dualizing module of G_Λ, which is trivial. Thus restricting the discussion to oriented models loses none.

Conversely, distinguish every lifted panel by its own label, obtaining the full reflection `Qhat_Λ=R_AΛ(P_Λ)`. The lifted triangulation of S_Λ is flag: lift the simplex on the distinct downstairs vertices of any clique. Sending each lifted panel label to its downstairs label induces a finite connected cover Qhat_Λ → Q_Λ. The covering charts use that this map is injective on every incident panel subgroup. This is the proof of `refl:cover-comparison`, with an arbitrary finite connected boundary cover; cyclicity is unused.

A manifold model for Q_Λ lifts to a manifold model for Qhat_Λ. Applying `refl:input` to the lifted chamber gives a marked filling of S_Λ, which Lemma G and (NL) force to be even. ∎

We do not assert this iff for lattices violating (NL); a loop has two ports but only one edge, and the quoted tensor theorem excludes loops. The qualification is sufficient for the final theorem.

## 7. A higher-rank height lemma, including the extension cocycle

**Lemma A.** Let Q be a finite connected aspherical complex, w:G=π₁Q → Z^r onto, and H=w⁻¹(2Z^r). Suppose Q_(2Z^r) has a closed n-manifold model M. Choose a primitive integer vector u, complete it to an integer basis u,u₂,…,u_r, and choose γ ∈ G with w(γ)=u. Put

\[
\Lambda_R=\langle(2R+1)u,\ 2u_2,\ldots,2u_r\rangle,\qquad R\ge1.
\]

If Q_ΛR has no closed n-manifold model for all sufficiently large R, no homeomorphism of M induces the outer automorphism of H represented by Ad_γ.

*Proof.* Suppose a homeomorphism h exists. Choose its universal-cover lift h̃ so that its action on the deck group H is exactly Ad_γ, by correcting the lift by an element of H if necessary. Let K=ker w and X=M̃/K. The deck group of X → M is L=2Z^r. The lift induces a homeomorphism F of X. For every l∈L, its deck transformation T_l satisfies

\[
FT_lF^{-1}=T_l, \tag{7.1}
\]

because conjugation by γ acts trivially on H/K. This equality is on X. We do **not** assert that the corresponding lifts commute on M̃.

There is a continuous L-equivariant height map b:X → R^r, measured in the basis u,u₂,…,u_r, with

\[
b(T_lx)=b(x)+l.
\]

One construction takes an L-periodic partition of unity subordinate to translates of finitely many lifted relatively compact sets and averages their lattice labels. This gives the required affine equivariance. Since X/L=M is compact, the map is proper: a compact set meeting every orbit has bounded height, and only finitely many lattice translates of it can meet the inverse image of a bounded height set.

By (7.1), `b(Fx)-b(x)` is L-invariant and bounded. Choose C with the absolute value of its first coordinate at most C. Set F_R=T_(2Ru) F. For R with 2R>C,

\[
2R-C\le b_1(F_Rx)-b_1(x)\le2R+C. \tag{7.2}
\]

The maps F_R,T_(2u₂),…,T_(2u_r) commute on X. They generate a free Z^r action: a word with nonzero F_R exponent changes b₁ with the corresponding strict sign, and a word with zero such exponent is a nontrivial original deck translation unless all its exponents vanish.

The action is properly discontinuous. If a translate of one compact set meets another, (7.2) bounds the F_R exponent. For each of the finitely many possible exponents, the other height coordinates bound the remaining deck exponents. It is cocompact: iterate F_R forwards or backwards to place b₁ in an interval of length 2R+C, then use T_(2u_j) to put all other coordinates in [0,2]. Properness of b makes this a compact fundamental set. Therefore

\[
N_R=X/\langle F_R,T_{2u_2},\ldots,T_{2u_r}\rangle
\]

is a closed topological n-manifold, with contractible universal cover M̃.

It remains to identify its fundamental group; replacing the extension by a semidirect product without checking its cocycle would be an error. Choose h_j∈H with w(h_j)=2u_j for j≥2. The deck group over N_R is generated on M̃ by K, the h_j, and

\[
Z_R=\gamma^{2R}\widetilde h.
\]

Here γ^{2R}∈H is a deck transformation. Its conjugation formula is exact:

\[
Z_R a Z_R^{-1}=\gamma^{2R+1}a\gamma^{-(2R+1)}\quad(a\in H). \tag{7.3}
\]

The commutators among h_j are the original elements of K. The commutators [Z_R,h_j] are, by (7.3), exactly the commutators [γ^(2R+1),h_j] in G. Conjugations of K also agree. Both this deck group and G_ΛR have quotient freely generated as an abelian group by these r images. Collect any word into the ordered form

\[
k Z_R^{a_1}h_2^{a_2}\cdots h_r^{a_r}
\]

using the conjugation and commutator relations just checked. Its image in the quotient determines all exponents uniquely. If they vanish, it is trivial precisely when k=1, because the action of K on M̃ is faithful. The identical collection in G_ΛR gives the same multiplication and the same uniqueness. Sending Z_R to γ^(2R+1), h_j to h_j, and K identically therefore is an isomorphism onto G_ΛR.

Consequently N_R is a closed manifold model of Q_ΛR. This contradicts the hypothesis for sufficiently large R. No order restriction on h was used. ∎

## 8. Proposed main theorem and proof

**Theorem T.** For every integer r≥1 there is a closed connected oriented aspherical topological four-manifold M_r such that the image of

\[
\operatorname{Homeo}(M_r)\longrightarrow\operatorname{Out}(\pi_1M_r)
\]

has trivial intersection with a subgroup isomorphic to `(Z/2)^r`.

*Proof from the preceding construction.* Use Q,w from Theorem F and take a manifold model M_r of Q_(2Z^r). Write H=π₁M_r=w⁻¹(2Z^r). Conjugation defines the standard outer action

\[
\theta:G/H\cong(\mathbb Z/2)^r\longrightarrow\operatorname{Out}(H).
\]

For any nonzero v∈(Z/2)^r, choose its representative u∈{0,1}^r. It is primitive. Choose an index a with u_a=1 and complete u to an integer basis using all standard e_j with j≠a. The determinant is ±1. Let Λ_R be the lattice in Lemma A for this basis.

For every R≥1 this lattice is not contained in 2Z^r, since (2R+1)u has a nonzero parity vector. It also satisfies (NL): if j≠a, e_j is one of the complementary basis vectors and cannot be an integer combination of their doubles and (2R+1)u. The remaining e_a has coefficient 1 on u in this basis, not divisible by 2R+1≥3. Thus no e_j belongs to Λ_R.

Theorem F excludes every manifold model for Q_ΛR. Lemma A excludes every homeomorphism representing θ(v). In particular θ(v) is not the identity outer class, since that class is represented by the identity homeomorphism. Therefore θ is injective, and its nonzero classes all avoid the homeomorphism image. As M_r is aspherical and has CW type, each outer automorphism is induced by a self-homotopy equivalence. This proves the theorem. ∎

This does not claim that M_r is hyperbolic, that all of Out(π₁M_r) is known, that M_r is asymmetric, or that the 2^r marked structures have different unmarked homeomorphism types. It does not give a single fixed manifold containing all ranks. The manifold and its finite presentation may grow with r. The result is not a new disproof of Borel, which is already in the accepted corpus; its intended content is the simultaneous fixed-dimension strengthening and the signed plumbing mechanism.

## 9. Verification, review targets, and reproducibility

`../experiments/i07_structures/check_twists.py` uses exact integers and bits. Its reproducible output is `checks.json`.

- It checks every local pair of nonempty deficient-bit sets for the two kinds of port pairing, and verifies that only the required singleton transition survives.
- It checks the selected-cap rule in all eight local bit cases.
- It checks 273 loopless rank-two finite lattice quotients with upper-triangular entries in the stated finite ranges: 40 even lattices satisfy the constraint and 233 non-even lattices fail it.
- It verifies the mixed-odd-relation counterexample to the uncoupled-channel attempt.
- It checks cap selections on even covers for r=1,…,5, and records the finite construction counts without materializing billions of bodies.

These are finite combinatorial diagnostics. **They do not validate smooth placement, the formal edge machinery, reflection, any infinite family, or any asymptotic assertion.** The general combinatorial statement is proved in Lemma C; the topology is addressed by the proof, not by the script.

Priority proof-review targets, in order:

1. Lemma G: verify that the explicit four-tip placement and middle-form computations are uniform in an arbitrary finite body list and tolerate different bit labels at the two ports of a plumbing. This must be checked geometrically, not inferred from the label terminology.
2. Lemma G §5.4: audit the marked tree-cut construction and the local-to-global formal data for arbitrary connected loopless plumbing graphs and a union of within-channel four-set law families. The exact middle/extra-loop counts and full nilpotent ideals are stated.
3. Positive reflection with reused downstairs panel labels and the full-panel finite cover used for the converse. The distinction between these two reflections is necessary.
4. Lemma A: check properness/cocompactness and the non-split extension identification. Commutativity is asserted only after quotienting by K; equation (7.3) retains the commutator cocycle upstairs.
5. Contribution review: decide whether this signed finite constraint gives a sufficiently substantial bridge beyond B's arbitrary-graph tensor theorem and single involution. A correct local relabeling application alone would not meet the research standard. The mixed-relation failure and the fixed-four-dimensional rank growth are the claimed additional mechanism and scope.

No independent review is represented as having occurred. If any of items 1–4 fails, Theorem T must be downgraded until repaired; Lemma C and the abstract height Lemma A can be retained separately as technical results, without increasing the substantial-finding count.

Reproduce the deterministic checks and validate the retained artifacts from the project root:

```sh
python frontier/experiments/i07_structures/contracts.py
python frontier/experiments/i07_structures/check_twists.py
python frontier/experiments/i07_structures/seal.py --verify
```

For a fresh network retrieval, `retrieve.py` and `literature.py` record the exact requests. Re-running them intentionally updates timestamps and input snapshots, and therefore changes the provenance manifests; it is not the command sequence for verifying the retained snapshot. Compare newly retrieved source byte hashes to the retained manifest before intentionally resealing with `seal.py` without `--verify`.

The retrieval scripts write only the assigned source/experiment directories. External primary downloads may later change at their hosting URLs; their retrieved bytes are preserved and hashed. Input snapshot hashes are historical and may differ after the parent updates shared research indexes. Artifact verification distinguishes those input changes from modifications to this report's own files. At the initial seal, only `frontier/iterations/README.md` differed from its historical input hash; no upstream artifact differed. No commit or staging is required to run these scripts.
