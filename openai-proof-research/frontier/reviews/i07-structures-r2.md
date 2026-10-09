# I07 structures: independent proof audit, round 2

**Verdict: PASS for the proposed proof, relative to the stipulated pinned corpus. No proof-blocking gap found. This is not contribution acceptance or a literature-novelty verdict.** The accepted substantial count remains **2**, R006/R008; the target remains 10. This construction is one prospective finding, not separate findings for Lemmas C/G/A, the cover classification, and Theorem T. No index, staging area, or commit was changed by this review.

The audited report is `frontier/iterations/i07-structures.md`, 44,910 bytes, SHA-256 `09631282a1d757480eecb53456017ec429ee8a790d4d8c1e1b71b04ba79136f9`. This was a fresh audit of that text, not an adoption of a prior review. I read the full report, project `AGENTS.md`, immutable revision record, relevant catalogue entries, and theorem contracts, and parsed the **entire** `sources/preprints-tree.json`. I compared the changed construction with the actual source proofs identified below. All applicable pinned-corpus results are premises; I did not audit upstream truth.

The conclusion audited is exactly: for every integer $r\geq1$, a closed connected oriented aspherical topological **four**-manifold $M_r$ has an injected $(\mathbb Z/2)^r\subset\operatorname{Out}(\pi_1M_r)$ whose intersection with the image of **all** self-homeomorphisms is the identity. In particular the claim excludes infinite-order representatives, keeps dimension four, and allows the manifold to depend on $r$.

## 1. Source scope and byte audit

The pin is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` of `https://github.com/openai/math`. In this review the following abbreviations designate paths under `frontier/sources/i07_structures/upstream/preprints/`:

- **B**: `Nonhomeomorphic-closed-aspherical-four-manifolds-with-the-same-homotopy-type-October-4-2026/build/`.
- **MT**: `A-marked-tensor-obstruction-to-four-dimensional-disk-embedding-September-24-2026/build/`.
- **PD**: `A-PD4-group-without-an-aspherical-manifold-model-September-24-2026/build/`.

The central comparison was against the complete proofs in B's `sections/chambers.tex`, `sections/formal.tex`, `sections/reflection.tex`, and the higher-rank-relevant part of `sections/cyclic.tex`; I also read B's complete `sections/tensors.tex` and introduction. Relevant companion passages checked directly include MT's plumbing, marked-body/framing, and exterior-dual constructions in `sections/01-geometry.tex`; its based edge-slice and potential statements/proofs in `sections/03-edge-germs.tex`; the marked-algebraicity interface in `sections/04-algebraicity.tex`; the adjoint-span and full-parameter correction in `sections/05-vertices.tex`; and PD's actual marked-exterior and connected-cut constructions in `sections/chamber.tex`. PD's reflected-duality and final marked-removal passages were also checked. These are source-proof comparisons for applicability, not attempts to re-establish all imported theorems.

The strongest accepted interface for the algebra is already B `ten:assignment`. It explicitly permits arbitrary finite loopless multigraphs, arbitrary nonempty local law families, zero-dimensional edge blocks, arbitrary endpoint signs, and full rings with only the individual relations $t_e^2=0$. It would be wrong to identify the new contribution as a generalization of that theorem. Conversely, B `ch:four-tip-model`, `for:cuts`, and `for:formal-data` are stated for its specific construction. Their changed applicability requires the construction/proof checks in Sections 3–5 below; their statements alone do not establish Lemma G.

The independent verifier [audit.py](../experiments/i07_structures_r2/audit.py) does not run the proposal's writing/retrieval/sealing scripts. Its retained results are [provenance-verification.json](../sources/i07_structures_r2/provenance-verification.json) and [input-hashes.json](../sources/i07_structures_r2/input-hashes.json):

- The complete inventory has **13,223 entries**, including **10,373 blobs**, and `truncated: false`. Every entry was parsed; duplicate paths were checked. The truncated root-tree cache was not used.
- All **253** retained TeX/BibTeX files match their recorded SHA-256, byte counts, and pinned raw URL. Each independently computed Git blob SHA-1, using `blob <length>\0<bytes>`, matches the complete inventory. The selected manuscript-directory TeX/BibTeX inventory has no omissions or unexpected retrieved files.
- All **37** contract statements match their exact source-line slices and statement/source SHA-256 values and contain the stated labels.
- All **280** original sealed artifacts match both size and SHA-256. There are no unsealed files in the original source/experiment scope.
- The only changed historical input is `frontier/iterations/README.md`, already distinguished in the proposal from its own sealed artifacts. `AGENTS.md`, upstream pin, complete inventory, catalogue, and other historical inputs match. The review records current input hashes rather than overwriting the historical snapshot.

This verifies retained bytes against the supplied immutable inventory and manifests. It does not claim an additional network attestation of that inventory. No source retrieval or upstream modification was needed.

## 2. Lemma C: PASS, including mixed relations and multiplicities

For a fixed channel $i$, let $D_i(v)\subset\mathbb F_2$ be the bits receiving at most one edge at $v$. Avoidance of every within-channel two-zero/two-one four-set makes this set nonempty. For the five edges of type $(i,j,c,q)$ from $v$ to $w=v+e_j$, simultaneous deficiency at the two corresponding ports would assign at most two of five edges. Thus

\[
D_i(w)\cap(D_i(v)+1-\delta_{ij})=\varnothing.
\]

The sets are nonempty subsets of a two-element set, so both are singletons, and their values obey $\sigma_i(w)=\sigma_i(v)+\delta_{ij}$. This holds along every coordinate direction, and backwards along those directions. Pulling back to $\mathbb Z^r$ gives $\sigma_i(z)=\sigma_i(0)+z_i\pmod2$. Every period must therefore have every coordinate even. This is a general proof, not an inference from the finite checks.

Conversely, if the lattice is even, $\sigma_i(v)=v_i\pmod2$ is well-defined. The selected-port predicate changes by one between the two endpoints of every edge, since the vertex value changes by $\delta_{ij}$ and the edge bit by $1-\delta_{ij}$. Exactly one endpoint is selected. Assigning to the unselected endpoint gives zero received edges of the selected bit at every vertex, so no installed law is wholly received there.

Condition (NL) is used correctly. Without it, the two ports of a loop would not correspond to distinct incident edges and B's theorem could not be applied. Parallel edges, including the two different lifted edges when $e_j$ has order two, remain distinct. Nothing in the deficiency argument deletes one of them. Five is sufficient; the proof does not need to optimize it.

The rejected uncoupled construction really fails. In $\mathbb Z/3\times\mathbb Z/2$, $g_1=(1,1)$ has order six and $g_2=(0,1)$ order two, so independent alternation along either generator is possible. But $3g_1+3g_2=0$ has odd coefficients. Exhausting all binary functions on these six vertices gives respectively 2 and 8 functions for the independent channel tests, and zero functions in each channel for the corrected all-direction constraints. The mixed-relation correction is necessary, not merely a different presentation of independent cyclic copies.

## 3. Lemma G, construction and full chamber data: PASS

### Finite placement and the changed cap configurations

There are $m=10r^2$ plumbing pairs and nine extra handles. In a fixed channel and direction, the two initial bits and the two terminal bits each contribute five ports of each bit. Thus each channel has $10r$ ports of either bit. The number of ordered distinct-port quadruples with pattern $(0,1,0,1)$ is

\[
(10r)(10r-1)(10r)(10r-1).
\]

Multiplying by $r$, the $10^4$ independent conjugator choices from $\{1,l_1,\ldots,l_9\}$, and $2^4$ independent signs gives precisely the reported $k$. The enormous count is finite for each $r$, as needed. No uniformly bounded handle count is claimed.

B `ch:four-tip-model`'s placement proof, particularly `chambers.tex:149–243`, actually uses four separately marked longitudinal tip annuli, finitely many reserved parallel tracks, and thin connector trees. Arbitrary specified whisker classes can be represented by the finitely many arcs with separated parallel tracks in the three-dimensional outside face. Independent ribbon twists occur in disjoint tip neighborhoods and are fixed near connector feet. The terminal circles and external conjugators remain the specified ones. This construction does not test whether the two ends of a plumbing carry the same color. Its framing construction uses product coordinates and normal winding, not a bit label.

The change therefore consists of a different finite list of four-tip placements on the same kind of uncolored plumbing blocks. Every retained body has four distinct ports and the same marked handlebody model. Omitting mixed-channel bodies removes requirements; it does not disturb a retained body's geometry. The coordinate-factor interchange of a plumbing chart, the meridian/longitude interchange, and the chosen framings are unchanged.

I specifically checked a new configuration that a global red/blue description can conceal: two opposite ports of a single plumbing may now have different bits and may occur on **the same upper torus**. This is allowed. The two terminal caps may intersect, but compression of that upper torus uses only one of them and its separated parallels. The individual core has no self-plumbing. The unused cap remains in the exterior as a null-homotopy; it need not be disjoint from the selected cap to serve that purpose. The source's proof of the compressed rim sphere uses exactly these facts (B `ch:exterior-duals`, MT's one-sided compression and sheet calculation). It does not require both caps of an upper torus to be mutually disjoint. On an even cover the actual selection excludes simultaneous use of opposite ends, including among different lifted bodies.

Consequently the claimed geometric property—embedded framed individual terminal caps, bodies disjoint, and cap intersections confined to opposite branches—survives the changed law list and labels. This is a checked extension of the source construction, not an invocation of a nonexistent general-graph chamber theorem.

### Exterior, group marking, middle module, and duality

The unmodified plumbing development is a tree of block graphs with contractible product-ball overlaps. Hence $X\simeq BF_{m+9}$, with the indicated independent plumbing generators and extra loops. Every bottom surface is a proper inward push of a disjoint boundary surface. Its two branch loops are null-homotopic in $X$; cap intersections do not invalidate those null-homotopies. The map of the whole punctured torus is therefore null-homotopic because it retracts to those loops and $X$ is a graph model.

These are the actual hypotheses of the **side-marked** exterior pushout, checked against PD `ch:exterior-model` and B `ch:exterior-model`. Retaining the side marking matters: replacing an unmarked homotopy equivalence here would not identify the normal circles needed in the negative argument. The cofiber computation kills the longitude $b_a$, leaves the normal generator $z_a$, and leaves two trivial two-cell attaching maps. It gives

\[
H=F(\tau_{i,j,c,q},l_1,\ldots,l_9,z_1,\ldots,z_k),
\qquad D\simeq BH\vee\bigvee^{2k}S^2.
\]

For the rim-sphere intersection computation, the two inner cap parallels have opposite signs and equal group labels because their path difference is the unused upper-tip loop, still capped in the exterior. The outer parallel index is held fixed; there is no cancellation based on incorrectly killing the new bottom normal circle. This is unchanged when the opposing port has a different bit or belongs to another body. It supplies $\lambda(u_a,g_b)=\delta_{ab}$ and $\lambda(g_a,g_b)=0$.

The remaining algebraic operations meet the complete reflection contract. The hermitian $u$-matrix has even identity diagonal coefficients. The free group has no nonidentity order-two elements, so its diagonal and off-diagonal terms have the required triangular halves. Subtraction of $g$-combinations gives a hyperbolic form. For framed representatives, symmetrization is injective on the additive Wall quotient here: coefficients on nonidentity inverse pairs are retained, and the identity coefficient is doubled over $\mathbb Z$. Thus zero self-pairing gives zero **full framed** quadratic invariant. The proposal does not silently discard the identity coefficient.

There are exactly $2k$ classes in a free rank-$2k$ module. Their pairings give a one-sided inverse, and direct finiteness of matrices over this free-group ring supplies the other inverse. This verifies a basis of the whole middle module rather than just independent hyperbolic planes. Attaching three-cells to that basis kills precisely the sphere summands. The source's nonsingular-summand/annihilator cap-product argument applies to this same middle module and produces the oriented PD4 pair. The relative regular-coefficient low-degree calculation gives boundary surjectivity.

These computations do not require a cyclic quotient. The height map sends each plumbing generator to $e_j$ and each extra/normal generator to zero. Each replacement has trivial height image, so its cover is a disjoint collection of identical replacements. A cover of index $n$ has $nk$ bodies and middle rank $2nk$ over the subgroup ring; restriction of scalars gives exactly these lifted basis elements. The coefficient projection retains the identity and both members of every retained inverse pair, so the framed Wall invariant lifts as claimed. Boundary surjectivity guarantees a connected lifted boundary. No subgroup-ring basis or connectedness hypothesis was lost.

## 4. Lemma G, positive and negative fillings: PASS

### Positive filling

Every upper torus has one tip of each bit in its channel. Lemma C therefore chooses one of its two caps. At every plumbing **exactly one endpoint** is selected, so no two used sheets are opposite-branch sheets. This eliminates every possible extra intersection in the verified local model, across bodies, channels, and lifts. It yields actual embedded framed sphere pairs with one intersection per pair; no disk-embedding conjecture is being invoked.

The pairs represent a full middle basis by the same pairing/direct-finiteness argument. Their disjoint neighborhoods are the plumbings of two trivial sphere normal bundles with one intersection, hence punctured $S^2\times S^2$ with boundary $S^3$. Replacing them by balls is an interior topological operation preserving the boundary marking and fundamental group. The complement is connected because a path through a removed neighborhood can be rerouted along its connected boundary.

In the universal cover, the direct sum of all neighborhood $H_2$'s maps isomorphically onto the original $H_2$, so the complement has zero $H_2$. The adjacent Mayer–Vietoris terms identify its $H_3$ with the direct sum of boundary $S^3$ classes and leave $H_4=0$. Gluing balls kills exactly those classes and introduces no $H_4$. The new universal cover is simply connected and acyclic; manifold CW type makes it contractible. Local finiteness of the lifted family justifies the direct sums. Classifying maps to the graph preserve the boundary group marking, and the boundary collar converts the resulting homotopy to a map of pairs equal to the identity. This supplies the claimed marked filling for every even finite-index lattice.

### Undoing laws and obtaining connected cuts

Dual handles kill the lifted normal-circle free factors, not merely a collection of null-homologous circles. Since those factors have height zero, there is one cancellation per lifted body and the remaining marked homotopy type is exactly that of $X_\Lambda$. The cocore disks have the installed law curves as boundaries. This recovers the correct input $W$, including its boundary map.

The source's connected-cut proof is more general than the phrase “cycle” might suggest. B's plumbing graph already has many parallel edges and a nonabelian free fundamental group. Its proof in `formal.tex:73–117` uses its **universal covering tree**, not a line, and uses the ambient graph marking plus the free extra loops. The new graph has the same required properties:

1. Forgetting the nine extra loops at each vertex gives the marked quotient onto $\pi_1\Gamma_\Lambda$. The associated cover's group is generated by the whiskered extra loops at tree vertices.
2. Outside faces, law-disk neighborhoods, and join-torus collars give compatible prescribed maps to the target tree. Contractibility of the fiber gives extension. The punctured smoothing and regular-value construction can be performed relative to those prescribed sets.
3. The component graph of the regular cuts is a tree: every loop in it lifts by paths in connected pieces, while each generator of the cover's group lies within one piece and maps trivially.
4. The prescribed outside faces give distinct principal vertices: their images lie in different components of the tree with midpoints removed. Each prescribed torus collar supplies the corresponding principal edge. Thus the entire plumbing tree is an embedded principal subtree.
5. An off-principal branch has a unique attaching principal vertex. A deck transformation stabilizing it fixes that vertex and hence is trivial. In fact two components attached at the same principal vertex cannot belong to one deck orbit unless identical. Finitely many quotient orbits therefore bound the **entire** collection attached there, not merely its valence. These finite branches can be merged by discarding their closed cuts.

This gives one connected cut with precisely the prescribed torus boundary per plumbing edge and connected vertex pieces containing all their law disks. The reasoning uses neither cyclic valence nor a global color on an edge. Condition (NL) is still needed later for the port/edge correspondence; the nine extra loops are not tensor edges.

### Linear and formal data, including actual ideals

For $n=[\mathbb Z^r:\Lambda]$, the plumbing graph has $n$ vertices and $10r^2n$ edges. Accordingly

\[
b_1(W)=b_1(\Gamma_\Lambda)+9n=(10r^2+8)n+1.
\]

This independently checks the reported replacement of the source's extra-loop count. The graph type gives $H^2(W)=H^3(W)=0$, so the signed Mayer–Vietoris restriction is an isomorphism in degree two and surjective in degree one. Its degree-one kernel is $H^1(W)/H^1(\Gamma_\Lambda)$; evaluation on the named $9n$ loops identifies it with $\mathbb C^{9n}$. Thus imposing zero extra evaluations removes exactly the kernel.

For a connected oriented torus-boundary cut, half-lives/half-dies supplies one nonzero boundary line. The two vertex restrictions annihilate the respective bounding longitudes, which are the two distinct coordinate slopes. Surjectivity excludes every noncoordinate line. Hence each cut independently determines its plus and minus ends. Channel/bit labels have no role in this choice. Imposing the plus-meridian zero conditions then gives exactly B's internal tangent isomorphism; the degree-two restriction and relative/absolute pairing give the full-column residual-gradient minor.

The extension of `for:formal-data` is justified by its actual proof, not by its statement. Up to the four-slot-law subsection, that proof depends only on the just-verified cuts, markings, linear isomorphisms, arbitrary incident plus/minus sets, and common edge restrictions of a flat background. All of these are available here. Graph cycles give freely chosen transports, not relations among the extra-loop holonomies. Eight nonidentity matrices from the nine-element adjoint-spanning family, together with the identity conjugator, suffice; the nine extra loops are more than enough. The background is constructed and recentered in the joint $\sigma$-adic rings before passing to $\mathbb C((\sigma))$, so no invalid later translation of unrestricted Laurent-coefficient formal series is needed.

The punctured-form model is applied only to vertex pieces and uses their filled cohomology. Each cut remains a compact smooth three-manifold, as the single-edge input requires. The common central edge coordinates and marked holonomy germs are retained at the two ends; the parameter-dependent coordinate change at a plus end is identity at parameter zero. Actual curvature ideals, not reduced representation varieties, pass through this construction.

The one place where the law family enters is local to a fixed four-set $L$. Every such within-channel set has an ordering $(0,1,0,1)$, and the construction supplies every independent conjugator/sign choice for that ordering. The bracket $ [[U_1,U_2],[U_3,U_4]]$ is nonzero; independently spanning endomorphisms on the four inputs span all scalar coordinate products. The Brunnian property puts the whole law expression in the product ideal $J_L$, and its higher terms in $\mathfrak m_vJ_L$. Consequently the actual law ideal $Q_L$ satisfies

\[
Q_L\subset J_L\cap I_v,
\qquad J_L=Q_L+\mathfrak m_vJ_L.
\]

Nakayama applies to the finitely generated module $J_L/Q_L$ over the complete local ring with its full parameter nilpotents, giving $J_L\subset I_v$. Laws involving other channels are never needed in this argument. Nor are the off-shell words assumed homotopy invariant: their agreement with holonomy is only used modulo the actual flatness ideal.

The final polynomial replacement also retains its estimates. For a plus edge, specializing only its own $t_e$ to zero gives $G_e(M_v)-1\in(I_v,t_e)$, while all other parameters remain. The cubic logarithm remainder therefore has

\[
t_eR_e(M_v)\in t_eI_v^3,
\qquad t_e(\partial_hR_e)(M_v)\in t_eI_v^2.
\]

The nilpotent correction preserves the fixed residual ideal and unit minor and is identity modulo that ideal. Its convergence is by powers of the whole nilpotent ideal, whose square is **not** set to zero. The resulting common algebraic edge germs, centered formal sections, exact potential vanishing, tangent isomorphism, and per-law gradient memberships are precisely all hypotheses of `ten:assignment`. That theorem plus Lemma C proves the negative filling implication. I found no remaining geometric-to-formal hypothesis merely assumed at this junction.

## 5. Theorem F, reflection and cover comparison: PASS conditional on G

The folding map is a retraction onto a chamber, so its fundamental-group map is a split surjection. Pulling back $P_\Lambda\to P$ gives the connected cover corresponding to $w^{-1}\Lambda$, with the original panel labels reused. Connectedness follows from the epimorphism to $\mathbb Z^r/\Lambda$.

For positive realization, distinct panels incident at a point upstairs have distinct downstairs labels. The reused-label gluing therefore has the usual manifold sectors at every boundary stratum. Label parity gives a consistent orientation. The marked filling equivalence is identity on the boundary and hence on every panel intersection. Collars and the boundary subcomplex structure justify homotopy-pushout gluing even though a topological filling need not be triangulable. The finite gluing gives a closed connected oriented manifold homotopy equivalent to $Q_\Lambda$, hence aspherical.

The negative direction correctly uses a different reflection. A clique in the lifted triangulation projects to distinct adjacent vertices downstairs; lifting the downstairs simplex from one clique vertex puts every other clique vertex in that lifted simplex by edge-lift uniqueness. Thus the boundary-cover triangulation is flag for an arbitrary finite cover. The coordinate homomorphism from the full lifted-label group to the downstairs-label group is surjective and injective on each incident-panel subgroup. Its kernel acts freely: in a chamber sector, any stabilizer would lie in that incident subgroup. This supplies the finite covering charts and proves the comparison map is a finite cover. The full reflection is connected because every coordinate is realized by crossing its nonempty panel.

A manifold model lifts through this finite cover. The lifted chamber satisfies the full `refl:input` contract by Section 3, so the full reflection yields a marked filling, excluded by Section 4 for a noneven loopless lattice. Using `refl:input` directly on the reused-label reflection would have been a gap; the report does not do that. Orientability of any aspherical model follows from the trivial dualizing-module orientation character, so no unoriented model escapes the exclusion.

## 6. Lemma A and the nonsplit extension: PASS

This proof handles arbitrary-order hypothetical homeomorphisms. Correcting a universal-cover lift by an element of $H=w^{-1}(2\mathbb Z^r)$ makes its conjugation action on $H$ exactly $\operatorname{Ad}_\gamma$. On $X=\widetilde M/K$, $K=\ker w$, the induced $F$ commutes with every $2\mathbb Z^r$ deck translation. This commutation is asserted only after quotienting by $K$.

An equivariant continuous height $b:X\to\mathbb R^r$ exists by the covering action and a locally finite partition of unity. It is proper because a compact set meeting every deck orbit has bounded height; a compact height set can meet only finitely many translates of that set. All coordinates of $b(Fx)-b(x)$ are bounded by deck invariance and compactness of $M$. For $F_R=T_{2Ru}F$, the first-coordinate increment lies in $[2R-C,2R+C]$, strictly positive for large $R$.

The transverse deck generators commute with $F_R$ and have zero first-coordinate displacement. A word with a nonzero $F_R$ exponent has a strictly signed first-coordinate displacement; a word with exponent zero is an original deck translation. This proves freeness. For intersecting translates of compact sets, the first-coordinate estimate bounds that exponent, and for each such exponent the other coordinates bound the transverse exponents. This proves proper discontinuity. Iterating $F_R$ brings the first coordinate into $[0,2R+C]$, then the transverse translations place the other coordinates in $[0,2]$. Properness of the full vector-valued height gives a compact set meeting every orbit. A single first-coordinate band alone would not be compact when $r>1$, but the proof uses the full box.

The upstairs generator is legitimately

\[
Z_R=\gamma^{2R}\widetilde h.
\]

Here $\gamma^{2R}\in H$ is an actual deck transformation. There is no action of the abstract element $\gamma\notin H$ on $\widetilde M$ being presumed. For every $a\in H$, the composite has conjugation $\operatorname{Ad}_{\gamma^{2R+1}}(a)$. In particular, with chosen transverse lifts $h_j\in H$, the actual transformation commutator $[Z_R,h_j]$ is the deck transformation represented by $[\gamma^{2R+1},h_j]\in K$. All $[h_j,h_k]$ and all conjugations of $K$ are also the original ones.

These data suffice to identify the extension, not just its outer action. A presentation with the actual group $K$, its generator-conjugation relations, and these pairwise commutators collects every word into

\[
kZ_R^{a_1}h_2^{a_2}\cdots h_r^{a_r}.
\]

The freely generated abelian quotient determines the exponents uniquely, and faithfulness of the $K$ action determines $k$. The identical collection relations and uniqueness hold in $G_{\Lambda_R}$. Thus the specified map is an isomorphism. There is no missing assumption that the original lifts commute, no need for $K$ to be centerless, and no suppressed central cocycle. The Heisenberg diagnostic described below illustrates why the commutators matter but is not the proof of this normal-form argument.

The quotient manifold has contractible universal cover and that fundamental group, and is therefore a model of the aspherical $Q_{\Lambda_R}$. This contradicts eventual nonrealization. No finite order of $h$, or relation among a collection of realizing homeomorphisms, was used.

## 7. Theorem T and acceptance boundary

For each nonzero binary vector take $u\in\{0,1\}^r$ and choose $a$ with $u_a=1$. The basis consisting of $u$ and the $e_j$, $j\ne a$, is unimodular. In this basis, $e_j$ for $j\ne a$ is a complementary basis vector and $e_a=u-\sum_{j\ne a}u_je_j$. Hence none of the $e_j$ lies in

\[
\Lambda_R=\langle(2R+1)u,\ 2e_j\ (j\ne a)\rangle
\]

when $R\ge1$: a complementary coefficient is odd in the first case, and the $u$-coefficient is 1 rather than divisible by $2R+1$ in the second. The generator $(2R+1)u$ also proves that the lattice is noneven. The rank-one case is included; there are no transverse generators then.

Theorem F supplies one manifold model for $2\mathbb Z^r$ and forbids every required $\Lambda_R$ model. Lemma A excludes every nonzero quotient conjugation class from the homeomorphism image. The standard map $G/H\to\operatorname{Out}(H)$ is a homomorphism without a split extension assumption. Its kernel is trivial because the identity outer class has the identity homeomorphism as a representative. This establishes the injection and the precise intersection statement simultaneously.

**No repair is required for proof correctness on the stipulated premises.** For exposition, it would help to add the same-upper-torus/opposite-port check from Section 3 and the explicit $b_1(W)=(10r^2+8)n+1$ count from Section 4 to the report. Those are clarifications of valid arguments, not replacements for a failed construction or estimate. The principal Lemma G is not passed merely because the report calls steps routine: its local placement, full middle basis, cap selection, connected-cut extension, and actual formal-ideal interface have each been checked above against the changed data.

A preliminary significance assessment is favorable enough to continue to the separately required novelty review. The elementary-abelian rank can grow while the dimension stays four, and each nonzero element is individually unrealizable; B's already stated arbitrary-graph tensor theorem and single self-map obstruction do not themselves state that conclusion. This review does **not** establish absence of a literature duplicate, exhaust every possible corollary of the corpus, or authorize counting the theorem as accepted. The separate primary-literature/contribution reviewer should judge whether the signed simultaneous constraint and the fixed-dimension realization bridge constitute the required substantial new deduction.

## 8. Independent diagnostics and reproducibility

Run, from the project root:

```sh
python frontier/experiments/i07_structures_r2/audit.py
```

The script writes only this review's assigned source/experiment directories. It records:

- All 18 pairs of nonempty deficiency sets and transition types, checking feasible integer splits of each five-edge bundle.
- All 936 rank-two Hermite-form lattices $\langle(a,0),(b,c)\rangle$ with $1\le a,c\le12$, $0\le b<a$. Exactly 23 have a coordinate loop and are excluded. Among 913 loopless cases, 126 even lattices are feasible and 787 noneven lattices infeasible under independent vector-bit propagation.
- Explicit full graph endpoint/cap assignments on even covers through rank six, retaining all five copies and both lifts of order-two edges, and checking actual received-port counts against every two-plus-two prohibition.
- The six-vertex mixed-relation example by exhaustive enumeration of all binary functions.
- The no-coordinate-loop and noneven properties of all 6,024 obstruction-lattice cases with nonzero binary $u$, ranks through eight, and $1\le R\le12$.
- A nonsplit integral Heisenberg example with 16,807 exact multiplication checks. The new longitudinal generator and transverse lift have nontrivial commutator $c^{2(2R+1)}$; replacing this extension by a direct product would fail this check.

All diagnostics passed. [checks.json](../experiments/i07_structures_r2/checks.json) retains the results. These checks do not establish smooth placement, PD duality, disk/cap topology, the formal construction, reflection, or an infinite-parameter theorem. Those conclusions depend on the source-contract comparison and arguments above. [review-artifact-hashes.json](../sources/i07_structures_r2/review-artifact-hashes.json) seals the review and its supporting artifacts, excluding that manifest itself.

Only `frontier/reviews/i07-structures-r2.md` and files under `frontier/{sources,experiments}/i07_structures_r2/` were written. No agents, commits, staging, shared-index edits, or other-project work were used. Final result: **proof PASS; contribution/novelty pending; accepted count unchanged at two.**
