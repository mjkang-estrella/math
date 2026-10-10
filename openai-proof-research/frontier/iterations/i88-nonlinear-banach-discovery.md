# I88 — nonlinear Banach geometry and approximation discovery

**Disposition: precise gap report; no substantial finding nominated.** Three distinct exact targets are screened below, with two developed approaches to the strongest approximation target. The proved partials are an exponential **evaluation-support** bound on the actual finite metric truncations, qualitative divergence of their required approximation **rank**, and a rank-one obstruction to converting support bounds into rank bounds by arbitrary finite-support perturbation. These are technical deductions, not a ninth finding. The desired explicit rank bound and the coupled absorption/AP construction remain unproved and unrefuted here. A proposed finite-binary-diamond strengthening is ruled out by an existing theorem.

All statements and lower proof operations in `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated premises. This report audits applicability and deductions, never upstream truth. No apparent disagreement with external literature is used. External sources are checked evidence, not additional stipulated premises. No worldwide-priority claim is made.

## Scope and evidence

Work is confined to this report, `frontier/sources/i88_nonlinear_banach_discovery/`, and `frontier/experiments/i88_nonlinear_banach_discovery/`. No shared indexes, other projects, old inputs, reviews, or seals were edited; no children were launched; no staging, commit, or publication was performed. Parent review, integration, counting, and publication remain separate. I80/I85/I86 and I84/I87 are outside this assignment. No active I86/I87 artifact is an evidence dependency.

AGENTS and the four current ledgers were read for the objective, current frontier, and prior screens; frozen copies are in `snapshots/`, with hashes in `inputs.json`. The supplied current state is eight accepted and two remaining; the fluid candidate remains held for contribution review. I12's coordinate-spiral obstruction already closes the dimension-free sphere-stability route. I03/I04 already develop invariant-halfspace constructions for bounded multipliers; their finite triangular cancellations do not supply an approximation or metric-equivalence bridge. I13's failed positivity, averaging, and fluctuation screens and I28's distinction between technical filtered persistence and a genuinely new realization inform the contribution assessment. None of those mechanisms is reopened.

The complete tree, not the old 719-manuscript catalogue or truncated root tree, controls scope: **13,223 entries, 749 manuscripts, 10,373 blobs**. The 9,340-file I14 corpus was enumerated with `rg --files --no-ignore`. I79's finalized maps supply the other 1,033 original bodies, including 776 PDFs and their extracted text. Every original body was checked against its Git blob SHA-1 and SHA-256; every searchable body was checked against its saved SHA-256. Existing bodies are referenced in place. No corpus download or recursive evidence copy was made.

`search-domain.json` records the exact 10,373-entry multiset, original paths/hashes and searchable paths/hashes. `queries*.json` and `search-*.jsonl` retain every matching line, path, and line number, including duplicate matches in different manuscript bodies and PDF extractions. Searches cover every mapped body, decoded as UTF-8 with replacement, with case-insensitive Python regular expressions. They are discovery screens, not claims of semantic exhaustion. The first broad search returned 721 lines across 71 manuscripts. The initial MAP/AP searches were overbroad; an attempted boundary repair was overescaped. Both failures are preserved. The final alphabet-boundary approximation search returned 38,608 lines across 704 manuscripts (short mathematical symbols still produce substantial noise); the final geometry search returned 299 lines across 32 manuscripts. Relevant title/family filtering, complete proof reading and companion inspection, not raw hit counts, determine the conclusions.

`families.json` names fourteen relevant manuscripts; `selected-inventory.json` records all 163 of their blobs, including PDF variants; `read-manifest.json` distinguishes complete proof-section reads from introduction-only or explicitly ranged screens. It is not a claim that every lower proof in every midpoint variant was read. All lower operations used in the new partial proofs were read completely. The exact free-space construction, both absorption constructions, the reflexive segment forest, its strongest joint-budget lens transfer, exact L1 moduli, independent products, doubling construction and the full cotype-cotype argument were inspected. The auxiliary recursive-potential variants and metric Markov cotype were screened to avoid identifying their different norms or invariants; no unseen lemma from them is imported.

Pinned abbreviations below denote manuscript directories under `preprints/` at the stated commit:

| Alias | Manuscript |
|---|---|
| F | Failure-of-Bounded-Approximation-in-a-Lipschitz-Free-Space-over-a-Uniformly-Discrete-Metric-Space-September-26-2026 |
| A | Bi-Lipschitz-Absorption-of-c0-Without-a-Linear-Copy-of-c0-September-26-2026 |
| L | Lipschitz-Equivalent-Separable-Banach-Spaces-Need-Not-Be-Linearly-Isomorphic-September-24-2026 |
| T | Asymptotic-midpoint-uniform-convexity-and-unbounded-diamond-distortion-in-a-reflexive-tree-space-September-27-2026 |
| J | Midpoint-lenses-in-segment-spaces-September-27-2026 |
| D | Diamond-distortion-from-midpoint-and-tree-energies-September-27-2026 |
| E | Exact-asymptotic-moduli-in-a-Daugavet-subspace-of-L1-September-27-2026 |
| P | Independent-products-in-real-L1-asymptotic-midpoint-convexity-without-AUC-renormings-September-27-2026 |
| H | A-doubling-Hilbert-subset-with-no-finite-dimensional-bi-Lipschitz-embedding-September-25-2026 |
| C | The-cotype-cotype-conjecture-under-the-approximation-property-September-23-2026 |
| N | Fixed-Points-of-Nonexpansive-Maps-in-Reflexive-Banach-Spaces-September-24-2026 |

Source paths, hashes, and theorem labels are resolved in the machine-readable manifests. Relative local source references here refer to the original sealed I14/I79 bodies, not copies edited for this report.

## Three exact targets and their status

**Q88, strongest target — intrinsic rank complexity.** Fix an integer p≥2 and F's actual bounded block M_p, anchor set A_p, graph sequence G_j, and parameters defined below. Put N_m=A_p∪⋃_{j≤m}V(G_j), with the **metric inherited from the full M_p**, and X_m=F(N_m). Let τ_m(n) be total variation distance between the empirical rooted colored radius-n type distribution of G_m and the independently colored regular-tree distribution. Seek explicit constants c_p,α_p>0 and an integer n_p such that, whenever n≥n_p, τ_m(n)≤1/(40V), and a real linear T:X_m→X_m satisfies

    ||T||≤p/2,       max_{a∈A_p} ||Tδ_a−δ_a||≤1/4,

one has rank(T)≥c_p ρ^(−α_p n). This is a concrete candidate, not an asserted theorem. Its indexing uses observable local statistics of the actual source graphs, not rescaled wedge blocks or an arbitrarily chosen subsequence. The proofs below do not establish it. Identity operators show that admissible maps exist at every finite stage, although their ranks can be large.

**S88 — coupled absorption and approximation.** Construct a separable real Banach space Z containing no linear copy of c0, with an onto bi-Lipschitz map Z⊕∞c0→Z, such that Z has AP but has no λ-BAP for every finite λ. Require a genuinely coupled construction and proof of these properties for that same space. A direct sum of independently supplied examples is not the intended contribution, and even that shortcut currently lacks AP for A's absorption space. This target is not established or refuted.

**D88 — finite binary obstruction in the displayed reflexive forest norm.** For T's actual space X=J_forest*, seek c>0 such that every embedding of the depth-k **binary** diamond into X has distortion at least c√k for all k≥1. This tempting strengthening of the countably branching result is false by the established finite-diamond characterization explained below. Countably branching, arbitrary finite branching, and binary branching are different targets. No claim about arbitrary branching b=b(k) is deduced from this rejection.

Additional screens below cover codimension complexity, doubling, cotype, fixed points, and the already-available MAP/midpoint combination. They do not furnish a fourth substantial candidate.

## Q88: exact source contracts

AP means that, for each norm-compact K and ε>0, a bounded finite-rank linear map approximates the identity within ε on K; its norm can depend on K,ε. λ-BAP imposes the common norm bound λ, BAP means some finite λ works, and MAP means λ=1. A rate needs further specified data: the compact set or anchors, error, norm allowance, and indexing/size parameter. AP alone is no rank-rate statement.

F, `reduction.tex`, proves a countable uniformly discrete pointed metric wedge M with F(M) having AP and failing every BAP. Its component M_p is countably infinite, of separation at least one and diameter at most

    B=300p²+150p+5.

The fixed finite anchors A_p contain o, and `thm:blocks` states that every finite-rank T0:F(M_p)→F(M_p) with ||T0||≤p satisfies max_a||T0δ_a−δ_a||≥1/2. This already quantifies over every rank. It is stronger than merely knowing failure of some BAP. The same source already records failure of nonlinear approximability and renormed-ℓ1 examples with quantitative BAP separation. Those are not I88 contributions.

For a bounded separated block the coefficient map is onto and satisfies

    (1/2)Σ|c_x| ≤ ||Σc_xδ_x|| ≤ BΣ|c_x|.                 (1)

For finite coefficients, the lower bound follows by prescribing f(o)=0 and f(x)=sign(c_x)/2, a 1-Lipschitz function on a 1-separated space. The upper bound is the triangle inequality. Passing to ℓ1 limits proves the bounds and closed range; density proves surjectivity. Thus this one infinite block is isomorphic to ℓ1 and has 2B-BAP. The wedge's failure of every BAP comes from unbounded obstruction constants across p. This is consistent with, and different from, its AP.

The geometry is countable and uniformly discrete, hence complete and separable. It is not proper: an infinite separated bounded block is not compact. It does not have bounded geometry in the usual sense sup_x|B(x,r)|<∞ for every r, since one such ball contains an entire infinite block. It cannot be doubling: iterated doubling would cover a bounded block by finitely many balls of radius less than 1/2. No reflexivity or dual-space property follows from countability or discreteness. Each block is ℓ1-isomorphic, and the whole wedge is not reflexive because it contains a complemented infinite block.

F fixes

    L=10p, R=30p, K=10p(R+1), D=K+2L+5,
    B=4R+D, V=1+4pB,
    even Δ≥4 with V/Δ<1/20,
    Q=Δ^(2L+1), H=Δ^(D+1), integer k>2ΔQH,
    ρ=ΔQH/k<1/2.                                      (2)

The symbols k and D in this section are a color count and a label cutoff, not diamond depth or embedding distortion. Finite Δ-regular colored multigraphs G_j converge in every fixed rooted radius to the independently k-colored regular tree. Incidences distinguish both orientations of a loop and all parallel edges. Every radius-2L metric ball has at most Q points. Labels h:M_p→{0,…,D}^k are 1-Lipschitz in the sup norm; at most H coordinates of h(t) are below D. A graph vertex x of color i has h_i(x)=0, and an anchor a(x) with h(a(x))=h(x), d(x,a(x))≤R. All these objects precede the operator.

F's actual graph construction uses finite random permutation models and one- and two-root collision estimates to select deterministic realizations. It proves convergence, not a canonical explicit vertex-count schedule for every local tolerance. The candidate Q88 specifies τ itself to avoid silently importing such a schedule. At each fixed radius there are finitely many rooted types, so pointwise convergence of their frequencies implies total variation convergence.

The inclusions X_m→X=F(M_p) are isometric: every real Lipschitz function on N_m extends to M_p with its Lipschitz constant by the scalar extension formula. Their increasing union is dense. Distances on N_m are inherited; deleting future vertices and recomputing shortest paths would be a different metric and is not authorized by this argument.

## Approach A: matched-walk support complexity

**Proposition A (technical, source-relative).** Fix p≥1 and all F data (2). Let n≥2 and m≥1 satisfy τ_m(n)≤1/(40V). Suppose a bounded real linear map T:X_m→X_m has norm at most 2p, error strictly less than 1 on every anchor, and range contained in span{δ_j:j∈S}, where S⊂N_m is finite and contains o. Then

    |S| > [k/(40VH)] ρ^(−n).                            (3)

The same proof permits codomain X and any finite S⊂M_p: only the domain must contain N_m. This is a statement about a common coordinate support, **not** a lower bound on rank(T).

**Proof.** Write Tδ_x=Σ_{j≠o}c_x(j)δ_j for x∈N_m. Define μ_x(j)=c_x(j) for j≠o and μ_x(o)=1−Σc_x(j). This signed measure has total mass one, and for every Lipschitz g on M_p,

    ∫g dμ_x=(Tδ_x)(g−g(o))+g(o).                        (4)

Assigning sign(μ_x(j)) on S and zero elsewhere gives a 2-Lipschitz test by separation. Therefore ||μ_x||TV≤1+2||Tδ_x||≤V. For each source vertex x, put

    b_x(t)=L(1−||h(x)−h(t)||∞/K)_+.

It has range [0,L], Lipschitz constant ≤L/K, and b_x(a(x))=L. The anchor approximation and ||T||≤2p give

    ||Tδ_x−δ_a(x)||≤2pR+1,
    ∫b_x dμ_x≥L−(L/K)(2pR+1)≥3L/4,                  (5)

since (2pR+1)/K≤1/5. Every calculation uses only vectors in the domain; no extension of T to X is required.

Call (x,j) compatible if ||h(x)−h(j)||∞≤K+2L+1=D−4. A matched walk is a nonbacktracking source walk with compatible states in S and successive state distances ≤2L. Let β be the fraction of G_m roots starting a length-n matched walk. For each state j put C_j={i:h_i(j)<D}; then |C_j|≤H and compatibility requires the source color to lie in C_j. Forgetting all other compatibility conditions gives a weaker event determined by the colored radius-n type. On the regular tree there are at most Δ^n source walks and |S|Q^n state sequences. Each uses n+1 distinct source vertices, so independent coloring gives probability at most (H/k)^(n+1). Thus

    β ≤ |S|(H/k)ρ^n+τ_m(n).                           (6)

This estimate is uniform in the chosen S, including supports selected after seeing G_m: total variation bounds every union of types. One never conditions random colors on the operator or its support.

For completeness the deterministic continuation operation is as follows. A root is bad if it starts a matched walk of length n. At a good vertex x, for each outgoing incidence e and state j let r_x(e,j) be the largest positive matched length starting through e with state j, or zero if none. All records are less than n. Declare e exceptional at (x,j) precisely when its record is strictly larger than every competing outgoing record. At most one incidence is exceptional for each state; a tie selects none. At a bad vertex declare all directions exceptional. Denote the exceptional-state set for e by E_e.

If e:x→y, (x,j),(y,j′) are compatible and d(j,j′)≤2L, at least one of j∈E_e or j′∈E_reverse(e) holds. Indeed, if both endpoints are good, let A_x,A_y be maximal records excluding e and its reverse. Prepending e to a maximizing continuation at y, or using e alone when that maximum is zero, gives r_x(e,j)≥1+A_y. Reversing gives r_y(reverse(e),j′)≥1+A_x. If neither direction were exceptional, A_x≥1+A_y≥2+A_x, impossible. The incidence formulation handles loops, parallel edges and repeated states without change.

Prescribe f_e=b_x on S\E_e and f_e=−b_y on S\E_reverse(e). Within either set the Lipschitz bound holds. Across the sets, distances ≥2L dominate the total size of the prescribed values. If the distance is <2L and either bump is positive, the triangle inequality for labels makes both pairs compatible; the continuation conclusion then excludes the simultaneous prescriptions. Otherwise both values are zero. The prescriptions are thus consistent and 1-Lipschitz. The scalar formula min_j(f_e(j)+d(j,t)), clipped to [−L,L], extends them to M_p.

Equations (4)–(5) give

    ∫f_e d(μ_x−μ_y) ≥ 3L/2−2L(|μ_x|(E_e)+|μ_y|(E_reverse(e))),
    |∫f_e d(μ_x−μ_y)| ≤ 2p.                           (7)

The second line uses d(x,y)≤1 and cancellation of constants in (4); a loop gives zero. Average over a uniform vertex and a uniform outgoing incidence. At good vertices each state contributes to at most one direction, so the expected exceptional variation is at most V/Δ+Vβ. Reversal preserves the uniform incidence distribution, including loops. Therefore

    2p ≥ 3L/2−4L(V/Δ+Vβ).                              (8)

If (3) failed, (6) and the assumed τ would give β≤1/(20V). As V/Δ<1/20, the right side of (8) would be strictly larger than 11L/10=11p, a contradiction. This proves (3). ∎

**Exact contribution comparison.** Every ingredient of this proof is already a lower operation of F: `lem:measure-bounds`, `lem:rare-walks`, `lem:exceptional-directions`, `lem:edge-test`, `eq:average-error`, and the abstract criterion `rem:abstract-obstruction`. I88 retains the pre-limit total variation error and solves the same inequality for |S| on finite truncations. It does not improve the continuation mechanism. Even though its exponential support bound is explicit, this is technical extraction, not substantial discovery.

### Why arbitrary finite-rank perturbation does not turn (3) into Q88

F's `lem:finite-support` writes T0=Σ_{i≤r}φ_i⊗v_i and approximates each v_i by a finitely supported vector. It gives arbitrarily small operator-norm error, but no cardinality bound on the resulting support. Merely counting the r basis vectors is invalid.

**Proposition A′ (a scoped counterexample to that shortcut).** For every N≥1 choose N distinct nonbasepoint x_i in M_p and set v_N=(BN)^−1Σ_{i≤N}δ_xi. Fix any φ∈X* of norm one and set T_Nu=φ(u)v_N. Then rank(T_N)=1 and ||T_N||≤1. If U:X→X is any bounded linear map whose range is supported on at most s nonbasepoint coordinates, with 0≤s≤N, then

    ||T_N−U|| ≥ (N−s)/(2BN).                            (9)

**Proof.** The upper estimate in (1) gives ||v_N||≤1; its lower estimate makes v_N nonzero. At least N−s selected coordinates lie outside U's support. For every u of norm at most one, the coefficient difference at each such coordinate is φ(u)/(BN). By the lower estimate in (1), ||(T_N−U)u||≥(N−s)|φ(u)|/(2BN). Take the supremum, using ||φ||=1; norm attainment is unnecessary. ∎

Consequently approximation within any η<1/(4B) requires more than N/2 support points, even for these norm-at-most-one rank-one operators. No universal perturbation-support bound depending only on rank, operator norm and accuracy exists for arbitrary operators on this fixed block. This does **not** disprove Q88: the operators in (9) need not approximate A_p. A valid new approach could exploit precisely that missing anchored structure. It would have to prove a structural localization or low-rank obstruction adapted to the anchor identities; none is supplied here.

## Approach B: finite-rank bidual limits and local reflexivity

This second construction starts from hypothetical bounded-rank approximants and actually builds a global forbidden operator. It does not use the finite-support perturbation or (3).

**Proposition B (qualitative rank divergence; technical).** Fix p≥2, 1≤λ<p and 0≤ε<1/2. For every integer r≥0 there is m_0 such that for all m≥m_0 there is no real linear map T:X_m→X, of rank at most r and norm at most λ, satisfying max_a||Tδ_a−δ_a||≤ε. In particular, the least rank of an endomorphism of X_m with these bounds tends to infinity as m→∞. This applies to λ=p/2, ε=1/4 in Q88. It gives no effective m_0 or exponential rank rate.

We use the standard principle of local reflexivity in its following precise form: for finite-dimensional F⊂X**, and 0<η<1, there is a linear P:F→X with ||P||≤1+η and P fixing F∩X, under the canonical identification. The primary author-hosted Goucher–Kania article states this as Theorem 2.4, with a stronger two-sided estimate. Its actual title, publication information and retained bytes are recorded below; the search-engine abbreviated title is not treated as metadata.

**Proof.** Suppose a cofinal sequence m_l admits such maps T_l with ranks ≤r. If r=0, extend the zero operator to X and use F's anchor obstruction immediately. For r>0, choose an Auerbach basis v_li in the range of each nonzero T_l, and pad with zero terms to r. This means the basis vectors and coordinate functionals have norm one. Existence follows by maximizing absolute determinant over tuples of unit vectors in the finite-dimensional range: replacing one maximizing column proves each coordinate functional has norm at most one, and its value on its own column proves equality. We may write

    T_lx=Σ_{i=1}^r φ_li(x)v_li,   ||v_li||≤1, ||φ_li||≤λ.

Extend each φ_li from X_{m_l} to X by Hahn–Banach, preserving its norm. View v_li in X**. Weak-star compactness of the finite product (λB_X*)^r×(B_X**)^r gives a subnet on which all coefficients and vectors converge weak-star, to φ_i and v_i** respectively. Define

    T**x=Σ_{i=1}^r φ_i(x)v_i**.

This is a finite-rank bounded operator X→X**. For any fixed x in the increasing union of X_m, x is in the domain eventually. For each f∈X*, the finite sum φ_li(x)f(v_li) converges to Σφ_i(x)v_i**(f), so T_lx converges weak-star to T**x. Norm lower semicontinuity gives ||T**x||≤λ||x|| on this dense union, hence on X. The same argument at each anchor gives ||T**δ_a−δ_a||≤ε.

Let F0 be the finite-dimensional span of T**X and {δ_a:a∈A_p} in X**. Choose 0<η<1 so that (1+η)λ≤p and (1+η)ε<1/2; the strict λ<p and ε<1/2 make this possible. Apply local reflexivity to F0. The composite PT**:X→X is finite-rank, has norm at most p, and

    ||PT**δ_a−δ_a||=||P(T**δ_a−δ_a)||≤(1+η)ε<1/2.

This contradicts F's fixed-anchor obstruction. Thus no such cofinal sequence exists, exactly the asserted eventual exclusion. The same conclusion holds for endomorphisms X_m→X_m by inclusion. Their least admissible ranks are finite because λ≥1 permits the identity. ∎

The construction first lands in X**, which need not equal X. Returning to X by local reflexivity is essential; coordinatewise convergence or weak compactness of the unit ball of X cannot be assumed. The slack λ<p is deliberately retained. This proof does not certify the endpoint λ=p. It also supplies no quantitative control of m_0: neither the compact subnet nor local reflexivity constructs such a rate. Relabeling a subsequence by r, or rescaling blocks in the wedge, would hide rather than solve that gap.

**What Q88 still needs.** Approach A makes the graph-depth dependence explicit but sees coordinate support. Approach B sees rank but loses all effective graph-depth dependence. A successful proof must connect low-dimensional range geometry to F's actual compatibility constraints, uniformly over diffuse signed range vectors and over all operators obeying the anchor conditions. Alternatively it needs a quantitative replacement for the bidual-limit step controlled by τ_m(n). No such lemma is proved; it is not safe to state the exponential rank bound conditionally on an unproved lemma and count that as the desired finding.

## S88: why the two nonlinear constructions do not yet couple to AP/no BAP

L constructs separable real Lipschitz-equivalent spaces, one containing c0(ℓ2) and the other not containing c0(ℓ2), with displayed bi-Lipschitz bounds 4/21 and 76/25. Excluding c0(ℓ2) is not excluding scalar c0. Its proof uses a weakly sequentially complete free space E over a Hilbert domain, a completely continuous linearization q of h−π_U, and weighted graph sequence spaces with (Qs_i)∈c0(H). The nonlinear triangular inverse is assembled from an onto Hilbert slot rearrangement. It is not a linear section of q. No AP theorem for the resulting graph spaces is proved by that construction.

A gives the stronger scalar-c0 exclusion, but by a different norm. It completes a quotient of finitely supported mass-zero molecules on the unit ball of c0⊕∞c0. Its norm is an ℓ2 combination of seminorms σ_d defined by admissible lists of specially generated tests. Tests include finite-coordinate corrections, local flattenings/remainders at nonincreasing dyadic scales, and tail factors. The countable classes carry separate Lipschitz bounds and exponents p=1+1/k. The norm is not simply the usual Lipschitz-free norm.

The bounded map Q and radial lift K(x)=||x||ζ(x/||x||) satisfy QK=g−P. This identity enables the explicit absorption inverse: from d, take (t,u)=g^−1(Qd), then b=d−K(t,u). The no-c0 proof fixes one detecting σ-class from a hypothetical bounded-sign sequence, converts lists to individual detectors, and constructs compatible growing detector sums. Its three localization cases depend on escaping labels, cylinder scales, or tails. Pointwise convergence of a fixed test operation on a fixed vector is not uniform boundedness of linear truncations on the completed norm.

Two concrete insertion attempts stop at separate obligations:

1. Push forward molecules by finite-coordinate truncation of the underlying c0 domain, then discretize. Finite-coordinate image alone is a continuum, so the induced molecule map need not have finite rank. Discretization must respect the quotient and be bounded for **every** σ-class. Pulling tests back by truncation/discretization is not shown to preserve the admissible signed-sum constraints, cylinder ordering and tail factors. Finite dependence of individual tests does not prove the required operator bound or AP.
2. Insert F's anchor blocks into the test norm, seeking contractive restrictions/retractions that carry its obstruction. This would require quantitative lower bounds on the embedded free-block norms and a bounded retraction to them, while preserving QK=g−P and the full no-c0 detector argument. Merely adding seminorms can destroy the Lipschitz lift; weakening them can lose the obstruction. No such compatible insertion and retraction are constructed.

Even a direct sum Z_A⊕F(M) requires AP of Z_A to prove the proposed AP conjunction, and would in any case be the excluded ordinary-sum mechanism. The legitimate target is a new compatible construction, not a new name for a sum. Likewise a continuum of weights or block labels produces no continuum of isomorphism types without a proved separating invariant. No cotype, Szlenk-index, reflexivity or duality assertion is inferred from the absence of c0.

## D88: finite diamonds versus countably branching diamonds

T's space is the dual of the disjoint-segment forest norm on the disjoint union of countably branching finite-height rooted trees. Height-h components are Hilbert-isomorphic with constants allowed to depend on h; their outer Hilbert sum is reflexive and separable. This does not give uniform Hilbert constants over h. Finite ancestral head and tail projections are contractive. T gives averaged midpoint growth at least √(1+t²/12)−1 in the displayed norm and proves that **no equivalent norm** is AUC by bounded paths with weakly null separated child increments.

The strongest relevant companion is J, not T's first displayed constant. J's joint-budget proof combines paired endpoint atoms. For a center x supported in finite ancestral H and arbitrary y with ||x±y||≤R it gives

    ||Q_H y||≤2√(R²−||x||²).                           (10)

The operation uses coefficient variance η and quadratic slack θ: opposite-sign crossing segments at a gate can be split, giving a shared budget; the projected signed endpoint mean and coefficient error are bounded by √(η+2θ) and √η, hence by 2√(η+θ). Arbitrary displacement, rather than displacement already in the tail, is part of this strongest interface. The full atomic/polar finite-head argument and joint-budget/consequence proof were read. One must not identify the infinite-height closed coordinate span with the full dual; J explicitly separates them.

D, `metrics.tex`, takes an infinite ε-separated lens, selects two deviations with arbitrarily close finite-head projections, applies (10) to their half-difference, and obtains ||x||²+ε²/16≤R². In a noncontracting embedding of the **countably branching** depth-k diamond, the child deviations are 2-separated. The stage-slope suprema therefore satisfy R_j²+1/4≤R_{j+1}², giving distortion²≥1+k/4. This improves T's 1+k/12 and is already a companion theorem, not a new I88 bound.

The finite-head pair selection is exactly where countable branching matters. D's alternative atomic slope-martingale preparation and direct adaptive/common-head routes were also checked: they first select a replacement path from infinitely many choices. A finite martingale at the end of that proof does not mean the initial graph was finitely branching. Replacing infinite choices by a finite b requires a uniform covering bound for an embedding-dependent head; no such bound follows from reflexivity or separability. Weak compactness would not preserve a lower norm-separation inequality under weak limits.

For the specific binary target there is a decisive prior result. Johnson–Schechtman's primary paper, Section 3, Corollary 1, gives: for every λ>1, every finite depth k and every nonsuperreflexive Banach space X, the binary diamond embeds in X with distortion at most 8λ. Their Section 2 defines the binary replacement metric; Section 3 constructs the embedding using a finite James sequence. The normalized source metric differs only by a common scale. T's X cannot be superreflexive: superreflexivity admits an equivalent uniformly convex norm, which is AUC, contradicting T's renorming obstruction. Thus the finite binary distortions here are bounded independently of k. D88 is rejected. This is compatible with the countably branching obstruction and does not exploit any inconsistency. See the [author-hosted primary paper](https://www.weizmann.ac.il/math/gideon/sites/math.gideon/files/uploads/diamond.pdf).

## Further compatibility and contribution screens

**Exact L1 moduli and codimension cost.** E supplies a specific real Daugavet subspace with unit ball precompact in measure and centerwise exact averaged modulus max(t/2,t−1), one-sided modulus max(0,t−2), and no AUC equivalent norm. The lower proof clips y by |x|/t. Its compact family of clipped vectors has a finite L1 ε-net; intersecting kernels of the sign functions of that net supplies the finite-codimensional subspace. The upper proof uses Daugavet diameter-two behavior and a finite-quotient correction. A conceivable new target is a bound codim(F)≤C_t ε^−q, uniform in all unit centers x, achieving the lower estimate within ε in that same space. The actual compactness proof gives no uniform entropy of the clipped families over x. The detailed heavy-tail construction and its constants do not supply it. Neither a polynomial codimension bound nor its failure is proved here.

**A MAP/midpoint combination is already routine.** P's independent positive mean-one multiplier products P_v, with finite second moment, admit finite predecessor-closed conditional expectations Q_TP_v=P_vT. These are contractive finite-rank projections on the actual closed span. Along increasing T exhausting the countable tree they fix each product eventually, hence converge strongly to the identity; boundedness upgrades convergence uniformly on compact sets. Thus the displayed space has MAP by a standard finite-net argument. P already gives positive averaged midpoint estimates for exponential and Gaussian-square laws and excludes every equivalent AUC norm. Combining those statements with its explicit projections is not a substantial new construction. P does not assert reflexivity, Daugavet, or measure-precompactness; none is added here.

**Cotype cannot fill the rank gap by changing its meaning.** C assumes AP, finite Rademacher cotype of X and finite Rademacher cotype of X*. Its lower operations already give uniform finite-rank Walsh decay, constants depending only on the fixed cotype data, and the compact-domain approximation argument. Its scalar Fourier index has binary-matrix rank, distinct from operator rank. The proof's finite-dimensional Hilbert factorization constant is operator-dependent and used only to contradict an infinite slow-decay sequence. Turning the output into a rank-rate theorem is not a parameter substitution. AP approximates a compact composite in operator norm; it supplies no uniform bounds for the uncomposed approximants. The compact domain is a quotient of a Hilbert sum of finite-dimensional spaces, and the source explicitly notes that coordinate truncations need not descend to that quotient.

For F, a complemented block is ℓ1-isomorphic, so the dual of the wedge contains an ℓ∞-isomorphic subspace. ℓ∞ has no finite Rademacher cotype: its first n unit vectors have Rademacher-sum norm one and coefficient ℓq norm n^(1/q). Isomorphisms change constants but not this divergence. Thus C's dual-cotype hypothesis fails for that attempted application. A's no-c0 statement does not imply finite cotype either. The separate metric Markov cotype theorem for ℓ1 uses movable nonlinear modified points in a Markov-chain inequality; it is not the dual-cotype input to C and cannot be substituted for it.

**Doubling nonembedding is already stronger than its title.** H constructs a single Hilbert subset with doubling constant at most 76,800 and no bi-Lipschitz embedding into any finite-dimensional Euclidean space. Its anisotropic sheet argument selects derivatives near a lexicographic maximum. The horizontal energy has an explicit decay estimate; the vertical step uses compactness near that lexicographic maximum, and the selected physical scale depends on the map. No explicit finite-cardinality obstruction rate is inferred from it. H already transfers the obstruction to Lp through Gaussian isometries and constructs compact examples in every infinite-dimensional Banach space using finite witnesses, finite-dimensional almost-Hilbert embeddings and separated clusters. Repeating compactification or that target transfer would duplicate existing lower proof operations. H's finite-witness extraction uses finite-dimensional target compactness and pays the stated distortion slack; an analogous global extraction for T's infinite-dimensional target cannot be assumed with the same constants. H is not uniformly discrete, and its doubling property cannot be assigned to F's infinite bounded separated blocks.

**Commuting fixed points are already supplied with the needed conditions.** N's introduction includes a proved corollary for an arbitrary pairwise commuting family on a nonempty closed bounded convex set in a reflexive real Banach space: the common fixed-point set is nonempty and is a nonexpansive retract. Its proof invokes Bruck's theorem using weak compactness, the fixed-point property and the conditional fixed-point property on invariant closed convex subsets, inherited from the one-map theorem. This is not naive iteration over possibly nonconvex fixed sets. Presenting a commuting-family or commuting-semigroup corollary as new would repeat the source. No extension to noncommuting actions or altered invariance conditions is claimed, and no independent audit of N's stipulated one-map proof is attempted.

## Primary literature checked and limits

Three bounded web-search rounds are retained verbatim as `web-search-{1,2,3}.json`; irrelevant search results and secondary expositions are not mathematical inputs. Actual response bodies, headers, final URLs, retrieval times, byte counts, hashes and PDF text extractions are in `external/`. All six requested primary/metadata responses returned HTTP 200. The final narrow novelty search was noisy and supplies no absence-of-prior-art certificate.

- Richard J. Smith, [Lipschitz-free spaces and Bossard's reduction argument, arXiv:2509.00722v4](https://arxiv.org/abs/2509.00722v4), latest version shown by the retained abstract page: 23 February 2026. Theorem 1.3 concerns **countable complete discrete** spaces with free spaces failing BAP; its proof also records AP. It is descriptive-set-theoretic, not an explicit uniformly discrete block construction or quantitative rank theorem. Theorem 1.3 and its proof were read; no identity of discrete and uniformly discrete is inferred.
- Cúth–Kalenda, [Lipschitz-free spaces over uniformly discrete metric spaces are 3-Schur, arXiv:2604.01875v1](https://arxiv.org/abs/2604.01875v1), latest version shown: 2 April 2026. Theorem 1.1 applies to every uniformly discrete metric space and gives 3-Schur, with optimal universal constant. Its introductory open-problem wording is historical context, never a reason to challenge stipulated F. This result would give a routine extra invariant, not the missing rank estimate; it is not needed in Propositions A, A′ or B.
- Goucher–Kania, [Invariant means on Abelian groups capture complementability of Banach spaces in their second duals](https://users.math.cas.cz/~kania/papers/GoucherKania.pdf), retained publisher-style Online First PDF, published 25 February 2021, DOI 10.4064/sm200706-15-1. Theorem 2.4 states the exact local-reflexivity form used in B. The search result's abbreviated title differs; the actual PDF controls attribution. This standard theorem is an explicit external dependency, not an alleged new operation.
- Johnson–Schechtman, author-hosted *Diamond graphs and super-reflexivity*: Sections 2–3, Proposition 1 and Corollary 1 were read, including the construction; the introduction states the uniformly-convex-renorming characterization. The retained author PDF is identified by URL and hash rather than an invented version number. It closes D88, not the countably branching question.

This bounded comparison suffices to reject the listed routine/repeated mechanisms and to expose the current gaps. It does not establish worldwide novelty of the candidate rank statement or the absorption conjunction, and no substantial status is sought for the technical partials.

## Stress tests, corrections, and handoff

`diagnostics.py` is a deterministic, standard-library, read-only finite test. It exhausts degree-four permutation multigraphs on one to three vertices, all two-state compatibility assignments, both possible reflexive symmetric two-state transition graphs and continuation cutoffs 2,3,4. It checks unique exceptional direction at every good state and the two-endpoint exceptional alternative, with loops, parallel edges and zero/tied records included. It also checks the exact rational budgets in (2), (5), (8) for p=1,…,4, and the diffuse rank-one support barrier for N=2,8,64,256. These checks stress the formulas and incidence conventions; the analytic proofs above, not the finite experiment, justify the universal propositions.

Pre-seal failures and corrections are retained in `preseal-corrections.md`: noisy MAP/AP searches; the overescaped first repair; a wrong assumed cotype section directory; missing optional HTML parser; truncated combined terminal displays repaired with targeted reads; the finite-support/rank confusion rejected by (9); use of induced finite metrics; and the strict norm slack needed in B. No failed approach is silently promoted or erased. No post-seal amendment or resealing is part of this record.

Run the offline verifier from the repository root:

    python frontier/experiments/i88_nonlinear_banach_discovery/verify.py

It reads only local files, checks the exact owned domain against `seal.json`, verifies immutable input references and all 10,373 pinned originals/search bodies, checks the complete tree/domain identity and I79 provenance map agreement, replays exact search multisets and finite diagnostics, and allows drift only in the four explicitly named ledgers whose snapshots remain fixed. It performs no fetch, write, repair, or reseal. Its stdout distinguishes **EVIDENCE PASS** from mathematical review. Hashes cannot verify a proof or confer substantial contribution status.

**Parent handoff:** no count increment; independent original-proof and contribution verdicts are not supplied by this author. Preserve A, A′ and B as technical partials. Reopen Q88 only with an anchored low-rank localization mechanism or a quantitative substitute for the bidual-limit step. Reopen S88 only with bounded finite-rank maps in A's actual quotient norm and a compatible transfer of F's anchors. The finite binary diamond target is closed by existing literature. No active fluid/close-algebra lane or parked arithmetic/combinatorial branch is affected.
