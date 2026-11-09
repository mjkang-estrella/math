# Standalone ordinary-proof investigation

This lane is Sol discovery only. Accepted campaign count at intake is 52/60 beyond 39 prior; this lane contributes zero. No Lean, mathematical enumeration, solver, git, child, contact, browser tab, publication or upload was performed. Every conclusion is about the fixed reservation, not the corpus at large.

## 367009: sustained spherical E1a route — HOLD

Exact target: for every minimally rigid graph G and every E1a extension G', c°₂(G')=2c°₂(G). The counts are complex spherical realizations modulo direct isometries, with reflections distinct. Real drawing counts cannot substitute. Source: 2502.04736v1 Definitions 1–2, Section 3, Figure 9, Section 7.2.1 Conjecture 2. Figure 9's inline SVG path data was inspected: the old three vertices form a triangle; the extension retains two triangle edges, removes the third and joins the new vertex to all three. This is source-diagram vector-path inspection, not a claim of raster visual review. The figure is preserved separately.

Write the old vertices as a,b,c with deleted edge ac and retained ab,bc; write u for the new vertex. Prescribed dot products are A=a·b, C=c·b, D=a·u, E=c·u, F=b·u, and all vectors have square 1. Put s=1-F². In the nondegenerate open set s≠0, resolve a and c into the plane span(b,u) and its one-dimensional perpendicular. Their plane components have prescribed inner product

P=(AC+DE-F(AE+CD))/s.

Their perpendicular squared lengths are

R=1-(A²+D²-2FAD)/s,
T=1-(C²+E²-2FCE)/s.

Consequently the missing dot product z=a·c satisfies (z-P)²=RT. For sRT≠0 there are exactly two distinct values P±sqrt(RT). For fixed linearly independent a,b,c, u is uniquely determined by its three dot products, so there is no further local twofold multiplier after fixing one branch. This is stronger than merely proposing reflection of u: reflection alone does not preserve all five constraints with abc fixed.

The tempting global argument is: condition on either z, complete G with its original triangle measurements, obtain c°₂(G) extensions on each branch, and sum the two branches. A second approach fixes the oriented triangle abc, counts extensions of the rest, and compares the local gadget's four SO(3)-orbits with the triangle's two SO(3)-orbits. Both approaches predict ratio two and agree on orientation factors. Neither local quadratic alone proves the full assertion.

Precise remaining bridge: construct an irreducible dominant measurement correspondence including all untouched edge lengths; show that for a common nonempty Zariski open set of G' measurements, BOTH z branches avoid the exceptional locus of the generic rigidity map for G. Then show the finite reduced fiber has c°₂(G) points on each branch with the same direct-isometry convention. A generic fiber of the old map is insufficient unless this dominance/exceptional-locus statement is proved. Stabilizer and orientation issues must be treated explicitly. The generic-degree interpretation in source Section 3 and Dewar–Grasegger 2309.16416 Section 4 is relevant but does not by itself certify this base change. Calligraphs and sphere realizations 2308.15305 Theorem 2.6 is a serious possible existing subsumer, not novelty clearance.

Source work: latest listed source version v1 and abstract history read; latest companion HTML retrieved and selected definition/theorem/gluing passages read. Full calligraph proof, journal versions/corrections, and all citing bodies were not reviewed. Current registry heads and routing indexes were fetched; absence of a title is not evidence of novelty. This is an ordinary proof route with an identified missing lemma, not CANDIDATE.md and not a Pi execution request. Even after a mathematical closure, the possible complete classical/source bridge requires adjudication before significance credit.

## 363119: sustained exact union-closure route — HOLD

Exact target: for every x≥5, with n=4x+4 and S exactly the Section 3 constructed family, |cl(S)|=23n²/32+35n/8−21. All of the construction matters; the literal record by itself omits it. Read 2405.10639v2 Sections 2–5, Theorem 1 proof and appendix descriptions. Version v1's Conjecture 3 is unchanged. The source has checked x=5,…,12; no computations were run here.

First mechanism: compress each of the four moving index families by extremal generators. Put m=n/2, q=n/4. The first two families together consist of A_i={1,4}∪[i+1,r(i)] for 5≤i≤m, with r(i)=m+i−2 for i≤q+2 and r(i)=m+i−3 for i≥q+3. Every such interval contains m+1 when n≥24. Hence for any nonempty set of indices I, its union is exactly {1,4}∪[min(I)+1,max_{i∈I} r(i)]. The function r is nondecreasing and has a plateau at q+2,q+3. This proves extrema compression, but shows why simply counting pairs min/max double counts: both ends of that plateau can give the same upper endpoint.

The last two moving families (excluding the separately listed special index 3n/4+1) consist of B_j={2,3}∪[5,a(j)]∪[j+1,n], where a(j)=j−m+1 on m+4≤j≤3q and a(j)=j−m+2 on 3q+2≤j≤n−1. For any nonempty J, union B_j is {2,3}∪[5,max a(J)]∪[min J+1,n]. Thus a mixed A/B union has at most two gaps in [5,n]. The extrema lemma follows directly by taking unions of prefixes, suffixes and overlapping intervals; no search is involved.

Second mechanism: take complements. Intersections of the B middle gaps and complements of A intervals give a canonical one- or two-gap representation. One must use maximal missing integer intervals, so empty and adjacent gaps collapse canonically. This removes the main cross-family overcount, but it is not yet a count of cl(S).

The 11 exceptional generators are S0,S1,S2,S3,S4,S(m+2),S(m+3),S(3q+1),S_n,S(n+1),S(n+2). Every union of the DISPLAYED generators is an extrema-compressed moving union joined with a union of exceptional generators. This is a correct structural reduction, not a license to count their representations independently. Exceptional sets can fill or shorten either gap, and different exceptional subsets can become the same union.

Additional source-definition hold: the retrieved Section 3 display has no S_(n/2+1), although the preceding family is indexed S0 through S(n+2). Literal alttext-token inspection confirms the omission in the HTML; the linked generator code and original typesetting have not been checked. Do not invent that missing set. The reductions here concern the displayed generators and cannot yet certify that they equal the intended full family. No correction credit is claimed.

Precise missing lemma: a disjoint, exhaustive classification of all resulting maximal-gap normal forms, including membership in {1,2,3,4}, together with their parameter ranges, followed by symbolic cardinality sums and proof that every normal form is attainable. Without it the coefficient 23/32 and the linear/constant terms are not proved. Interpolating source values or using its Θ(n²) theorem would not prove the exact formula. The empty subfamily is also included by the literal Notation 1 definition; the source's computational convention must be reconciled before alleging any off-by-one discrepancy. No endpoint-correction credit is sought.

This is not an exclusion for ease or being in a familiar family. No complete classical theorem proving this exact count was found. A full proof could be relatively discrete to formalize, but no bounded implementation plan is authorized before the missing count and source/novelty/significance gates close.

## 362949: sustained stack recurrence route — HOLD

Exact target: all positive t and all n≥2t+1, the parity-dependent two-step cardinality recurrence for Sort(t,n)(123,132). Read 2405.01854v1 Introduction, Preliminaries, Propositions 3.1–3.2, Lemmas 3.3–3.6, concluding proof/Conjectures 4.1–4.5. Abstract history lists only v1. The source's periodic-point notion and exact definition of Sort must be carried into any endpoint; they cannot silently be replaced by classical West sorting.

Local operational lemma: if an existing top-to-bottom stack already avoids 123 and 132, pushing a fresh value y is legal iff at most one existing stack entry exceeds y. Proof: all old triples were legal, so a new forbidden triple must begin with y, and either ordering of two later entries greater than y makes 123 or 132. Conversely two such entries form one of those patterns. This yields a faithful threshold transducer: repeatedly pop until at most one larger entry remains, then push. It is a mathematical lemma, not an executed algorithm.

First recurrence route: delete two stabilized small entries from a periodic target, standardize the rest, and attempt a constant-fiber insertion inverse. The source's half-decreasing periodic characterization has small entries in alternate slots, so this is natural. The failure is at the INPUT: deleting entries can change whether a pending push has one or two larger stack entries, changing an arbitrarily long sequence of pops. It does not commute with an iterate merely because the output's two slots are stable.

Second route: track a marked threshold state through t passes and build a recursive preimage decomposition instead of deleting directly. The local lemma gives the exact information needed at a single push. But the distribution of the bottom element and threshold states is not yet determined by length and t; no uniform fiber of (n+3)/2 or (n+4)/2 has been proved. A decisive missing result is a reversible insertion/deletion theorem on actual t-sortable permutations, including all boundary n=2t+1 cases, with these exact fiber sizes.

Semantic caution: the introductory generalization to reaching periodicity is not a complete explicit definition of Sort(t,n) at Conjecture 4.5. Under a tentative one-pass-to-periodic interpretation, if the input's first entry is not 1 then 1 remains immediately above the bottom after it is pushed, hence outputs penultimately. This observation is not a resolution of the literal conjecture and no small-endpoint objection is offered as a new result. The exact intended Sort definition needs source qualification. No enumeration, transducer execution, or new proof claim occurred.

## Existing-resolution bridges and compact parks

367948: 2504.06941 labels the exact three congruences (1.8)–(1.10) as Conjecture 1.2 and devotes Section 4 to proving it. The proof derives modulo 128 for 144n+42 in (4.15), derives divisibility by 3 for 9n+6, and combines coprime factors to obtain 384 at 144n+42=9(16n+4)+6. Its dyadic branches and Lemma 4.1 give the remaining all-alpha families; direct variable matching, not a new modular proof, identifies the entire literal target. Exclude as already resolved in its own source; no claim that all cited theta identities were independently reproved.

369497: Huang–Ouyang–Dong 2007.13308 Theorem 3 gives e≤2v+4x−12 whenever 2≤x≤y. For the literal hypotheses x≥3 and y≥6x−12, y−x≥5x−12≥3, so these hypotheses hold. No relabeling, duality or additional planarity hypothesis is needed. Wang 2507.19762 Theorem 2 quotes the same prior result. The original Theorem 3, definitions and initial Section 5 proof claims were read. This is an explicit complete subsumption bridge, not a new bound.

370847: AHK 1511.02888 Conjecture 1.1 is explicitly proved by the paper and is the exact coefficient absolute-value log-concavity target after replacing their rank r+1 by the record's rank r(M). The index range 1≤k≤r is exactly the interior range. For a matroid with a loop, pairing subsets I and I∪{loop} cancels the characteristic polynomial termwise, so all coefficients are zero and every inequality is 0≥0; rank-zero loopless matroid has polynomial 1 and no interior inequalities. For loopless positive rank the primary theorem applies directly. No normalization of the polynomial is being mistaken for the unreduced target. Definitions, primary Conjecture 1.1, Theorem 1.4, and selected Section 9 coefficient/Hodge passages were read; not the entire Hodge proof.

375776: Anagnostopoulou-Merkouri 2511.08705 Theorem 2 states R_ns(G)≤7 for all finite almost simple G. By the definition read immediately before it, all tuples of length R_ns are regular. If r≤7 and a 7-tuple is given, choose its first r components and conjugating elements with trivial intersection, then choose arbitrary conjugators on the remaining components; intersecting additional subgroups keeps the intersection trivial. This proves the literal 7-tuple assertion under the source's explicit core-free maximal/non-standard convention. Theorem 3 separates alternating, sporadic, classical and exceptional cases, and 2607.03307 reports this completed proof. The proof's many case bodies have not been exhaustively audited; no independent reproof or new result is claimed.

370025: the survey's Section 5 Theorem 5.1 and Conjecture 5.2 are followed immediately by Fanelli's resolutions of the first two sequences and a public plantri-based resolution of the third. The literal target matches those three sequences exactly. Do not present a future finite computation as a new discovery. Classification certificates and Fanelli's actual original body were not read, so record this as a public-resolution/source-certificate hold rather than independent certification of the nonexistence claim.

374931: actual source Conjecture 5.14 remains stated as a conjecture; its p^k q Theorem 5.12 is strictly narrower than p^x q^y. The raw record's references saying 'refuted' cannot be relied on. Extending the valuation argument requires control of both prime allocations across all three complementary divisor differences; no full proof or witness. Hold, not exclusion.

375754: source Conjecture 1.4 is the literal Ore-degree statement. Theorem 1.6 gives only 620/1987 rather than 1/4. The Chung et al. resolution cited later is h_2, not the Ore-degree conjecture. The graph H may omit edges present in G, so using an induced bipartite graph theorem is not justified. Full extremal inequality remains missing.

362447: source Conjecture 3.1 is the four modulo-192 progressions. The preceding modulo-24 result leaves an additional factor 8. A route via the eta-product generating function needs an actual 2-adic dissection or a proved modular certificate and coefficient-to-partition bridge. None supplied; no coefficient evaluation executed.

368934: source Conjecture 7.13 and following discussion explicitly distinguish the easy-to-transfer beta congruences from proving even one beta instance of (7.7). A beta-transfer theorem leaves the base 7-adic U_49 recurrence and all-alpha valuation missing, so it cannot settle the target. No constant x_alpha supplied.

368597: arbitrary d(n) across [3,n−3] and both w.h.p. implications are essential. Source Theorem 1.5 only establishes one implication in a restricted degree range; Section 7 identifies a missing slowly-growing matching-factor concentration estimate. The union operation must be the source's edge-disjoint random graph law, not an unconditioned multigraph union. A parallel-edge objection to another law would be a semantic error. No full contiguity route survives.

370653: source Conjecture 6.3 is exactly {1,3,n}∈Δex(K). The following proof assumes it to derive a barycentric-subdivision conjecture; it does not prove 6.3. Generic matrix-rank nonvanishing for every triangulated closed surface remains missing.

370960: source HTML contains severe mathematical/TeX conversion debris in the inspected passages. Translation-equivalence must be its actual interval relation, not order isomorphism. No faithful quotient-to-electrical-network bijection constructed. Hold source-definition/ordinary-proof gap; no claim of a reliable complete primary theorem read.

371705: source Section 7 Conjecture 7.1 matches the classification, while locally 2-arc-transitive/local primitive results impose extra assumptions. No reduction from arbitrary flag transitivity to those assumptions was established. Park full classification.

371802: source conjecture and surrounding Theorems 2–3 establish restricted subclasses. A global mean-curvature cancellation from vexillarity is still required; determinantal minimality alone is insufficient. Park all partial permutations.

363038: source Conjecture 1.2 is all normalized Schubert polynomials; its factorization results need a zero-one Grothendieck restriction. No proof that arbitrary w admits it. Park the missing all-permutation Lorentzian bridge; no conclusion from a familiar conjecture title alone.

363193: source Conjecture 5.2 identifies Corollary 4.3 (the raw record leaves that label incomplete) and the POP for {13452,23451}. Shape-Wilf arguments in preceding results do not yet give the missing equivalence with that POP. The actual full 13-set list/figure and citing proofs were not all inspected; hold source/constructive-bijection gaps.

363291: source Section 5 proves a unique dense shape, a ziggurat, but does not thereby furnish the all-n de Bruijn coloring needed for prismatic existence. Printed text/diagram encodings and later remarks were inspected, not all figures visually. The coloring-to-prismatic semantic bridge remains open here. This is a distinct target; no reuse of the protected r313 tiling endpoint is attempted.

## Read and novelty limits

All 20 full literal statements were read. All 20 source HTML bodies were retrieved, but retrieval is NOT proof review. The strongest routes and exclusion statements have the specific read scopes above; other records received selected statement/context review only. Source-read-inventory.json records these depths. The 270 exact historical allowlisted paths were processed by bounded term screening, excluding crown-vnumber paths and protected lanes. No exact-ID historical matches were found by the corrected recursive JSON-key/ID check. Broad words generated many irrelevant hits; historical-screen.json is machine screening evidence, not a claim of historical proof reading.

Pinned OpenAI revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb and catalogue were read for routing. Current public repository page reports 4eaee87548250b2682affda7d05d947c05554bae; LeanPool page reports 01db1d7049cf9668bda1e9e106875ee1278b43e6. Both LeanPool import index and projects.yml were fetched and text-screened. These are routing checks, not exhaustive proof-body clearance. No GitHub API, MathDB recent.json, Wiley, denied IEEE/SIAM routes, CiteSeer, ResearchGate or TLS bypass was requested. Search results incidentally listed some denied hosts; those listings were not followed or used as proof.

No exact full source-qualified new ordinary endpoint survived all gates. CANDIDATE.md is therefore intentionally absent, and no dormant Pi implementation is being recommended. If a route is later completed and qualified, root must separately authorize execution by Pi spark/GLM-5.3-Flash-EXL3, high thinking, with actual semantic endpoint, full bridges, allowed axioms only and extracted rebuild. No helper/proxy or proposed quadratic identity substitutes for the realization-count conjecture.
