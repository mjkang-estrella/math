# I257 — Independent rooted-packing correctness gate

Date: 2026-10-12. **Verdict: PASS.** The exact rank-transfer theorem is mathematically correct under its stated hypotheses. The bounded-component extension also follows with the exact Aharoni–Haxell condition. No required repair or unresolved correctness objection remains.

Candidate: I248, `frontier/experiments/i248_combinatorial_structure_discovery/analytic-attempt.md`, all 167 lines read, SHA256 `47a0fa44fdc57a1c2009da17f14a6dab8aa6d05fec63d49e55f013d49487886b`. This gate reconstructs the unchanged proof independently and does not rely on author confidence or interrupted I254 observations. I254's unfinished files were preserved without reading them. No other live review was read.

## Exact result approved by this gate

Fix d≥2. For n≥N_d, integer 1≤s≤10 log n, and 0<r<1 satisfying r^(ds+binom(d,2))≥n^(−1/100), set p=1−(1−r)^(128d). There are deterministic typical classes D under G(n,r) and E under G(n,p), with errors tending to zero uniformly in r,s, such that for every G∈D, H∈E, Y⊆[n] with |Y|≤n^(2/3), and family R of d-slot edge-presence patterns with at most s prescribed root neighbors per slot,

    ν_R(H;Y) ≥ min{2d ν_R(G;Y), floor((n−|Y|)/(16d²))}.

The quantifiers cover the full Cartesian product D×E and pattern families chosen after observing either or both hosts. Root-neighborhood overlap and repetition are unrestricted. Nonedge constraints, nonroot candidate lists, growing d, and a spanning conclusion are excluded. D and E may depend on the parameters; uniform errors do not mean one event for all real r.

## Proof reconstruction and objections

The complete independent reconstruction is [analysis.md](../experiments/i257_rooted_packing_proof/analysis.md). It verifies the following chain rather than assuming the author's conclusion.

1. Compression operates on distinct slot-root incidences and internal slot pairs, with support size b=ds+binom(d,2). Its direct argument includes empty supports. Closing R before compression and Q afterward preserves unordered subordination and bounds |Q| by d!ceil(2r^(−b)).
2. Every source R-packing has smoothed weight at least half its size. For the maximum weighted disjoint packing, max of conditional expectations is bounded above by conditional expectation of the ordinary packing rank after global addition. The direction is correct and no block-indicator independence is assumed.
3. Resampling a nonroot incident-edge coordinate block changes only d-sets containing that vertex. Deleting the one affected term from an optimum proves oscillation at most one for both weighted and ordinary packing. Product-block concentration is therefore valid. Every nonempty test has mean μ_Q≥n^.99/(4d), and all small root sets and compressed families cost only exp(O_d(n^(2/3)log n+n^.01(log n)²)) tests.
4. Uniform random selection among a random host's maximum packings is invariant. Conditional on cardinality it is uniform on all d-matchings by group transitivity. This is not a claim about a fixed host. Independent layer size-success events factor, preserving independence; uniform trimming then yields independent uniform q-matchings even after success conditioning.
5. In the filtration of processed trimmed matchings, the next matching remains independent of the occupied nonroot set B. A prefix-preserving transposition couples permutation completions and changes at most two avoidance indicators. The resulting martingale tail bound is exp(−c q²/N), uniformly over the random past.
6. With q=floor(min{μ_Q/2,a}) and a=floor(N/(16d²)), all floor losses are paid by μ_Q≥6 and a≥2. If μ_Q/2≤a then q≥μ_Q/3 and 64d successful layers supply more than 8dμ_Q unless stopped at a. If μ_Q/2>a then q=a and two successful layers reach a. The union law is exactly G(n,p).
7. Failure of the deterministic union-host test implies failure of every auxiliary witness, so the joint witness error bounds the marginal host error. Union bounds establish E for all tests. The separate source and target inequalities imply the Cartesian product claim, including adaptive R.

The reconstruction supplies an explicit common error of the form

    (1+128d) exp(K_d[n^(2/3)log n+n^.01(log n)²]−c_d n^.98),
    c_d=1/(262144d^4),

capped at one, after a cutoff depending only on d. It also checks empty families, edge-free patterns, s>|Y|, repeated types, and saturation at the cap.

The application pads each component of J−Y with isolated placeholders. Total padded support is at most d|W|≤n/(1000d²), so fillers fit. The target compatibility hypergraphs are d-uniform on the common nonroot set. For every nonempty index set I the source provides |I| disjoint blocks, and a≥2d|W| for large n, hence their target union has matching number at least 2d|I|>d(|I|−1). This is exactly the sufficient Aharoni–Haxell hypothesis reproduced as FLN Theorem 2.6. Choosing representative blocks and discarding fillers gives the embedding fixing Y. Repeated hypergraphs are legitimate indexed demands. There are no root-root obligations. This application is not a second nomination.

Optional exposition improvements are to write out product conditioning, the permutation-completion coupling, the marginal host-failure inclusion, and the padding inequality. They are already justified by the submitted hypotheses and argument; none is a mathematical repair required for PASS.

## Primary comparison and precise read limits

The pinned graph-decomposition manuscript was independently retrieved at the stipulated commit, authenticated against the preprints-tree Git blob, and read in full: `main.tex`, lines 1–841, including `lem:compression`, `prop:transfer`, direct embedding proofs, and final assembly. The source transfer is scalar one-vertex Hall. Its separate maximum-degree embedding operation does not join internal block edges to a fixed-root rank comparison. The companion `consequences.tex` was independently retrieved, authenticated, and read in full, lines 1–50; its two-union cover does not supply this packing operation. No pinned result's truth was audited.

[Ferber–Luh–Nguyen v3](https://arxiv.org/abs/1606.05923v3) was independently retrieved and authenticated. Read all §§1–2.3 and every argument of §2.4, including both complete embedding/matching lemma proofs and Theorem 2.6. This is substantive prior art for compatible-block hypergraphs, independent sprinkling, and hypergraph Hall. Their distance-three batch separation gives disjoint root neighborhoods across different blocks; the Janson δ_2 calculation uses that separation. I248's unrestricted overlapping-root setting is instead handled by its weighted-packing and exchangeable-layer proof. Whether this distinction is substantial is not decided here.

The original [Aharoni–Haxell publisher PDF](https://onlinelibrary.wiley.com/doi/pdf/10.1002/1097-0118%28200010%2935%3A2%3C83%3A%3AAID-JGT2%3E3.0.CO%3B2-V) and download link redirected to the abstract page. The original topological proof was not obtained or read; the exact criterion is verified from the fully read primary FLN application. No original Riordan proof was read or used. FLN §3 was incidentally partly displayed during extraction-boundary diagnostics, not systematically read or relied on. Other pinned companion arguments mentioned in the discovery history were not read in this gate and are not proof inputs.

The [withdrawn 2609.20864v2 record](https://arxiv.org/abs/2609.20864v2) was read as an overlap lead only. Its v1 argument was not read and is not a trusted theorem. No MathDB prominence search or score was undertaken. Full provenance and read extents are in [literature.md](../sources/i257_rooted_packing_proof/literature.md) and [reading-and-failures.md](../experiments/i257_rooted_packing_proof/reading-and-failures.md).

## Disposition and artifacts

Mathematical correctness: **PASS**. Required repairs: **none**. Unresolved correctness objections: **none**. Contribution/substantiality: **not adjudicated**. Acceptance/count: **unchanged; twenty targeted, ten accepted**.

Authored files are this review, `frontier/experiments/i257_rooted_packing_proof/{analysis.md,reading-and-failures.md,input-authentication.json}`, and `frontier/sources/i257_rooted_packing_proof/literature.md`. Fully read primary excerpts are retained only in the latter source directory. [Input authentication](../experiments/i257_rooted_packing_proof/input-authentication.json) records exact input bytes, independently retrieved source hashes, and hashes for the other authored outputs and all retained excerpts. Its own SHA256 is detached in the final response to avoid self-reference. No shared files, counts, indexes, staging, commits, publication, research code, tests, numerical experiments, snapshots, or communications were changed or initiated.
