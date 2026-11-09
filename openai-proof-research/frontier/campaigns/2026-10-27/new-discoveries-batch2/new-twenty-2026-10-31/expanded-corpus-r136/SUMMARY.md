# Expanded corpus r136 — research handback

No new full-scope solution or Lean endpoint survived. All 20 reserved IDs have individual, ID-keyed entries in `results.json`; every entry has zero discovery credit and requires root acceptance. Nothing is self-accepted. This is a bounded research pass, not a worldwide novelty clearance or a proof of the parked conjectures.

The source records were extracted byte-for-byte with their terminating newline, one-based chunk line, chunk SHA-256 and raw SHA-256. `outputs/provenance.json` and `raw/` preserve them; `results.json` also hashes each literal statement. All 20 current arXiv landing pages and PDFs were obtained with dated URL/status/hash receipts. Older versions were also retained for the six papers with multiple listed versions. `outputs/source-passages.json` records targeted passages; targeted reading must not be confused with reading every proof.

## Important dispositions

* **329391, full Heffter arrays:** publicly resolved by Archdeacon–Boothby–Dinitz, [1509.00430](https://arxiv.org/abs/1509.00430). I read the construction report's definitions and final complete case table, which includes the integer and shiftable refinements. No nomination.
* **358313 and 375387, Menger variants:** already refuted. The current v5 source for 358313 explicitly says so. Nguyen–Scott–Seymour's primary [counterexample paper](https://web.math.princeton.edu/~pds/papers/coarsemenger/paper.pdf), Theorem 1.3 and construction, supplies a family for every ball radius at k = d = 3. This is not a new finite witness, and it does not settle the separate distance-two question.
* **364491, nilprogressions:** the source itself labels Section 2 “Proof of Conjecture 1.2,” contrary to the corpus's no-resolution prose. It omits the Hales–Jewett adaptation; the proposed independent-coordinate construction also has a questionable free-word injection because different coordinates commute. I record a source-reported resolution with an unverified gap, not a certified theorem or a new correction.
* **361237, near-Eulerian precoloring:** a historical source scan located a public [reviewed counterexample](https://raw.githubusercontent.com/graph-theory-AI/Graph-Theory-LLM-Proofs/96f91048c5282ac2b8bed0b7e8dc454cf38ba636/verification/2312.13061__01.md). I read the full report. Its arbitrary-d family uses an extra unselected long face; the report repairs the original author's mistaken viability definition with an actual triangular-grid witness, and calls the result a formulation loophole. It is both public prior work and unsuitable for fresh campaign credit. I did not independently replay its large grid construction.
* **353155, directed total distance:** a late-discovered alias repeats **342014**, already parked in r34. On finding the alias, I stopped the route and canceled its active order-eight shard. New computations remain supplemental evidence, not a new nomination.
* **330299, cycle saturation:** source authors report t = 8; [Khan2609.33035](https://arxiv.org/abs/2609.33035) claims t = 9, with finite computations in two structural cases. I read its theorem and final proof assembly but did not replay its ancillary computations. A new counterexample route must therefore concentrate on t >= 10.

## Finite investigations

### 358702 — safe colorings, the strongest remaining finite route

The source's bad conditions use inclusive cyclic-arc color intersections. Its proved good-coloring class is a sufficient subclass and equals the nonbad class at k = 5, but not at k = 6. Searching only that proved class would add nothing, so the experiments isolate **nonbad, nongood six-color boundary patterns**.

`scripts/safe.py` enumerates restricted-growth proper cycle colorings, a complete quotient by color relabeling (not by dihedral symmetry), through length 11. It finds respectively 1, 0, 2 and 11 nongood/nonbad patterns at lengths 8, 9, 10 and 11. All 392 sampled extension tests passed. There are none at smaller lengths in that range.

`scripts/safe-extended.py` then completely enumerates boundary patterns using at most five colors:

| Boundary length | Patterns enumerated | Nonbad/nongood | Disk extension tests | Failures |
| --- | ---: | ---: | ---: | ---: |
| 12 | 140152 | 36 | 2160 | 0 |
| 13 | 559923 | 91 | 5460 | 0 |

Each selected pattern was tested on disks with 2, 4, 8, 12, 20 and 30 interior vertices, ten generated disks per order. Disks start with a wheel, receive triangular-face insertions, then random valid internal diagonal flips; boundary chords are prohibited. Extension is decided by an exact minimum-remaining-values coloring backtrack. Repeated generated disks are possible: these are test counts, not counts of distinct isomorphism classes. The source reports no finite computational verification range to surpass; these lengths target its unproved class directly.

No counterexample was found. The remaining gap is extension in **all** planar disks, not one more successful sample. A new generator should search critical interior list obstructions rather than rely on wheel-based random walks. A surviving finite witness could have feasible Lean cost, but would still require literal planarity/embedding, all bad-condition checks and nonextension semantics.

### 331351 — adjacent faces in unique three-colorings

`scripts/planar.py` filters every graph in the NetworkX graph atlas through order seven for minimum degree at least three and vertex connectivity at least three. This leaves 157 graphs: 113 nonplanar and 44 planar, all of which already have an adjacent (3,k) pair with k <= 4.

The second stage generates 80 graphs at each of orders 8, 10, 12, 15, 20, 25 and 30, flips triangulation edges and deletes edges while preserving three-connectivity. There were 9372 accepted deletions and 560 terminal tests. Of these 9932 tests, only six avoided the desired small-face pair, and none had a unique proper three-coloring. This exposes a weakness of the generator: almost all samples are rejected before the coloring test. It is not exhaustive larger-order coverage. The source's k <= 5 discharging proof does not by itself strengthen to k <= 4 from three-connectivity.

### 330299 — cycle saturation beyond the printed verified cases

`scripts/cycles.py` uses the source's exact Observation 2.1: an edge's endpoints have no t-vertex path and a nonedge's endpoints exactly one. It checks 206 generalized Petersen parameter triples with outer-cycle size p = 5 through 18, 1 <= k < p/2, and t in {10,11,12} with t <= 2p. Every instance fails; the first failed pair and capped path count are retained. This family is only a diagnostic; there is no circulant-family nomination and no claim of exhaustive graph coverage. The source's reduction to two-connected graphs explains why tree sweeps would be uninformative.

### 332408 — Dyck chains: necessary diagnostics only

Using the exact I-sum seed formula, cell arm/leg definition of dinv, nu and rho, `scripts/dyck.py` checks **every integer partition lambda of sizes 1 through 24** and every forced R iterate. No seed-deficit or iterate-deficit anomaly appears. This extends necessary seed checks well beyond the individual lambda shapes listed in the 2016 source, but it does **not** establish any infinite chain decomposition, valley property, simultaneous size coverage or n-oppositeness. Modern local/tail-chain papers already have substantial computational coverage. These diagnostics are not new mathematics or a Lean endpoint. A useful next experiment would require a complete finite inconsistent subsystem for the two opposite chains, not these local invariants.

### 353155 — retained supplemental computation, route stopped

Before finding historical alias 342014, `scripts/digraph.py` made 375000 single-arc proposals across 15 pairs (n,r), with n from 6 to 12 and r from 3 to 5, seeded by the source family. It found no lower value or equality state with an anomalous degree signature. This signature test alone is not an isomorphism proof.

The exact small-order searches do perform exact isomorphism tests. For outradius three, each vertex has outdegree at most n - 3, and

`W >= 2*n*(n-1) - m + n`,

because every row has a vertex at distance at least three. The source value is `W = n*n + 3*n - 4`, so a possible improvement/equality must have at least `(n-2)^2` arcs. Some vertex consequently has outdegree n - 3, and can be labeled zero with prescribed neighbors. The total deficit from degree n - 3 is at most n - 4. This gives complete finite searches within the threshold, not searches over all unrestricted adjacency matrices.

* n = 6: 1850000 normalized matrices checked; 24 qualifying labelings, all W = 50 and all isomorphic to the source construction.
* n = 7: 887627 complete matrices after safe two-neighborhood pruning; 96 qualifying labelings, all W = 66 and all isomorphic to the source construction.
* n = 8: CPU-capped before completion. A subsequent first-row shard was canceled when the r34 alias was discovered. No complete order-eight count is claimed.

These bounded computations are unformalized diagnostics. The general conjecture remains unresolved here and the historical stop applies.

## Other dispositions and quantifier checks

The other entries contain source-backed hard-gap dispositions. In particular:

* 327064 concerns an **online low/high game**, not signed vertex labels, and asserts an eventual threshold for each fixed number of internal vertices.
* 329121 is the full big-line-big-clique threshold conjecture; Bonnet's 2026 (6,4) claim is only a parameter case. A fixed point set cannot refute an unspecified threshold.
* 367965 requires color-permutation-invariant sets C. Dropping that source hypothesis would produce a worthless trivial “proof.”
* 368487 contains classical Erdos-Hajnal as its two-color special case; 354794 is explicitly equivalent to Gyarfas-Sumner. Finite sweeps do not resolve either unspecified bound.
* 372277 asks for **some absolute additive list bound**, not the smaller degree-plus-two conjecture. A small fixed-k failure cannot refute it.
* 373316 is a quantitative inverse theorem uniform over tensor dimension, despite the reservation's finite-discrete filter.
* 360696 asks for uniform treewidth bounds; a fixed finite graph cannot refute cleanliness.
* 330678 requires **cyclic** push-to-the-top codes. The source's existing S7 code is not a new proof of the stronger conjecture. No near-spanning S7 nonexistence computation is claimed.
* 354066 still needs coefficientwise Matching-Jack positivity/statistic existence. Source integrality and positive marginal sums do not imply it. No symbolic Jack computation is claimed.

Thus this reservation contains many threshold or famous structural problems despite its reserve6 metadata. No candidate is promoted merely because it is labeled open or has no MathDB solution.

## Prior work, versions and trust limits

Read the three required AGENTS files, both campaign ledgers and prior campaign context; the brief's inherited credited/excluded family restrictions remain in force. Initial exact-ID/title scans found no substantive reserved-ID review; a later source/alias scan found r34's 342014. Same-paper r67 and r89 entries concern different conjectures and were retained as context. The historical scans are bounded prose/results/ledger scans, not complete semantic campaign coverage.

Live GitHub `/commits/HEAD` checks on 2026-11-03 found:

* OpenAI/math: `4eaee87548250b2682affda7d05d947c05554bae`.
* Omega/trureturing: `0351ade966a10f692cac8478dcc33851b8e36231`.
* Graph-Theory-LLM-Proofs: `96f91048c5282ac2b8bed0b7e8dc454cf38ba636`.

Complete nontruncated Omega D5 and Problems trees were fetched at the observed head. Filename/ID/source screening is not exhaustive proof-body review. No worldwide novelty or all-registry-proof clearance is claimed. Primary bodies, version pages, receipts and public review provenance are retained in `sources/`; modern literature gaps are explicit in the results.

No author contact, browser tab, git operation, publication or shared-ledger edit was made. All artifacts are lane-local. NetworkX 3.4.2 was downloaded as a hash-bound source ZIP and imported from a lane-local extracted directory; no package was installed globally and no pip was used.

## Resource and formal status

Every Python/numerical invocation used `scripts/capped.sh`: two-CPU taskset affinity, CPU 120 seconds, wall timeout 140 seconds, MALLOC_ARENA_MAX=2, and an aggregate process-group RSS watchdog killing above 6 GiB. The watchdog samples, so this is not a transient-peak or cgroup guarantee. One initial overly broad historical rg capture reached the watchdog threshold and was killed (receipt retained); subsequent history scans stream and bound displayed lines. The order-eight search reached the CPU cap; its shard was explicitly canceled on the alias discovery. Other experiments were small. No heavy processes overlapped.

**No Lean or leanchecker was invoked**, since no genuine full-scope ordinary proof survived. There is no dummy bounded Lean theorem, no source-independent surrogate, and no claimed kernel certificate. The pinned Lean/mathlib dependencies were not modified. No background numerical job remains at handback.

Reproduction commands are `scripts/capped.sh NAME python3 scripts/NAME.py ...`, run from this lane; read each script's arguments. Full outputs and resource receipts are in `logs/`, structured coverage in `outputs/`, and SHA-256 bindings in `manifest.json`. Do not rerun the deliberately retained broad `research.py history` failure as a preferred history method.
