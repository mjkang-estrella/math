# r212 — Karam's common-center ball-growth question remains unresolved

One precise attributed target was sustained. It is fresh to the bounded qualified original/alias screen, not certified new to all history or currently unresolved worldwide. Zero full nominations; no PROOF.md, Lean or manuscript. Root alone accepts/counts/stages; administrative snapshot counts are 9 additional / 39 total, next40.

## Actual source and chronology

Steve Karam, *Ball growth at all scales in universal covers of short metric graphs*, arXiv:2610.20088v1, Conjecture D, printed p4. Latest actual URLs https://arxiv.org/pdf/2610.20088 and https://arxiv.org/abs/2610.20088. Abstract history lists v1 only, submitted 14 October2026 12:27:42UTC. Identifier DOI alias10.48550/arXiv.2610.20088. PDF SHA256 0b4e91ccfec7a432190ee29320836d66682c0d7d0ed2647d764d6d56885aeee5. No journal version authenticated. Versioned URL aliases were screened but not separately retrieved. Retrieval clock is30 OctoberUTC, later than supplied environment date. http.jsonl contains exact retrieval UTC, URLs, headers, sizes and body hashes. All obtained scientific bodies were frozen into sources/ and frozen/ and hashes compared before extraction/reading; only frozen copies were extracted.

Literal quantifiers: for EVERY finite connected metric graph Γ (loops and multiple edges allowed), EVERY assignment of positive real edge lengths, EVERY integer first Betti number b=e−v+1≥2, and EVERY λ>0 with total length L≤3λ(b−1), there EXISTS ONE vertex u of the universal covering tree such that, for EVERY real R≥0,

    length B(u,R) ≥ V_λ(R),
    V_c(R)=3c(2^k−1)+3(R−kc)2^k, k=floor(R/c).

Ball length is one-dimensional Hausdorff measure; lifted metric is the source metric. Leaves, degree-two vertices, bridges, loops, multiple edges and arbitrary b are allowed. The center must be a graph vertex and must work simultaneously at all radii. Changing the center with R is insufficient. Edge lengths cannot be assumed individually≤λ. Cover vertices projecting to the same base vertex give equal ball lengths by deck transformations.

Read actual source definitions, Conjecture D, Theorems A/B, full Sections2–5 proofs and full Section7 including Example7.2. Surface application Section6 is outside this target and not independently audited. The source proves the weaker V_(3λ) bound; this is public, not a fresh slot. Theorem B's edgewise upper bound is stronger than the average-length premise and cannot simply be substituted.

## Closest actual classical proof and its full applicability limit

Seonhee Lim, *Minimal Volume Entropy on Graphs*, https://arxiv.org/pdf/math/0506216 and https://arxiv.org/abs/math/0506216, actual v1 submitted11 June2005 15:25:01UTC. PDF SHA256 b644bc946031abfd001cfd585e981068f27405bcd937f7b429b9088725450f12. Abstract gives Trans.AMS360(2008)5089–5100; journal body not separately authenticated/compared. Read graph/path/entropy definitions, path-growth argument Lemma1, Theorem4 and its positive eigenvector/path expansion proof, and full Theorem5 proof and regular specialization Corollary7. Graph-of-groups Section4 is not relied on. Other original Kapovich–Nagnibeda, Rivin and Sabourau bodies were not obtained; no assertion of exhaustive closest-body coverage.

The actual proof supplies an exact classical bridge to ENTROPY. Set A_h(e,f)=1_(e followed by f without immediate reversal) exp(−hℓ(f)). The positive eigenvector equation at spectral radius1 characterizes h. With y_e=exp(−hℓ(e))x_e, apply arithmetic-geometric mean to the deg(t(e))−1 successors, then multiply all oriented-edge inequalities. Each y_f cancels with its full multiplicity. For total length L this gives

    h L ≥ (1/2) sum_v deg(v) log(deg(v)−1).

For a cubic graph this is hL≥3(b−1)log2. Equality forces equal edge lengths, as the source's equality calculation shows. Thus if a cubic metric of mean edge length λ is not equilateral, h>log2/λ. Since log B_v(R)/R→h for every vertex and log V_λ(R)/R→log2/λ, all vertices dominate for all sufficiently large R (take a gap smaller than half the strict entropy difference, then maximize the finitely many root thresholds). This is a full eventual-radius bridge for each fixed nonequilateral cubic graph. It supplies neither an effective uniform threshold nor control of its compact initial-radius interval. In the equilateral case B_v=V_λ exactly at every R. No full classical exclusion of Conjecture D is claimed.

## Sustained full-scope route: an exact positive-part expansion

For any core metric graph with degree≥3, let W_n(v) be the oriented n-edge walks starting at v without immediate reversal; loops have two inverse orientations, which are distinct. Let ℓ(w) be the sum of edge lengths. The universal tree has one lifted endpoint for each such walk, and radial degree increases by deg(end(w))−2 at that endpoint. Integrating this radial point count gives exactly

    B_v(R)=deg(v)R + sum_(n≥1) sum_(w∈W_n(v))
                  (deg(end(w))−2)(R−ℓ(w))_+ .                 (1)

Every sum is locally finite since the finite graph has positive minimum edge length. Formula(1) follows also by subdividing the radius interval at all lifted vertex distances: both sides vanish at0, have the same initial slope deg(v), and have the same slope jump at each distance, with multiplicities included. This covers bridges, repeated traversals, parallel edges and loops; it does not enumerate only simple paths.

For cubic Γ with mean unoriented edge length c=L/e, every root has 3·2^(n−1) n-walks. If the root is uniform and each next non-reversing edge is uniform among two choices, every oriented edge at every position is uniform. Initial edges are uniform since all degrees equal3; stationarity follows because every oriented edge has exactly two predecessors and successors. Consequently the mean ℓ(w) over all roots and n-walks is nc. Convexity of x↦(R−x)_+ gives

    (1/|V|) sum_v B_v(R)
       ≥ 3R + sum_(n≥1) 3·2^(n−1)(R−nc)_+ = V_c(R).        (2)

The final equality is checked on intervals [kc,(k+1)c]: initial slope3, slope doubling at each positive multiple of c, and value0 at0. For every finite R one may sum Jensen through floor(R/minℓ); beyond that all LHS terms vanish, and since minℓ≤c all RHS terms vanish too. Thus(2) is a full proof, not an inference from the finite checks. It proves a good vertex exists for EACH radius. For vertex-transitive weighted cubic graphs (automorphisms preserving lengths), all B_v coincide, so it proves a single center works for all R. In particular EVERY positive-length theta graph satisfies the full inequality at c=(x+y+z)/3: exchanging its two vertices preserves all three lengths. This is a routine consequence of the complete averaging bridge just exhibited, not a separate fresh nomination; Example7.2's special equality is reproduced by the checker.

## Reduction to cubic graphs and exact missing lemma

It suffices to prove the common-center statement for all finite connected cubic metric multigraphs. Indeed prune degree-one edges and smooth degree-two vertices in an arbitrary graph. This preserves b, reduces L and leaves a nonempty branch core. Its universal cover embeds isometrically in the original cover, so its ball lower bound transfers. Replace each degree-d≥4 branch vertex by a finite trivalent tree with d external half-edges, giving every added internal edge length ε>0 and retaining old edge lengths. The graph stays connected and b is unchanged; all vertices are now cubic. Its mean edge length is c_ε=(L_core+Mε)/(3(b−1)), tending to c_0≤λ. A cubic common-center theorem gives one vertex type per ε. Along a sequence ε→0, choose a subsequence with a fixed type; it collapses to an ORIGINAL branch vertex. Ball lengths converge at every fixed R to that vertex's core ball length: within bounded radius only boundedly many original positive-length edges can be crossed; internal replacement trees have no cycles and only finitely many routing paths between external half-edges. Hence there is a finite uniform list of relevant old-edge itineraries, their lengths converge, and added-edge contributions vanish. The same subsequence works at every rational R; continuity extends the bound to all real R. Since c↦V_c(R) is nonincreasing (actual source Corollary3.1), B_v≥V_(c_0)≥V_λ. This also handles degree-two source subdivisions without selecting an interior nonvertex center.

For a cubic graph with N vertices and c=L/e, define G(R)={v:B_v(R)≥V_c(R)}. The exact missing universal lemma is:

    For EVERY finite connected cubic metric multigraph, EVERY positive
    edge-length assignment, and EVERY N-tuple R_1,...,R_N≥0,
                 intersection_(j=1..N) G(R_j) is nonempty.    [UNPROVED]

This finite-tuple property is equivalent to a common good vertex at ALL radii for that graph: if none works globally, for each of its N vertices choose one radius where it fails; these N radii have empty intersection. The other implication is immediate. Thus the lemma, together with the above cubic reduction, would prove the FULL source question. It retains unbounded graph size, arbitrary positive real lengths, arbitrary radii and the same center. Equation(2) proves only each G(R) is nonempty, not their intersection. No nesting, Helly property or common minimizer for this family has been proved. A plausible route is a non-backtracking renewal comparison with a vertex potential yielding the finite-intersection property; Lim's multiplicative eigenvector bound does not provide it.

The stronger claim that EVERY vertex is good is false, exactly: use the dumbbell multigraph with loop length4 at vertex0, loop length6 at vertex1, and joining edge length4. It is cubic, b=2,L=14,c=14/3. At vertex1 and R=6, formula(1) gives 3·6+(6−4)=20: only the endpoint across the joining edge is reached strictly before6. But V_(14/3)(6)=14+6(6−14/3)=22. Vertex0 instead has B_0(6)=18+3·2=24. This is a geometric proof of failure of an all-vertices strengthening, not a source counterexample. It pinpoints the selection issue rather than excluding the target.

## Bounded controls, objections and disposition

checks.py uses exact integer walk-distance dynamic programming and rational volume arithmetic; no numerical integration. It checks697 seeded connected cubic multigraph metrics with2,4,6,8,10,12 vertices at24,062 radii through6c. All path distances and model breakpoints in that bounded interval are included, so piecewise linearity certifies the interval for those graphs only. Some root works throughout each tested interval;2,048 individual roots fail somewhere. Sixty-one independent theta branch-recurrence comparisons and the source's special theta equality pass. No sampled graph result proves existence on all radii, unbounded graphs or arbitrary real lengths. Seed generation is not exhaustive. No counterexample to Conjecture D was found.

Strongest substantive objection: average domination is compatible with radius-dependent good roots; a common-center argument is missing. Strongest novelty objection: the source is recent, the older entropy/graph-growth literature may contain an applicable stronger result, and the averaging/positive-part ingredients themselves are classical and routine. No theorem is excluded merely because its proof is short. No credit is requested for the theta consequence, asymptotic consequence, path identity, counterexample to the stronger all-root statement, finite checker or reduction.

Qualified index refreshed1,560 original paths (11 new/changed relative to r209);2,576 inherited reference aliases remain separate. Actual r111–113 reports retained. r207/r208 original-index union added no paths. r208 alias schema mismatch was preserved and its attempted union stopped; r209's inherited aliases remain the bounded alias corpus. Changed reports include r210/r211 work and their later root handbacks, read and frozen. Exact arXiv/DOI/full-title/author/entropy aliases have zero hits; broad 'Conjecture D' and 'all-scale' searches have unrelated hits, preserved in target-screen.json. This is a bounded screen, not all-history clearance. Byte-equal aliases were not promoted and histories were not recursively copied.

Current arXiv title/author/conjecture searches were frozen. Title search found the target and an unrelated paper; exact author/conjecture phrase search returns no results and is intrinsically weak since arXiv search does not search full text. Earlier broad searches mostly returned already-public resolutions, not fresh slots. No complete current public proof-registry head/tree/body was authenticated: inherited GitHub API/raw/codeload/diff/patch denials respected. No ScienceDirect, Google challenge, denied SIAM URL, neilsloane doc route or parked historical reconstruction was attempted. Subscription literature and journal-version bodies remain gaps. Current bounded searches cannot clear all history or certify worldwide priority/unresolvedness.

Administrative NEXT/ledger/context are snapshots only and never live scientific bindings. Workflow deviations and failed alias union remain preserved. Final separate guarded verifier checks scientific originals/copies and hashes, assigned/guard bindings, immutable historical references, exact extraction and checker replay, and the complete file manifest. manifest.json explicitly excludes itself and verification-receipt.json. Only the receipt is written afterward. No shared/git/count/MathDB/public edits, browser, external messages, uploads, children, Lean or manuscript.
