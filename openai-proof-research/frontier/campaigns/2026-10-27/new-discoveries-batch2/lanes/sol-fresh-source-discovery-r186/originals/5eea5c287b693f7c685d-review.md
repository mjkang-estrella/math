# Independent review of the signed-diagonal C57 certificate

Date: 2026-10-29. Verdict: **PASS as a complete exact computer-assisted mathematical proof of the scoped containment assertion.** No mathematical/checker defect found. This is not a kernel certificate, a noncomputational all-cases geometric proof, a novelty/source clearance, or an acceptance recommendation. Credit 0; counts remain 5/30 additional, 35/60 total. Root owns acceptance. No formal-worker files or running formalization were inspected, polled, or changed.

## Scope and independent work

The audited endpoint is: for every finite edge-connected subset P of Z² with exactly 11 cells, some integer translation places P inside C = {|x|+|y| ≤ 5} minus {(±2,±2)}. Holes in P are allowed, and orientations are fixed. This gives the same candidate upper bound a(11) ≤ 57, not optimality, first failure, a broader construction law, or additional credit.

I read the repository and campaign AGENTS.md, ledger.json, NEXT.md, candidate discovery.md, SUMMARY.md, provenance.json, supplied Python checker, domain construction, generator implementations and supporting preliminary review. All 58 entries in candidate provenance.json matched SHA256 and byte length before copying to input-copy/. Every required binary table was decompressed and checked on this copy. The original and copied 58 files were rehashed afterward; hash-before.json and hash-after.json record them. The unlisted provenance.json itself was also copied and separately hashed. Nothing in the candidate was edited. No supplied checker or generator was executed. The root replay and earlier exhaustive review are not premises of my checker verdict.

My independent_check.py reconstructs vertices and centers directly as parity-constrained integer signed-diagonal pairs. It reconstructs collision groups, inclusion pruning, undirected edges and both lexicographic file orders. It also cross-checks the supplied group metadata against these reconstructions, but that metadata is not an input to the proof checks. The independent inequality checker widens bytes to signed int16, transposes the matrix, builds common group intersections by mask recurrence for base cases, checks absolute edge differences, and enumerates disjoint pairs by fixing one mask and traversing its complement. The supplied checker instead uses per-vertex cover submasks, directed edges, and partitions of a union mask. This is a fresh exhaustive local verifier, not a replay or a comparison of solver outputs.

The run verified 31 tables, 1,874,144 bytes/entries and 238,227 gzip bytes. Counts: 1,018 base inequalities, 2,781,200 undirected edge inequalities (each absolute-value check establishes both directions), and 184,239,622 disjoint-merge inequalities, each unordered mask pair once per vertex. All nonempty-mask entries lie in [1,12]; every full-mask entry is exactly 12. Row zero is also range checked but has no mathematical role. independent-evidence.json records every domain and raw-table SHA256.

## Mathematical reduction

For u=x+y, v=x−y, the integer lattice is exactly u≡v (mod 2), with inverse ((u+v)/2,(u−v)/2). Edges have |Δu|=|Δv|=1 and max(|u|,|v|)=|x|+|y|. For an 11-cell connected set, each signed span is at most 10: a simple path between extrema has at most 10 edges. Both spans are positive because an edge changes both coordinates. No acyclicity or absence of holes is assumed.

Reflection y↦−y swaps spans. After arranging a≥b, write U=min u, V=min v and choose e≡V−U (mod 2) with e∈{0,1}. Required signed translation is (−U,e−V); its components have equal parity, so its inverse Cartesian translation is integral. All 1,681 extrema pairs in [−20,20]² were additionally tested as elementary arithmetic diagnostics, including negative minima. The proof is the displayed parity identity, not that bounded test.

For e=1 and odd a, (u,v)↦(a−u,v−1) maps the entire parity box to e=0. In Cartesian coordinates its linear part is (x,y)↦(−y,−x), and its translation ((a−1)/2,(a+1)/2) is integral. If instead b is odd, (u,v)↦(u,b+1−v) has linear part (x,y)↦(y,x) and integral translation ((b+1)/2,−(b+1)/2). Both are affine D4 maps preserving grid adjacency. The script checks these complete box maps and edges for all 110 nominal triples. Keeping both even/even parities and only e=0 otherwise leaves 70 domains. These maps need not be distinct orbit representatives: coverage is what matters.

C is invariant under D4 (rotation and reflection generators verified on all 57 cells). If normalized Q=gP+d satisfies Q−c⊂C, then P+g⁻¹(d−c)⊂g⁻¹C=C. Thus D4 only reduces the analysis; the resulting placement of the original P is a translation. There is no illicit rotation of a piece at placement time.

For a set with the stated four exact extrema, every radius-5 diamond center has a−5≤s≤5, e+b−5≤t≤e+5 and s≡t (mod 2), and conversely every such center contains its whole bounding box in that diamond. The four forbidden offsets are precisely (±4,0),(0,±4). Therefore failure of every placement is equivalent to hitting each collision group, together with four extrema groups. This implication and its converse are exact; no center is omitted on a boundary. Keeping inclusion-minimal distinct groups preserves the hitting property: each deleted group contains a retained group. My program explicitly checks this domination for every original group, including empty groups.

An empty collision group makes failure impossible; it is not an empty center list. The only retained domain with no centers is (10,10,1); its graph has 60 vertices and four remaining boundary groups. Its table has 960 entries and proves a lower bound 12. In that domain there really is no diamond placement, so this cardinality obstruction is necessary. It is correctly included rather than discarded vacuously.

## Forced-cell cases

The independently reconstructed singleton groups give:

| Domain | Forced vertices | Supersets of size at most 11 | Connected supersets | Hitting supersets |
|---|---:|---:|---:|---:|
| (7,3,0) | 16 | 0 | 0 | 0 |
| (7,4,0) | 10 | 11 | 0 | 0 |
| (8,3,0) | 10 | 9 | 0 | 0 |
| (8,4,0) | 8 | 576 | 3 | 0 |

These are complete supersets of the forced set, including the forced set itself when its size is ≤11. The 576 count is 1+15+105+455. All three connected sets in the last case miss retained groups; they cannot simply be called disconnected. Total 596 checks. The 35 empty-group domains, these four cases, and the 31 tables partition all 70 domains.

## Generic potential theorem: ordinary proof

Here is a precise proof of sufficiency of the three inequalities, independent of the generator recurrence. Work in any finite undirected graph. Let M be a nonempty finite set of group labels, and let T be a finite nonempty connected vertex set rooted at z, hitting every group in M. Choose a spanning tree on T. For each label i∈M choose exactly one witness vertex wᵢ∈T in its group. This is possible even if group memberships overlap: a vertex may receive many labels, but each label is assigned once.

Orient the tree away from z. For each vertex v let Mᵥ be the labels assigned in its descendant subtree. Ignore subtrees with Mᵥ empty. Define Kᵥ, whenever Mᵥ is nonempty, as v together with the paths inside its subtree from v to its assigned witnesses. Claim L(Mᵥ,v)≤|Kᵥ|. Prove this by induction upward.

If v itself is assigned a nonempty label set A, the base inequality gives L(A,v)≤1 and initializes the construction at {v}. Each relevant child w has nonempty M_w and by induction L(M_w,w)≤|K_w|. The edge inequality gives L(M_w,v)≤|K_w|+1, the size of K_w∪{v}. If there were no initial labels at v, initialize with the first such child bound instead. There must be a first child if Mᵥ is nonempty but v carries no label. Every further child, or a child after initial root labels, contributes a disjoint nonempty label mask. Apply the merge inequality, subtracting one for the common vertex v. Different child subtrees are disjoint, and all these rooted sets intersect exactly at v, so repeated merges give exactly |Kᵥ| as the resulting bound. A labeled leaf is covered by base; an unlabeled root with one relevant child is covered by edge; an unlabeled vertex with several children initializes from one child and then merges. The case of no assigned labels anywhere is excluded by M nonempty, so no L(∅,v) assumption is needed.

At the original root M_z=M and K_z⊆T. Hence L(M,z)≤|T|. Overlapping *memberships* do not create overlapping *assigned label masks*. No monotonicity in masks, optimizer correctness, empty-mask rule, or disjointness of the groups themselves is needed. All-group lower bound 12 contradicts |T|≤11.

As an additional diagnostic, tree_edge_checks.py exhausts every triple of nonempty labeled group memberships on each four-vertex tree shape (path/claw): 6,750 systems, 6,630 with overlapping memberships. Exact potentials were constructed by brute force over the at-most-15 nonempty vertex subsets, and all base/edge/merge inequalities checked. The explicit inductive bound was tested on 92,992 rooted hitting subtrees, including 31,406 empty-root-assignment cases. This finite diagnostic supports implementation of the induction; the preceding argument, not tiny-model enumeration, proves the generic theorem.

## Arithmetic and binary interface

The used Python generator has uint8 distances initialized to 0,1,99. Floyd updates add values ≤99, thus ≤198, before taking a minimum ≤99. Positive table values stay in [1,12]; merges add at most 24 then subtract 1, with minimum sum 2, so neither overflow nor underflow occurs. Distance extension adds ≤111. The supplied verifier first checks [1,12], then computes ≤13 on edges and sums ≤24 before subtracting one on merges. Its uint8 operations are therefore safe as written. Python mask integers are unbounded, and its NumPy int32 mask indices fit because the maximum k is 14. The unused C++/Node attempts are not part of the trusted certificate path; their reported failures are not successful checks.

The independent verifier uses signed int16 throughout inequality arithmetic, so the verdict does not depend on those uint8 bounds. The file layout is one byte per entry, mask-major and vertex-minor, including mask zero. Vertices are lexicographic (u,v); group labels are lexicographic sorted vertex-index lists. Reconstructed metadata agrees exactly; all gzip outputs have exactly n·2^k bytes. Independent decompression reads at most expected length plus one and rejects wrong lengths. There is no endian issue for bytes. A hypothetical different group order cannot be silently substituted while preserving the checked base semantics. Indexing uses literal mask union and complement, not arithmetic addition on potentially overlapping masks.

## Falsifiers, limits, and formal interface

The strongest checked falsifier is against the five-center shortcut, not against this complete certificate. The supplied 11-cell P is connected, has exact minimum integer diamond radius 4, blocks all five Cartesian centers (0,0),(±1,0),(0,±1), and has precisely one good radius-5 C-center: (1,−1). The seven-cell prefix also blocks the five centers. I independently checked these using literal Cartesian subsets of C. All possible centers are covered by the finite radius-5 neighborhood of one fixed occupied cell. C itself has 57 cells and is connected. Thus the shortcut would be false even at exact size 11/radius 4; the actual proof avoids it.

No defect requiring a candidate edit was found. The decisive unresolved trust boundary is ordinary executable verification: Python, NumPy signed exact operations, gzip and OS, not Lean kernel reduction. The candidate's phrase “no ordinary all-cases geometric proof” is appropriate if it means no noncomputational replacement. It must not be interpreted as a missing mathematical case in the complete computer-assisted argument. The generic graph lemma above has an ordinary proof; the 31 finite inequalities are checked computationally. No numerical approximation is used or offered as proof.

An optional formal interface is: a finite graph, finite nonempty group-label set, membership relation, and a natural-valued L on nonempty label subsets and vertices; prove base, edge and merge premises imply the connected hitting-set lower bound. Over naturals write merge as L(A∪B,z)+1 ≤ L(A,z)+L(B,z), with L≥1, avoiding truncated subtraction. Separately prove integral signed normalization, all-center collision equivalence, inclusion pruning, and exact finite table decoding/order checks. The four forced cases require certified subset exhaustion. This is an interface suggestion only; no Lean implementation or claim about the ongoing implementation is made. Compressed bytes are a storage improvement only: 31 tables and 1,874,144 entries do not imply faster Lean elaboration/reduction.

This review made no HTTP/search requests and inherited no source, chronology, priority, novelty or substantive clearance. The source/investment lanes and earlier mathematical proof remain separate. No new public URL was relied on, so there is no fresh web-access/hash claim. All evidence here is dated local immutable material with hashes. No git operations, child agents, external messages, uploads, accounts, browser tabs or shared/other-lane edits occurred.

Reproduction from this lane: `OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 timeout 180 python independent_check.py` and the same command with `tree_edge_checks.py`. Each process sets hard AS 536870912 bytes, CPU 160/165 seconds and alarm 175 seconds; BLAS is limited to one thread. Both runs passed; runtimes and exact diagnostics are in the evidence/log files. No new full animal enumeration or Lean work was performed.
