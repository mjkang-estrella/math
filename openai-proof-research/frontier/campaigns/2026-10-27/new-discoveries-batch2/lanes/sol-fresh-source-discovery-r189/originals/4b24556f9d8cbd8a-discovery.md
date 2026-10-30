# Target, source and decision

ZERO: no full ordinary resolution and no nomination for review or counting.
This is a fresh source investigation, not a continuation of r142, r139,
r135, arithmetic r144 or an old NEXT gap. No PROOF.md is justified.

Paone–Paone, *Line-Graph Signature Beyond the 2-Core: Exact Counterexamples,
Rooted Response, and Extremal Constructions at Fixed Cyclomatic Number*,
DOI10.5281/zenodo.21706797, v1.3 dated30July2026, Conjecture5.4, PDFp9.
For **every finite connected simple graph G**, let c(G)=|E|-|V|+1 and
s(L(G))=n_+(A(L(G)))-n_-(A(L(G))). The claim is
2s(L(G)) <= c(G)+1. No minimum-degree, bipartiteness, cactus, size or
nonsingularity restriction is added. A single graph violating it refutes
the universal claim. For c>=1 the equivalent extremal assertion is
f(c)=floor((c+1)/2). The source also includes trees in the universal inequality.

The current Zenodo API response identifies v1.3 as the last deposited version;
created30July2026, modified10August2026. The actual391809-byte deposited PDF,
SHA2567c8afba6cc3be742d46675d51b5f167a55b66fc721901129c30a508d58a0e304,
was retrieved30October2026 at00:05:48 UTC. This actual UTC rollover is not
backdated to the27October campaign name or29October local date. The web
edition carries a shorter title; its matching claim is checked against the PDF.
This is a preprint, not a peer-reviewed resolution.

The source's Proposition5.2, PDFp8, proves only s(L(G))<=c(G). Its proof
chooses a spanning tree, uses known tree Laplacian spectra to get
s(L(T))<=0, then principal-submatrix interlacing adds at most c to the
signature. This leaves precisely c-floor((c+1)/2) of possible excess.
Repeating that argument cannot supply the desired factor of two.
Theorem5.3 constructs the matching lower value; those public constructions
are not discoveries here. Theorems4.1/4.2 already refute monotone2-core
reduction; both are reproduced as controls, not nominated.

Closest author follow-ups read: *Line-graph inertia of roses and generalized
theta graphs*, v1.0,1August2026, DOI10.5281/zenodo.21744051, Theorems5.1/6.2,
signature Corollaries5.2/6.3 and Corollary9.1; and *Response Protection for
Line-Graph Equality Families*, v1.0,4August2026,
DOI10.5281/zenodo.21793638, Theorems4.1,5.1,6.1. The first handles complete
specific graph classes by path elimination and residue classes; the second
constructs a protected equality family with c=2k+1 and signature k+1 using
four-subdivision and amplifier attachment. Their actual hypotheses do not
cover arbitrary graphs or arbitrary pendant forests. They are public before
this lane. No new rose/theta formula, equality family or four-subdivision
invariant is claimed. The classical Schur complement, inertia congruence,
incidence identity, interlacing and rank-one update are not new results.

# Exact mathematical reduction and missing bridge

Write M(G)=Q(G)-2I. The unoriented incidence identity gives

    s(L(G)) = sig(M(G)) + |V|-|E| = sig(M(G)) + 1-c(G).

It remains valid for bipartite graphs and singular matrices: the extra zero
singular values in the edge space contribute eigenvalue-2 to line adjacency.
Thus the full conjecture is exactly

    sig(M(G)) <= floor((3c(G)-1)/2).

Suppose H is the nonempty2-core and r vertices form pendant trees. Partition
M(G) on core/forest as [[M(H)+D,C],[C^T,B]], with D the diagonal of the
numbers of forest neighbors of each core vertex. The source's rooted-tree
invertibility lemma applies to B; each attached rooted tree has the boundary
degree convention of M(G). Its parity proof is important here, since M(H)
itself may be singular. Congruence eliminates B and gives

    sig M(G) = sig B + sig(M(H)+D-C B^(-1) C^T).

Each tree attaches at one core vertex, so the correction is diagonal. For r
individual leaves B=-I_r and the correction is twice the diagonal of their
support multiplicities. Consequently the universal missing bridge is

    sig B + sig(M(H)+D-C B^(-1) C^T)
      <= floor((3c(H)-1)/2)

for **all** cores and all graph-realizable rooted forests. No such bound is
proved here. Even proving it for extremal cores would leave nonextremal
cores that gain signature. The source's Conjecture6.2 is exactly the
remaining quantitative forest-slack issue, conditional on control of cores.
The diagonal corrections and B-inertia must remain coupled; treating the
correction as an arbitrary independent diagonal perturbation discards graph
constraints. The finite checks do not establish this bridge.

The source follows a successful coarse proof with this stronger question;
there is no demonstrated complete classical subsumer here. Conversely,
bounded searching and empty path matches are not novelty clearance. Even a
future full proof would require independent eligibility/classical review.

# Concrete obstruction to an insufficient proof route

The exact edge list of H is in check-results.json under synergy.core.
It has14 vertices,20 edges, c=7 and line-adjacency inertia(7,1,12), so s=-5.
At support x=0 or y=9, one attached leaf gives inertia(8,0,13), still s=-5.
Attaching both gives(9,0,13), hence s=-4. Thus no-gain conclusions for
individual attachments cannot simply be added, even on a genuine2-core.
The conjectured upper bound is4; this example is far below it and refutes
neither Conjecture5.4 nor the extremal-core conjecture.

Independent Gauss–Jordan elimination of M(H) has rank13 and verifies kernel
vector (-3,-1,-1,-3,3,1,1,-3,1,5,1,1,-1,1). Its coordinates at0 and9 are
nonzero, so neither e_0 nor e_9 lies in the column space of symmetric M(H).
Both scalar responses are undefined. No inverse/pseudoinverse substitution
or arbitrary choice of response is made. Direct line-graph elimination
reproduces all four stated inertias. The source already warns about
interacting attachments; this concrete diagnostic receives zero credit.

The strongest objection to any proposed conclusion is the missing universal
graph-realizable inertia bound above. The exact source falsifier would be a
finite connected simple G with 2s(L(G))>c(G)+1, certified by exact inertia.
The diagnostic falsifies only the stronger independent-attachment heuristic.

# Checks, screening and access limits

checks.py: 2,000 deterministic seeded tree-plus-chord graphs, c2..7, starting
order8..26 and adding0..8 forest vertices. These are sampled labeled graphs,
not uniformly sampled isomorphism classes. Exact Fraction congruence uses
nonzero diagonal pivots, hyperbolic2x2 pivots when every diagonal vanishes,
and a zero block otherwise. No floating eigenvalues or tolerance decisions.
All2,000 pass;24 are independently constructed in edge space. Published
c2 and c4 positive-gain controls both reproduce. Seed and digest retained.

structure.py:80 explicit c2 cores: theta path lengths1..5 with at most one
length1, two cycles of lengths3..6 joined by bridge paths1..4, and two cycles
identified at one vertex. Enumerates4,980 one/two-leaf placements, including
two leaves at the same support. Maximum signature1, no violation. This is
not an exhaustive arbitrary-subdivision/forest proof; reduction across
attachments requires an additional argument. Original outputs and all caps
are retained. The diagnostic's kernel is verified by direct exact products.

Early source screen before downloads queried exact identifiers, titles,
authors and aliases in complete original SUMMARY/discovery/PROOF/review/
DECISION report bodies. The retained r133 gzip index426515 aliases was
filtered by report role; current hashes refresh changed/new originals.
Scans cover1,640 then1,642 original report paths, with no match cutoff,
no missing/oversize bodies in that scope, and preserve original r111–r113
science. Broad matches were reopened in full, including r56's unrelated
bootstrap work, r121/r68/r85's public W2 exclusions and r139's prior screen.
The lone exact Annor lexical match is an unrelated Hessian-normal word
boundary collision, reopened and rejected. Complete hit bodies are retained
in history-*.json, not just snippets. No absence across all possible file
roles or unindexed binary source bodies is claimed.

The Zagreb lead202610.2972 was searched by ID/title/authors before fetching;
403 stopped access, so no primary statement clearance. Annor2506.03646v1
Conjecture7 was followed to latestv3: the conjecture is removed, rather than
being treated as a surviving current question. Chakraborty–Foucaud–Hakanen
2509.00383v1 records metric conjectures. Chen–Ma2607.27573 latestv2 and
2608.17944v1 give public full mixed-metric upper bound and equality analysis;
actual theorem/proof bodies read. The sharper vertex/edge2c-1 target was
only screened, not resolved here; full exceptional-family bridges were not
audited. An earlier commentary's broad metric exclusion should be read with
this qualification. No new proof of that sharper conjecture is asserted.

Registry screening reuses hashed r133/r137/r141/r142 lineage and the root
edge-irregulator retained tree bodies. Latest qualified inherited observation:
Omega490f6bccbf445ab8e111a16b0b8670a5dd7c9a9c at29October23:50UTC;
OpenAI7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a unchanged. Both
aa026→a19a and a19a→490f comparison lists are capped300. r140 clears only
three source-facing Markdown paths in selected scopes of the first interval.
Our bounded exact target lexical scan has no hit in the retained trees and
comparison bodies. This does **not** clear omitted paths or unexamined
current theorem bodies. No moving-head chase, badge inference or priority
claim. Actual live author theorem bodies and deposition chronology were read.
Further target-specific current public-proof body clearance remains required.

Public web queries include exact title, bound, authors, aliases and registry
terms. Original source and author follow-ups located; no full proof located
in this bounded screen. Search responses are not an exhaustive literature
audit. Source author absence assertions are not adopted as proof of novelty.

Failures retained: missing networkx on first check run, replaced with a
lane-local standard-library graph representation; initial structure loader
missing __file__; subsequent nonsingular-only response solve failed on the
singular diagnostic, repaired with rank/range/kernel-aware elimination.
Each failed log is preserved. Author metric PDF404; accessible arXiv full
HTML used. Zagreb403 not retried/bypassed. No429/challenge evasion.

All computational helpers, retrieval/edit scripts and pdftotext ran through
the unchanged required helper_guard.py with AS/groupRSS512MiB, CPU210s,
wall230s, nominal40ms sampling, BLAS/OMP1 and no bytecode. Sampling cannot
exclude unsampled peaks. Native bounded reads and apply_patch are outside
the helper as authorized. All writes remain in this lane. NEXT is mutable
as-read context, explicitly outside the scientific freeze. No children,
git, browser tabs, external mutations, count changes, Lean or manuscript.
