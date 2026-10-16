# Source contracts and reading record

Myeongjin Kang; no affiliation. 2026-10-16. Original prose CC BY 4.0.
All third-party copies under inputs/private remain private, with upstream
rights. Hashes and byte lengths of every local copy are in inputs-manifest.json.
This round accepts the stipulated pinned theorems; it does not audit their truth.

## Authenticated r6 context

Frozen sibling directory: ../fresh-structural-discovery-r6.
External seal SHA256 supplied by the parent:
8cd0210428791a68f2e0a10b9447217996fb3a45967cc3b4203bca51ba647921.
Fresh inline standard-library code authenticated that seal, the two
manifests, all 57 entries (40 input, 17 output), and exact 61-file inventory
before any package code could run. No r6 program was executed in this round.
All five pinned Git blobs were independently recomputed using the Git blob
header and matched to the complete preprint tree. Originals are preserved.
inputs/private/r6-before.json contains the independent pre-research snapshot.
The final verifier independently snapshots and hashes the frozen sibling
before and after executing ONLY this round's read-only programs.

Read the full prior report supplied in the user message, the prior local
source-contracts and verify.py, all explore.py and generate_probe.py, and
relevant source bytes below. The prior checks.py was not executed or needed.
The conditional write in generate_probe.py is acknowledged; no unconditional
read-only claim from its old documentation is relied upon.

The prism basis/classification proof and splice proof were checked at their
mathematical interfaces, as supplied in the user message and authenticated
candidate. The new rank criterion and parity obstruction do not assume splice
closure. The prism argument needed for the denominator diagnostic is proved
again in candidate.md. No previous result is upgraded to independent PASS.

## Pinned OpenAI source

[Repository](https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Prefix: preprints/Paired-states-and-Hamiltonian-cycles-in-cubic-bipartite-planar-graphs-September-24-2026/.
The exact primary mathematical file is
[build/paper.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Paired-states-and-Hamiltonian-cycles-in-cubic-bipartite-planar-graphs-September-24-2026/build/paper.tex).
Local inputs/private/upstream/paper.tex.

This round read TeX lines 1–240 and 750–835 in full, covering introduction,
thm:main, thm:partition, the duality interface, the end of the gluing proof,
and the main and both corollary proofs. It did NOT re-read or audit the entire
state cancellation proof in between. All five original retrieved files are
copied and authenticated, but retaining a file is not a full reading claim.
The immutable original retrieval record is inputs/private/r6-retrieval-upstream.json.

Accepted exact statements:
- thm:main: every finite simple undirected cubic bipartite planar
  3-vertex-connected graph is Hamiltonian.
- thm:partition: a finite simple sphere triangulation with at least four
  vertices and properly black/white triangular faces has a partition into
  two induced trees with any specified edge on a specified facial triangle
  assigned together and its third vertex assigned to the other tree.
- cor:edge-avoidance: each single specified edge of a graph in thm:main can
  be omitted by a Hamiltonian cycle.
- cor:pfaffian-paths: every three-edge simple path in every finite simple
  cubic 3-vertex-connected bipartite Pfaffian graph extends to a Hamiltonian
  cycle. The source invokes GSW Theorem 4.16 and planar Pfaffianity.

The full preprint tree (13,223 entries; not truncated) and catalogue family
were inspected for companion paths. The only matching preprint directory is
this one. This is a path/family check, not a content read of unrelated papers.
No affine-rank or cycle-count premise is imported from these statements.

## Gorsky–Steiner–Wiederrecht

[Matching Theory and Barnette's Conjecture, arXiv:2202.11641v3](https://arxiv.org/pdf/2202.11641v3),
local inputs/private/literature/gsw.pdf and gsw.txt, inherited authenticated bytes.
Read exact text lines 390–430, 475–595 and 640–715, including the Pfaffian
orientation definition, Theorem 4.6, Observations 4.10–4.11, Lemma 4.12 proof,
Theorem 4.16 statement/proof, and the Section 5 exact C4 definition and
Theorem 5.1. The beginning of Lemma 5.2 was seen; its full proof was not used.
No claim of re-reading all of GSW or original HMM in this round.

Theorem 4.6 states every planar graph is Pfaffian. The conformal-cycle
orientation definition is used directly to prove the parity calculation.
Theorem 5.1 supplies generation from the cube by cube and C4 expansions.
The exact expansion requires four distinct cofacial endpoints, u,y in one
bipartition class and v,x in the other, and two odd paths after deleting uv,xy
from the facial cycle. It replaces these two edges by eight specified edges
on four new vertices. No arbitrary two-edge subdivision is substituted.

Observation 4.11's printed path-length typo is not used: candidate.md derives
all six traces directly from the pinned three-edge P4 interface. The trisum
proof is comparative context, not an affine-rank theorem.

## Björklund–Kaski–Nederlof

[Another Hamiltonian Cycle in Bipartite Pfaffian Graphs, arXiv:2308.01574v2](https://arxiv.org/pdf/2308.01574v2),
local inputs/private/literature/another-full.pdf and another-full.txt.
Read introduction/overview through Section 1.3; conventions and planar
Pfaffian discussion; Section 2.2 good-color definition; all of Sections
2.5–3.1 including construction (9)–(11), Lemmas 14–16 and their proofs,
and the switching proof of Theorem 1 (text lines 587–895). The complete
later algorithm proofs and Section 3.4 were not re-read in this round.

Exact used comparative interface: for a fixed anchor and a fixed good
half-coloring lambda, every perfect matching in F_lambda projects to an
anchored Hamiltonian cycle; every extending Hamiltonian cycle has such a
matching (Lemmas 14–15). Lemma 16 produces an anchor-avoiding directed cycle
and hence another Hamiltonian cycle. No assertion that the union of all
such fibers has full real rank, or that their switch graph reaches every
edge, is in that interface. The source explicitly notes the latter issue
in its introduction. These results are not used as unproved rank claims.

## Other primary reading and search

The new bounded search is recorded in literature-screen.md. Search results
were used as leads only. No new mathematical deduction relies on an unread
external theorem. The contemporary Gibbons working note was already read
in r6; the search surfaced it again, and this round does not recertify its
census or import any code/fixture/transfer certificate.
