# Source contracts and actual reading extents

Myeongjin Kang; no affiliation. Original prose CC BY 4.0. 2026-10-16.
All local paths below are relative to this round directory. Files under
`inputs/private/` are reading inputs, not releasable original work.
SHA256, byte lengths and (where applicable) pinned Git blob hashes are
in the retrieval records and the sealed input manifest.

## Pinned OpenAI premise

Repository https://github.com/openai/math ; revision
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

Exact preprint prefix:
`preprints/Paired-states-and-Hamiltonian-cycles-in-cubic-bipartite-planar-graphs-September-24-2026/`.

Exact files retrieved and Git-blob authenticated:

* `build/paper.tex` -> `inputs/private/upstream/paper.tex`.
* `build/references.bib` -> `inputs/private/upstream/references.bib`.
* `build/triangle-figure.tex` -> `inputs/private/upstream/triangle-figure.tex`.
* `README.md` -> `inputs/private/upstream/README.md`.
* `paper.pdf` -> `inputs/private/upstream/paper.pdf`.

Each URL is the raw prefix
`https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/`
followed by the exact path, as recorded individually in
`retrieval-upstream.json`. All five blobs match `sources/preprints-tree.json`.

Read extent: entire `paper.tex`, including all proof sections, all of the
bibliography and figure source. PDF retained as a reading copy; the
mathematical read used the exact TeX, not a separate PDF-proof audit.
The README was read as metadata. The catalogue and complete preprint tree
were parsed for companion paths: only this directory matches this family.
This is not a content search through every unrelated manuscript.

Accepted input interfaces (truth stipulated, not audited):

* `thm:main`: finite simple undirected cubic bipartite planar
  3-vertex-connected graphs have a Hamiltonian cycle.
* `thm:partition`: simple sphere triangulations, >=4 vertices, properly
  black/white colored triangular faces; specified facial triangle and
  specified edge; two induced trees with the prescribed label pattern.
* `cor:edge-avoidance`: any specified edge in the first class can be omitted.
* `cor:pfaffian-paths`: finite simple cubic 3-connected bipartite Pfaffian
  graphs; every three-edge path extends to a Hamiltonian cycle.

Operation-level proofs read in full: `prop:pairs`, `lem:disk`,
`prop:forest-state`, `lem:cancel`, `lem:circulation`,
`eq:group-product`, `eq:leading-coefficient`, `lem:root-components`,
`lem:P-forest`, the separating-triangle assembly, and both corollary proofs.
No affine-span premise or quantitative number of cycles is assumed.

## Gorsky--Steiner--Wiederrecht (GSW)

*Matching Theory and Barnette's Conjecture*, arXiv:2202.11641v3,
15 August 2022; Discrete Mathematics 346(2), 113249 (2023).
Primary versioned URL https://arxiv.org/pdf/2202.11641v3 .
Local `inputs/private/literature/gsw.pdf`, text `gsw.txt`.

Read extent: abstract/introduction and definitions relevant to tight cuts,
braces and splices; Section 4 from Lemma 4.1 through Lemma 4.5 and its full
proof; Theorems 4.6--4.8, Corollary 4.9 and proof; Observations 4.10--4.11,
Lemma 4.12 and proof; Theorems 4.13--4.14, Corollary 4.15 and proof,
Theorem 4.16 and proof. Section 5 from its start, Figure 3, the full exact
C4 definition, Theorem 5.1 and the following discussion through the
statement of Lemma 5.2. Later Section 5 term search only, not full proof read.

Contracts used: ordinary splice correspondence is an antecedent,
not a new construction here; Theorem 4.16 is the source of the pinned
P4 corollary. Theorem 5.1 states generation from the cube by cube and C4
expansions. Its C4 input has four distinct endpoints on a common facial
cycle, with the two remaining paths odd, and the specified color alignment.
The local expansion is reproduced exactly in candidate Section 5.
The generation statement is credited to HMM through this primary paper;
this round does not purport to re-prove it from the original diagrams.

Observation 4.11 prints a path-length wording inconsistent with a C4;
we use the explicitly stated P4-Hamiltonian consequence and the six
square traces. No new result depends on interpreting an impossible
four-edge simple path inside a square. The finite witness checks all six
traces directly. No source typo is used as a false premise.

## Björklund--Kaski--Nederlof (BKN)

*Another Hamiltonian Cycle in Bipartite Pfaffian Graphs*.
Primary full version https://arxiv.org/pdf/2308.01574v2 ,
local `inputs/private/literature/another-full.pdf`, `another-full.txt`.
Also primary conference version
https://drops.dagstuhl.de/storage/00lipics/lipics-vol297-icalp2024/LIPIcs.ICALP.2024.26/LIPIcs.ICALP.2024.26.pdf ,
local `another.pdf`, `another.txt`; DOI 10.4230/LIPIcs.ICALP.2024.26.

Read extent of conference version: Section 1 through the conventions,
Sections 2.1--2.4 including complete Lemma 6 proof, Section 2.5 through
the perfect-matching/good-coloring setup (Lemma 8 interface, not its entire
later proof). Full version: introduction and structural statements;
all Section 3.4, including both complete corollary proofs. Theorem 1's
algorithm proof was not read in full or reimplemented.

Corollary 4 requires bipartite Pfaffian, minimum degree >=3; for each
edge, its Hamiltonian-cycle count is zero or at least four. Corollary 5
requires cubic bipartite Pfaffian; the total count is zero or at least six.
These are comparison results only. Their proofs use good colorings,
switches on each bipartition side, and a credited parity theorem. They
do not assert growing affine rank. The finite diagnostic family is not
claimed closed under their algorithms or to represent a graph with only
those eight cycles.

## Holton--Manvel--McKay (HMM)

*Hamiltonian Cycles in Cubic 3-Connected Bipartite Planar Graphs*,
JCTB 38 (1985), 279--297; DOI 10.1016/0095-8956(85)90072-3.
Primary author-hosted scan:
https://users.cecs.anu.edu.au/~bdm/papers/HoltonCubicBipartite.pdf .
Local `inputs/private/literature/hmm.pdf`.

Read extent: visually inspected every complete scan page printed
279--288 (PDF pages 1--10), retained PNGs `hmm-pages/page-01.png` through
`page-10.png`. This includes the reductions definition and Figures 1--8,
Lemma 1 and proof, Lemma 3 with its cube route proof (continuing on 285),
Lemmas 4--5 and proofs, and the beginning of Lemma 6's proof through 288.
The remainder of Lemma 6 and pages 289--297 were NOT read. Text extraction
is empty and is not treated as a reading receipt. The generation theorem
used in the reduction is GSW Theorem 5.1 as stated there; no broader HMM
proof-read claim is made. The diagram inspection confirms the intended
local R0 square and R4 cube operations, not a new theorem.

## Primary contemporary working note

Austin B. Gibbons, `THEORY.md`, repository `AustinBGibbons/barnette`.
URL read https://raw.githubusercontent.com/AustinBGibbons/barnette/main/THEORY.md .
Local `inputs/private/literature/gibbons-theory.md`.
Read extent: entire 286-line file at the retrieved bytes. The mutable
branch URL is not a version pin; its SHA256/length freeze the actual copy.
No claim about the author's current repository after retrieval is made.

This is a working note, not a peer-reviewed theorem. It records the same
linear counting lower bound as a research target and supplies a prism
count proof; it does not give H. Its warnings against unproved local
counting transfers were read. No code, fixture, transfer certificate or
asserted numerical census from that repository is used as evidence here.
The round's finite witness and computations were generated independently.

## Leads that are NOT assumed mathematical inputs

Goedgebeur--Ozeki--Van Cleemput--Wiener, *On the minimum leaf number of cubic
graphs*, author PDF https://tgt.ynu.ac.jp/ozeki/2018GOVW.pdf ,
local `min-leaf.pdf`, `min-leaf.txt`: title, abstract, Sections 1--2 through
the historical Tutte discussion on printed p.3 read; remainder not read.
It led to a binary cycle-space antecedent, which is different from real
affine span.

Horton, *On two-factors of bipartite regular graphs*, Discrete Mathematics
41(1) (1982), 35--41, DOI 10.1016/0012-365X(82)90079-6:
primary publisher abstract at
https://www.sciencedirect.com/science/article/pii/0012365X82900796 read
online. PDF retrieval failed (403 through terminal, browser internal
error). The full theorem hypotheses/proof were NOT read and no deduction
in this round relies on them. In particular a two-factor binary-span
result is not silently used to prove a Hamiltonian real-affine result.

The EJC article DOI 10.37236/13673 was opened as a search lead; its title,
abstract and introduction establish it concerns CAI partitions, not H.
No theorem or proof from it is used. No local copy was needed.

## Campaign context

Read AGENTS.md; upstream metadata; catalogue (all family headings and
selected exact abstracts); parsed all 13,223 complete-tree entries;
NEW-TEN campaign ledger and TWENTY-FINDINGS acceptance/veto record;
R023--R026 finding records; full poly-Zp contribution review, in particular
its Section 3 operation-level reduction; and its parent disposition.
These copies reside in `inputs/private/context/`. The current user message
supersedes historical scope, count and ownership text. All earlier vetoes
were retained. No mathematical result is imported from those vetoed lanes.
