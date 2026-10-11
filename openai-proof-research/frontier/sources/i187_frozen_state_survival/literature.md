# I187 source receipt and dependency/novelty boundary

2026-10-11. **E183 UNRESOLVED.** Eight accepted, two remaining.
Immutable upstream revision:
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.
All OpenAI results there are stipulated true. No upstream truth audit.

Paths below are relative to
`/home/mj-kang/Documents/Dev/math/openai-proof-research`.

## 1. Contract and focused companion check

`AGENTS.md` and `sources/upstream.json` were read in full.
Family 180 was read in `sources/CONTENTS.md`, lines 4177--4192,
with keyword context. Actual manuscript statements, not its summary,
are the theorem inputs.

The complete, nontruncated `sources/preprints-tree.json` was used
for focused Paired-states/Barnette/Pfaffian/Hamiltonian-cycle path
searches. The matched directory contains these paths:

* `preprints/Paired-states-and-Hamiltonian-cycles-in-cubic-bipartite-planar-graphs-September-24-2026/README.md`
* `preprints/Paired-states-and-Hamiltonian-cycles-in-cubic-bipartite-planar-graphs-September-24-2026/build/paper.tex`
* `preprints/Paired-states-and-Hamiltonian-cycles-in-cubic-bipartite-planar-graphs-September-24-2026/build/references.bib`
* `preprints/Paired-states-and-Hamiltonian-cycles-in-cubic-bipartite-planar-graphs-September-24-2026/build/triangle-figure.tex`
* `preprints/Paired-states-and-Hamiltonian-cycles-in-cubic-bipartite-planar-graphs-September-24-2026/paper.pdf`

The directory entries at lines 57321--57373 were read with adjacent
context; `truncated: false` was confirmed in the search output.
The retained README was read in full. This focused check identified
one relevant manuscript and its assets, not a distinct companion
theorem. It was not a whole-catalogue or exhaustive differently-titled
companion-paper survey. The truncated root-tree cache was not used.

No remote retrieval was made. All intentionally accessed mathematical
inputs were local to the assigned project.

## 2. Actual pinned source text

Manuscript: *Paired states and Hamiltonian cycles in cubic bipartite
planar graphs*.

Pinned raw locator:

https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Paired-states-and-Hamiltonian-cycles-in-cubic-bipartite-planar-graphs-September-24-2026/build/paper.tex

Retained file actually read:
`frontier/sources/i164_structural_graph_discovery/upstream-paper.tex`.

SHA-256:
`03f59643501a21f2b20c138ff10769fde41523008845b2528bf646b4a769dd56`.
This matches the I187 brief's anchor.

The full main TeX text, lines 1--838, was read in two overlapping
ranges, 1--430 and 428--838. The included figure, bibliography and
compiled PDF were not opened. No fresh remote byte comparison is
claimed.

| Statement/operation | Main-text lines | Use in this attempt |
| --- | --- | --- |
| `thm:main`, dual formulation | 79--170 | Scope of Hamiltonicity and source-image construction. |
| `lem:duality` | 189--206 | Complementary plane tree/forest duality, including the preimage criterion. |
| `thm:partition`, state definitions | 208--237 | Properly face-two-colored simple sphere triangulation, roots, states and one root-edge prescription. |
| `prop:pairs` and proof | 245--345 | Pair existence under no separating triangle; density and integral-flow operation read, not audited. |
| `lem:disk` and proof | 354--403 | Signed directed-cycle sum, with state-bijection hypothesis. |
| `prop:forest-state`, `eq:J`, `eq:Z` | 407--442 | Forest objective and actual finite exponential sum. |
| `lem:cancel` and proof | 446--483 | Fixed-second-state involution; only the first state changes. |
| `lem:circulation` and spoke comparison | 485--561 | Strict positive orientation-weight difference, including simple detours. |
| `eq:group-product`, `eq:leading-coefficient` | 525--589 | Unfiltered orientation grouping, order and common-phase argument; not assumed for a filter. |
| `lem:root-components` | 598--614 | Three opposite-edge tree components, one root each. |
| White-face-tree recovery | 623--660 | Deleted spokes, rooted white tree, assigned far endpoints, selected edges. |
| `lem:P-forest` and inducedness | 663--718 | Selected-edge acyclicity and actual Hamiltonian complement. |
| Separating-triangle assembly | 720--758 | Read to delimit prescription scope; unnecessary here after the new cut proof. |
| Dual hypotheses in main proof | 760--792 | Simplicity/triangulation argument, with connectivity paid separately here. |
| `cor:edge-avoidance` | 794--805 | One-edge prescription scope. |
| `cor:pfaffian-paths` | 807--828 | Read, not applied as a combined frozen-matching/survival theorem. |

The external results cited by the manuscript were not independently
retrieved or used. The source itself proves the duality, disk,
cancellation, circulation and recovery operations invoked here.

## 3. Exact task and reviewed prior facts

Read in full:

* `frontier/iterations/iteration187-frozen-state-survival-brief.md`.
* `frontier/iterations/i186-theta-region-balance-parent-disposition.md`.
* All five I186 outputs, authenticated against the five detached
  anchors before proof work.
* `frontier/iterations/iteration184-alternating-cycle-brief.md`.
* `frontier/experiments/i183_cptp_finalization/analytic-review.md`.

These retain the exact exterior, arbitrary disk, complete fibres,
patch and original E183 quantifier. They also supply the reviewed
continuation distinctness, matching-deletion bijection, and lost
completion. The historical phrase "strictly stronger in scope" in
I183 is not treated as proof of strict logical separation.
The finalized I186 stopping decision is binding, and its symbolic
length-five data are not treated as an admissible graph.

Only Section 5, lines 386--474, plus heading/keyword hits of
`frontier/iterations/i164-structural-graph-discovery.md` was read.
Its unique-partner, recovery-injection and Vandermonde state-count
argument separates multiplicity from prescribed survival. Its
fixed-root image limitation is not promoted to an E183 example.
No historical experiments or broader sections were audited.

## 4. Dependencies of the written deductions

* **Source hypotheses:** the exact graph hypotheses, brace
  two-extendability already used in the reviewed setup, elementary
  cubic bipartite counts, and plane separation. The small-cut and
  vertex-connectivity implications are proved in full, rather than
  attributed to an unread connectivity theorem.
* **Frozen prescription:** the source's deleted-spoke white-tree
  recovery. The selected forest is called $K_s$, the black-face set
  $\mathcal B$; neither is confused with patch $A$ or lost $P$.
* **Disjointness:** unique black-face ownership and opposite versus
  incident sides give $Q_s\cap K_s=\varnothing$.
* **Conditional preimage criterion:** planar separation, matching
  edge counts, rooted orientations, the read source duality, and
  uniqueness of assigning a tree's edges once to every nonroot.
  No general surjectivity assertion is used.
* **Restricted cancellation:** the actual fixed-$s$ involution.
  Dependence on $s$ alone pays its invariance.
* **Restricted group calculation:** the actual independent
  orientations, disk phases and positive spoke differences, followed
  by a finite algebraic factorization. The endpoint-only mark is
  calculated from intersections of triangle sides.
* **Hamiltonian/type conclusion if nonzero:** the source selected
  forest theorem and full lifted path tracing in the unchanged
  graph. Nonvanishing itself is the unpaid step.

No external theorem needs a new hypothesis check because none is
imported. These are elementary, scoped deductions from the stipulated
source and exact setup, not a demonstrated new-to-literature result.
They do not receive contribution credit merely because they are
written in this round.

## 5. Evidence boundary and original verdict

The input JSON records sixteen actual input-file hashes: the five
anchored I186 outputs, brief, finalized disposition, manuscript,
instructions/contract, catalogue/path list, I184 brief, I183 review,
I164 report and retained source README. Whole-file hashes do not
claim whole-file reading. Output hashes are detached.

No graph/state/matching scans or tests, experiments, research code,
historical replays/rebuilds, source copies, snapshots/seals, agents,
ancestor/shared-ledger edits, staging, commits or publication occurred.
Internal written/document checks are not independent mathematical
review or proof-assistant verification.

The inherited parent replay reports and finite controls are not
universal evidence. There is no source-image nonvanishing theorem
under the survivor prescription here, and no fully hypothesized
counterexample. **Original E183 is UNRESOLVED.** Z184, exchange,
(T) and Q164 remain unchanged. No sequel or publication is initiated.
