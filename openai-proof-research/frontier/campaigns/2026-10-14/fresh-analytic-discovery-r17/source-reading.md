# Sources, contracts and reading limits

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.
Read 2026-10-16. Source theorem truth is stipulated; no upstream audit.

## Immutable sources

Upstream pin: `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` in openai/math.
The complete `sources/preprints-tree.json` was used for paths and Git
blob identities. Each retained TeX file was retrieved from its immutable
raw GitHub URL and checked against its catalogue Git blob. The two
identity JSON files record full upstream paths, local paths, sizes,
Git blobs and SHA256 values. Authentication is not a claim to reading
all retained bodies.

Family 089, planar manuscript:

- `introduction.tex`, all 239 lines: `thm:main` is the constant-distortion
  L1 theorem for every finite connected planar positive-edge-weighted
  graph. The constant is independent of size and edge-length ratio.
- `consequences.tex`, all 75 lines: standard flow-cut interpretation and
  fixed almost-embeddable consequence via Lee--Sidiropoulos and the
  bounded-treewidth companion. These are already source consequences.
- Remaining retained files: authenticated, not claimed as fully read.

Family 089, bounded-treewidth manuscript:

- `01-introduction.tex`, all 265 lines, including the final 235--265
  reread after the earlier output: `thm:main` gives a constant depending
  only on treewidth for all finite connected positive-edge-weighted
  graphs in that class. The source distinguishes four uses of bounded
  whole-bag cardinality and sketches the youngest-reservation argument.
- `02-cut-laws.tex`, all 468 lines in successive bounded reads: finite
  cut measures, gluing, uncertainty transport, threshold and launch
  tests. In particular the complete proof of `prop:uncertainty` was read,
  not merely its theorem label.
- `03-particles.tex`, all 279 lines in successive bounded reads:
  `lem:trace-update`, `lem:particle-bounds`, and
  `prop:particle-realization`, including proof and final constants.
- Other retained files: authenticated; no full-body reading claimed.

Family 333, smooth isometric immersions of closed surfaces in R4:
`introduction.tex`, `global-construction.tex`, `primitive-statement.tex`
were read in full; `velocity-loop.tex` 1--180 was read. The main contract
is immersion, not embedding. The primitive operation supplies prescribed
rank-one metric additions under preferred-normal and boundary-jet
conditions. The loop construction does not provide global C1 closeness
or injectivity preservation. Other retained files were authenticated,
not claimed as read. No theorem from this family is used as a premise
of the graph obstructions.

## External primary bodies

Lee--Sidiropoulos STOC 2009 author PDF is retained privately at
`inputs/primary/lee-sidiropoulos.pdf`, with URL, size and SHA256 in
`retrieval.json`. The extracted text was read at lines 100--250 and
590--752. The latter includes full proofs of the random-retraction and
peeling operations; the first interval supplies introduction context.
The complete almost-embeddable reduction proof was not read. Its theorem
is explicitly invoked in the pinned companion, whose consequence is
accepted on its actual stated hypotheses.

Lee--Poore 2013 was located via the author publication listing and
abstract; the publisher PDF returned 403. No body reading is claimed.
Search-only leads included Lee--Mendel--Moharrami on node-capacitated
flow-cut gaps, Chekuri--Shepherd--Weibel on cut sufficiency, Gromov's
isometric-embedding discussion, and De Lellis's Nash survey. These did
not become mathematical premises or independently certified novelty
comparisons. Secondary search snippets are not proof-body evidence.

## Campaign and eligibility screen

Read AGENTS.md and sources/upstream.json in full. Read the current
`review-entry-parent/next-discovery-brief.txt`; the posterior-critical-wave
`fresh-r15-brief.txt` was read in bounded portions, including rereading
300--743 after truncation; the complex-projector `fresh-r17-brief.txt`
was read in full in bounded portions. The linked linear-Ryser brief's
1--110 lines were additionally read for inherited exclusions; no full
reading of its 1750-line historical proof appendices is claimed.

Read the full final two-temperature contribution report and the complete
235-line fixed R2T candidate in `fresh-analytic-discovery-r16/candidate.md`
(SHA256 `7392c10ee88ba844ae2115cb48bbeff0ba8aaf40641bae42b818825d12778230`).
The TECHNICAL verdict is preserved. No family 228 continuation was attempted. Family
173 remains separately owned by the S2 work. The current NEW-TEN ledger
and older TEN/TWENTY ledgers were consulted at relevant entries; no
claim is made to reading every historical proof through these ledgers.
Catalogue family headings were screened structurally, not treated as
theorem statements.

Bounded older report searches/readings covered I88 nonlinear Banach,
I13 discovery, I132 discrete probability, I135 complex analysis, I134
discrete optimization, and relevant I07/I331 continuity. They excluded
already developed Banach absorption/free-space, random-sign,
Brennan-endpoint and related routes. Some long output was truncated;
no complete reading of those reports is claimed. The relevant older
R012 propeller and R020/R022 information-theory developments were also
used as exclusions, not reopened.

A final content search over frontier Markdown/text, excluding retained
inputs, source snapshots and this owned directory, for family 089,
planar graph metrics, clique-sum closure and L1/bounded-treewidth strings
returned no developed-report hits. An earlier unfiltered search mostly
returned repeated catalogue snapshots and was truncated; it is not
evidence of exhaustive exclusion. A missing hit establishes neither
novelty nor final eligibility. No target was frozen on that basis.

The current brief requests a compact receipt, so no large historical
snapshot archive or full certification apparatus was added. The final
receipt binds observed files and checks retained source identities; it
does not certify mathematical truth or completion of a nomination gate.
Third-party PDFs and TeX are private research inputs, with their rights
retained. All writes remained in the assigned round-17 directory.
