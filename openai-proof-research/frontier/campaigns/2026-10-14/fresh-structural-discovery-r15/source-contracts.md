# Sources, actual reading, and rights

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

All stipulated source truth is at openai/math commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Raw retrieval used
https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/
followed by the exact preprint path. inputs/pinned-records.json specifies
EACH retained path, local copy, byte count, SHA256 and Git blob SHA1.
Each blob was independently matched to sources/preprints-tree.json using
SHA1 of `blob <byte-length> NUL <bytes>`. The complete tree is nontruncated.
Byte authentication is not source reading. All third-party copies remain
private and retain their original rights.

## Family162, the selected dependency

B = preprints/Balanced-Counterexamples-to-Rysers-Conjecture-at-Prime-Orders-September-27-2026/build/.

- B/paper.tex, blob93b277615495c01754b4575b045cba89a95f82a1:
full354lines read. thm:main has the sufficiently-large PRIME quantifier,
exactly q+1 nonisolated vertices in each of q+1 parts, intersection and
tau=q+1. It does not assert linearity. cor:tree-cover and its proof already
supply the standard graph consequence. The full assembly proof was read
for which configuration properties are actually obtained, not audited.
- B/construction.tex, bloba66cc581bb62ee628d006a1fd87b59b94fe0c61e:
full341lines read, including definitions, tuple compatibility,
eq:det-core, eq:det-split-intersection, all three deterministic hypotheses,
eq:det-size-condition and full prop:deterministic-reduction proof.
The new obstruction uses exactly the partitions, occupancy/multiplicity,
retained constituent points and designated split pair. It does NOT assume
the concentration or local-cover estimate implies linearity. In fact it
proves that no intersecting linear refinement can exist.
- B/candidates.tex, blob94a8dcdb8bc37e81bcd9e9a54f8aea85e28ef926:
lines1-190 and347-432 read. Full prop:candidate-graph statement and
its concluding occupancy/multiplicity proof were read; the intervening
incidence-count body was not. B=ceil(log q) comes from this interface.
The new proof requires no probabilistic estimate beyond the stipulated
source's existence. No historical/source code was run.

E = preprints/A-Counterexample-to-Rysers-Covering-Conjecture-September-23-2026/build/.

- E/paper.tex, blob141ed64572de469c899d6d12d21790ee066128fa:
full301lines read, including thm:main, cor:tree-cover and its proof,
field thresholds and complete proof overview. Its input section bodies
were not read or retained here. This companion screens duplicate graph
transfers and distinguishes the extension-field range. No new deduction
uses an uninspected part of that construction.

## Other pinned screens

The complete exact reading extents for every retained blob, including
files authenticated but not read, appear in inputs/reading-records.json.
The full introductions of the negative finite-lattice solution, infinite
matroid counterexample and residually finite2-group were read at their
actual main statements and proof overviews. The finite-lattice
characterization companion was explicitly reread through line90, covering
m:main and its finite-witness/Busy-Beaver qualifications. Their proofs are
not dependencies of the two new checkpoints. Small driver TeX files are
retained/authenticated for source layout only, not counted as theorem reading.

## External primary literature

inputs/primary-records.json binds actual retained HTML bytes, URLs,
SHA256 and reading extents. These are primary papers, not search summaries.

- Francetic--Herke--McKay--Wanless, arXiv:1508.00951v3,
https://arxiv.org/html/1508.00951v3 : rendered lines34-186 and247-307
read. This includes Lemmas2.1-2.2/Theorem2.3 and their proofs,
Corollaries2.4-2.5, Theorem2.8 statement, Theorem3.1 and its complete
construction/proof and displayed9-cover. Computational proof enumeration
was not rerun or audited. The degree bounds and structured-cover
counterexample are primary antecedents, not our discoveries.
- Vazquez Avila, arXiv:2108.01108v1,
https://arxiv.org/html/2108.01108v1 : rendered lines38-122 read, including
the explicitly named linear Ryser assertion and the2-packing interfaces.
Its cited antecedent proofs were not read separately. These statements
are not used in either new proof; in particular no universal claim is
inferred from its phrase that the conjecture is nearly proved.
- Bahmanian, arXiv:1710.05804v1,
https://arxiv.org/html/1710.05804v1 : rendered lines44-149 read, covering
precise hinges/detachment definitions, full Theorem4.1(A1)-(A4),
Nash-Williams Lemma4.2 and the splitting step in Section5.1. Rest of
proof not read. It balances degrees and full-edge multiplicities through
two laminar families, not intersection of EVERY pair of distinct edges.
Its word 'simple' excludes repeated vertex hinges WITHIN an edge; it is
not our condition of at most one common vertex BETWEEN distinct edges.
No theorem about all intersecting detachments is attributed to it.

This is bounded primary comparison, not an exhaustive literature review,
a claim of priority, or a certification of current universal open status.
