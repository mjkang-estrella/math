# Source contracts, reading extents, and operation comparison

Myeongjin Kang; no affiliation. 2026-10-16. Original prose CC BY 4.0. Third-party files under `private/` retain their rights and are not publication payloads.

## Immutable corpus

Repository https://github.com/openai/math, revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The complete `sources/preprints-tree.json`, not `tree.json`, supplied every path and Git blob identity. All 53 downloaded source text blobs were authenticated against those Git identities. Retrieval alone does not mean semantic reading.

The exact paths, local filenames, SHA256, sizes and Git blob identifiers are in `private/source-manifest.json` (12 family155 files) and `private/lattices/manifest.json` (41 family206 files). A pinned raw URL for every lattice file is obtained by prefixing its recorded path with `https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/`.

### Selected family206

`Finite-Congruence-Lattices-Characterization-and-Undecidability-September-24-2026/build/sections/`:

- `introduction.tex`: main theorem m:main and proof organization read. Distinguishes representation from embedding, global from pointwise Palfy–Pudlak equivalence, and solution-valued templates from computable syntax bounds.
- `graph.tex`: entire file read, including full proof of f:criterion and f:cor-witness-bound. The three finite graph tests supply semidecidability. The connectivity clause, not just color separation/triangle inequalities, supplies onto-ness.
- `diophantine.tex`: entire file read. n:positive-circuits defines the input language. n:circuit-template computes a unit count from syntax but constructs an actual template only after a positive solution is given. n:undecidable computes a witness bound from a hypothetical decision oracle; n:interval-undecidable is the separate full subgroup-interval conclusion. These are stipulated source theorems, not audited here.
- `weighted.tex`: introduction, units/stock and actual-template definitions, labels/cuts proof, beginning of the footprint proof, and the complete t:weighted-realization statement/proof read. The intervening long structural reading proofs were NOT read or independently verified. Their final theorem is stipulated. The literal object is the entire interval [S_Z × Y,S_(Z union units)]. Its arithmetic is recovered in one common cell alignment, possibly through a nontrivial image, with carrier-to-order bound 60^m m!.
- `counting.tex`: introduction/controls and full n:template-bound statement and proof read. Intermediate compression and private-square proofs were not read. Phi(t) bounds the literal lattice cardinality independently of numerical weights. The bound does not identify its order table.
- `minimum.tex`, `quantitative.tex`: selected statements and beginnings/end of displayed output only; the combined display was truncated. No claim of complete reading and no proof dependence on these sections.
- Other downloaded text: inventory context only, not read as mathematical premises.

Companion `A-Negative-Solution-to-the-Finite-Lattice-Representation-Problem-September-24-2026/build/sections/introduction.tex`: complete introduction read. Its main:congruences asserts a finite nonrepresentable lattice; main:group is the separate subgroup-interval obstruction. Its field transfer is already explicitly present. The later structural proofs were not read, and none is used beyond these stipulated conclusions.

### Rejected family155

`A-translational-tile-with-no-fully-periodic-tiling-in-dimension-three-September-23-2026/build/sections/`:

- `01-introduction.tex` and `07-three-dimensions.tex`: complete bodies read, including grid-center rigidity, marked-point kernel invariance, and the full periodic-tiling exclusion. The theorem does not assert connectedness or absence of every individual nonzero period.
- `02-word-rule.tex`, `03-cyclic-encoding.tex`: complete bodies read. The line rule and cycle exclusion encode simultaneous activity; ordinary channels factor through L_n(x)=x_2+n x_1.
- `04-activation.tex`: full ordinary/seed activation and extraction argument read.
- `05-common-solution.tex`: block-inverse proof and ordinary-output construction read; a combined display truncated part of the seed construction. The full seed model was not read.
- `06-stacking.tex`: downloaded/authenticated, not read. No new theorem depends on it.

The idea to adapt the cyclic encoding to undecidability, and the connected-tile idea, were screened out before MRC was frozen.

## External primary sources

Exact downloaded bytes, URLs and SHA256 are recorded in `private/external-manifest.json`.

1. [Demaine–Langerman, arXiv:2610.12392v1](https://arxiv.org/html/2610.12392v1), October8,2026. Read the main theorem, full five-stage proof overview, definitions of connectedness and lattice/real tilings, and formalization-scope discussion. Its stated theorem is single connected-polycube co-RE-completeness in Z3 and R3; the overview explicitly identifies the same cyclic-encoding adaptation, followed by quotient lifting and connectivity. This suffices to reject that proposed novelty. The linked full Lean proof and longer technical article were not audited. This is external comparison evidence, not a newly stipulated upstream theorem used in MRC.

2. [Pudlak–Tuma, 1977 preliminary communication](https://www.dml.cz/bitstream/handle/10338.dmlcz/105785/CommentatMathUnivCarol_018-1977-2_19.pdf), pp409–414. Full extracted text read. It states finite partition embeddability and sketches the join-quotient/regraph proof (Theorems1–2). OCR has defects in intermediate formulas, which are not used. The definition of embedding as injective meet/join homomorphism and the main statement are clear. This is a proof sketch, not the full 1980 proof; candidate Section4 cites the established theorem and independently supplies its local-diagram consequence. No endpoint-preserving variant is assumed. The initial web PDF request timed out; direct retrieval then succeeded. The PDF and its terms remain private.

3. [Calude–Nies, Chaitin Omega Numbers and Strong Reducibilities](https://www.cs.auckland.ac.nz/~nies/papers_till_09/CaludeNies_ChaitinOmegaReducibilities.pdf): definitions of wtt/tt, Theorems2.1–2.3 and displayed proofs read through the reference list in the extracted body. This comparison confirms the classical distinction between bounded use and total truth-table processing. Candidate Section5 does NOT identify its base-4 rational cut with a Chaitin Omega digit set, and does not rely on the paper's randomness or complexity theorems. Its separate cut/selector argument is proved directly and carries no novelty claim.

Search results mentioning criticisms of the pinned family206 theorem were not used to reassess it. Upstream theorem truth remains stipulated as requested.

## History and eligibility

Read AGENTS.md and current original task instructions. Read the full short next-discovery brief; opening instructions/exclusion passages and relevant appended review portions in the r17 structural and r15 analytic briefs; ledger headings/acceptance summaries and targeted relevant sections of NEW-TEN, TEN, and TWENTY. Large nested historical briefs and the older264KB TEN ledger were not read in full this round; no full-history semantic-read claim is made. Their exclusions in the inherited brief were retained.

The targeted history searches covered family numbers, finite-lattice/congruence-lattice/weighted-template names and operations, and returned the prior r15 finite-lattice SCREEN. That actual screening.md was read completely: family206 had no developed full target there; it excluded minimal-negative/field/self-dual and witness-size repackagings. MRC uses none as its claimed new operation. The earlier cost-interpolation I82, Egyptian I204/I205, thin-tree/signing and other developed directions were rejected, not restarted. Family173 is parent-owned, family089 is analytic-r17-owned; no overlap.

The R2T contribution report's decisive operation table and parameterized reduction were read. No recursive-shell or parameter variant is pursued. History search is bounded evidence of eligibility, not a global priority theorem.

## Operation-level disposition

- Source graph witness enumeration: antecedent, unchanged.
- Source computable template bound + bounded replacement: antecedent; Section2's bounded-use completeness is technical.
- Actual finite group intervals: automatically representable by their coset action, so cannot realize negative circuit instances.
- Local meet/join constraints: only embeddability; classical finite partition embeddings separate them from full representation.
- Generic reducibility plus Boolean operations: insufficient, by the explicit cut/selector argument.
- Needed new operation: one solution-independent COMPLETE finite lattice table, with full-representation soundness and completeness. Not supplied.

Status is UNRESOLVED_FULL_MRC, not TECHNICAL as a verdict on a claimed completed target, and not DUPLICATE. There is no full target proof to send to independent acceptance gates.
