# I257 reading, failed attacks, and access limits

Date: 2026-10-12. Independent mathematical correctness review of the unchanged I248 candidate. Final verdict PASS. No contribution or acceptance verdict. Twenty findings targeted; ten accepted; no count change.

## Actual local inputs

Read AGENTS.md and sources/upstream.json completely. Read all of the original I248 discovery brief (10 lines), final report (42), analytic proof (167), reading-and-failures record (37), authentication JSON (223), and literature record (46). The analytic proof SHA256 matches the exact assigned hash. The author's authentication and confidence were not substituted for independent proof checks.

Read the bounded catalogue entry for family 175, sources/CONTENTS.md lines 4081–4094. An earlier rg query returned matching catalogue lines for 169 and 175; none was used instead of the actual manuscripts. Parsed sources/preprints-tree.json for provenance and used only the two selected pinned paths' blob entries as evidence. Hashing a complete input does not imply reading every argument or catalogue entry in it.

An initial filename search returned many AGENTS.md/upstream.json paths inside older frozen source directories and was truncated. These were names only; no such directories' contents were opened or copied. There was no snapshot creation, giant history replay, or prohibited live-review content read. The entire I254 directory and I247/I249/I250 contents were left unread. No sibling, agent, or parent communication was used as mathematical evidence.

## Independently retrieved and fully read primary material

The present I248 source directory exposed its literature record and retained FLN §2.4 excerpt. Pinned manuscript excerpts claimed by its manifest were not available there, so the selected actual pinned sources were retrieved anew, not inferred from the manifest.

- Graph Decompositions at the Integral Expectation Threshold, pinned build/main.tex: all 841 lines read, including all stated contracts, the complete compression and transfer arguments, maximum-degree and star-forest embedding arguments, and assembly. Retained as two excerpts covering lines 1–488 and 489–841. Whole-source SHA256 and Git blob match the stipulated tree entry. Its truth was not audited.
- Integral and fractional expectation thresholds are equivalent, pinned consequences.tex: all 50 lines read, including the entire two-union corollary proof. Independently authenticated. No other companion proof is claimed read in this gate.
- Ferber–Luh–Nguyen, arXiv:1606.05923v3: retrieved the PDF in memory and extracted using pdftotext -layout. Read the entire retained §§1–2.3 excerpt and all of §2.4. This includes the full partition lemma proof, exact α-good definition, embedding hypotheses, both complete §2.4 lemma proofs, the full Janson calculation, and the exact hypergraph Hall theorem contract. The §2.4 extraction is byte-identical to the already fully read I248 excerpt and its PDF SHA256 matches I248's record. Original proofs behind the cited Riordan and Janson inputs were not read or used as new inputs to I248.

Only these fully read excerpts were retained. No full PDF or workspace/source-tree snapshot was written.

## Retrieval failures and limits

The first FLN extraction attempted to locate the §3 boundary with four spaces after its number; the actual extracted heading uses five. It reported a missing boundary and refused to retain a partial result. The diagnostic displayed part of §3 and references and was truncated. This incidental display is not claimed as a systematic read, is not a proof input, and was not retained. The corrected boundary extracted exactly all of §2.4 and matched the fully read original excerpt. This was text extraction, not a numerical test or research experiment.

The Aharoni–Haxell publisher PDF URL and the abstract page's Download PDF link both redirected to the abstract landing page. Two bounded searches did not locate the original argument at the authors' institutional sites. No full original topological proof was obtained or read. The exact sufficient condition was read in FLN Theorem 2.6, together with the entire primary application argument. This limitation affects source reading extent, not the self-contained rank theorem; the corollary invokes that standard theorem explicitly.

The arXiv 2609.20864 primary v2 record was read completely at its substantive metadata/abstract scope. It states withdrawal and mentions overlapping/repeated neighborhood lists. No v1 proof was retrieved or read. It is only overlap evidence, not a trusted theorem and not a basis for a correctness objection or contribution PASS. Search snippets and nonprimary results were not used as mathematical authority. No MathDB search was made for this correctness-only task.

## Failed mathematical attacks

1. Resampling an entire edge block might change many candidate sets. It does, but every changed set contains the indexed vertex, and an optimum packing uses at most one such set. Deletion gives the claimed constant one even for the weighted optimum.
2. Compression might misuse reused roots or excluded empty supports. Slot-root incidences are distinct edge coordinates, and the self-contained compression argument explicitly includes empty supports. Closing slots preserves the pattern inclusion required at transfer.
3. Maximizing before taking expectation might reverse the inequality. The candidate's inequality is max E≤E max and is justified conditionally on the source; it is in the correct direction.
4. Fixed-host maximum matchings are not uniform. True, but the proof uses averaged exchangeable hosts plus uniform optimum selection, conditional on cardinality only. Uniformity follows from group transitivity.
5. Success conditioning or adaptive occupied sets might destroy independence. Size-success events factor over layers; trimming is uniform and independent; the past filtration exposes only earlier matchings. The next matching retains the required uniform law.
6. A permutation exposes dependent blocks. The prefix-preserving transposition coupling bounds each Doob conditional range by two, so the exponential tail follows without block independence.
7. Floors or cap stopping might lose the amplification factor. The two μ_Q/2-versus-a cases and the explicit uniform lower bounds on μ_Q and q pay the losses. The cap is reached in two successful rounds when q=a.
8. Auxiliary random witnesses might fail to define a deterministic typical class. Host-test failure implies every witness fails; its marginal probability is bounded by the joint witness failure probability. E is directly defined by deterministic rank inequalities.
9. R could be selected from both hosts to evade fixed-family estimates. D and E already impose every finite compressed test. Compression of the selected R still lands in that pre-imposed universe.
10. The application might confuse union matchings and disjoint color representatives, or require disjoint roots. The strict union-rank inequality is exactly the AH sufficient condition for indexed d-uniform hypergraphs on the nonroots. Padding fits, roots are fixed outside that vertex set, and repetition of types is permitted.

None yields a correctness defect for the exact candidate. Optional exposition expansions are paid in analysis.md; no repair is imposed. No new theorem, second nomination, acceptance, or count increment is authored by this gate.

## Operations and retention

No subordinate/delegated agents, live sibling reads, research code, tests, numerical experiments/scans, shared edits, staging, commits, publication, or outside communications occurred. Python was used solely for retrieval, text extraction, provenance hashing, and writing the assigned authentication record. Markdown writing and analytic inequalities are the review work itself. All commands used the required project directory. All written paths have the new I257 prefix or lie in its assigned source directory. I254 was preserved.
