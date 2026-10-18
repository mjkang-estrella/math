# Reading and provenance limits

All upstream truths at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated; this is not an upstream audit. source-tree-selection.json comes from the complete preprints-tree.json, not truncated tree.json. source-receipts.json authenticates44 retrieved non-PDF blobs by pinned raw URL, Git blob SHA1, SHA256 and length. Retrieval does not imply reading. Four primary PDFs and their extracted texts have separate identity receipts. Bodies are private/ignored, not relicensed or included for release.

## Pinned upstream source reading

- Failure-of-rational-injectivity-for-maximal-coarse-assembly-October-5-2026: full build/sections/01-introduction.tex,02-geometry.tex,05-transfer.tex. Thus actual geometry and the maximal-norm transfer were read. The persistence, maximal-index and sliding proof sections were NOT read in full; their mechanisms are known here from the introduction only.
- A-counterexample-to-the-coarse-Novikov-conjecture-September-23-2026: full build/sections/01-introduction.tex. Relevant bibliography citations were inspected. Its other proof sections are retrieval-only.
- A-Torsion-Free-Counterexample-to-Reduced-Baum-Connes-Injectivity-September-23-2026: full build/sections/00_introduction.tex and07_completion.tex; the Hanke–Schick bibliography entry and relevant citations were inspected. The full graphical-presentation, random-lift, trace and finite-witness proof sections were not read. The introduction and completion explicitly state the detector and maximal nonvanishing used here.
- Thomason-Model-Structures-in-Every-Strict-Higher-Dimension-September-25-2026: full build/sections/01-introduction.tex,03-relative-prisms.tex,04-labelled-pieces.tex,05-couniversality.tex,06-subdivided-attachments.tex,07-model-structure.tex,08-method-context.tex. Section04 was reread alone and the first100 lines of07 reread to remove ambiguity from an earlier output truncation.02-foundations.tex was inspected through labels/references and statements used by later sections, not read in full.09-presentability and the bibliography were not read fully. No complete source proof audit is claimed.

## Primary papers actually consulted

Line ranges below refer to the retained extracted .txt files as displayed during reading; they describe reading extent, not article pagination.

- Hanke–Schick, The strong Novikov conjecture for low degree cohomology, arXiv0705.2578v1: extracted lines1–170, including full Theorem1.2, Corollary1.3 and the opening almost-flat-bundle construction. The rest of the proof was not read. Used for exactly the stated low-degree pairing nonvanishing theorem, applied also to integer multiples.
- Pavlov, arXiv2208.02954v1: initially retrieved; searched introduction/theorem and relevant section excerpts only. SUPERSEDED and not a theorem dependency. Its Cartesian claim was checked against the corrected version before conclusions.
- Pavlov, arXiv2208.02954v4: current arXiv version history/metadata, introduction lines1–135, lines278–379 (definitions and h-monoidality/monoid-axiom discussion), full §4 lines379–480, and lines480–715 (§5 through the word filtration, ordinary monoid attachment proof, Theorem5.6 and opening enriched definitions). Earlier output truncation in the §3 portion was repaired by rereading278–354. Later enriched-category proofs were NOT read. The precise nonexistence argument and actual ordinary monoid operations, rather than v1's statement, control this screen.
- Stephan, On equivariant homotopy theory for model categories, arXiv1308.0856v2: lines200–340, including Lemma2.5, Proposition2.6 with proof, Remark2.7, Proposition2.8, orbit-diagram definitions/Lemma2.9 and Theorem2.10 statement plus proof opening; lines510–535 including Example2.18. Not the full paper or full Theorem2.10 proof. The stronger categorical fixed-pushout hypothesis is explicitly not asserted by r41.

Search-only leads included Lenz global category models, White commutative-monoid transfer, and Chuang–Lazarev monoid localization. Their bodies were not read and they supply no theorem dependency. An attempted arXiv HTMLv3 URL returned404; no reading is claimed from that failure. No exhaustive literature review is claimed.

## Authored history and validation

History reads and their limits are recorded separately in history-reconciliation.md. Parent/other-agent messages provide coordination and count status, not independent mathematical review. The square obstruction is an exact coefficient proof, not a finite sampling claim. No empirical diagnostic or Lean theorem is offered as proof. Integrity controls check only the sealed payload and source identities.
