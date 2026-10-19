# Provenance and actual reading limits

## Repository context

AGENTS.md and sources/upstream.json were read. The full `sources/preprints-tree.json` was parsed: 13,223 entries, truncated=false, all path/type/SHA records inspected programmatically and path uniqueness checked. Selected canonical files were matched to this complete tree and their Git blob SHA1 recomputed. The truncated sources/tree.json was not used. Pin: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. All pinned theorem statements and proof operations are stipulated, not truth-audited.

The entire CONTENTS.md bytes were processed and all 372 headings parsed; attempted full terminal display truncated. Selected entries were semantically read, not every body of the 638,727-byte catalogue. The campaign ledger opening/current requirements (lines1–240) were read; operational-history searches had truncated displays, so no complete semantic reading of all history is claimed. R023–R040 acceptance records were read across successive batches; earlier truncated batches were supplemented by individual reads and the later remainder batch. Their underlying review/manuscript/release packets were not all read. These records identify paid families, not new author gate assignments.

## Pinned source bodies

All retained canonical files and raw URLs are individually inventoried in source-receipts.json, with Git blobs checked against the complete tree and SHA256 of downloaded bytes. Retention is not a reading claim.

- 047: sections01–06 and references.tex fully read, including construction/stabilization, degeneration, bundle, reduction and rigidity. Exact used labels: prop:stabilization, deg:valuation, prop:graded, prop:principalization, prop:linearization, prop:homogeneous-lift, prop:rigidity. Section07 display had a small truncation; only its visible portions were read and no deduction depends on its omitted portion.
- 208: complete consequences.tex read; incompressible classification (cor:incompressible-classification), characteristic-two uniqueness and generalized reconstruction (cor:generalized-tannaka) compared by their actual proofs. Other downloaded sections are retained source context, not claimed semantically read in full.
- 254: complete 08_stabilizers.tex read, including stab:parabolic, stab:initial, intersection/rank descent, nonclique and complete parabolics, stab:single-detector and effective membership proof. Other retained proof sections were not newly read in full. Same-family harmonic/K(pi,1)/non-CAT(0) companions were located via the complete tree and history, but their bodies were not fetched and cleared afresh; no deduction depends on them. This limits that abandoned screen.

## Successful primary versions and proof extents

Exact URLs, PDF SHA256, extraction SHA256 and version identity are in primary-receipts.json. Line extents refer to retained pdftotext -layout files, not journal lines.

- Dutta–Lahiri arXiv1908.03549v1: text175–320; Lemma3.1, Theorem3.2 proof, Lemma3.3 proof, Theorem3.4 full proof and part3.6. The application uses C[p], not C[p,t].
- Finston–Maubach publisher PDF2010: text70–245; Lemma1.1, Lemma2.2 proof, Mini Mason, Theorem2.5 statement and Lemma2.7 proof. The displayed reciprocal-exponent and subsum conditions were actually checked; no unread general strengthening is assumed.
- Coulembier–Etingof–Ostrik arXiv2306.09745v1: selected text504–585 and665–715, with Theorem4.2.1 complete proof recovered560–614 and Lemma4.3.3 proof695–704. Section4.1 definitions/coend and section4.3 GR/MN assumptions were read. Not a full foundational proof audit or whole-article read.
- Blufstein–Paris arXiv2204.05142v2: opening and selected Proposition2.3 construction/proof portions (125–170,200–260); full Lemma2.4 and Theorem1.1 proofs (265–335). Some intervening Proposition2.3 material was not read. No full-article claim.
- Gupta arXiv1309.1368v1: Corollary3.4, full explicit stabilization proof of Theorem3.5 recovered274–331, Theorem3.6 statement/short proof. Earlier Proposition3.3 proof was not read. Positive-characteristic nontrivial-line conclusions were not transferred to characteristic zero.
- Freudenburg–Moser-Jauslin `adjoinedroots.pdf`: successful author-host version, not asserted byte-identical to final journal2013. Opening1–25, section4 text445–645 (Lemma4.1, Theorem4.1 full proofs and corollaries), text865–970 (Theorem8.1 and Theorem8.2 stable-rigidity proof) read. The root-adjoining compatibility and stable Brieskorn rigidity were tried at their actual interfaces. Not a full-paper read.

The Daigle–Freudenburg–Moser-Jauslin abelian-grading follow-up author URL failed (terminal connection refused; web502). Abstract/search snippets were navigation only, never proof input. Searches do not constitute worldwide priority clearance. No browser UI was used. Local extraction is not a guarantee of PDF typography; no layout claims are made. A missing SymPy import was observed; it was not installed or used. All supporting diagnostics here use Python's standard library.
