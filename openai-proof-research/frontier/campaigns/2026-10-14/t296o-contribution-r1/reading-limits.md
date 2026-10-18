# Reading limits, provenance and boundaries: T296O contribution r1

Reviewer: independent Factory review sub-agent (contribution/eligibility role only). No nested agents, shared-index edits, staging, commits, uploads or publication. Writes were limited to this directory. Scratch was `/var/tmp/t296o-contrib-r1`. No third-party body is stored here.

## Read in full
- Repository `AGENTS.md`.
- Author packet r77: `scope-freeze.md`, `candidate.md`, `comparison.md`, `reading-limits.md`, `checkpoint.md`, `MANIFEST.json`, `verify.py`, `diagnostics.py`, `source-receipts.json`, `primary-receipts.json` and `diagnostics-results.json`. Hashes are in `input-binding.json`.
- Pinned source 296 sections `introduction.tex`, `independence.tex`, `perturbation.tex`, `generation.tex` and `consequences.tex`, all complete including proofs, from the author's private canonical copy. The copy's git-blob identity was verified against the complete tree by both verifiers.
- Pinned `lean/docs/296.md` (re-retrieved to scratch).
- `t133e-contribution-r1/verify.py`, the helper adapted here.

## Read in part (extracted text from the author's private copies; PDFs re-downloaded and hash-matched, not visually inspected)
- Ma–Shi–Yang arXiv:2604.21482v2, `similarity.txt` lines 60–229 and 385–924, plus grep hits in lines 16–45. These cover Theorem 1.1, Theorem 1.2 statement, Def. 2.1, Lemma 2.2, Cor. 2.3, Lemmas 3.1–3.7, Prop. 3.8, Remark 3.9, the proof of Theorem 1.1, Prop. 3.10, Remark 3.11, Cor. 3.12 and the start of Cor. 3.13. Section 4 (similarity) was not read.
- Shi arXiv:1911.07696v2, `irreducible.txt` lines 1–150 (introduction, Theorems 3.5 and 4.1 statements). The proofs were not read.
- Dykema–Sinclair–Smith–White arXiv:0706.1953v2, `dssw.txt` lines 1–60 and 1040–1090 (abstract/introduction; Lemmas 6.1–6.2 and Theorem 6.3). Ligature loss in the extraction did not affect the statements used.

## Not read
- Source `main.tex`, `preamble.tex`, `README.md`, `references.bib` and the canonical PDF.
- Catalogue neighbours 287, 288, 289 and 300 beyond their catalogue entries.
- Any other literature. No web literature search was performed. Bibliography pointers in the source and primaries were not followed.
- The parent directory `t296o-parent/` (beyond the NEW-TEN ledger paragraph that mentions it) and **the parallel review directory**. Neither was opened.

## History screen
Repository-wide `rg` over Markdown, excluding `**/private/**`, catalogue copies, the r77 packet and `frontier/campaigns/2026-10-14/t296o-*/**`. Phrases searched: relative generation, generator problem, relative generator, irreducible inclusion, unitary orbit, norm-generic, Popa, free Haar, II1 factor, singly generated. Hits inspected: `fresh-parent-discovery-r10/screen-289.md` (one matching line), T286F files (one matching line each) and the T296O paragraph of `frontier/NEW-TEN-2026-10-14.md`. Lexical absence is not an eligibility certificate.

## Boundaries
- The contribution verdict is conditional on correctness, which was not reviewed here.
- The finite diagnostics and integrity controls certify no theorem.
- The free-product witness and the MSY coverage argument in review.md §3 are the reviewer's own short deductions. They are used only to delimit what the read MSY operation covers. They are not claims about the whole MSY paper or the literature.
- No exhaustive novelty claim is made in either direction.

Original prose: CC BY 4.0 as in the author packet. Code: MIT.
