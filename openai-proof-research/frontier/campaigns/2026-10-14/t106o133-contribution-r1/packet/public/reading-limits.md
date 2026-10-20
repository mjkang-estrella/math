# Reading limits: T106O133 contribution review r1

All reads took place on 2026-10-20, in this order: the project and parent files, then the author packet, then the pinned sources, then the primary literature, then the web. The verdict was formed after all reads listed here. There were no late reads after drafting `review.md`, except re-checks of line numbers for citations already made.

## Project and parent (read in full unless noted)
- AGENTS.md
- discovery-structural-r133-parent/review-context-r1.txt
- discovery-structural-r133-parent/contribution-r1-brief.txt
- frontier/NEW-TEN-2026-10-14.md, lines 1-90 (acceptance rules; line 7 is a status line about this nominee and was read)
- sources/upstream.json
- sources/CONTENTS.md: keyword search and the entries for families 102, 105 and 106
- sources/preprints-tree.json: path searches

**Not read:** other parent files, any proof-review brief, dispatch or result, any other review, and the active roots arithmetic r97 and analytic r131.

## Author packet (authenticated before use)
- Read in full: REPORT.md, FINAL.json, packet/MANIFEST.json (checked structurally), and all of packet/public/{frozen-statement, proof, working-notes, reading-limits, report, rights}.md.
- packet/public/fetch.py: lines 1-60.
- packet/private/primary/primary-receipts.json and packet/private/source/receipts.json.
- Author copies used for primary reading (authenticated by the manifest):
  - kowz-arxiv-2003.11351.txt (KOWZ arXiv v3): lines 255-340 and 1570-1590, plus keyword greps.
  - fmw-eccc-2026-179.txt (ECCC original): lines 230-305 and 4450-4458, plus keyword greps.
- **Not read:** the author's verify.py and controls.py, the author's scratch/ files, the author's copy of the BBN HTML and text (I used my own TeX source instead), and the author's copy of the FMW TeX source.

## Pinned sources (own copies, Git-blob authenticated)
- **106:** read in full: introduction.tex, preliminaries.tex, construction.tex, lists.tex, alignment.tex, coefficient.tex and parameters.tex. Grep only: alignment-proof.tex and main.tex. Not read: references.bib, README.md, the PDF and the Lean docs.
- **105:** 00-introduction.tex in full; 02-construction.tex lines 260-339; 07-parameters-output.tex lines 120-277; greps of all build TeX. The rest is unread, including the full soundness analysis.
- **102:** 00-introduction.tex lines 18-142, and a grep of 07-consequences.tex.

## Primary literature (own downloads in packet/private/primary)
- **Banakh-Barsukov-Nakajima, arXiv 2605.09815v2** (TeX source; the abstract page confirms v2 of 18 Oct 2026 is the latest).
  - Read: Introduction.tex lines 225-260, 355-420 and 440-520; Prelims.tex lines 120-170; MonCliques.tex lines 95-150; Conclusions.tex lines 1-40.
  - Also: keyword greps of all sections and appendices, and of bibliography.bib.
  - Not read: proofs, the appendices beyond grep, and EdgeColorings.tex.
- **Brakensiek-Guruswami, arXiv 1704.01937v2** (TeX source): pcsp.tex lines 285-300 and 545-551, plus keyword greps. The SODA 2018 version was not read.
- **FMW**:
  - ECCC TR26-179 revision 2 (PDF, 119 pages): keyword greps and the Implications section, lines 232-271.
  - arXiv 2610.12378 abstract page: submission history (v1 only) and links (no ancillary files).
  - ECCC report page: revision list (original, revision 1 and revision 2).
  - The supplementary material of the original Remark 1.13 was not located and is unread. Revision 2 no longer contains Remark 1.13.
- **Not read:** BKLM (multi-slice invariance) full text; Guruswami-Sandeep; Avvakumov et al. 2504.07592; Wrochna-Zivny 1907.00872; Zhu's circular-colouring survey. The folklore facts are cited from KOWZ instead.

## Web (bounded)
- WebSearch: "Fei Minzer Wang 4-to-1 games supplementary material ChatGPT applications" and "Brakensiek-Guruswami conjecture proved odd cycle C5 colorable NP-hard 2026".
- FetchUrl: Fortnow/Gasarch blog post of 11 Oct 2026. Its output was also stored by the harness outside this root.
- curl: the Fortnow OpenAI-TCS catalogue page (keyword greps only).
- Result: no BG resolution found. This is a limited sample, not an absence certificate.

## Writes and disclosures
- All of my own writes are inside this root.
- Harness tooling stored some command and fetch outputs outside the root (in /tmp and the ~/.factory tool-output cache). I did not write them.
- I did not modify any author, parent or shared file, did not change git state, and did not start nested agents.
- No browser UI, upload, contact, publication, formal, manuscript or release work.
