# T106O133 correctness review r1: reading limits

## Project rules and dispatch (read in full)
- AGENTS.md; discovery-structural-r133-parent/review-context-r1.txt; proof-r1-brief-prepared.txt.
- The parent directory listing showed contribution-r1-brief.txt, contribution-r1-dispatch.json,
  proof-r1-dispatch.json, intake.json, assessment.md, replay.* and task-status.json by name only.
  None of them was opened. The t106o133-contribution-r1 root was seen only as a name in a
  directory listing and was not entered. arithmeticr97 and analyticr131 were not entered.

## Author root (immutable; read only, after detached-anchor authentication)
- Read in full: packet/public/{frozen-statement, proof, working-notes, reading-limits, report}.md
  and outside REPORT.md.
- Not read: packet/public/{rights.md, verify.py, controls.py, fetch.py}, artifact-controls.json,
  scratch/*, packet/private/source/* (I used my own pinned copies), FMW, 2605.09815 and the full KOWZ text.
- Partially read: packet/private/primary/primary-receipts.json (first 1500 bytes);
  kowz-arxiv-2003.11351.txt lines 255-300 plus a 4-hit search for the Conjecture 1.2 wording.
  The KOWZ extraction was used only to confirm the label wording of Corollary B; I did not
  re-fetch or independently authenticate it against arXiv.
- All 56 author files hashed before reading and before sealing; no change (input-fingerprints.json).

## Pinned sources (own copies, raw URLs at the pin, git blob SHA-1 equal to preprints-tree.json)
- Source 106: main.tex, sections/{introduction, preliminaries, construction, lists, alignment,
  coefficient, parameters, alignment-proof}.tex read in full, line by line. README.md and
  references.bib fetched, not read. The PDF and Lean docs were not fetched.
- Source 105: build/00-introduction.tex fetched; lines 60-99 read and a keyword search over the
  whole file (rich, odd cycle, homomorphism, brakensiek, independent set, colourable). The rest of
  105 is unread.
- sources/preprints-tree.json: titles of all 749 top-level preprint directories, keyword scan only.
- sources/CONTENTS.md: not read in this review.

## Not done
- No web search, no external primary-literature fetch, no FMW supplement search, no BG original
  paper. No large numerical search: the only computation is arc_check.py (exact rationals,
  k = 1..7, at most 630 boundary pairs per case) and one inline negative control.
- No nested agents, git or shared-index changes, publication, upload, contact, browser UI,
  formal or manuscript work.

## Late reads
- After drafting review.md: KOWZ line-number confirmation (lines 281-282) only.
