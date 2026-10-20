# Reading limits, searches and isolation disclosures (T184I134 contribution review r1)

## Briefs and rules (read in full)
AGENTS.md; frontier/campaigns/2026-10-14/expanded-target-2026-10-17/research-brief-2026-10-20.txt;
frontier/campaigns/2026-10-14/discovery-structural-r134-parent/contribution-r1-brief.txt; sources/upstream.json.
Parent context read in full: discovery-structural-r134-parent/assessment.md and substantive-handoff.json (text field).
Not read: frontier/NEW-TEN-2026-10-14.md acceptance section (the role brief restates the criteria used); parent
intake.json, replay.json, replay.py, task-status.json (hashed where listed, not read).

## Author root (immutable; read-only)
Read in full: packet/public/frozen-statement.md, proof.md, report.md, working-notes.md, reading-limits.md; outside
REPORT.md; FINAL.json. Listed only: packet/private (source copies, five primary PDF/text pairs and receipts.json, empty
history directory), scratch/, verify.py, sanity.py, fetch.py, family_map.py, rights.md, artifact-controls.json.
The author's sanity.py was not re-run (not a mathematical gate).

## Pinned source (own copies, Git-blob authenticated; packet/private/source/receipts.json)
Independence manuscript: optimizer.tex, closure.tex, introduction.tex read in full; coupling.tex lines 255-318 (end of
the proof of thm:weighted-triangles and eq:optimizer-triangle); invariant.tex lines 1-45 (cross-mass definition and
thm:weighted-triangles statement); grep for X(C), a_C definitions in coupling.tex. Not read: entropy.tex, splitting
figure, the remainder of coupling.tex and invariant.tex, main.tex, references.bib, README.md.
Correspondence-colouring companion: history.tex read in full; all section files grep-searched for counting /
independence-polynomial / degree-sequence terms (no counting statement found). Not read in full: introduction,
adjustment, rounds, completion, triangles.

## Primary literature (own downloads; packet/private/primary/receipts.json)
- Davies arXiv:2609.04654v1: text lines 1-460 and 996-1787, i.e. Sections 1-2.2 and ALL of Section 3 (3.1, 3.2 with
  Lemma 16, 3.3 Theorem 17 with Lemma 18 and full proof, proof of Theorem 5, 3.3.1 full proof of Theorem 6, 3.4
  Theorem 19 with proof), Section 4, Appendices A-B, references. Not read: lines 461-995 (local-demand proofs).
- Kang, Zenodo 23351325 v1 (13 Oct 2026): text lines 1-659 (Sections 1-4: Theorem A, Conjecture B, Lemmas 2.1-2.4,
  Corollary 2.5, Lemmas 3.1-3.2, Lemma 4.1 statement, Theorems C and D with proofs, Section 4.2) and 1177-1296
  (Section 7, AI declaration). Not read: Section 5, Section 6, Appendix A.
- Cooper-Dutta-Mubayi arXiv:1310.6672v1: lines 60-330 displayed with tool elision; Theorem 4 / Remark 5 not re-read in
  full here (used only for the conceded part 3, and restated by Kang Corollary 2.5 / Section 7.1).
- Buys-van den Heuvel-Kang arXiv:2503.10002v1: acquired, authenticated, not read.
- Not acquired: Cooper-Mubayi author final (author's copy exists; not needed); DMS2012; DKPS2020; Dhawan locally-sparse
  papers; Davies-Dhawan-Gallardo-Methuku-Nguyen-Seo-Spiro (Davies ref. [11], listed "To appear 2026"; no public copy
  found in one search); Davies-Sandhu-Seo-Tan arXiv:2605.05149 (abstract-level search result only); Lee-Seo
  arXiv:2602.02450; Martinsson-Steiner; Shearer 1995; Li-Rousseau-Zang.

## Web searches (navigation only; 6 queries, 2026-10-20)
1. number of independent sets K_r-free graphs degree sequence lower bound independence polynomial clique-free
2. "Fractional colorings of K_r-free graphs with local demands" Davies Dhawan Gallardo Methuku Nguyen Seo Spiro
3. Davies Sandhu Seo Tan "Degree-sequence bounds for independent sets via multivariate local occupancy" arXiv 2605.05149
4. K_r-free graph number of independent sets exp(n log^2 d / d) Ajtai Erdos Komlos Szemeredi conjecture 2026
   (found the Kang Zenodo deposit)
5. arXiv 2026 independence polynomial lower bound K_r-free graphs hard-core free energy entropy-minus-edge potential
   triangle bound
6. Fetch of https://zenodo.org/records/23351325 (landing page: v1, published 13 October 2026, md5 of the PDF).
No exhaustive literature search; no worldwide-priority statement is made in either direction.

## Project history
See packet/private/history/history-search.md (patterns, exclusions, inspected hits, outcome). Active roots
fresh-arithmetic-discovery-r99/ and fresh-analytic-discovery-r133/ were excluded and never entered.

## Isolation
- One slip: during the broad history pass a path list was redirected to /tmp/x (outside this root) at about 10:13 local
  time; I deleted it a few minutes later. No other writes outside this root. The harness itself may keep command output
  under /tmp.
- No git operations, no shared-index edits, no nested agents, no author-root mutation, no browser UI, no publication or
  contact.
