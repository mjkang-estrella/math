# Reading limits, round 2

Line numbers refer to `../t212m-manuscript-v1/` sources (hashes in
`checks.json`) and to the private AH text extraction
`../../fresh-analytic-discovery-r74/private/ahlberg-hoffman-v2.txt`
(SHA256 f7679476…d4af, 4048 lines), which stays in its git-ignored private
location.

## Read in full this round (line by line)

Manuscript (frozen, unchanged since round 1; hashes rechecked):
`public/sections/02-cap.tex` (140 lines), `03-metric.tex` (109),
`04-reference.tex` (194), `05-labels.tex` (173), `06-splice.tex` (128),
`08-use-sites.tex` (109).

AH arXiv:1609.02447v2 text extraction:

- 942–1338: Section 6 complete, all proofs (Lemmas 6.1–6.4, 6.6–6.9, 6.11,
  Claim 6.10, Proposition 6.5).
- 1340–1552: Section 7 complete, all proofs (Proposition 7.2 with Claim 7.6,
  Lemmas 7.3–7.5, Definition 7.1).
- 2679–3085: Section 10 complete, all proofs (Theorem 10.1, Lemma 10.2,
  Remark 10.3, Theorem 10.4, Lemmas 10.5–10.7, Theorems 10.8–10.12, Remark
  10.13).
- 2640–2678 and 3086–3103: boundary confirmation (end of Proposition 9.13;
  Section 11 opening). Section 11 (midpoint problem) is not invoked anywhere
  in Section 10 or by the manuscript and its bodies were not read.

Interface re-verification reads (round 1 had read these fully; re-read here
to audit interfaces directly, not to redo the gate): 160–254 (Section 2
definitions); 319–475 (A1/A2, Remarks 3.1–3.3, shape theorem, Proposition 3.4
with proof); 479–563 (measurability, Section 4 statements); 564–648 and
700–741 (proofs of Lemma 4.1, Propositions 4.2–4.5); 743–824 (Section 5
intro, Theorem 5.1 recap, Theorem 5.2 statement); 936–948 (tail of Lemma
5.6). Lemma 4.6 at 649–671 and Lemmas 5.3–5.6 at 824–948 are relied on from
round 1's full read of 255–983.

## Relied on from prior gates (not re-read)

- Round 1 manuscript review read AH 255–983 and 1555–2712 (Sections 2–5 and
  8–9 in full) and the entire manuscript; its findings for Sections 8–9
  (including the 8.6 same-status replacement and the 9.10/9.11 wall
  replacement), for D/S/P/W, and for Sections 01 and 07 of the manuscript
  are relied on explicitly. This round independently re-derived only the
  interfaces that Sections 6, 7, 10 need from those sections.
- DH `damron-hanson-v1.txt`: not re-read. Sections 6, 7, 10 of AH invoke DH
  only through Theorem 5.1/5.2 (existence of reference geodesics), whose
  replacement is the manuscript's Section 4 construction audited in round 1;
  DH 3–5 continue to be used as stated under the cap's verified A2′
  hypotheses, which the round 2 brief explicitly permits.
- S source sections, DHb, ADH, Cerf–Théret, Boivin, Cox–Durrett, Kesten:
  not re-read; unchanged from round 1's recorded positions.
- The formal support (14 support + 17 controls) and layout/PDF rendering:
  settled in round 1; not redone, per the round 2 brief.

## Prior reports read

`../t212m-manuscript-review-r1/`: review.md, reading-limits.md, checks.json,
verify.py, controls.py (full). `../t212m-parent/manuscript-r1-adoption.json`
(full; its closure-pending paragraph is this round's exact task) and
`manuscript-r2-brief.txt` (full). AGENTS.md and the acceptance rules in
`frontier/NEW-TEN-2026-10-14.md` (read).

## Trust and independence

No nested agents; no frozen-author edits; no staging, commits, ledger writes,
uploads or publication; no acceptance/count decision. Controls run only on
disposable copies under /var/tmp. Primary bodies are not copied into this
public report directory; only line references and interface paraphrases
appear. Checksums and the seal verifier certify identity of bytes only.
