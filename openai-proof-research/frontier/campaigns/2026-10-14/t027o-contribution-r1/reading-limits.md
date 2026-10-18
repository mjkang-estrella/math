# T027O contribution review: exact reads and limits

## Project files read

- `AGENTS.md`, `sources/upstream.json` (SHA256 `3784eb61…f30c`), NEW-TEN
  acceptance rules, `sources/preprints-tree.json` (parsed in full for the
  family path list).
- Author packet, all after anchor checks: `scope027o.md`, `candidate027o.md`
  (complete), `source-and-credit.md`, `reading-limits.md`, the parent
  `pickrell-xia-comparator.md`, `source-precheck.json`, primary and context
  receipts, `verify.py`, `control-tests.py`, contribution brief, templates
  and dispatch.
- Not read: the proof-review brief, any parallel proof draft or proof
  verdict.
- Not relied on: `orbit-work.md`, `formal-interfaces.md` and the
  diagnostic scripts and JSON outputs. I did not execute the diagnostics;
  only `verify.py` (in place, read-only) and `control-tests.py` (on a
  `/var/tmp` copy) ran.

## Source027 (pinned copy inside the author packet, identity checked)

- Read: `introduction.tex` (full), `dynamics.tex` (full), `surfaces.tex`
  lines 1–60 and 180–265, `arithmetic.tex`, `README`, bibliography keys.
- Not read: `model.tex`, `reduction.tex`, `descent.tex`, `diagrams.tex`,
  the rest of `surfaces.tex`. `paper.pdf` was not retrieved or checked.
  These parts concern the integral model, rank reduction, Jordan descent,
  diagram density and the finite-field irreducibility count. They are
  stipulated true and are not where a single-orbit statement would appear,
  but a single-orbit remark there was not excluded by reading.

## Primary comparators

- Coccia–Litt: Prop. 3.1.7, Lemma 3.1.8 (with proof), Prop. 3.1.10,
  Prop. 5.0.1, Thm. 5.0.2, and the introduction's citations. Other sections
  not read in full.
- Goldman 1986: §§4.2–4.7 spot-checked (Thms. 4.3, 4.5, 4.7).
- Mantelos: Thm. 1.1 and the cycle identities. Loewy's paper body not read.
- Pickrell–Xia I: lines 20–1058 of the author's text copy, covering §2.1,
  §2.2, §3 Thm. 3.1 and Lemma 3.10, Appendix A and Appendix B through B.5.
- Golsefidy–Tamam: PNAS 2025 full text from PMC (Theorems I–L and the
  Larsen–Pink remark). Orbit-closure preprint `G_T_OrbitClosure.pdf`:
  abstract, contents and a search for rank terms (SL_d, SL_n, rank, Larsen,
  Chevalley) only; body not read. `GT_MCG-all.pdf` and the IMRN
  exceptional-orbits paper not read.
- Litt survey arXiv 2409.02234: §5.4 (Questions 5.4.3, 5.4.4, 5.4.11,
  Theorems 5.4.12, 5.4.13 and the surrounding text).
- Martin-Baillon bibliography on mapping-class dynamics (2023 PDF; the
  retrieval URL was not retained, the file is identified by title, author
  and hash): full text.
- MathOverflow 332994 and 455985: questions, answers and comments, read as
  pointers only. Their claims (Kapovich comment; Speyer and Jacques
  examples; Lawton thesis) were not checked against primary papers.
- GLX21: abstract only. PX02b, Biswas–Koberda–Mj–Santharoubane, Whang,
  Larsen–Pink: bodies not read.

## Searches

Web searches for higher-rank single-orbit or dense-orbit integral results,
Litt's publication list, Golsefidy's research page, and project history
(see `history-search.json`). These are bounded and are not a worldwide
novelty clearance.

## What could change the verdict

- A located paper proving Zariski density of one integral (or one
  algebraic) mapping-class orbit on closed-surface SL_r character varieties
  for r>=3 would make T027O DUPLICATE or TECHNICAL. None was found.
- A cheap reduction from a known generic-spanning theorem to a single
  integral orbit (section 4 item 3 of the review) would lower the verdict to
  TECHNICAL. I found none and argue one point-specific certificate is
  needed.
- Unread source027 sections could only affect this if they contained a
  single-orbit statement or the same certificate.
