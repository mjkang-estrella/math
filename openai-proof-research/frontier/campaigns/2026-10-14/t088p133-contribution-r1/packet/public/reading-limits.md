# T088P133 contribution review: reading and search limits

Provenance: Factory Droid / claude-opus-5-5 / high, 2026-10-20 (UTC times below where shown). Reviewer:
Myeongjin Kang (no affiliation). CC BY 4.0.

## Briefs and rules (read in full)
- AGENTS.md (1298 bytes); expanded-target-2026-10-17/research-brief-2026-10-20.txt (5570 bytes);
  discovery-analytic-r133-parent/contribution-r1-brief.txt (9600 bytes); fresh-analytic-r132-brief.txt and
  fresh-analytic-r133-brief.txt (both in full, for scope/authorization context).

## Author packet (immutable root fresh-analytic-discovery-r133/)
- Read in full: packet/public/FROZEN-THEOREM.md, proof.md, report.md, reading-limits.md; work/notes.md;
  FINAL.json; REPORT.md; CONTROL-RESULTS.json; packet/MANIFEST.json.
- certificate.py and geometry_control.py: read (certificate.py in full; geometry_control.py skimmed) and
  re-run on copies inside this root (artifact checks only). controls.py and verify.py: run on a copy with the
  detached anchors; not read line by line.
- scratch/*.py: listed, not read line by line (author exploration; not review evidence).
- Detached anchors verified against actual bytes at start and at sealing: FINAL
  4656a93d80d1b67f4d349f3f95382ab8b03e644e45ad61b22629a86bd5c2cd09, MANIFEST
  9ab6adfb17b4e612ad8bee1175109c15b73a1975b67dcc4c580dd955e3306324, REPORT
  3659f82ea364b41303f4097e7df0d12ef380cab5a2d43b0f6bc39ed1405d49fd, scope
  86e1f30e2c867215026b2a4c2bc0c50144660618c486d2b2029e044bfce8d354, proof
  971506a4ea3de75a883da6d0eced6b11b0b997cc2a6598c2e0487ee5a6e2bc84.

## Parent materials
- discovery-analytic-r133-parent: assessment.md, intake.json, replay.py, replay.json (all read in full),
  substantive-handoff.json (read in full), task-status.json (skimmed). contribution-r1-brief.txt read in full.
- Late parent-side additions after my start snapshot (parent activity, not mine): commit-validation.json and
  contribution-r1-dispatch.json; hashed and copied to work/parent-late-additions.txt; content noted (a
  trailing-whitespace exception preserving author bytes; the dispatch record for this task).

## Primary literature (independent acquisition; bodies under original rights in private/primary/)
- FHLX, arXiv:2610.13953v1 (only version; submitted 2026-08-16): e-print source (tar with
  ______-2026.8.26.tex, 1705 lines), PDF (390192 bytes), HTML (525571 bytes), abstract page. Read: the full
  TeX body — Sections 1–4 and the bibliography. Extent: complete.
- Saroglou 2011, Mathematika 57 (2), 329–353: author-host HTTPS still fails TLS verification (reproduced the
  author's failure; not bypassed). Obtained an archived copy of the same author PDF from web.archive.org
  (snapshot 2026-02-09, 223000 bytes, 30 pages). Read: abstract, Sections 1–2 (introduction, Theorems 1–2,
  Corollaries 1–2) and Section 7 (concluding remarks) in full; Sections 3–6 (proofs) not read line by line.
- Saroglou 2015, arXiv:1409.4347v2: e-print source (Second_projection_bodies.tex) downloaded; introduction
  read; whole body searched for facet-count/dimension-restricted upper-bound content (dimension-3 focus and
  lower bounds only).
- Brannen 1996 (Mathematika 43, 255–264; DOI 10.1112/S002557930001175X via Crossref) and Brannen 2005
  (Adv. Geom. 5, 1–13): bodies NOT obtained — Wiley 403 (JS wall), Cambridge abstract endpoint HTTP 500,
  Sonoma State faculty page 403. Known only via FHLX's and Saroglou's introductions and abstract snippets.
- Chen–Feng–Li–Xi–Xu 2026, *Petty's conjectured projection inequality in dimension three* (MathSciDoc
  2608.23001): body NOT located (candidate MathSciDoc URL patterns did not resolve to the paper). Scope
  (dimension 3) taken from FHLX's quotation of its Theorems 1.1–1.2 in the FHLX original text.
- Klefsjö 1982 (Naval Res. Logist. Q. 29, 331–344) and Klefsjö 1983 (J. Appl. Probab. 20, 615–626): Crossref
  metadata and abstracts retrieved (confirm the HNBUE/L-class Laplace characterization used as Lemma 6);
  bodies not read. Rolski 1975, Barlow–Proschan, de Boor/Curry–Schoenberg primary bodies: not retrieved.
- Henk 2025 (Acta Math. Sci. 45, 96–103), Lutwak–Yang–Zhang 2001: known from FHLX's introduction only.

## Pinned sources (stipulated true; no truth audit)
- All 13 .tex/README blobs of the two pinned preprints fetched from pinned raw URLs
  (raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/...) and authenticated
  against the complete preprints-tree.json (13223 entries, truncated=false, tree SHA-256
  eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b) by git blob SHA-1 and size: all match;
  register in work/upstream-acquisition.json. Copies under private/upstream/ (original rights).
- Source P main.tex read in full. Petty companion: README, main.tex, 01_introduction, 06_conclusion,
  07_consequences read; 02_gauges/03_spherical/04_norm/05_position searched (not read line by line) for
  upper-bound/few-facet/Brannen content — none; it is a lower-bound (Petty) paper.
- lean/docs/088.md fetched at the pin and at adc7f1241b42e322a6451854ab7e4b4c146bf78a: byte-identical (1964
  bytes); records only the Petty lower bound and the n = 20 product counterexample.

## Project history (actual bodies read)
- iterations/i43-convex-isoperimetric-discovery.md §1.3 (RP4; read in full) and §1.2 for context.
- fresh-analytic-discovery-r112/packet/public/research-report.md: the 088 paragraph and disposition framing.
- fresh-analytic-discovery-r131/work/notes.md: read in full (1681 bytes; UNSEALED record, not rerun).
- fresh-analytic-discovery-r132: REPORT.md, packet/public/report.md, work/notes.md (all in full);
  discovery-analytic-r132-parent/intake.json (in full).
- Verdict calibration: t184i134-contribution-r1/packet/public/review.md (in full); verdict lines of the
  campaign's other contribution reviews (grep-level survey); t205m, t117q, staircase verdict rationales
  (excerpts).

## Project alias searches (this review, 2026-10-20 ~10:39 PDT)
- rg -uu (hidden+ignored, no size cutoff) over frontier/, excluding .git, the active roots
  fresh-structural-discovery-r135 and t164f99-contribution-r1, and this review root.
- Pass 1 terms: HNBUE; "Laplace bound"; "log-concave density". Pass 2 terms: "stochastic order",
  "convex order", "hypoexponential", "sign pattern", "D(b)", "E W^", "Curry–Schoenberg", "B-spline".
- Result: "HNBUE" occurs only in r133 and its parent. Other hits are copied corpora (pinned preprint copies,
  mathlib, site-packages) or unrelated families; operative 088 hits are I43/r112/r131/r132, all read as above.
  The author's earlier broad 1692-hit query was not re-run; the narrowed mechanism-alias passes are the
  disclosed substitute.

## Web/search bounds (2026-10-20)
- WebSearch (6 queries): "Saroglou Volumes of projection bodies of some classes arXiv"; "reverse projection
  inequality simplex polytopes n+2 facets ... dimension four"; "Brannen Volumes of projection bodies
  Mathematika 1996"; "Brannen conjecture projection body simplex dimensions 4 to 8 arXiv 2026";
  "\"reverse projection inequality\" polytopes \"n+2 facets\""; "Schneider projection problem maximal volume
  projection body simplex counterexample dimension 9 follow-up"; plus "B-spline maximum value bound sum of
  pairwise knot distances"; "Klefsjö useful ageing property Laplace transform"; "density at zero of linear
  combination of independent exponentials sharp upper bound".
- Crossref API queries: Brannen 1996; Klefsjö 1982/1983; Curry–Schoenberg (last query rate-limited once).
- Access failures: Saroglou 2011 author host TLS (worked around via archive.org); Wiley/Cambridge/Sonoma
  403/500 (Brannen 1996/2005 bodies not obtained); Semantic Scholar API 429; MathSciDoc CFLXX page not
  located. No MathSciNet/zbMATH subscription access used.
- These are bounded searches. They support "no antecedent found", not worldwide priority.

## Deliberate exclusions
- Not entered or read: fresh-structural-discovery-r135/ and t164f99-contribution-r1/ (active rounds), per the
  brief. Copied corpora, .git, formal/mathlib and site-packages content excluded from history reads.
- No correctness audit of the author proof; no audit of pinned-source truth.
