# T117Q contribution review r2: reading and search limits

Paths are relative to `openai-proof-research/frontier/campaigns/2026-10-14/` unless stated.
Line numbers refer to the pdftotext outputs named below.

## Project rules and records

- `../../../AGENTS.md`, `../../../sources/upstream.json` (pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb).
- `../../NEW-TEN-2026-10-14.md`: lines 1–80 (acceptance rules, count 14/20) and the T117Q
  entries at lines 1368–1402 (status notes only, not evidence).
- `t117q-parent/`: contribution-r2-dispatch.txt, contribution-review-dispatch-r2.json and
  contribution-response-anchor.json (identity and dispatch only). Not opened:
  `t117q-proof-r1/`, `t117q-formal-development-r1/`, any `t117q-formal-v1/`, and any
  parallel reviewer draft.

## Round 1 and parent response (read in full)

- `t117q-contribution-r1/`: review.md and reading-and-search-limits.md in full;
  verify_review.py read before running. MANIFEST.json was used for authentication.
- `t117q-parent-literature-r1/`: response.md in full; grid_control.py, grid-control.json,
  integrity_controls.py, verify.py, provenance.json and retrieval.json read in full.

## Author packet (`fresh-structural-discovery-r59/`)

- candidate.md read in full in this round. verify.py read (first 40 lines plus its usage)
  before running.
- I relied on round 1 for the other author files and did not re-read them.
- Source117-1 (author private copies, blob-verified): main.tex lines 270–290 re-read, and
  a keyword grep of all source117-1 tex files for talagrand/kkl/influence/cotype/schatten/
  trace/noncommut. That grep found no hits, apart from the main.tex lines displayed.
- Round 1's full reading of the source construction was not repeated.

## Primary bodies

Bodies in `t117q-parent-literature-r1/private/` are identical (SHA256) to the round-1 cache
where they overlap.

| Work | Read in this round |
|---|---|
| Jiao–Luo–Wu, arXiv 2610.21445v1 (s1-scale2026.txt) | All 1182 lines (full paper including proofs and references) |
| Cordero-Erausquin–Eskenazis, arXiv 2010.11583 (cee2023.txt) | Lines 480–524 in full (definitions (34)–(36), Theorem 13, (38), KKL remark) and lines 1940–2014 in full (proof of Theorem 13, Remarks 38–39). Lines 440–479, 525–560 and 2015–2030 (§9.1–9.2, Theorem 42 statement) were seen only in displays that elided some lines. Theorem 42's proof was not read. |
| Mendel–Naor, Metric cotype, arXiv math/0506201 (mn2008.txt) | Lines 415–440 (Theorem 1.12 statement), 2773–2790 (Lemma 6.12 and proof), 3005–3090 (proof of Theorem 1.12, Remark 7.5, start of §8). MN Theorem 4.1 and the cotype proofs were NOT read. |
| Giladi–Mendel–Naor, arXiv 1003.0279v3 (gmn2011.txt) | Lines 377–505 (§1.3, Questions 1 and 3) as displayed; some middle lines were elided by the display |
| Naor–Pisier–Schechtman, arXiv 1710.08896 (nps2018.txt, round-1 cache) | Lines 240–334 (Theorem 4, §1.3, Theorem 12 as stated there). Theorem 12's proof was not read. |
| Naor–Young, arXiv 1701.00620 (naor-young2018.txt) | Lines 590–640 (Question 13 and its discussion) |
| Luo–Wang–Zhou, arXiv 2610.03407v1 (author copy lww2026.txt, SHA256 22d2d9e6…0402) | Lines 1–40 (abstract: S_1 has Talagrand type (1, psi_{1,1})), plus line locations of Theorem 1.1. Proof not read. |
| Escudero Gutiérrez–Muguruza, arXiv 2405.03517 (author copy) | Lines 215–259 (§3.2, Question 2) |
| Mendel–Naor, Nonlinear spectral calculus and super-expanders, arXiv 1207.4705v3 (retrieved by this review into `private/`) | Keyword grep only, for S_1/Schatten/trace class/nuclear. No relevant hit. Not read. |

A second retrieval intended as Naor's "Comparison of metric spectral gaps" used a wrong
arXiv id (1403.6620, an unrelated differential-geometry paper). It was discarded from
scratch and not used. The comparison paper itself was not read.

## Web search (bounded)

The following queries were run, scanning the first 5–10 results by title and snippet only:

- negative-type average distortion into S_1;
- expanders and S_1 nonlinear spectral gaps;
- noncommutative Poincaré inequalities with trace-class values and sparsest cut;
- "trace class"/"Schatten" with average distortion and expanders;
- quantum/nuclear-norm sparsest cut and negative-type integrality gaps;
- Cheng–Wang–Xiang L_1 sharp cotype (identity only);
- 2026 trace-norm negative-type lower bounds;
- the LWW S_1 Talagrand paper (abstract confirmation).

No result stated a uniform-average or bi-Lipschitz lower bound for negative-type metrics
into S_1. This is a snippet-level screen, not a literature clearance.

## Not read (open leads)

- Cheng–Wang–Xiang arXiv 2609.08749 (L_1 sharp cotype; only cited via JLW).
- Proofs of LWW Theorem 1.1, CEE Theorem 42, NPS Theorem 12, and MN Theorem 4.1.
- Lust-Piquard–Pisier noncommutative Khintchine duality, Haagerup–Pisier, Buchholz and
  other operator-valued Gaussian sources, which could bear on whether Lemma 2 is a known
  exercise.
- Naor's "Comparison of metric spectral gaps" and surveys on S_1 nonlinear spectral gaps
  or expanders.
- Devanur–Khot–Saket–Vishnoi and Khot–Vishnoi (KKL-type negative-type quotients).
- Lee–Naor (negative-type Heisenberg metric).
- Linial–London–Rabinovich and Arora–Lee–Naor are used in optional item E1 only as
  standard theorems, not read.
- Forward citations, MathSciNet and zbMATH (no access used).

Consequence: literature novelty is NOT demonstrated. The classification is new-to-project
SUBSTANTIAL with bounded coverage.
