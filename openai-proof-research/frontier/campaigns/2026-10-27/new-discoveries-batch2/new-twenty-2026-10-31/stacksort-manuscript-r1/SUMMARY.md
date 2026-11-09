# Draft manuscript and dossier for MathDB 345545 (root review required)

This dossier presents the refutation of the Defant–Propp stack-sorting degree conjecture, arXiv:2002.07144 v3/v4 Conjecture 4.4 (EJC 27(3) P3.51, Conjecture 23). Zero accepted credit; there is no self-acceptance, and the root reads the paper and decides.

## Delivered

- **Paper.**
  - `paper.pdf`: nine pages, titled "The stack-sorting degree grows faster than 1.80^n: a refutation of the Defant–Propp interval conjecture".
  - Its source: `paper-src/paper.src.md` with the generated tables and `status.json`, the expanded `paper.md`, and `scripts/render.py`.
  - The paper states its draft status and AI assistance. It asserts no human author or affiliation.
- **Proof and records.**
  - `PROOF.md`, `STATEMENT-CORRESPONDENCE.md`, `REPRODUCE.md` and `gate-E-map.json`.
  - The exact MathDB raw line `raw/345545.jsonl` (sha256 4ed483b9…d0e2), with `raw/345545.provenance.json`.
- **Sources and evidence.**
  - Source copies and receipts in `sources/`: arXiv v1–v4, the EJC PDF, DOI landing, arXiv abstract, OpenAlex records and Troupes.
  - Evidence copies in `evidence/`: rounds 1–6, the review, the root ruling, the candidate, the final fidelity review and the root registry refresh.
- **Lean packet.** `lean/stacksort-source6.zip` is BYTE-IDENTICAL to round 6 (sha256 9b734e2f…cf5c2f), with `lean/ZIP-RECORD.json`. A safe extraction (`safe-extraction/`, `safe-extraction-report.json`) found 100 regular files and 92 modules whose hashes all equal the round-6 record. The six endpoints are declared, and there are no forbidden tokens outside comments and strings.
- **QA and manifests.**
  - QA images and receipt: `qa/page-1..9.png` and `qa/receipt.json`.
  - Manifests: `SOURCE-COPIES.json` and `DOSSIER-MANIFEST.json`.
  - The full ZIP `stacksort-full-dossier.zip`, plus `DELIVERY.json` with the final hashes.

## Content

The paper covers:

- the source definitions, Theorem 2.5, inequality (1), the sup formula, and Conjecture 4.4 verbatim with its sampling evidence;
- the version history: v1/v2 have the (1.6, 1.8) remark, which is also refuted; the conjecture is in v3/v4 and is EJC Conjecture 23; Troupes restates it with the bound 1.62924;
- a complete ordinary proof: the decreasing-tree and postorder readout; the top-max recursion on tuples of words with T1–T4; doubling from (1) and the series-free iteration; the root-split inequality; the base-130 certificate; the wrap-up with non-vacuity;
- why the sampling heuristic failed (Jensen; typical versus mean growth);
- the reviewer's observation, stated plainly: P_1..P_13 plus root split already suffice, at base 910;
- tables of P_n for n ≤ 20 and of selected n up to 82, with the derived bounds;
- the formal architecture, a paper-to-Lean correspondence table covering both readings, and a round 1–6 history table;
- the audits, axioms, controls and trust limits (the direct P_5/P_6 kernel reductions exceeded the caps but are covered by the proved recursion);
- related work and access limits, with no priority claim.

## Correction to the brief

The brief's "the exact data proves L ≥ 1.8047" is slightly too strong. The exact bound at a = 82 is β_82 = 1.8046832…. The integer test P_82·10000^83 > 4·83·82!·18047^83 FAILS, while P_82·100000^83 > 4·83·82!·180468^83 holds. The paper therefore states L ≥ 1.80468 and says explicitly that 1.8047 would be too strong (`evidence/math-check.json`).

## Status of the other lanes

- **Fidelity review (stacksort-fidelity-r1).** Final. Gates A–D are PASS; D is bounded (an 84-module endpoint closure build, resumed once, with leanchecker on the endpoint module only). Gate E is QUALIFIED_PASS with seven items, all applied and mapped in `gate-E-map.json`.
- **Root replay (stacksort-parent-final-r1).** PENDING. No `replay-result.json` existed at handback, and no claim is made about it. Its `registry-refresh.json` (CLEAN path screen) is present and is cited.

## Checks in this lane (diagnostics, not proof)

A fresh Python implementation (`scripts/check_math.py`) checked the following:

- brute force for P_1..P_8;
- T1–T4 on all tuple pairs with M ≤ 6;
- the recursion, which reproduces the frozen P_1..P_82;
- root split for n ≤ 82 and doubling for 2a+1 ≤ 81;
- G_130 = `lower130` and G_129 = `lower129`;
- the certificate and the controls at base 129 and threshold 1.95;
- the seed-depth thresholds 13→910, 14→446, 16→230 and 20→130.

## Discipline

No child agents. No Lean, lake, leanchecker or solver. No git, network, publication, upload, messages, accounts or browser, and no shared-ledger or other-lane edits. Every write is in this lane. The reportlab bundle is a byte-identical copy from chanlevine-manuscript-r1 (hash-bound, excluded from the ZIP). Symbola and Liberation Serif Italic were copied from system fonts.

Every process ran under `scripts/cap.py`, one at a time, with 2 CPUs, CPU 120 s, wall 140 s, an RSS kill at 1.5 GiB and MALLOC_ARENA_MAX=2. The peak sampled RSS was about 50 MB. Frozen inputs were hash-bound before (`hashes/inputs-before.sha256`, 672 files; `hashes/extra-read-before.sha256`, 25 files) and re-verified after (see `DELIVERY.json`). No jobs remain running.
