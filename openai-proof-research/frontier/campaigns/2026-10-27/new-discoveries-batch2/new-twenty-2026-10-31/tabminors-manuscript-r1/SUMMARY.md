# tabminors-manuscript-r1: draft manuscript and Lean dossier for MathDB 359279

Status: DRAFT. Zero accepted credit. Root performs the final fresh replay and the paper review. Prepared by Claude Opus 5.5, working alone, with no child agents, no git and no Lean runs.

## Result

Conjecture `conj:k+4` of Erickson–Herden–Meddaugh–Sepanski–Hammon–Mohn–Ruiz-Bolanos (arXiv:2307.13161; JCTA 209 (2025) 105950) is **false**.

The two hooks below are distinct elements of YT(12) with mM₈(T₁) = mM₈(T₂):
* T₁: first row 1 5 7 8 12, first column 1 2 3 4 6 9 10 11;
* T₂: first row 1 2 3 7 10 11, first column 1 4 5 6 8 9 12.

Each multiset has 19,958,400 minors. The Lean endpoint is `TabMinors.not_conjecture : ¬ Conjecture`, with axioms propext, Classical.choice and Quot.sound.

There is also an ordinary proof, **not** Lean-verified, that no bound n ≥ k + c works for any constant c. It uses a hook weight formula and pigeonhole. The n = k + 5 failure (k = 11, n = 16) has been confirmed three times.

## Deliverables

* **Paper.** `paper/tabminors-draft.pdf` (5 pages) and its source `paper/build_paper.py`, built with ReportLab and no TeX.
  * Every page was rendered to `qa/page-1..5.png` and inspected visually. Receipt: `receipts/pdf-visual-qa.json`.
* **Ordinary proof.** `PROOF.md`. Statement map: `STATEMENT-CORRESPONDENCE.md`.
* **Lean modules.** `formal/TabMinors.lean` (sha256 66fee9a4…5fd7), `formal/Controls.lean`, `formal/AuditFull.lean`, `negative/NegControl1.lean` and `negative/NegControl2.lean`.
  * All five are byte-identical to `tabminors-parent-check-r1/fixed2/src` (`MODULE-HASHES.json`).
* **Replay.** `replay.py` is a portable driver adapted from root's run.py. It was not run by this lane.
  * It reads the `LEAN_BIN` and `LEAN_PACKAGES` variables.
  * It refuses to run if oleans already exist, and checks the pins.
  * Builds are strict, and leanchecker runs on each of the three modules.
  * It checks the 140-declaration AuditFull, requires both negative controls to fail, and runs a freshness self-test.
  * It writes receipts. Instructions are in `REPRODUCE.md`; pins are in `pins.json`.
* **Sources.**
  * `sources/mathdb-359279.jsonl`; hash in `receipts/raw-line.json`.
  * `sources/arxiv-2307.13161/` (e-print, `main.tex`, abs page).
  * `sources/prior-359279/` (Herden slides, DIMACS page, abstracts) and `sources/review-downloads/` (Jiradilok abs, OpenAlex record).
  * Fetch receipts: `sources/receipts-*.txt` and `evidence/review-r1/*-receipts.txt`.
* **Evidence.**
  * `evidence/lane-r118/` (lane proof, scripts, logs);
  * `evidence/review-r1/` (review and independent scripts);
  * `evidence/root-parent-check/` (root run.py, result and logs);
  * the root adjudication.
* **Archives.**
  * `tabminors-source-only.zip`: what root needs for the replay.
  * `tabminors-full-dossier.zip`: everything except `tmp/`.
  * Hashes are in `archive-hashes.json`. Manifests: `SOURCE-MANIFEST.json` and `DOSSIER-MANIFEST.json`.

## Checks made by this lane, without Lean

* **Safe extraction test of the source-only ZIP** (`receipts/extraction.json`): PASS. Paths are safe, no symlinks, every manifest hash matches, there are no build products, the Lean files are identical to root's fixed2, and `replay.py` parses.
* **Independent Python check** (`scripts/check_pair.py`, logs in `logs/check_pair.json` and `logs/check_c5.json`): PASS.
  * T₁ and T₂ are SYT and distinct, with mM₈ equal (19,958,400 each).
  * mM_k differs for k = 1..7.
  * The Lemma 3 hook formula reproduces both multisets exactly.
  * The Lean literals A8 and B8 equal the true multisets.
  * The source figure T − 8 is reproduced.
  * The n = 16, k = 11 hook pair has equal mM₁₁, and Lemma 3 holds on it.
* **Forbidden tokens.** None of sorry, admit, axiom, unsafe, partial, native_decide or ofReduceBool occurs in `TabMinors.lean`, `Controls.lean` or the negative controls. AuditFull uses such words only as audit identifiers.
* **Replay PASS.** Root's prior replay of these exact bytes passed (`receipts/root-replay-pass.json`). The final fresh replay of the ZIP is pending at root.
* **Frozen inputs.** 415 files were hash-bound before and after the work, and none changed (`receipts/frozen-bindings.json`).

## Corrections and caveats carried into the paper

* At n = 12 there are **4 colliding pairs (8 tableaux)**, not "4 colliding rows". This is labelled as a diagnostic.
* The source has **seven** authors, including J. Mohn and I. Ruiz-Bolanos. The paper cites all seven, not five.
* The journal body (JCTA 2025) was not read. Monks and Cain–Lehtonen were not read. Only the abstract of Jiradilok was read. The bibliography marks what was actually read.
* The noncomputable annotations are explained. They avoid the compiler-generated `_unsafe_rec` partial companions.
* The trust limits are stated: the kernel, leanchecker, the read-only mathlib cache, and a reviewed (not proved) statement correspondence.
