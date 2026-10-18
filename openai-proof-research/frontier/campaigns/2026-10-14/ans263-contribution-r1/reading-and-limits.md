# Exact reading and limits — ANS263 contribution review r1

Reviewer: Claude Opus 5.5. Line numbers refer to the retained files in the author packet `fresh-analytic-discovery-r32/private/` (hashes in `input-binding.json`). Their pinned-blob authenticity was replayed through the author verifier (`checks/author-positive.out`). "Read" means displayed and read in this session. A file that was only hashed or grepped is listed as such.

## Project rules and pin
* `AGENTS.md`: read in full.
* `sources/upstream.json`: read in full (pin fd4aeeb2…eeb).
* `sources/preprints-tree.json`: not semantically read. The author verifier checks it (13223 entries, truncated=false).

## Author packet (read in full unless stated)
* Read in full:
  * `263-working-proof.md`;
  * `263-scope.md`;
  * `263-scope-freeze.json`;
  * `263-comparison-and-support.md`;
  * `reading-and-limits.md`;
  * `README.md`;
  * `checkpoint.md`;
  * `263-history-screen.json`;
  * `verify.py`;
  * `exponent_checks.py`;
  * `private/context/analytic-r32-parent-event-lemma.md`;
  * `private/263/lean-doc-263.md`.
* Not read as bodies (hashed and verified only): `source-receipts.json`, `263-source-receipts.json`, `primary-receipts.json`, `263-lean-doc-receipt.json`, `exponent-checks.json` (compared by the verifier).
* Not read: `private/261/*`, `private/context/preprints-tree.json`, `private/context/AGENTS.md`, `private/context/upstream.json` (copies).

## Source R — Generalized outer-electron radii (build/)
* Read in full: `sections/01-introduction.tex` (183 lines), `02-inputs.tex` (205), `03-scales.tex` (203), `04-profile.tex` (340), `05-tails.tex` (252), `06-interface.tex` (57) and `companion-locators.tex`.
* Not read: `paper.tex`, `references.tex`, `figures/scales.tex`.

## Source E — Generalized ionization energies (build/)
* Read in full: `sections/01-introduction.tex` (228), `02-pricing.tex` (348), `03-comparison.tex` (756), `04-barriers.tex` (352), `05-limit.tex` (332) and `foundation-locators.tex`.
* `06-fixed-sectors.tex`: headings only (grep). Body not read.
* Not read: `paper.tex`, `glyph-mappings.tex`, `figures/barrier-step.tex`.

## Source F — Uniform excess charge (build/sections/)
* Read in full: `05-observations.tex` (438) and `15-interfaces.tex` (56).
* Partially read:
  * `01-introduction.tex`: lines 1–80;
  * `12-neutral-sectors.tex`: lines 1–140 (Lemmas 12.1, 12.2);
  * `11-atomic-propagation.tex`: lines 1–60, plus grep lines (probability/threshold lines 75–76, 114–209, 404, 421, 474).
* `10-atomic-comparison.tex`: grep for ground-state hypotheses only.
* `04-screening.tex` and all molecular sections: **not read**. I rely on E §2's restatement of F Prop 4.5 and Cor 4.9 and on F §15.
* Whole-source grep over all three companions for "approximate ground / approximate minim / near-minim / approximate state / low-energy state / minimizing sequence": no approximate-state treatment found. The only hits are minimizing sequences used for existence in F §2 and F §7.

## Primary
* Lieb–Simon 1977, retained OCR text: lines 1650–1700 (approximate ground state definition, motivation, Thm III.2) and lines 1830–1900 (start of the concavity/Rayleigh–Ritz proof). OCR is visibly imperfect, and no transcription of the formulas is claimed.
* Solovej 2003, retained text: lines 190–285 (Thms 1.4, 1.5 and the introduction remark on the outermost region, lines 264–270).
* No other primary bodies were read. No independent web/literature search was performed in this review. Literature coverage beyond these two is the author's disclosed search and is not re-verified.

## Campaign history
* `frontier/NEW-TEN-2026-10-14.md`: lines 1–65 read, plus grep of TECHNICAL/SUBSTANTIAL disposition lines (≈786–979).
* `frontier/TEN-FINDINGS.md`: grep for Coulomb/ionization/263/atom only.
* `ans263-parent/contribution-review-brief.txt` and `ans263-parent/author-side-reading.json`: read.
* `ans263-parent` other files: not read.
* `ans263-proof-r1`: **deliberately not read**, as instructed.
* `ans263-formal-v1`: not read.
* Grep over `frontier/` for outer radius, generalized ionization, Generalized outer, Sommerfeld and outer-electron, excluding private, sources, the r32 packet and the proof review: hits classified in review §5. A further grep for Coulomb in `findings`, `iterations` and `reviews` lists the R032, I217–I223 and other unrelated files by name only.
* `ab194-contribution-r1/verify.py`: first 60 lines read for verifier-layout conventions only.

## What is not claimed
* No proof verdict and no audit of upstream truth.
* No worldwide priority or literature-exhaustiveness certificate.
* No acceptance, count, formal or manuscript claim.
* Exponent scripts (the author's and mine) are finite rational arithmetic, not proofs.
