# Reading, search and proof limits

Exact extents actually read by this reviewer. "Grep" means keyword hits were inspected, not a full reading. Line numbers refer to the reviewer's `pdftotext -layout` or HTML-to-text extractions held in `/var/tmp/t008m-cr1/` (temporary, not sealed).

## Project files

* AGENTS.md (full); sources/upstream.json (full; commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb); sources/preprints-tree.json hashed and parsed (truncated=false), not read line by line.
* frontier/NEW-TEN-2026-10-14.md: lines 1–20 (criteria) plus grep hits for substantial/technical/routine/contribution verdict wording. The remaining ledger was not read in full.
* Brief t008m-parent/contribution-review-r1-brief.txt (full).
* Parent files read: parent-primary-screen.json, lewin-primary-receipts.json, parent-verification.json. Seen only in a directory listing and NOT opened: proof-adoption.json, proof-r1-parent-verification.json, single-cap-addendum.md, parent-diagnostic-replay.json. One tasks.json line describing the proof-review disposition was displayed by a grep (see review.md §6). t008m-proof-r1 was not read.
* History: proposals/algebra_geometry.md lines 125–136; `git log -S` gives commit cf875aeb (2026-10-08) for the free-GT rejection. A regex search of frontier/iterations, proposals and frontier/findings for Grothendieck–Teichmüller, Ihara and T008M found only that line. This is a bounded history search.

## Frozen author packet (read-only)

Full: candidate-008.md, scope-008.md, source-and-credit.md, reading-limits.md, verify.py, checkpoint.md, provenance/seal-repair.md, primary-receipts.json. manifest.json was hashed and parsed by the verifier, not read row by row. diagnostic-008.py, diagnostic-008-result.json, formal-interfaces.md, controls.py, REPRODUCE.md, LICENSES.md, the family200 files and receipts were not read (identity only).

## Source008 (author private copies, blob identities rechecked)

* build/sections/01-introduction.tex: full (equations, thm:main, noncanonical generators).
* build/sections/04-deletion.tex: full (prop:deletion-representation, lem:edge-table, lem:deletion-kernel, prop:projection-injective).
* build/sections/02-algebra.tex: lines 20–89 (lem:lie-lattice, finite and weighted alphabets); grep for representation terms elsewhere.
* Sections 03, 05–08, preamble and figures: not read. Source truth is stipulated, not audited.

## Primary literature

* Nisan 1991 (stored PDF): §§2–4 read, including the definition of M_k(f) and the proof sketch of Theorem 1; §§5–6 not read in full.
* Cagliero–Rojas 2020, arXiv:2006.04676v1 (author HTML copy): introduction and §1.1 including the higher-step conjecture and experiment tables (text lines 1–269); grep of upper-bound wording through the rest. §§2–4 proofs not read by this reviewer.
* Burde–Eick–de Graaf 2008, arXiv:0807.2345v1 (author HTML copy): §6.2 and Table 2 for N_{n,c}; grep hits elsewhere. §§2–5 not reread by this reviewer.
* Mazorchuk–Steinberg, arXiv:1107.1413v3 (author HTML copy): §7.1 including Theorem 24 and its proof, and the effective-versus-faithful terminology in §2 (grep). §§3–6 and §8 not read.
* Lewin 1974 I (ResearchGate OCR of pp. 293–308, mislabelled "II"): Lemmas 1–7 and statements of Theorems 1–17, with Theorems 9 and 11 read in context. Not every proof read; OCR quality limits. Lewin II not obtained. AMS PDFs: 403 or bot-challenge HTML, discarded.
* Burde–Moens 2010, arXiv:1006.2062v1: text lines 1–340 (§§1–3.3 start, including Lemma 2.10, Proposition 3.3); grep of §4 (filiform bounds), not fully read.
* Moens 2017, arXiv:1703.00338v1: abstract, §1 (Theorem 1.0.1, Corollaries 1.0.2–1.0.3, Birkhoff quotient remark), §5; §§2–4 not read.
* Moens 2009 dissertation: extraction lines 655–690, 915–940, 2310–2330, 4040–4100 only (trivial square-root lower bound, free nilpotent remarks, open problems).
* Cagliero–Rojas 2014, arXiv:1407.0226: abstract and introduction via the web tool (version not recorded); stored v1 PDF keyword-searched only.
* Gul–Weiß 2016, arXiv:1606.02247: abstract, introduction and open-problem remarks via the web tool (version not recorded); stored v1 PDF keyword-searched only.
* Wehrfritz 1995 Glasgow Math. J.: metadata only.
* Not obtained or not read: Lo–Ostheimer 1999; Lewin II; Reutenauer, Free Lie Algebras; Schützenberger and Fliess rational-series/Hankel realization; any truncated path algebra minimal faithful module paper; Hirose–Sato and the other source-cited GT antecedents.

## Searches

This session's recorded web searches: "minimal faithful representation free nilpotent Lie algebra upper bound r^{k/2} explicit construction"; "faithful module truncated tensor algebra dimension square root number of words prefix suffix construction"; "free nilpotent group rank r class c faithful unitriangular representation dimension smaller than 1+r+...+r^c"; "nilpotent algebra of words faithful representation dimension free nilpotent associative algebra minimal matrix size truncated free algebra". Earlier searches in the same review located Lewin, Wehrfritz, Nisan, Gul–Weiß, Cagliero–Rojas 2014 and Burde–Moens; their exact query strings were not logged. Search engines are not exhaustive. No novelty or priority certificate follows.

## Proof and computation limits

* No proof verdict. The candidate's proof was assumed correct for classification only.
* The reviewer's unweighted remark (review.md §4) has its own three-line proof. It was not independently reviewed. reviewer-sanity.py checks one finite case (r=2, m=n=4, 61 states, 510 words) and is an illustration, not evidence for any general statement.
* Hashes, inventory checks and mutation controls authenticate bytes only. No mathematical inference is drawn from them.
