# Reading and search limits: T337E proof review r1

Review prose CC BY 4.0.

## Read in full

* `AGENTS.md`, `sources/upstream.json` (pin `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`), and the status and acceptance section of `frontier/NEW-TEN-2026-10-14.md` (lines 1–24). The count was given no weight.
* Parent context, as context only: `t337e-parent/proof-r1-dispatch.txt` and `t337e-parent/sealed-preflight.json`.
* Frozen author packet `fresh-analytic-discovery-r58/`: `proof.md` (all 225 lines), `original-scope.txt`, `checkpoint.md`, `source-map.md`, `contribution.md`, `reading-limits.md`, `337-working-interface.md`, `formal-plan.md`, `verify.py`, `controls.py`, `diagnostic.py`, `controls-result.json`, `diagnostic-result.json`, `lytchak-retrieval.json`, `lytchak-web-reading.json`, `stadler-receipt.json`. Other receipt files and `canonical-bindings.json` were run through the author verifier but not used by the reviewer's own source check.
* Source337 (`private/source337/`, authenticated against the canonical tree): `01-introduction`, `02-currents`, `03-radial`, `04-sobolev`, `05-minimizer`, `06-chords`, `07-conclusion`, `08-classical`, in full. This includes `thm:main`, `lem:compact-reduction`, `thm:current-background`, `lem:extremizer`, `eq:normalization`, `lem:quadratic-mass`, `lem:euclidean-chart-metrics`, `prop:radial`, `prop:base`, `prop:small-set`, `prop:sobolev-space`, `prop:compact-embedding`, `prop:minimizer`, `prop:chord-transform`, `lem:chord-density`, `rem:chord-sphere`, the variance argument and `lem:top-dimensional-constancy`.
* Stadler, arXiv:2212.07100v1, author copy `private/stadler2212.txt` lines 760–999: Appendix A opening, Proposition A.1 with its full proof, Sublemmas A.2–A.3 and Corollary A.4. This is the source of R1.
* Lytchak, *Differentiation in metric spaces*, archived preprint (receipt below), local `private/lytchak-wayback.txt` (pdftotext 26.01.0, 1476 lines): lines 230–279 (§1, including Theorem 1.6), lines 335–984 (§§3–8 and the first lines of §9: ultralimits, Busemann functions and Example 4.2, cones and completion §5.1, CAT(κ) cones and exp §5.3, tangent spaces and Example 6.8, Remark 6.12, differentials and §7.7 strong differentiability, §8), and lines 1340–1477 (the last lines of §11, §12 and references).

## Not read

* Lytchak local lines 985–1339 (§9 after its opening example, and §§10–11). The reduction of Theorem 1.6 for n>1 to n=1 in §12 ("standard reasoning ([Kir94] and [MM00])", Kirchheim and Margulis–Mostow) was read but not re-proved. Theorem 1.6 is a published theorem; I used its statement and the definitions it depends on.
* The equivalence of the archived preprint to the published St Petersburg Math. J. text was not verified. Its numbering is preprint pages 1–34.
* Stadler outside lines 760–999. Only Appendix A is a premise.
* The author copies of smooth337, source081, Schulze, Basso, Tolsa and NTV. Smooth337 and source081 were only identity-checked against the canonical tree (16 and 13 blobs). None of these is a premise of a step I validated; proof.md's operative citations are source337, Lytchak and Stadler, plus standard facts.
* Source337 `paper.tex`, bibliography and the source PDFs (`paper.pdf` files were not copied by the author).
* The parallel proof reviewer's draft and any T337E contribution review. These were deliberately not opened.

## Standard facts used without a separate primary read

Each is textbook-level or re-derived in `review.md`: 1-Lipschitz nearest-point projection onto closed convex subsets of complete CAT(0) spaces; existence of asymptotic rays and Busemann functions in complete CAT(0) spaces; the flat strip theorem and the product decomposition of the parallel set of a line; McShane extension; Federer's constancy theorem (4.1.31); flat-norm continuity of pushforwards under uniformly Lipschitz maps converging uniformly (straight-line homotopy formula); monotonicity of the density ratio for area minimizers in CAT(0) spaces (as stated in Stadler A.1).

## Retrieval and search

* The dispatch reported that the full Lytchak PDF could not be retrieved. I tried MathNet (timed out) and the Semantic Scholar API (HTTP 429). The general fetch service returned HTTP 500; `curl` was used directly.
* Success: `http://web.archive.org/web/20250418194602id_/http://www.mi.uni-koeln.de/~alytchak/preprints/differentiation.pdf`, 311187 bytes, PDF SHA256 `8c1b70c128c6b9f19fbd887e107346dd808c75c7c2303bbf9b0a5534a64a6595`, 34 pages, PDF title metadata `g6-lyt-2.dvi`, created 2012-11-20. Text extraction `pdftotext -layout` SHA256 `dd65a02883ed70bab4a7b910ef61a62526fb2067ab5bae5553dae72273a36e31`. Both are kept in ignored `private/` and are sealed in `manifest.json`.
* No literature or novelty search was performed. This is a proof review, not a contribution review.

No checksum in this packet is mathematical or novelty evidence.
