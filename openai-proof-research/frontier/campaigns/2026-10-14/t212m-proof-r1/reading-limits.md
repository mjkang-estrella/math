# Exact reading limits of this review

Paths are relative to `frontier/campaigns/2026-10-14/fresh-analytic-discovery-r74/`.
Line numbers refer to the files whose SHA256 values are recorded in checks.json.

## Author packet, read in full

candidate-proof.md, dependency-map.md, cap-author-cap-core.md,
cap-author-shape-and-length.md, cap-shape-interface.md,
dh-limiting-coupling.md, cubic-wall.md, structural-author-bridges.md,
ah-6-8-integration.md, ah-9-10-integration.md, same-status-lowering.md,
label-stability-interface.md, stationary-extension-cocycle.md,
parent-author-extension-cocycle-linearity.md,
parent-author-halfplane-transfer.md,
parent-author-status-preserving-perturbations.md, tail-and-modification.md,
comparison-and-dependencies.md, README.md, validation-limits.md, verify.py,
controls.py.

## Author packet, not read

mechanism.md (historical linear-cap note; its bigeodesic argument is restated
in candidate-proof.md §3 and tail-and-modification.md, which were read),
cap-author-checkpoint.md, the author's reading-limits.md, interface-checker.py,
and the JSON receipts other than the top-level keys of manifest.json. Their
SHA256 identity was checked through the author manifest, not their content.

## Primary sources (packet `private/`)

ahlberg-hoffman-v2.txt: lines 200–224, 255–294, 300–978, 1340–1359,
1590–1749, 1935–2614, 2679–3098, plus grep hits for "tangent" (195, 210, 268,
286, 753, 792, 813, 821, 824, 837, 2749, 2897–2898, 3547, 3560, 3895).

damron-hanson-v1.txt: lines 135–214, 1140–1164, 1330–1609, plus grep hits at
277 (A2'), 325 (Definition 1.9), 334, 364–372 (Theorem 1.11), 559, 582, 592, 604
(line family definitions), 1008, 1189, 1338, 2130–2143, 2289–2305.

Source212 (`private/preprints/No-bigeodesics-in-planar-first-passage-percolation-September-24-2026/build/sections/`):
01-introduction.tex lines 1–49 (theorem statement 24–37); 02-preliminaries.tex
in full; 03-sectors.tex partially, plus a whole-file search showing no
independence, resampling, absolute-continuity, product, ergodicity,
stationarity or translation step; 04-exceptional.tex, 05-budget.tex,
06-forks.tex, 07-tilts.tex, 08-conclusion.tex in full;
09-boundary-comparison.tex not read (cited by the author only as an
alternative route; see review O6). A whole-directory search for moment and
expectation uses was run.

Not read: adh-v2, cerf-theret-v2, pattern-v1, the strict-convexity companion
manuscript, and all PDF renderings. None is a premise of the essential chain.

## Statement-level reliance

Proof bodies of DH Sections 3–5 (other than the ranges above) and of AH
Sections 4, 6, 7 and 10 were relied on at statement level after checking
their hypotheses for the cap metric and locating every finite-energy use
(AH Remark 3.2; AH 8.6; AH 9.5–9.10; DH Section 6).

The parallel review directory `t212m-parent` was not opened.
