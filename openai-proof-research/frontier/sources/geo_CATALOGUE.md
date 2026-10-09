# Geometry scout source catalogue (prefix geo_)

Retrieved 2026-10-08. Upstream pinned at openai/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Raw base: https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/<dir>/<file>

## geo_pdf/ (pinned upstream PDFs; .txt = pdftotext -layout)

| sha256 | file |
|---|---|
| `3467c8077855a568…` | geo_pdf/Abelian-covers-Gale-correspondences-and-the-Hodge-conjecture-for-powers-October-6-2026.pdf |
| `a6a00fc2a23a2b34…` | geo_pdf/Abelian-covers-Gale-correspondences-and-the-Hodge-conjecture-for-powers-September-30-2026.pdf |
| `e59953bdc640de5f…` | geo_pdf/A-Conditional-Reduction-for-Algebraic-Kuga-Satake-Correspondences-September-10-2026.pdf |
| `e52ae0e71ab4c7b5…` | geo_pdf/A-high-arity-counterexample-to-Pixton-completeness-in-Chow-September-24-2026.pdf |
| `8e46fd4f5d330e8b…` | geo_pdf/Algebraicity-of-Kuga-Satake-Correspondences-for-K3-Surfaces-October-3-2026.pdf |
| `205469761edcdec9…` | geo_pdf/Algebraicity-of-Weil-classes-on-split-abelian-eightfolds-September-18-2026.pdf |
| `c9fde2b758f25505…` | geo_pdf/Algebraic-Kuga-Satake-correspondences-and-Hodge-conjectures-on-a-K3-quadratic-locus-September-30-2026.pdf |
| `afb7bf56f8d97111…` | geo_pdf/Blochs-Conjecture-for-Surfaces-with-pg-equals-q-equals-0-September-24-2026.pdf |
| `d3ecf115570d0b89…` | geo_pdf/Elliptic-Squares-and-Zilber-Pink-for-Curves-in-A2-September-24-2026.pdf |
| `73aefa0b0e5578df…` | geo_pdf/Fujitas-freeness-conjecture-September-23-2026.pdf |
| `c35e20c01dcefe76…` | geo_pdf/K3Oka.pdf |
| `146466e3aa616985…` | geo_pdf/Kobayashi.pdf |
| `640701a0ea8d8026…` | geo_pdf/Milnes-rationality-conjecture-for-abelian-varieties-October-7-2026.pdf |
| `b3fe604d79a47008…` | geo_pdf/Milnes-rationality-conjecture-for-abelian-varieties-September-23-2026.pdf |
| `53e8f20495ac6168…` | geo_pdf/The-Abelian-Zilber-Pink-Conjecture-September-24-2026.pdf |
| `fd6298d9c106fea9…` | geo_pdf/The-E-times-CM-Component-of-Zilber-Pink-for-Curves-in-A2-September-24-2026.pdf |
| `6e3e66a407773ad5…` | geo_pdf/The-rational-Hodge-conjecture-for-CM-abelian-varieties-October-6-2026.pdf |
| `b8bdfb9767cc20f2…` | geo_pdf/The-rational-Hodge-conjecture-for-CM-abelian-varieties-September-30-2026.pdf |
| `48515a3987802b29…` | geo_pdf/The-rational-Hodge-conjecture-for-products-of-K3-surfaces-October-4-2026.pdf |
| `c035db86eb706573…` | geo_pdf/Weil-classes-and-Hodge-classes-on-abelian-powers-October-6-2026.pdf |
| `ef66240969f38c9a…` | geo_pdf/Weil-classes-and-Hodge-classes-on-abelian-powers-September-30-2026.pdf |

Upstream path for each geo_pdf/<dir>.pdf is preprints/<dir>/<file> as listed in geo_pdf/list.txt, plus:
- Kobayashi.pdf = preprints/Canonical-ampleness-of-compact-hyperbolic-Kahler-manifolds-September-23-2026/canonical-ampleness.pdf
- K3Oka.pdf = preprints/Every-complex-K3-surface-is-Oka-September-23-2026/paper.pdf

Three files are withdrawal notices (ReportLab PDFs, revision adc7f1241b42e322a6451854ab7e4b4c146bf78a archived): products of K3 surfaces (Oct 4), Kuga–Satake algebraicity for K3 (Oct 3), Weil classes on split abelian eightfolds (Sep 18).

## geo_lit/ (external literature)

| sha256 | file | source |
|---|---|---|
| `4b4dec800eeebd3f…` | geo_lit/gt-v30-n3-p08.pdf | https://msp.org/gt/2026/30-3/gt-v30-n3-p08-p.pdf (Floccari, G&T 30 (2026) 1129–1154) |
| `66de41ca6bc19428…` | geo_lit/moonen-zarhin-math9901113.pdf | https://arxiv.org/abs/math/9901113 (Moonen–Zarhin, Math. Ann. 315 (1999)) |

## geo_mathdb/ (MathDB API snapshots)

Endpoints used: https://mathdb.com/api/search/suggestions?q=…, https://mathdb.com/api/search?q=…, https://mathdb.com/api/posts?importance=<band>&tag=<tag>&limit=100&offset=…, https://mathdb.com/api/posts/<uuid>. Valid importance bands (server message): landmark, celebrated, erdos, named, corpus. Files: list_landmark.json, list_celebrated.json (40 items), named_algebraic_geometry.json (636 items, tag algebraic-geometry), and per-problem records p_<number>.json / <uuid>.json.
