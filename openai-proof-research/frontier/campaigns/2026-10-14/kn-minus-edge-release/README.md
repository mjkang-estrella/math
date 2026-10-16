# Complete graph minus an edge: local release preparation

Myeongjin Kang, no affiliation. Original prose CC BY 4.0; original code MIT.

This preparation combines the revised 15-page paper, reproducible finite checks,
scoped Lean sources and the independent audit evidence. The complete mathematical
claim covers every n >= 2 and every edge of K_n, in ordinary crossing number.
The path-product corollary covers every m >= 4 and paths of n >= 1 edges and is
one application of the same result. The new lower-bound range is odd complete
orders n >= 15; its new product input is odd m >= 13 and path length n >= 2.

The pinned upstream statements are stipulated mathematical premises. The new
proof has an independent proof PASS and a separate substantial-contribution
review. No worldwide priority is certified. The original manuscript audit asked
for three documentary/reproducibility repairs; the r2 paper implements them.
The final independent revision gate is pending in this preparation. Assembly
refuses a pending gate. This directory alone awards no acceptance or count.

After assembly, `FINAL-GATE.json` records the actual parent integration of the
independent revision audit. Its evidence is bound by an externally supplied hash.
Historical pending/count fields inside frozen author and review files retain
what was true at their creation; they are not silently rewritten. This README
records preparation history, not an assertion that a final gate has occurred.

Paper and complete manuscript public payload:
`frontier/campaigns/2026-10-14/kn-minus-edge-manuscript-r2/main.pdf`.
Formal sources: `frontier/campaigns/2026-10-14/kn-minus-edge-formal-v1/`.
Independent formal review: the neighboring `kn-minus-edge-formal-review-r1/`.

The full crossing theorem is **not formalized**. See `FORMAL-COVERAGE.md`.
`REPRODUCTION.md` distinguishes portable checks from historical repository-only
commands. `RIGHTS.md` explains the explicit public selection. Local Zenodo and
MathDB metadata have no DOI, account, routing or submission identifiers.
Nothing has been publicly uploaded or submitted.
