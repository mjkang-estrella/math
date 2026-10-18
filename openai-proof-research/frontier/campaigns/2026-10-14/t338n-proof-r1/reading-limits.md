# T338N review round 1: precise reading record

Every path below is relative to the repository root
`/home/mj-kang/Documents/Dev/math/openai-proof-research` unless absolute.
"Full body" means every line of the file was read. Hash verification status refers
to the packet's anchor/receipt chain, all of which matched byte-identically
(see review.md, integrity section).

## Campaign rules and catalogue

- AGENTS.md — full body.
- frontier/NEW-TEN-2026-10-14.md — full body (campaign rules; pinned upstream
  theorems stipulated true at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb;
  review-only role; write only the assigned directory).
- sources/preprints-tree.json — hash-verified against its external anchor;
  structure inspected (13223 entries, truncated=false); used to confirm exactly
  one uniformization manuscript family (13 text blobs + paper.pdf).

## Frozen author packet (frontier/campaigns/2026-10-14/fresh-analytic-discovery-r89/)

Full body, anchors verified:
- MANIFEST.json, candidate.md, scope-status.json, completion.json,
  nonnegative-flow-bridge.md, local-null-propagation.md,
  fixed-time-factorization.md, comparison.md, reading-limits.md,
  mechanism-checkpoint.md, README.md, source-receipts.json, primary-receipts.json,
  interface-results.json, check_interfaces.py, verify.py.

verify.py was read before execution and then run with the prescribed arguments;
result PASS_IDENTITY_ONLY (16 public files, exit 0).

## Private source338 bodies (hash-verified against pinned Git blobs)

Full body:
- private/build/sections/preliminaries.tex (479 lines)
- private/build/sections/flow.tex (878 lines)
- private/build/sections/charts.tex (1070 lines)
- private/build/sections/discs.tex (703 lines)
- private/build/sections/variation.tex (895 lines)
- private/build/sections/ellipsoids.tex (522 lines)
- private/build/sections/introduction.tex (258 lines)
- private/build/main.tex (inclusion order and authorship header)

Not read (bodies): dynamics.tex, uniformization.tex. Reason: the deduction applies
only the source's MAIN theorem, stated in introduction.tex, as a stipulated
black box at its original strict hypotheses; the proof of that theorem is upstream
truth under the campaign rules and outside this audit.

Targeted grep census across preliminaries/flow/charts/discs/variation/ellipsoids
for strict/positive curvature usage: all hits accounted for in review.md (two
strict inputs total: the replaced Busemann/Richberg construction and the discarded
charts.tex strict contraction/covector steps; everything else unrelated).

## Private primary extractions (hash-verified)

- private/ni-tam.txt, lines 1755–1864: Thm 4.2(i) statement and proof, Remark
  4.1(a)(c). Verified: splitting M = N x M'; N compact simply connected; M'
  complete noncompact with smooth strictly psh bounded-gradient psi; no curvature
  upper bound in the hypotheses; N's classification credited to
  Mok/Howard–Smyth–Wu; M' simply connected via the product.
- private/gu.txt, lines 1–120: Thm 1.1 (compact generalized Frankel), proof
  skeleton via orthonormal 2-frame bundle P and HSW reduction. The
  orthonormal-frame (vs all-pair) convention confirmed here.
- private/survey.txt, lines 650–1069: Cao–Chen–Zhu Thm 2.8 statement and full
  proof: bounded + nonnegative bisectional hypotheses; P = all ordered nonzero
  pairs; Mok reaction inequality via phase-averaged perturbation (lines 893–958);
  reaction equation and zero-set invariance via Brendle–Schoen Prop 2
  (lines 959–1000); rotation expansion and conclusion (lines 1014–1044).
- private/brendle-schoen.txt, lines 1–240: Prop 1 (local, Omega open in R^n,
  compactly supported coefficients) and Prop 2 (compact base). The author's
  localization uses Prop 1 on chart covers of compact path images; Prop 2 unused.
- private/beauville.txt, lines 74–198: de Rham with "compact" replaceable by
  "complete"; Berger list; SU(m) iff Ricci-flat; Sp subset SU.
- private/liu.txt, lines 1–120: Thm 1.1 statement (maximal volume growth
  case). Confirmed unused in the deduction (paid-class boundary only).
- private/berger.txt: spot check at line 2032 (Ch III §9 Thm 3; imperfect OCR as
  the author flags). Berger's full classification proof not read; the Berger list
  is used as a named classical theorem per campaign convention.
- The eight private PDF companions were not independently re-read; their text
  extractions above are hash-verified against the pinned blobs.

## Not consulted

Original de Rham and Mok paper bodies; any companion papers of source338; any
external literature beyond the packet's private extractions; any shared ledger or
other campaign directory (read-only awareness of t338n-parent's existence only).
