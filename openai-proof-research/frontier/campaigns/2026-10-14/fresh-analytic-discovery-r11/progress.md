# Progress log: fresh analytic discovery r11

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

## Checkpoint 0: continuity and inventory

* Read AGENTS.md, sources/upstream.json, the current ledger
  frontier/NEW-TEN-2026-10-14.md, the full mandatory
  fk-frechet-parent/fresh-r9-brief.txt (F candidate, F contribution review,
  parent corrections P1-P4, dispositions), and the embedded r10 / Coulomb r2
  reports and parent responses in the assignment.
* Family-level catalogue entries (sources/CONTENTS.md) for the analysis,
  probability, PDE, geometry and dynamics families were scanned, and the
  historical iteration/campaign topic list (887 iteration files) was searched
  by keyword to find source families never used as a research lane.
* Families with zero historical lane hits include: 153 (Bernoulli
  convolutions), 375 (De Giorgi / Allen-Cahn), 086/083/082 (singular
  integrals), 352 (Calabi flow), 327 (Markov type), 333/334 (isometric
  immersion), 349 (Solomon-Yau), 226/233 (double dimer, Ashkin-Teller).
* Excluded lanes retained: Coulomb/Riesz/contact calibration (P, two attempts),
  C, U, H, B, T2, EPnI, BG4, Liouville, restricted-host mixing, Randers,
  three-state reconstruction, FK F/G and the alpha=1/2 endpoint, SAT,
  ball-slab, Bell, scalar/nilpotent variance, W11 affine subtraction, poly-Zp,
  permanence (I-intermittent-rate-permanence), hot spots (neumann-eigenmap),
  Brenier, Erdos similarity (I36), standard map, Artin R, crossing.

## Checkpoint 1: first serious screen, family 153

Pinned source files for family 153 downloaded to inputs/private/source-153/;
all eight Git blob SHA1 values match sources/preprints-tree.json.

## Checkpoint 2: target chosen and scope frozen (2026-10-16T12:45:16Z)

* Read sal:main / sal:construction / sal:loss in full (salem.tex), np:main
  (nonpisot.tex), main.tex introduction, references.bib.
* Primary literature screen: Cheng-Fang-Ma-Zhang arXiv:2610.12072v2 (strict
  Hausdorff-dimension drop for every quartic Salem number; entropy Lemma 2.1
  with a 2 log N separation term), arXiv:2610.09902v1 (correlation dimension,
  quartic in (1,2)), Marshall-Maldonado-Solomyak arXiv:2601.15035 (log*-type
  Fourier decay only), Dajani-Kalle arXiv:1708.05544 (withdrawn). No
  degree >= 6 Salem result found.
* Quartic-only paid; frozen target T: singularity of nu_{1/beta_6} for the
  sextic Salem root of x^6-x^4-x^3-x^2+1.
* original-scope.md sha256 143778fc32d5eb1f668b4b941ad1bd184b19c71b1bfb2792bee78b1effdd2bdd
  (file set read-only).
* Screening heuristic already recorded: with product multipliers
  prod(beta^k - beta^-k), the action doubles per factor while simultaneous
  Dirichlet approximation of two angles gives at most a factor
  1 + 2/(d-1) = 2 growth of log(1/delta) in degree 6 (critical), before the
  lower constraint k >= 2 b_m is imposed.

## Checkpoint 3: proof attempt, first pass (2026-10-16)

* Route chosen: finite-scale entropy route (one seed suffices) instead of the
  pinned infinite-recursion route. Derived a seed criterion valid for every
  Salem degree 2d (separation exponent 2(d-1) log N); constants for beta_6:
  q = 3, Q = beta^3 = 2.7515, C_{beta,Q}(1/2) about 6.33.
* Reduction: T follows from one A in Z[beta_6] with
  2(L - Lambda) - sqrt(2 Lambda) > log(32 e pi^2 q / gamma^2)
  + log(4 log N + C). Roughly L - Lambda >= 8 is needed.
* Numerics (evidence only, scripts/salem_numerics.py, scripts/seed_search.py):
  greedy product chains for beta_6 have Lambda/L from 70 rising to 3400;
  the quartic control chain falls from 13.8 to 10.3. Local search over
  {-1,0,1}-polynomials of degree <= 80 (A != 0) gives best L - Lambda about
  -5.3, far from +8.
* Obstacle under investigation: product multipliers double the action per
  factor, and two-angle Dirichlet growth with lower constraint k >= 2b is at
  best critical.

## Checkpoint 4: final (2026-10-16)

* Outcome: UNRESOLVED. Target T neither proved nor disproved. Not counted; no
  self-PASS.
* Proved in candidate.md: Theorem S (finite seed criterion, every degree),
  Corollary S' (beta_6 constants: q = 3, Q = 2.7515, R = 3.4921,
  C_sep = 10.95, C_{beta_6,Q}(1/2) = 6.33), Proposition O1 (sharpness up to
  constants), Proposition O2 (action doubling for product multipliers).
* Correction: R was misprinted as 3.4925 in candidate.md; verify.py computes
  beta/(beta-1) = 3.4921 and the text now says so. No other number changed.
* Unpaid operation: the seed problem for beta_6. Product multipliers are
  critical in degree six (Section 4.2), and the searches found no seed.
* Deliverables: README.md, RIGHTS.md, git-identities.json, verify.py
  (read-only), inputs-manifest.json, outputs-manifest.json,
  verify-receipt.json, seal.json, seal.sha256.
