# Progress and checkpoints, structural round 16

Myeongjin Kang; no affiliation. 2026-10-16. Prose CC BY 4.0.

## C0. Setup and authentication
- Read AGENTS.md and the brief, and snapshotted context
  (`inputs/context/`).
- Authenticated LR-r2 against the external seal 06c49552…8c3e4:
  34 files, 6 directories, payload 1566297 bytes
  (`inputs/lr-r2-authentication.json`). A wrong anchor was rejected.
- Surveyed all 372 catalogue families and the complete
  preprints-tree.json, and excluded families used by earlier rounds and
  the brief. Chose family 156 (Borsuk failure in dimension 9).

## C1. Source reading and screening
- Retrieved 14 files from pinned raw URLs. Read the 11 TeX/README files
  in full (extents in `source-contracts.md`). Blob SHA-1s were later
  verified, all equal to the tree.
- Screening: Kalai 1505.04952v1 (retained) and web searches.
- Identified the complex analogue X ⊂ R^8, one dimension lower, and the
  Hesse-SIC hole obstruction.

## C2. Freeze
- `original-scope.md` was frozen at 2026-10-16T15:35:49Z, SHA256
  133c0d45fdd9f4a1c328dee664b142ac2cf09c6d0600fcc1ed53bdb565dea838.
  It is unchanged since (re-hashed in the manifest).

## C3. Lower bound (Theorem A)
- A first idea, averaging f over the eigenspaces of A, is NOT continuous
  where eigenvalues merge. Example: diag(1 + 1/n, 1, 0). Rejected.
- Replaced it by the source-style square-root integral
  E(Q) = 3∫H(Q^{1/2}u)dμ, re-proved in the Hermitian setting. The odd map
  S^8 → S^{m−1} gives m ≥ 9.

## C4. Hole structure
- Corrected a screening misstatement: hole–SIC overlaps are 0 and 1/2,
  not 1/3. The holes are the 12 MUB vectors, with M_0 = 1/2 there. The
  covering value of the Hesse SIC is exactly 1/2 (Lemma 9, proved by the
  elementary p_j / phase inequality).
- Bessel: orthogonal pairs inside a closed cell occur only at hole
  pairs, and they do occur there, so every closed cell has diameter
  exactly √2.

## C5. Upper bound (Theorem B, Corollary C)
- First-order analysis at a hole. The six neighbour functionals split
  into two 120° trios in z_2 and z_3. min-max duality shows that one
  trio's average gain must be positive.
- Bipartite orientation: 12 lines and 12 holes form 4 triangles, so a
  cyclic orientation lets each hole be favoured once.
- The four latitude functionals at s_0 are R-independent, and the
  explicit d_0 = (1 + i)(0, 1, 1)/2 is positive on all four favoured
  poles (κ ≥ 1/√24). WH covariance spreads this to all nine points.
- Explicit local constants: r = 1/(12√3), ε ≤ 1/50. The far region is
  handled by compactness.
- Diagnostic `tools/diagnose_b8c.py` (output in `diagnostics/`) agrees.
  Sampled minimum of M_ε: 0.504 at ε = 0.01. This is evidence only.

## C6. Write-up and integrity
- candidate.md (full proof candidate), source-contracts.md,
  primary-comparison.md, README.md, status.json.
- Manifest, detached seal, read-only verifier, and unchanged-source
  receipts.

## Not done
- No independent review, explicit η, interval certificate, manuscript,
  Lean, commit or staging.
