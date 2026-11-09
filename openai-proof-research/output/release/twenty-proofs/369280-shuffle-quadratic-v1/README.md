# Quadratic eigenvector of the one-shelf position matrix

MathDB 369280. Independently reviewed and verified.

Known mathematical result: special case of Tripathi, arXiv:2602.07920v1, Theorem I. New-to-this-package Lean verification; no priority claim.

Complete proof: [PROOF.md](PROOF.md); paper: [main.tex](main.tex); Lean: [formal/ShuffleQuadratic.lean](formal/ShuffleQuadratic.lean).

The release includes `verify_outcome.py` and dependency pins. Run `python3 verify_outcome.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages`. In the campaign checkout use `../../verify_outcome.py`.

See [independent review](review.md), [verification](verification.json), and [audited declaration list](formal/Checks.lean).

The supplemental exact-rational and mutation experiments described in the paper live in the development checkout at `frontier/campaigns/2026-10-25/shuffle-quadratic-lane/verification/`. Those optional scripts are not included in this standalone release; the universal Lean proof and its verifier are included.
