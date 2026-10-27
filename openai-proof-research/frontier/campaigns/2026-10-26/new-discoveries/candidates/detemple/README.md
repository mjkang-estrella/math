# DeTemple complete-monotonicity threshold: literal interior refutation

This packet contains one result about Yang--Chu--Zhang Conjecture1(ii), related
to MathDB328867. There exists a strictly positive parameter a<155/294 for which
the literal function -G_a is not completely monotone on(0,infinity). The Lean
proof gives actual positive midpoint witnesses using psi=Gamma'/Gamma. It proves
the negation of the sufficient-condition assertion, with no residual premises.

The separate explicit rational point a=527/1000,x=1/50 is a mathematical
certificate, not an asserted Lean endpoint. Conjecture1(i), an optimal replacement
threshold, and absolute priority are unclaimed. The whole MathDB record is not
declared resolved because it includes the separate part(i).

## Read and replay

- paper.pdf/main.tex: final two-page manuscript; mathematics unchanged from review.
- formal/SourceDefs.lean,LogObstruction.lean,SourceEndpoint.lean: literal proof.
- verification/verify_candidate.py and pins.json: strict reproducible verifier.
- reviews/final/review.md: independent five-gate review, including access limits.
- check_certificate_corrected.py: current optional rational arithmetic check.
- PRELIMINARY-RECONCILIATION.md: the old checker defect and its correction.

Run the verifier with the pinned Lean4.34.1 binary and pinned package directory:

    python3 verification/verify_candidate.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages

The expected result is21 declarations in3 modules, empty module logs, and only
propext,Classical.choice,Quot.sound. Source dependencies and versions are pinned
in verification/pins.json. The local project toolchain paths are recorded in the
review provenance. No new axiom or externally asserted digamma identity is used.

## Provenance and historical files

All45 independently reviewed originals are preserved byte-for-byte, including
the old credit0/status snapshots. reviewed-parent-hashes.json and
reviewed-file-locations.json bind their exact locations. Only main.tex,paper.pdf,
and paper-qa.json have presentation-only release versions; their reviewed originals
are under reviewed-originals/. The frozen formal/verifier bytes are unchanged.

PROOF.md,STATUS.md,FORMAL-ADDENDUM.md,candidate.json and the original checker
contain historical pending-status wording. This README, the final review and any
subsequent acceptance.json supersede that wording. The original check_certificate.py
omits a constant in its auxiliary general-a symbolic identity; it is retained
solely as a review record. Use check_certificate_corrected.py instead. Neither
checker is a premise of the Lean proof.

The independent review found no prior or subsuming resolution in a bounded
screen. One Yang--Tian JMAA gamma-ratio-remainder body remained paywalled; no
comprehensive MathSciNet/zbMATH search or worldwide-priority guarantee is claimed.
The archived candidate keeps credit0 until the parent records a successful fresh
extracted replay in a separate acceptance.json. That post-replay record is outside
the deterministic immutable archive.
