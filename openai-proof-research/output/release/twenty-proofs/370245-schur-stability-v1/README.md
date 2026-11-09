# A rational counterexample to both Schur stability assertions

MathDB370245; one outcome. Full Lean certificate, independently reviewed and verified. Both universal stability assertions fail in the same example; the two operators are not counted separately.

[Paper](main.tex), [complete proof](PROOF.md), [Lean](formal/SchurStability.lean), [source provenance](metadata.json).

The extracted release includes `verify_outcome.py`, `build_paper.py`, and pinned dependencies. Run `python3 verify_outcome.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages`. In the campaign checkout use `../../verify_outcome.py` instead. Source paths in historical lane metadata refer to `frontier/campaigns/2026-10-25/schur-stability-lane/`; full third-party texts remain there.

This is a formal verification of a specialization of Patel's posted family, with no mathematical novelty claim. The actual matrix inverse, full complex spectra, and exact spectral radii are part of the certificate.

[Independent review](review.md) and [verification](verification.json) bind the full certificate and paper.
