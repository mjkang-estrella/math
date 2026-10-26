# Endpoint correction for positivity rigidity

MathDB325243; Conjecture11 in arXiv1303.6651v1. Independently reviewed and verified.

The printed conclusion constrains p_(s+1), although no premise includes that coefficient. This is a literal endpoint correction, not a disproof of the intended coefficient-rigidity problem after that endpoint is removed.

[Paper](main.tex), [written proof](PROOF.md), [Lean](formal/PositivityRigidity.lean), [source record](source.json).

An extracted release includes `verify_outcome.py`, `build_paper.py`, and pinned dependencies. Run `python3 verify_outcome.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages`. From this campaign checkout use `../../verify_outcome.py`.

See [independent review](review.md) and [verification](verification.json).
