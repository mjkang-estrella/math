# Global convexity of the Bernstein basis square-sum

MathDB327180; one outcome. Related327181 and327182 are corollaries in the same packet and are not counted again. Known mathematical result, formally verified through a finite Fourier identity.

[Paper](main.tex), [proof](PROOF.md), [Lean](formal/BernsteinShape.lean), [source provenance](PROVENANCE.md).

An extracted release includes `verify_outcome.py`, `build_paper.py`, and dependency pins. Rebuild with `python3 verify_outcome.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages`. In this campaign checkout use `../../verify_outcome.py` instead. Full third-party sources remain in the development lane.

[Independent review](review.md) and [verification receipt](verification.json) certify this complete known-result formalization.
