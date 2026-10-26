# Graph-normalization adjacency inequality

MathDB349070. Full Lean proof, independently reviewed and verified.

- [Written proof](PROOF.md)
- [Paper source](main.tex)
- [Lean](formal/GraphNormalization.lean)
- [Primary-source provenance](primary-reference.json)

The extracted release includes `verify_outcome.py`, `build_paper.py`, and dependency pins. From the release root run `python3 verify_outcome.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages`. In this campaign checkout use `../../verify_outcome.py` instead. The result is a known majorization consequence, not a proof of general iterative convergence.

See [review](review.md) and [verification receipt](verification.json).
