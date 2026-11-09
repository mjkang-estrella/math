# Four algebraic properties of signed-set fusion

MathDB [366458](https://mathdb.com/p/366458). Status: independently reviewed and verified.

Four explicit algebraic assertions in the source signed-set model; no foundational set-theory claim.

- [Paper source](main.tex) and release `paper.pdf`
- [Complete written proof](PROOF.md)
- [Lean certificate](formal/SigmaFusion.lean)
- [Independent review](review.md)
- [Coverage](coverage.json) and [verification record](verification.json)
- [Source record](source.json) and [primary-source provenance](primary-reference.json)

All 25 local declarations compiled with Lean 4.34.1 and the pinned mathlib dependencies, using only standard foundational axioms. The release includes the verifier and dependency pins. From an extracted release directory, run:

```sh
python3 verify_outcome.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages
```

For this campaign checkout, run `python3 ../../verify_outcome.py .` instead. Dependencies must already be compiled. The verifier creates a fresh isolated source copy and reports every local declaration and its axioms. Release receipts record the original build; `formal/Checks.lean` preserves the audited declaration list. To rebuild the paper, use the included `build_paper.py` with `--tectonic /path/to/tectonic` and an available TeX cache. The generated two-page PDF was rendered and visually inspected.
