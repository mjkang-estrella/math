# Taxicab three-halves candidate (MathDB341671)

Status: full mathematical/source/formal review PASS; strict novelty HOLD. Discovery credit: **0** until the remaining novelty question is resolved.

The proof establishes the source inequality for the ordinary topological interior of every nondegenerate triangle in arbitrary coordinates, using explicit L1 vertex distances and the primary source's supporting-line distance formula. The stronger closed-convex-hull version and a sharpness family are also verified. Sharpness is known prior work and is not a new discovery.

- `main.tex` and `paper.pdf`: complete paper, labelled research draft.
- `formal/Scalar.lean`: scalar concavity, threshold simplex and weighted extension.
- `formal/TaxicabGeometry.lean`: exact coordinate formula and barycentric bounds.
- `formal/TaxicabErdosMordell.lean`: actual convex hull/interior theorem and sharpness.
- `reviews/`: independent mathematics, source, prior-art and formal reviews.
- `sources/provenance.json`: primary sources and hashes.
- `verification/audit.json`: fresh all-declaration audit; 55 declarations, only propext, Classical.choice and Quot.sound.

## Replay

Use Lean4.34.1 and the exact mathlib/dependency commits in `verification/pins.json`. Set paths to an existing checkout of these dependencies, then run:

```sh
python3 verification/verify_candidate.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages
```

The verifier checks dependency commits and tracked-file cleanliness, compiles byte-identical isolated source copies with warnings treated as errors, and prints the type and axiom dependencies of every local declaration. A successful formal replay does not clear the independent novelty gate.

For the paper, compile `main.tex` with a TeX installation supporting amsmath, amsthm, geometry and hyperref. The project used Tectonic0.17.0 and checked the rendered five-page PDF for layout and missing references.

## Remaining issue

The closest 2018 paper by Ghandehari–Martini has not yet been available in full from an accessible primary source. Kurusa2024 reports a weaker norm-dependent lower bound and attributes a sharpness configuration to it; both independent reviewers found no prior unrestricted proof, but classify novelty as provisional. No absolute priority claim or strict discovery count is made. This is a substantive proof candidate, not an accepted campaign outcome yet.
