# Sharp fractional-binomial converse: MathDB 352508

One proposed new resolution of Gerhold–Simon Conjecture 3.2. The certificate proves the complete conjecture for every real exponent at least 2, every natural degree, and all nonnegative inputs. It also proves a stronger biased bound and optimality of the source coefficient. These are one combined outcome, not separate discovery credits.

For positive inputs normalized to p+q=1, let

    F(a) = Σ(j=0..k) Γ(ak+1)/(Γ(aj+1)Γ(a(k−j)+1)) p^(aj)q^(a(k−j)).

The proof establishes log-convexity in a and the exact anchors F(1)=1 and F(2)=[1+(q−p)^(2k)]/2. Convex extrapolation gives F(a)≥F(2)^(a−1)≥2^(1−a). Homogeneity and explicit zero cases give the full source statement. The classical Gamma-ratio convexity is credited to prior work; its finite-grid proof is included in Lean rather than assumed.

## Contents

- `paper.pdf`, `main.tex`: four-page paper, full proof and attribution.
- `formal/`: seven Lean modules, 67 declarations.
- `reviews/`: independent mathematical, source, novelty and final formal reviews.
- `verification/audit.json`: isolated pinned replay and complete axiom inventory.
- `verification/declaration-types-and-axioms.log`: actual declaration types and dependencies.
- `sources/provenance.json`: primary-source URLs and downloaded-byte hashes. Third-party articles are referenced rather than redistributed.
- `NOVELTY.md`: precise contribution and retrieval limitations.

## Reproduce

Install Lean 4.34.1 and use the exact Mathlib and dependency revisions in `verification/pins.json`, with their compiled libraries available. Run from this packet's root:

```sh
python3 verification/verify_candidate.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages
```

The verifier checks dependency commits and tracked-file cleanliness, compiles byte-identical isolated copies with warnings as errors, inventories every local declaration, and accepts only `propext`, `Classical.choice`, and `Quot.sound`. It does not use `sorry`, `admit`, new axioms, `unsafe`, or `native_decide`.

The three main endpoints are `FractionalBinomial.source_conjecture_352508`, `FractionalBinomial.homogeneous_biased_bound`, and `FractionalBinomial.sharp_coefficient`. Source and literature review are separate from formal validity. No external publication, posting, or upload is implied by this local packet.
