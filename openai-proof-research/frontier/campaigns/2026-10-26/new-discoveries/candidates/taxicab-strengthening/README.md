# Minimum-side taxicab refinement: MathDB341671

Status: mathematical/source/formal review **PASS**. Strict novelty **HOLD** pending closest-prior-work comparison. Accepted discovery credit: **0**. This supersedes the earlier base-bound candidate as the SAME ONE proposed mathematical outcome.

For arbitrary taxicab triangles and ordinary closed-triangle points, the certificate proves

    R_A+R_B+R_C ≥ (3/2)(r_a+r_b+r_c+min(r_a,r_b,r_c)).

Vertex distances use explicit L1 coordinates; side distances use exactly the primary source's supporting-line formula. The ordinary geometric interior theorem has no orientation restriction. The packet also proves both optimal-coefficient statements using a nondegenerate strictly interior equality configuration. The old conjecture, scalar helpers, equality configuration and two sharpness consequences receive no separate counts.

## Contents and replay

- `paper.pdf` and `main.tex`: complete five-page research paper.
- `formal/`: six complete Lean modules, including the generic nonnegative polynomial inequality and exact geometric bridge.
- `reviews/`: independent mathematical, exact-source and final formal reviews; inherited geometry authorship is explicitly disclosed.
- `verification/audit.json`: fresh isolated replay of all68 declarations; only propext, Classical.choice and Quot.sound.
- `sources/provenance.json`: primary-source URLs and hashes.
- `PROOF.md` and `NOVELTY.md`: derivation and explicit limits of the new-to-literature claim.

Replay with Lean4.34.1 and the exact dependency revisions in `verification/pins.json`:

```sh
python3 verification/verify_candidate.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages
```

The verifier checks exact commits and tracked-file cleanliness, compiles byte-identical isolated source copies with warnings as errors, and checks every local declaration's type and axiom dependencies. A successful replay does not clear the separate novelty gate.

## Novelty limit

Independent reviews accept this as a substantive proof candidate, unlike the excluded Vandermonde known-results connection. No prior additive-minimum-side result was located. However, the full2018 Ghandehari–Martini paper remains unavailable from the public sources examined. A local path or lawful accessible link was requested optionally while other research continues. The proof is not represented as an accepted new discovery until this overlap risk is resolved.

The known sharpness of the older coefficient3/2 is credited to prior work. The new interior equality concerns the REFINED sum-plus-minimum functional; its old unrefined ratio is9/5, not3/2. Generic normed-space interpretation is not separately counted or claimed as a generic Lean theorem.
