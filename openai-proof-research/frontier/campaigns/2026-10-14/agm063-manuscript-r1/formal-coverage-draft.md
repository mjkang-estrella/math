# Scoped formal coverage: implementation read, audit adoption pending

This is a successor implementation worker's reading, not an independent formal
audit. The final manuscript paragraph and final PDF are deliberately unchanged
until the root adopts the separately sealed formal review.

The exact implementation manifest supplied by the root is
`ca6bdb0cccd691d0c8a94ff8ec3bfbd9ccdd87a64ba5b4cf344a1b1c73b8ad9c`.
The implementation's complete `AGM063.lean`, `coverage.json`, `README.md`, and
read-only `verify.py` were read. The source digest is
`b0f6f04a3c2f5899e953323bae04cb04594f2225b7a6cfc38b5fe12bbf6822c3`.

Proposed final coverage, subject to the adopted audit:

The separate Lean support package proves 29 supporting theorems among 35 public
declarations. It covers finite degree budgets and strict numerical cutoffs;
integer composition-dimension and quotient-dimension inequalities; two-endpoint
set inclusions from supplied saturation and constancy hypotheses for a map on
the open subtype; induction through actual reflexive-transitive chain closure;
linear-functional vanishing on a spanning set and contradiction with a supplied
positive witness; and Picard/pseudoindex induction and parameter arithmetic.
The package contains 11 proved semantic-control theorems (14 control
declarations), seven false-goal rejection controls and four subprocess-wrapper
controls. These counts describe the implementation, not the geometric theorem.

In particular, Lean assumes the saturation, support containment, numerical
dimension bounds, spanning, intersection witness and generator-preservation
hypotheses at the relevant abstract interfaces. The manuscript's geometric
proofs that these hypotheses apply are not formalized. No Fano manifold,
stable-map or Chow moduli theory, virtual cycle, refined intersection, quotient
existence/properness/equidimensionality, horizontal-family dominance argument,
Mori contraction, projective-bundle classification or converse invariant
calculation is formalized. The full five-type theorem remains a human proof
conditional on stipulated S1 and essential S2 and the cited classical inputs.

The exact independent audit verdict, manifest and parent adoption must be read
and recorded before these implementation results are described as audited.
