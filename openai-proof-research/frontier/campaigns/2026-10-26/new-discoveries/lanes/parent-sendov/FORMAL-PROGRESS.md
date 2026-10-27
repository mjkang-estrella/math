# C*-Sendov formalization checkpoint — credit 0

26 October 2026. The accepted campaign tally remains 14/30.

The parent has implemented three source modules, with **92 declarations**, and
replayed all of them in a fresh isolated directory with pinned Lean 4.34.1 and
mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. The strict replay passed:
warnings are errors; every declaration was inspected through its reported type
and axiom dependencies; only propext, Classical.choice and Quot.sound occur.
The receipt and all 92 reports are preserved in verification/partial92-*.

## Completed supporting formal proofs

- Explicit exponential phase, principal square root branch, continuity, nonvanishing,
  the exact square identity, bounds, and the two endpoint obstructions.
- The literal scalar deleted-factor derivative and classification of its scalar
  zeros, including the noncollision of roots and critical roots.
- The actual algebra C(Set.Icc (0:ℝ) 1, ℂ), its explicit roots and critical elements,
  a genuine monic degree-three polynomial, and its derivative's exact polynomial
  factorization. The latter is proved coefficientwise after evaluation at time;
  no integral-domain property of the function algebra is assumed.
- The equivalence between the source's star-order unit disc and pointwise norm
  bounds, all input disc hypotheses, strict critical-element norm bounds,
  and supremum distances greater than 21/20 for both displayed branches.

## Outstanding work

The complete literal MathDB353909 endpoint is **not yet proved**. Integration
of the generic continuous-selection theorem and the continuous positive convex
weights remains outstanding, with a dedicated Pi implementation lane working on
those ingredients. The source/math/bounded-novelty review is independently in
progress. A final independent formal and manuscript review, deterministic packet,
and extracted fresh replay will still be required before acceptance.

The manuscript main.tex is a mathematical proof draft. Its three-page PDF builds
without overflow or undefined references and all pages were rendered and viewed.
Final pagination and the formal-verification section will be revised when the
complete endpoint and review are available. The draft is not an accepted packet.
The original hand-proof/source freeze at 3c62435432 remains unchanged.
No formal claim about MathDB353908's extra density-of-invertibles hypothesis is made.
