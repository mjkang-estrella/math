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


## Subsequent110-declaration checkpoint

The new SourceStatement.lean makes the degree-three specialization of the
literal353909 claim explicit, with generic root arrays, exact sourceClosedDisc
(including sqrt(r)), genuine positive A-valued convex coefficients, and the
conclusion quantified over all derivative zeros. It also states the published
completely split derivative variant and proves the bridges to the displayed
polynomial and critical roots. The sourceCStarStructure term explicitly checks
that the concrete function algebra is a commutative unital C*-algebra.

The theorem source_positive_convex_from_real_weights bundles continuous real
weights into continuous complex-valued elements and proves positivity in the
actual C*-order, their algebraic sum1, and the exact convex combination. It is a
bridge theorem with hypotheses; those hypotheses must still be discharged by
the explicit critical-root construction before any final refutation claim.

A new isolated strict replay passed all110 declarations in four modules. All
new types and axiom reports were read; only the standard three axioms occur.
Receipts and exact source hashes are in verification/partial110-*. The partial92
receipt remains the older historical checkpoint. Full selection and convex-weight
integration, final review, paper/packet, and extracted replay are still pending.
