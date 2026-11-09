# Capability inspection and proof decomposition

Inspected pinned mathlib source modules (read-only):
- Probability/Distributions/Exponential.lean: concrete expMeasure, probability instance, explicit CDF. There is no all-natural-moments theorem in this file.
- Probability/Distributions/Gamma.lean: concrete density normalization; general exponential-power integrals appear in the special-functions dependencies.
- MeasureTheory/Constructions/Pi.lean: finite product measure, probability instance, pi_pi rectangle formula.
- Probability/Independence/Basic.lean: iIndepFun_pi gives independent coordinate clocks without existence assumptions.
- Analysis/Convex/Mul.lean: convexOn_pow on Ici 0 for every natural exponent.
- MeasureTheory/Integral/Bochner/Basic.lean: integral_mono, integral_add, integral_const_mul; all used in the generic integration helper.
- Algebra/BigOperators/Ring/Finset.lean: Fintype.sum_pow gives ordered tuples with repetitions.
- Algebra/BigOperators/Group/Finset/Defs.lean and Data/Fintype/Perm.lean: permutation reindexing and factorial cardinality.
- Topology/Order/Lattice.lean: Continuous.finset_inf'_apply proves the lifetime minimum measurable.

No ready-made chamber decomposition for this coefficient formula was identified in this targeted inspection. This is not an exhaustive absence claim about mathlib.

Sustainable analytic continuation: establish the scalar exponential tail and a.e. nonnegative clock support, turn the already proved rectangle formula into joint survival, then formalize mixed layer cake and the labelled coordinate chambers. Keep the chamber result as a separate general analytic lemma with explicit finite-dimensional volume, not an expanded computation for fixed n or d. Repeated-edge tuples must retain all d! labelled chambers.

An alternative finite vertex-order/spacings representation was considered mathematically. It removes the d-coordinate chamber integration only by replacing it with another order-statistic law and a coefficient identity. Neither bridge is already present here, and positive coefficients alone are insufficient. No alternate proof is claimed.

Build adaptations: importing the entire Mathlib failed because a cached unrelated private olean was missing. Specific imports avoid that dependency. The umbrella Mathlib.Tactic caused a capped allocation failure; it was removed. A direct inf'-induction elaboration exceeded the cap and was replaced with the finite-infimum continuity theorem. All these failures and diagnostics are retained in build-01 through build-13. No upstream file or cache was changed.
