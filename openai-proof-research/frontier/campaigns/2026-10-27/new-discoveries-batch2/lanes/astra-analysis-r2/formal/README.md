# Formal scope: excluded lead, not a source endpoint

Replay with:

    python run_lean.py ExclusionCore.lean

The runner uses exactly /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean and builds LEAN_PATH from the existing package libraries under the supplied 2026-10-14/formal/.lake/packages path. Requested mathlib pin: d13f23b723b8a846827a245b89c10fc7d3f11612. No package or shared build file is changed.

ExclusionCore.log prints actual public theorem types and axiom sets. Four elementary declarations compile. Each uses a subset of propext, Classical.choice, Quot.sound. No sorry/admit/axiom declaration/unsafe/native_decide is used.

- cycleDenom_pos: positivity of the explicit rational cycle denominator.
- proposedCoeff_ne_zero: nonvanishing of the DEFINED coefficient expression when parts>0 and weight<=n. The formula is not proved to be a coefficient of the source psi_n in Lean.
- resummation_cancellation: exact commutative-ring cancellation after the formal-series equation has been obtained. It does not supply that equation.
- degree_four_Bell: a universal rational polynomial identity matching the source degree-four expression.

The complete ordinary argument is in ../PROOF.md, but the literal all-degree source Lean endpoint is ABSENT. Unproved formal bridges would include: exact Bell/Stirling recurrence encoding; locally finite generating-series resummation; generalized binomial theorem with series-valued exponent; logarithm/exponential inverse identities at that series; coefficient extraction in the multivariate ring; exact transport to all specializations and partition support. These bridges were not pursued after the entire family was found already proved in Matsuno2607.10106v1. No discovery count, acceptance, or full-source formalization is claimed.
