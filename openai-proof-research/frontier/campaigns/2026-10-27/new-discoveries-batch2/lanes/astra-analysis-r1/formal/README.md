# Formal status: elementary checks only, zero discovery credit

Run from any directory:

```
python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/astra-analysis-r1/formal/run_lean.py ExclusionChecks.lean
```

The runner uses exactly `/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean`
and the cached packages beside pinned mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

The literal endpoint in `ExclusionChecks.lean` is **not** Zhou's conjecture.
Five declarations prove the elementary reciprocal-kernel identity, the Miura
algebraic elimination, its centered form, its parameter symmetry, and an
elementary midpoint consequence of antisymmetry. Their axiom reports use only
the three permitted standard axioms. There are no proof holes.

A full source-faithful implementation would additionally need:

1. Source sn coefficient recurrence and sn² convolution, with the exact
   factorial/sign convention used in Zhou Theorems 4.1 and 4.3.
2. The all-order formal-power-series Miura identity and coefficient recurrence,
   rather than only the scalar algebraic identity now checked.
3. Uniqueness of that recurrence and the parameter-reflection coefficient
   identity, including the midpoint derivative result.
4. The exact source quadratic substitution (5.60), its chain-rule factor,
   and the mapping from its coefficients to c/d/e/f in (5.61),(5.62),
   (5.88),(5.89). An abstract sequence with the same parity is not this bridge.
5. If using literal analytic integral definitions instead of the explicit
   source coefficient formulas, the relevant Jacobi/infinite-series/integral
   identifications and coefficient uniqueness as well.

No conditional theorem with these obligations assumed has been presented as
a completed source certificate. This work was stopped because the underlying
result is already an immediate corollary of Xu–Zhao Lemma 4.4. Completing the
formalization would not make it a genuinely new mathematical outcome.
