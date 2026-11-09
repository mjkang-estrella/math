# Literal SourceClaim integration interfaces

Integration entry point: `formal/SourceClaim.lean`.
All inherited `.lean` files and `run_lean.py` are copied byte-identically from
root's frozen formal directory at the user-specified commit
`bec2db123a22bcf178fa512f8eedc81cf3ce5ba8`. No import renaming is needed.
`provenance.json` records their original paths and SHA-256 values.

The final kernel-checked declaration has exactly this type:

```lean
JacobiShifted.source_claim : JacobiShifted.SourceClaim
```

The unchanged definition expands to:

```lean
∀ r : ℕ, 1 ≤ r →
  (∀ m : Fin 2 →₀ ℕ,
    JacobiShifted.TwoLocal
      ((2 : ℚ)^JacobiShifted.dyadicExponent r *
        (JacobiShifted.sourceKappa r).coeff m)) ∧
  ¬ JacobiShifted.TwoLocal
    ((2 : ℚ)^(JacobiShifted.dyadicExponent r - 1) *
      (JacobiShifted.sourceKappa r).coeff (Finsupp.single 0 r))
```

`formal/SourceClaimInterfaces.lean.log` contains actual `#check` of both forms,
`#print axioms` of the endpoint, and `#print` of the unchanged literal definitions
`SourceClaim`, `sourceKappa`, `dyadicExponent`, and `TwoLocal`.

The direct subinterfaces are in `JacobiShifted.SourceBridge`:

* `sourceKappa_twoLocal (r : ℕ) (hr : 1 ≤ r) (m : BinaryFiltration.Exponent)`:
  `TwoLocal ((2 : ℚ)^dyadicExponent r * (sourceKappa r).coeff m)`.
* `sourceKappa_pure_u_ne_zero (r : ℕ) (hr : 1 ≤ r)`:
  `(sourceKappa r).coeff (Finsupp.single 0 r) ≠ 0`.
* `sourceKappa_pure_u_valuation (r : ℕ) (hr : 1 ≤ r)`:
  `padicValRat 2 ((sourceKappa r).coeff (Finsupp.single 0 r)) = -(dyadicExponent r : ℤ)`.
* `sourceKappa_pure_u_sharp (r : ℕ) (hr : 1 ≤ r)`:
  the exact negated `TwoLocal` conjunct of `SourceClaim`.

`HalfSubstitution.lean` proves `scale_coeff_expansion` for every integral
parameter polynomial. `SourceUpperBound.lean` identifies the actual literal
log coefficient with `transportedPrimitive` using the existing normalized
uniqueness theorem. Both facts are closed; their interface has no hypothetical
source bridge, divisibility-preservation, or primitive-existence premise.

`DyadicArithmetic.twoLocal_iff_valuation_nonneg` applies to every rational,
including zero. `DyadicArithmetic.catalan_valuation` applies to every natural
index, including zero. The coefficient nonvanishing theorem is proved before
using valuation multiplicativity or division.

The exhaustive audit uses actual module-origin metadata, including generated
helpers. Its proof-module set is `DyadicArithmetic`, `HalfSubstitution`,
`SourceUpperBound`, `SourceSharpness`, and `SourceClaim`. Audit elaborator
implementations are separate from this mathematical declaration set.
