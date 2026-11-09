# MathDB 343536 — round 3

PARTIAL CONDITIONAL FORMALIZATION. Root decides; no acceptance or credit claimed.

Closed: ExceptionalNoIso, as Grid343536.exceptional_no_iso (GridExceptional.lean)
and GridFinal3.exceptionalNoIso. This is a theorem with no unproved premises.
It proves the abstract order-isomorphism obstruction for both exceptional squares.

The certificate proves at most 7 equitable partitions at 2×2 and at most 9 at 3×3,
against at least 10 distinct explicit subgroups of the full automorphism group.
It does not need, or claim to have separately proved, that the full group has order 8.
All finite computations use kernel reduction, not native evaluation.

Remaining, unchanged: Grid343536.FreeClassification and Grid343536.MainOrbit.
GridFinal3.mathdb_343536 is conditional on exactly those two Props.
The unconditional endpoint has NOT closed.

After closing the first target, work moved to FreeClassification.
GridFreePaths proves the full free-vertex assertion for all paths, in either
orientation, using first-row determinism. The inherited negative direction is
already unconditional. The positive direction for both dimensions at least 2,
outside the exceptional squares, remains open. MainOrbit was not started,
respecting the required target order.

All 13 round-2 sources remain byte-identical. See frozen-before.sha256,
frozen-after.sha256 and frozen-zip.sha256. The frozen zip was safely extracted
and its sources compared with the round-2 source directory.

See VALIDATION.md and replay-report.json for the validation outcome.

The exact remaining definitions are still in frozen src/GridFinal.lean:

    def FreeClassification : Prop :=
      ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
        (HasFreeVertex (G m n) ↔ ¬ (2 ≤ m ∧ m = n ∧ n ≤ 3))

    def MainOrbit : Prop :=
      ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → ∀ r : Setoid (Fin m × Fin n),
        IsEquitable (G m n) r → r = orbitSetoid (G m n) (Hpi r)

Next round: first close the positive free-vertex direction for m,n ≥ 2.
Prove that a fixed oriented corner flag forces a fixed side, distinguish
side lengths in nonsquares, and extract a fixed oriented flag from a fixed
near-corner in squares ≥ 4. Handle ladder end columns separately. Then,
and only then, start the inherited MainOrbit border/layer plan.
