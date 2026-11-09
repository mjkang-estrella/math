# MathDB 343536 — Round 5

PARTIAL CONDITIONAL FORMALIZATION. Root decides; no self-acceptance or credit.

Closed: MainOrbit for all ladders 2×n and n×2, n≥3, as
Grid343536.main_orbit_ladder and main_orbit_transposed_ladder.
Together with frozen round-4 results this covers all positive grids with a
dimension at most 2, and also 3×3.

Also closed: concrete positive cell-invariant layers for all ordinary grids,
their unique-predecessor propagation property, the saturated border multiset
rule, abstract non-backtracking colour-walk propagation and first-marker timing,
and the literal internal-top-side two-neighbour rule.

NOT closed: main_orbit_proved : MainOrbit and the unconditional endpoint.
The exact remaining obligation is Grid343536.OrdinaryBorderTransitivity in
src/GridFinal5.lean: colour-preserving A0 witnesses between related border
vertices for m,n≥3 outside 3×3. GridFinal5.mathdb_343536 is conditional on it.
PROOF.md explains the remaining geometric construction, without treating it
as proved. No placeholders discharge it.

The input zip SHA-256 is
384a9c6a9a4e28e0e922f6545c1516216578fb8f4c73d5e469d157fddc2e378d.
All 31 inherited modules are byte-identical; see the before/after manifests.
Six mathematical modules and Audit5 are new. See VALIDATION.md and the
replay reports for exact validation status and separate LOCAL/upstream audits.
No novelty or acceptance determination is made by this implementation lane.
