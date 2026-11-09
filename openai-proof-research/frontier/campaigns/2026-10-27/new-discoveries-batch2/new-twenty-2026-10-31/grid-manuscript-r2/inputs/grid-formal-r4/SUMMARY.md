# MathDB 343536 — Round 4

PARTIAL CONDITIONAL FORMALIZATION. Root decides; no self-acceptance or credit.

Closed this round: **FreeClassification**, as the sorry-free theorem
`Grid343536.free_classification` in src/GridFreeClassification.lean.
This is the full classification for all positive m,n and full graph
 automorphisms. It has no MainOrbit premise. ExceptionalNoIso remains closed
by the unchanged Round 3 theorem.

Still open: **Grid343536.MainOrbit**. Consequently the unconditional endpoint
has NOT closed. GridFinal4.mathdb_343536 has exactly MainOrbit as its premise.

MainOrbit is now proved unconditionally for every path in either orientation,
and for both exceptional squares, 2×2 and 3×3. General ladders and ordinary
rectangles/squares still need the border-transitivity and layer proofs.

The full exact remaining Prop is the frozen definition in src/GridFinal.lean:

    def MainOrbit : Prop :=
      ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → ∀ r : Setoid (Fin m × Fin n),
        IsEquitable (G m n) r → r = orbitSetoid (G m n) (Hpi r)

The stabilizer proof follows the required order: fixed oriented corner flags
force fixed sides; nonsquares cannot interchange directions by corner timing;
near-corners in squares ≥4 fix their unique adjacent corner; ladder corners
fix a degree-separated end column. Row determinism finishes each case.

All 23 frozen modules are byte-identical. The input zip hash is
42498b10fb28faf228a1ac4ba7a509dbcd850c38caa47b03f359c2c566fa2030.
Eight new modules include seven mathematical modules and Audit4. Validation
results are in replay-report.json and verification/replay-report.json;
LOCAL and upstream metadata are reported separately. All process logs remain
in this lane. Development failures are retained and are not certificates.

Next round: establish the saturated border neighbour multiset rule for m,n≥3;
prove non-backtracking colour side walks and corner timing; construct each A0
border witness and use row determinism. The transposition conjugation bridge
is now proved in GridTransposeGroup. Build concrete cell-invariant positive
layers for ordinary grids and ladders, prove border transitivity for ladders,
then apply positive_layer_propagation. Use the completed path and exceptional
cases for those branches. This would close the sole remaining Prop MainOrbit.

No git, shared ledger edits, network, publication, uploads, external messages,
browser tabs or child agents were used. No background job remains at handback.
