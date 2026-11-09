# Uncredited MathDB 334599 research certificate

Lean endpoint: `Supervenience.literal_conjecture_false`.

`HierarchyConjecture` asserts strict expressivity at every arity. The file defines the actual languages and arbitrary ternary-frame semantics, then translates all arity-2 formulas to equivalent arity-1 formulas, contradicting the n=1 step. The proof is uniform in formulas and models.

This is a research packet, not a claim of novelty or acceptance. The journal text is unread because of a publisher challenge. The Boolean-cell adaptation objection remains material. See the lane's MATHEMATICAL-NOTES.md and results.json.

Extract into an empty directory. With the pinned cache in DEPENDENCIES.json available, run:

    python scripts/leanrun.py -o lean/Hierarchy.olean lean/Hierarchy.lean
    python scripts/leanrun.py lean/Audit.lean

The wrapper invokes Lean with -j1 -DwarningAsError=true. Resource caps are applied separately by scripts/limited.py. For leanchecker, place the pinned binary directory on PATH and set LEAN_PATH to this extraction's lean directory followed by each cached dependency's .lake/build/lib/lean, then run `leanchecker -j1 Hierarchy`.

Audit.lean selects declarations by originating module (not a hand-picked list), checks local safety/axiom status, and computes transitive axioms, including generated/private names. The only permitted axioms are propext, Classical.choice, Quot.sound. The full upstream cache is trusted rather than rebuilt.
