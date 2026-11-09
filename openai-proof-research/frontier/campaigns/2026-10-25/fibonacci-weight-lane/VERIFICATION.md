# Verification result

PASS: clean rebuild with Lean 4.34.1 and pinned mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`.

All 24 declarations, including the period type, have matching `#check` and `#print axioms` coverage. The only observed axioms are `propext`, `Classical.choice`, and `Quot.sound`. Compilation uses `-DwarningAsError=true`. No sorry, admitted proof, native_decide, unsafe declaration, or custom axiom is used.

The full conclusion is `FibonacciWeight.fibonacci_weight_preservation`. The concrete recurrence, inverse, reduction, commutation, surjectivity, equal fibers, exact fiber cardinality, quotient construction, entire-orbit image, orbit partition, and minimal-period identification are proved. The zero fixed point has a separately checked length-one theorem. There is no unpaid bridge.

The rebuild receipt is `formal/build/audit.json`; its source hashes were checked after the build. Logs are `formal/build/FibonacciWeight.log`, `formal/build/Checks.log`, and `formal/build/rebuild.log`. The downloaded arXiv HTML and assigned MathDB JSON match their source-manifest hashes, and the MathDB snapshot is byte-identical to the assigned queued source.

The paper source is `paper/main.tex`. No paper PDF was produced. `notes/review.md` is self-review; independent review is pending parent integration. The existing proof is credited to Shivam Patel, and no novelty claim is made. No publication, shared-index modification, or commit was performed.
