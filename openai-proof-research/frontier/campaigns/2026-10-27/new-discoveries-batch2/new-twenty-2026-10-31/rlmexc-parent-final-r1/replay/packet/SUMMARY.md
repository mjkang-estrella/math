# Lean formalization lane rlmexc-formal-r1

The literal dual endpoint `AK350721.conjecture_refuted : ¬ VoRConj ∧
¬ MathDBConj` is proved without residual hypotheses. Both parts use n = 9,
k = 3 and coefficient −1 of x_{1,5,7,8} y_{2,3,4,6,9}. General definitions
use the literal inversion count, separate value sets, `Equiv.Perm.partition`
including fixed points, and membership via `MvPolynomial.map` from ℕ.
The finite characterization has exactly eight permutations and avoids S_9
enumeration. Complete partitions and inversion counts are certified.
A non-vacuity control proves `InNat (F 3 3)`.

The dependency audit permits only propext, Classical.choice and Quot.sound.
The local declaration metadata audit covers 168 declarations. The fresh
extracted replay logs and measurements are in `replay/logs/`; see results.json
for the recorded completion status. All nine modules are compiled separately
and each has its own explicit-module leanchecker invocation.

Deliverables: source.zip, module-order.txt, PROOF.md,
STATEMENT-CORRESPONDENCE.md, REPRODUCE.md, results.json, and replay/logs/.
The infinite family and optional n = 8 instance are not formalized.
No acceptance or novelty adjudication is claimed; root decides.

## Development limitations and process notes

Broad `Mathlib` and `Lean` imports, and early arithmetic tactics, exceeded
memory limits. Limits were not raised. The final implementation removes those
imports and uses explicit bounded arithmetic cases. Successful final replay
logs are retained in full; early development logs were overwritten during
iteration, so they are not a complete history of failed attempts.

Two tiny capped Python source-generation calls were issued while previous
Lean tool sessions were still pending, contrary to the requested strict
one-heavy-process sequencing. A lane-local flock now enforces serialization
in the wrapper, and the fresh replay is strictly sequential. No worker or
watchdog is left running at handback. No child agents, git commands, network
requests, ledger edits, or writes to other lanes were used.
