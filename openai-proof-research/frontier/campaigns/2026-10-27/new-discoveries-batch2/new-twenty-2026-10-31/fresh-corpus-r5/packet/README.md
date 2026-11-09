# MathDB 326640 Lean candidate

Run `python replay.py --lean /path/to/lean --dependency-root /path/to/pinned/.lake/packages --output fresh-output --leanchecker /path/to/leanchecker`. Uses Lean 4.34.1 and mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. The replayer verifies all manifest revisions without git commands or dependency writes, sets at most two CPUs/threads, copies the source into a fresh directory, treats warnings as errors and audits four endpoint/semantic-bridge axiom lists. Optional leanchecker checks the generated olean.

The theorem is `Majority.mathdb_326640`; definitions and all structural bridges are in Majority.lean. No checker oracle, sorry, admit, added axiom, unsafe, native_decide, or ofReduceBool. Only propext, Classical.choice and Quot.sound occur in the audited dependency closures. See ../PROOF.md for the exact source, full proof, and novelty/significance limitations. This packet has not been independently accepted.
