# Exact formal coverage

17 named declarations: 2 definitions and 15 theorems, with generated module constants audited independently. Lean 4.34.1 supports finite-poset order-ideal rank interpolation, unique-rank cross-comparability/ordered cuts, and two distinct ideals when ordered cuts are excluded. Chain, product and antichain controls check necessity/nonvacuity.

Unformalized: geometric no-cut hypothesis; ideal/partition correspondence; skew diagrams and exceptional predecessors; Kostka/LR/Pieri and configuration enumeration; source representation maps; finite character bases; low-capacity bound and full all-m induction. This is not a formalization of the full staircase-square theorem.

Trusted: Lean kernel and pinned cached dependency objects. Dependency objects were not independently rebuilt. Only propext, Classical.choice and Quot.sound occur in the audited declarations. Some builder receipt booleans are asserted rather than measured; the independent review's actual cache fingerprints and exact statement pins are separate evidence. This release preparation did not rerun Lean.
