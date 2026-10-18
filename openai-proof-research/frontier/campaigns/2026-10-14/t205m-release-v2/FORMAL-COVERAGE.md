# Exact formal coverage

17 named declarations: 2 definitions and 15 theorems, with generated module constants audited independently. Lean 4.34.1 supports finite-poset order-ideal rank interpolation, unique-rank cross-comparability/ordered cuts, and two distinct ideals when ordered cuts are excluded. Chain, product and antichain controls check necessity/nonvacuity.

Unformalized: geometric no-cut hypothesis; ideal/partition correspondence; skew diagrams and exceptional predecessors; Kostka/LR/Pieri and configuration enumeration; source representation maps; finite character bases; low-capacity bound and full all-m induction. This is not a formalization of the full staircase-square theorem.

Trusted: Lean kernel and pinned cached dependency objects. Dependency objects were not independently rebuilt. Only propext, Classical.choice and Quot.sound occur in the audited declarations. Some builder receipt booleans are asserted rather than measured; the independent review's actual cache fingerprints and exact statement pins are separate evidence. This release preparation did not rerun Lean.

The ideal–partition bridge is unformalized. The 17 declarations split into 7 support and 10 controls (2 definitions, 15 theorems). The 21 selected formal files are unchanged from the original selection. Parent selected-formal-portability.json, SHA256 b259ad0dcb5285ca810066201d1b54722d9f83297da6503341cd84e7d83552b3, records the successful fresh local rebuild with pinned Lean 4.34.1 and mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. This release relies on that receipt and does not repeat Lean compilation.
