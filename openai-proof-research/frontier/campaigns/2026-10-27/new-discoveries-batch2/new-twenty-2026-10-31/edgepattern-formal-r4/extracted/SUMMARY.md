# MathDB 342414 — incomplete r4 implementation

The requested arbitrary-tree rooted isomorphism and unconditional refutation were not completed. This packet is partial and zero credit unless root accepts a later completed endpoint.

All 266 inherited Lean modules remain byte-identical to r3. New `StructureR4.lean` proves seven structural results: root degrees, child cardinality identity, the two root child counts, the child bound, exhaustive distance-two coverage, triangle exclusion, disjoint root branch sets, and unique common neighbors. The exact declarations, including helper definitions and generated declarations, appear in the full audit. `AuditR4.lean` inventories imported local declarations, their full expression DAGs for types and opaque bodies, modules, safety flags and transitive axioms. It reports policy violations explicitly instead of stopping at the first one.

The input packet hash matches the assigned SHA-256. All input hashes are checked before and after. No prior-art search was repeated, no git or shared ledger was used, and no child agents were started. Validation details are in replay and negative-control receipts. The exact remaining obligations are in GAPS.md.
