# Round 5B implementation, not acceptance

The unconditional maximumFinalCount_proved target is NOT closed. No acceptance or credit is claimed. Root decides. CommonCutCount was not worked on.

New sorry-free content in StackSortDel5 modules:

- Exact literal tuple membership equivalence for maximum deletion and insertion, with empty children omitted and the zero-size reduced domain included.
- A finite suffix reconstruction family whose membership is exactly childrenTuple equality and whose cardinalities are 1, 2, 1.
- Reconstruction of every maximum-final tuple, the converse, and uniqueness retaining the left/right unary choice.
- The actual tuple-level equivalence deletionEquiv between ReducedPairs and MaximumPairs, without any counting hypothesis.
- Exact raw-support and clipping lemmas, including deletion literalX = deletion XI for all supported positive inputs.
- Equality of Nat.card for the deletion domains. The final theorem maximumFinalCount_of_bridges is conditional on exactly FixedMaximumDecomposition and TaggedDeletionCount, both explicit ordinary Lean Props in StackSortDel5Final.lean.

Still required: sum the finite oriented reconstruction fibers over the nine reduced arity pairs, and count maximum-final collisions by their maximum-containing irreducible final block. The latter gives the fixed-maximum shuffle coefficient choose (M-1) (b-1). Neither cardinality assembly is claimed completed. See PROOF.md for exact next steps.

The 73 frozen round-4 modules are byte-identical to the pinned archive, checked by extraction and comparison; before/after hashes are retained. New code is confined to seven StackSortDel5 modules. Validation and audit totals are recorded in results.json. The source-only archive is stacksort-source5b.zip. Fresh extraction, strict serial replay, explicit-module leanchecker, and all-new-declaration transitive audits use the scripts and logs supplied with this lane.

No child agents, git, network, browser, external messages, publication, upload, or shared ledger edits were used. All writes and temporary files are lane-local. Every Lean, leanchecker and Python process runs under the lane RSS watchdog, two-CPU affinity, CPU 120 s / wall 140 s caps and MALLOC_ARENA_MAX=2; Lean uses -M3500. No background job is retained at handback.
