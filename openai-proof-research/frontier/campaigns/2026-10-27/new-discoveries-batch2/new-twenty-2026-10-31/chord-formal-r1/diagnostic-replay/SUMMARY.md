# MathDB 329080 — formalization round 1

Status: PARTIAL, NOT ACCEPTED. Root decides. Credit is zero.

Completed Lean material: a computable endpoint-pairing diagram model; literal rotation/reflection equivalence closure and setoid; the three-half-edge rotation-system evaluator; the two-dart evaluator including both empty-circle terms; exact Euler genus relation; and a uniformly valid representative (123123)(44⋯nn). Kernel proofs establish the range of 123123, the complete one- and two-chord genus-range statements, and the printed conjecture's small-size falsity. Additional small boundary bridges, negative controls, and individual n = 4 range witnesses are supplied in separate bounded modules.

The full intended endpoint is conditional, with five explicit, unproved mathematical hypotheses in ChordRemaining.lean. The exactly-four endpoint remains conditional on its exact finite enumeration target. Generic face-count correctness, the rotation-to-dart first-return bridge, integrality/existence, deletion, planarity, transfer, finite completeness, shortest odd cycles and arc rigidity still require proofs. No placeholder proof or new axiom is introduced. See PROOF.md and STATEMENT-CORRESPONDENCE.md for exact limits.

The independent Python regression checks both boundary models on all 995,572 labelled-diagram/side-assignment pairs for n = 1 through 5, with zero mismatches, Euler parity and nonnegativity checks, and all requested numerical negative controls. It finds 0, 0, 1, 4, 1 equivalence classes with range {1,2}. These finite Python counts are evidence, not formal classification proofs.

The original monolithic four-chord check exceeded the kernel memory/per-call limits. Its failed logs are retained. The successful approach splits Boolean assignment checks into small kernel-decided chunks; all runs retain the same resource caps.

Reproduction and replay instructions are in REPRODUCE.md; exact module hashes, endpoint status, remaining Props and LOCAL/upstream audit totals are in results.json. The source archive excludes object files and is replayed from a new empty extraction inside this lane. The closure audit includes generated declarations and opaque proof values and checks set equality against the imported module inventories.
