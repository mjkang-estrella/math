# Handback: complete literal Lean refutation

Status: implementation and fresh extracted strict replay complete. This is not acceptance; root decides. No residual propositions or conditional endpoint remain.

`SlowNim360653.conjecture1_false : ¬ Conjecture` refutes the literal uniform-Nash conjecture at n=ℓ=3, x=(4,4,5), C=7. It uses globally legal positional strategies, deterministic source GM (minimum multiple/rightmost tie, largest-entry fallback), total play length, exact rational payoffs, admissibility over every legal profile, and unilateral Nash deviations. General mass-decrease, length-bound, fuel-independence and no-exhaustion lemmas supply the total-play foundation.

`literal_bridge` certifies both actual coordinate traces, lengths 6 and 5, and player 0's payoffs −1 and +1. `seven_admissible` proves C=7 exceeds every legal profile length using the general bound floor(mass/(n−1)). `two_every_profile_nash` is the non-vacuity control: every two-pile profile is Nash for every initial state, player count ℓ≥2, and rational C because all lengths equal initial mass.

Modules, in dependency order: Basic, Play, Witness, Control, Certificates, Audit. Every module passed `lean -M3500 -DwarningAsError=true` and `leanchecker MODULE` in the fresh source.zip extraction `replay/fresh2`. The endpoint axiom closure is exactly propext, Classical.choice, Quot.sound. The metadata audit passed for 129 mathematical declarations, including generated declarations. The mathematical source scan passed. Audit.lean was manually inspected: its only special operation is a read-only Lean environment inspection command; it introduces no mathematical axiom or substitute implementation.

Deliverables: source.zip; src/; modules.txt; resumable replay.sh and resource-limited run.sh; PROOF.md; STATEMENT-CORRESPONDENCE.md; REPRODUCE.md; results.json; logs/; full successful extracted logs in replay/fresh2/logs/. The archive contains source, drivers, documentation and bound source evidence only, with no oleans or replay stamps.

Initial compile/debug failures are preserved in logs/. The first extraction `replay/fresh1` failed at leanchecker module discovery because an overly broad LEAN_PATH entry masked the intended module name. The driver was corrected to expose only its own build directory plus pinned dependencies; fresh2 then passed all steps. No limits were increased after failures.

All work and temporary/cache/build files remain lane-local. No Python, child agent, git, network, shared-ledger edit, external publication, or upload was used. No background process is left by the runner. The optional general family and fallback-free witness were not attempted.

Source/novelty limitation inherited from root's ruling: MathDB 360653 is the target, 361128 a duplicate. The sibling DAM version of record remains unread. No novelty or acceptance claim is made here. The witness is not claimed minimal.
