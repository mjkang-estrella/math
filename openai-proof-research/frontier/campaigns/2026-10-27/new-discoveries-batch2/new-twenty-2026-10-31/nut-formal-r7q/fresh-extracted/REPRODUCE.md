# Replaying the unified Nut8 packet

Extract nut-r7q-source.zip into a new empty directory. Set LEAN_BIN to the Lean 4.34.1 executable (commit 5045d0056413266e57c625dcd7c365b10e377c52), and LEAN_PACKAGES to the read-only mathlib package cache at revision d13f23b723b8a846827a245b89c10fc7d3f11612.

Run `python3 -I replay.py --init-only`, then repeat `python3 -I replay.py --resume --steps 1` until replay-state.json says PASS. Larger step counts are sequential batches. Each step launches one capped process and writes a unique full log plus a resource receipt. Progress is saved after each successful process. The initial invocation refuses any existing .olean file. Resume verifies source hashes and all recorded output hashes and refuses unrecorded oleans. Do not inject cached objects into a fresh replay.

The driver rebuilds all 1,151 unified inherited and endpoint modules in dependency order using `lean -j1 -DwarningAsError=true`, then runs leanchecker once per module per process. It executes 128 additional auditors, covering all 1,024 local modules in the import closure of Nut8Final, including generated declarations. Auditors print each declaration's module, full type, opaque-accessible body, unsafe/partial/axiom flags and transitive axioms, rejecting anything beyond propext, Classical.choice and Quot.sound. Auditors use bounded iteration and are outside the proof closure. Finally the driver rejects false assertions and exercises existing-olean refusal. PASS requires every phase.

Resource limits per process: 2 CPU affinity slots, 120 CPU seconds, 140 wall seconds, sampled private RSS at most 5.75 GiB, MALLOC_ARENA_MAX=2. All HOME and temporary paths are inside the extraction. No background service is used.

`--development` is a separate cache-assisted development mode. Its state is never final validation evidence. The original r6q and r6p Lean sources are retained byte-for-byte, including historical audit modules; new AuditFinal modules are additional auditors and are never imported into Nut8Final.
