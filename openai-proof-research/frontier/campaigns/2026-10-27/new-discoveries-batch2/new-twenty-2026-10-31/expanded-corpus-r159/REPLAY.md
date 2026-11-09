# Replay and trust boundary

Extract lean-packet.tar into a new empty directory inside this lane. Create lean/,logs/,tmp/,cache/,outputs/ there. All scripts infer their root from their own location. Use:

    scripts/leanrun rebuild ABSOLUTE/lean/Antimagic.lean -o ABSOLUTE/lean/Antimagic.olean
    scripts/checker checker Antimagic
    scripts/leanrun audit ABSOLUTE/lean/Audit.lean -o ABSOLUTE/lean/Audit.olean

The scripts point to the prescribed Lean4.34.1 binary and read-only mathlib/package caches at the pinned campaign path. The audit writes outputs/audit.tsv. It seeds all97 declarations in the Antimagic module, including generated declarations, and closes dependencies by inspecting types, values and inductive companions. The only transitive axioms are propext,Classical.choice,Quot.sound. No local unsafe,partial,implemented-by or extern declarations occur. See outputs/validation.json.

The completed fresh-replay directory contains results of exactly this process. Its formal sources are byte-identical to lean/. The later packet update only adds/updates the explanatory ordinary-proof and source-comparison documents. The formal source hash remains444d5df26217f4085e462dbdea61586ef9f52d8d33b51641e243c5a0f361a2c0.

Precompiled dependencies are trusted. This checks the new theorem against the pinned cache; it is not an upstream source rebuild. Kernel checking does not independently establish mathematical novelty, significance, or source-statement fidelity. Root must review those separately.

Watchdog sampling checks aggregate process-group RSS every0.1s, killing above6GiB; prlimit CPU120s,timeout140s,taskset CPUs0,1; MALLOC_ARENA_MAX=2. Lean calls include-M3500. No concurrent heavy task is required for replay.
