# Reproduction

Use Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52, with the supplied read-only mathlib package cache at revision d13f23b723b8a846827a245b89c10fc7d3f11612. Both were provided by the assignment; the mathlib detached HEAD was read directly and matched. No git command was run.

Extract `adverse-381433-source.zip` to a new empty directory **inside this lane**. Set:

```sh
export LEAN_BIN=/absolute/path/to/lean-4.34.1-linux/bin/lean
export LEAN_PACKAGES=/absolute/path/to/formal/.lake/packages
python3 -I replay.py
```

`LEAN_BIN` may also name the binary directory. The driver refuses an extraction containing existing `.olean`, `.olean.private`, or `.olean.server` files, sanitizes inherited Lean search paths, and builds local modules in dependency order using `lean -j1 -DwarningAsError=true`. It runs leanchecker separately on every proof module, audits every proof declaration including generated constants, and runs six mathematical negative controls and one freshness control. It never starts concurrent heavy jobs.

Every Lean or leanchecker call is supervised by `scripts/bounded.py`: affinity at most 2 CPUs, CPU limit 120 seconds, wall limit 140 seconds, private RSS sampled every 0.1 seconds and killed above 6 GiB, `MALLOC_ARENA_MAX=2`. Each call has a complete log and JSON receipt. The process group is killed on limit violations and cleaned after exit. Local proof code contains no unsafe or partial declarations, new axioms, sorry, admit, native_decide, or ofReduceBool.

`formal/Audit.lean` selects declarations by defining module, not namespace or a hand-picked endpoint list. Its log includes each name, module, full expression type, full body from `value? true`, unsafe and partial flags, and transitive axioms. The unabridged log is gzip compressed because raw expression trees are large. The allowed axiom set is exactly propext, Classical.choice, Quot.sound. The audit instrumentation declares no persistent constants itself.

The checked initial extraction is `fresh-replay/`. `receipts/extraction.json` binds its archive and sources. `SOURCE-MANIFEST.json` binds the proof and replay source files. A final delivery archive adds documentation and evidence without changing those source files. Replay receipts bind the source files again after the build. The archive contains no oleans or other compiled Lean artifacts.

Development logs preserve failed attempts, including two watchdog terminations: the initial broad Mathlib import, and a mistaken leanchecker `--help` invocation (this checker treats it as an unrestricted project check). Narrow imports and explicitly named checker modules resolved them. Only the fresh replay receipts determine final validation status.
