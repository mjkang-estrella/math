# Reproduce r5

Extract `contact-r5-source.zip` into a new empty directory. Set `LEAN_BIN` to the Lean 4.34.1 executable (commit `5045d0056413266e57c625dcd7c365b10e377c52`) and `LEAN_PACKAGES` to the read-only mathlib package cache at revision `d13f23b723b8a846827a245b89c10fc7d3f11612`. Run:

```sh
python3 -I -B scripts/replay-r5.py
```

The driver refuses existing local `.olean`, `.ilean`, `.ir` files or a build directory. It sanitizes all Lean sources, then builds all 28 modules with `-j1 -DwarningAsError=true`, invokes leanchecker separately for each module, inventories all local declarations, and runs 13 failing negative controls. The inventory records full type and opaque-inclusive body expression DAGs, unsafe/partial flags and transitive axioms. Only `propext`, `Classical.choice` and `Quot.sound` are allowed.

Every Lean and leanchecker call is serial and watchdog-wrapped: affinity at most two CPUs, CPU 120 seconds, wall 140 seconds, sampled private RSS 6 GiB, and `MALLOC_ARENA_MAX=2`. Logs and JSON receipts are retained under `replay-logs/`. Python runs isolated with bytecode writing disabled. No package cache writes are needed.

Use `replay-r5.py`: inherited drivers intentionally remain byte-identical and cover earlier stages only. The packet contains source files and documentation, without compiled artifacts. Local development logs are separate from the fresh extracted validation at `work/extracted-01/replay-logs/`.

The literal endpoint is in `formal/Refutation.lean`; it imports the contact-six theorem and explicit contact-two exclusion. Root review and acceptance remain required. Counts stay 22/40 beyond the previous 39.
