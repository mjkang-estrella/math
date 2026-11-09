# Reproduce Coverage8 and the conditional endpoint

Extract `nut-r6p-source.zip` into a new empty directory. Run sequentially:

```sh
export LEAN_BIN=/path/to/lean-4.34.1-linux/bin/lean
export LEAN_PACKAGES=/path/to/pinned/.lake/packages
python3 -I replay.py > replay-console.log 2>&1
```

Use Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`, and the read-only mathlib package cache pinned to `d13f23b723b8a846827a245b89c10fc7d3f11612`. The driver takes both paths from the environment, clears other environment settings, uses only packet-local HOME and TMPDIR directories, and refuses any existing `.olean` under its directory. It compiles every module in dependency order with `-j1 -DwarningAsError=true`, runs leanchecker on each module, and requires all negative controls to fail without hitting a resource cap.

Every Lean and leanchecker invocation passes through `scripts/run_capped.py`: at most 2 CPUs, 120 CPU seconds, 140 wall seconds, sampled private RSS at most 6 GiB, and `MALLOC_ARENA_MAX=2`. Processes run sequentially. Each call has a full log and a JSON resource receipt under `logs/`.

`AuditR6.lean` audits every declaration belonging to every other packet module, including generated declarations, with its full type, opaque-inclusive body, unsafe/partial/axiom flags, and transitive axioms. It rejects every axiom except `propext`, `Classical.choice`, and `Quot.sound`. The audit module itself contains commands and no mathematical declarations.

The mathematical endpoints are `Nut8.coverage8 : Nut8.Coverage8` and `Nut8.nut8_target (hp : Nut8.PerSupport) : Nut8.Target`. This packet does not prove `PerSupport` or an unconditional `Target`. Root acceptance remains separate.
