# Strict source-only replay

Use the exact assigned Lean 4.34.1 binary (commit
5045d0056413266e57c625dcd7c365b10e377c52) and mathlib package cache pinned at
d13f23b723b8a846827a245b89c10fc7d3f11612. Extract `nut-r2-source.zip` into a NEW
empty directory inside the authorized lane. Set `LEAN_BIN` to the absolute Lean
binary and `LEAN_PACKAGES` to the absolute `.lake/packages` directory. Run:

```sh
python3 -I replay.py
```

The driver refuses any existing `.olean` below its extraction root. It creates
only local formal outputs, home, tmp and logs; it clears the environment and
sets local HOME/TMPDIR, single Lean worker and allocator controls. Each Lean
and leanchecker call runs under `scripts/run_capped.py`. The driver sequentially
builds all eleven modules with `-j1 -DwarningAsError=true`, invokes leanchecker
separately for each, audits all declarations from all ten mathematical modules,
and rejects three negative controls. `Audit` itself adds no named logical
declarations. The watchdog samples private memory in the child process group
and enforces the assigned CPU, wall, affinity and memory caps.

The failed-driver negative control reruns this command after rebuilding; it
must refuse the existing oleans before invoking Lean. That refusal is recorded
separately from the three Lean negative controls.

The Python diagnostic search can be rerun with `python3 -I scripts/check_grammar.py`
under the same watchdog. It reads the copied graph catalogue and writes local
JSON. Python output is not a Lean proof. No package installation, network,
browser, native evaluation, or background service is required.

This replay validates only an INCOMPLETE packet. See GAPS.md for obligations
needed before the milestone or original problem can be claimed.
