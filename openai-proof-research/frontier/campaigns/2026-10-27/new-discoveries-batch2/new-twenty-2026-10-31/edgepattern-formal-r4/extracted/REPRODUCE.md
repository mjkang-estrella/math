# Portable strict replay

Extract the source packet into a new empty directory. Set `LEAN_BIN` to the pinned Lean 4.34.1 binary (commit 5045d0056413266e57c625dcd7c365b10e377c52), and `LEAN_PACKAGES` to the read-only packages directory containing mathlib pinned at d13f23b723b8a846827a245b89c10fc7d3f11612 and its built dependencies. Then run:

```sh
python3 -I scripts/replay.py
python3 -I scripts/negative.py
```

The replay refuses every preexisting olean inside the extraction. It rebuilds all local modules with `-j1 -DwarningAsError=true`, then runs leanchecker on every module. It clears inherited Lean/Lake variables and supplies an empty HOME and a lane-local TMPDIR. Each Lean or leanchecker call runs under the sampled private RSS watchdog, 120 second CPU cap, 140 second wall cap, two-CPU affinity and MALLOC_ARENA_MAX=2. Calls are sequential. Logs and individual receipts are retained. The RSS threshold is 5.75 GiB, below the assignment's 6 GiB cap.

`AuditR4` emits complete local declaration and expression inventories. `TOTAL_POLICY_VIOLATIONS` must be read separately from a successful process exit: an audit execution can finish while reporting forbidden inherited safety flags. A successful replay of this partial packet does not prove the missing classification or unconditional endpoint.

The source-only archive excludes all compiled artifacts. Input hash manifests and the copy receipt bind immutable inherited sources. `scripts/check.py` is development-only, is not in the portable packet and is not used by strict replay.
