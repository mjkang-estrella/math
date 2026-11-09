# Portable source replay

Use Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`, and the read-only mathlib packages pinned at `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Extract `nut-r4a-source.zip` into a new empty directory. The packet contains source only. Set LEAN_BIN to the absolute Lean executable and LEAN_PACKAGES to the directory containing the pinned package directories. From the extracted directory run:

```sh
LEAN_BIN=/absolute/path/to/lean LEAN_PACKAGES=/absolute/path/to/packages python3 -I replay.py
```

The driver refuses any existing `.olean` anywhere beneath its directory. It uses a sanitized environment with local HOME and TMPDIR and compiles modules serially with `lean -j1 -DwarningAsError=true`. Each compiler and leanchecker invocation has two-CPU affinity, a sampled private-memory cap of 6 GiB, a CPU cap of 120 seconds, a wall cap of 140 seconds, and MALLOC_ARENA_MAX=2. The watchdog covers the process group. All runtime outputs are written beneath the extracted directory.

Each source module is independently checked by leanchecker. R4Audit enumerates every declaration from all local modules, including generated declarations, with full type, opaque body via value?, module, unsafe/partial/axiom flags, and transitive axioms. It rejects flags and axioms outside propext, Classical.choice and Quot.sound. It also prints axioms for each declaration. The complete audit is `logs/strict-R4Audit.log` in the replay directory.

Six negative controls must fail: an incorrect determinant, an unrelated theorem substituted for Target, a false real sign identity, a wrong semi-edge sign, an attempt to use endpoint_of_finite without supplying FiniteObstruction, and replay into a directory with existing oleans. Negative compiler errors and resource receipts are retained in logs. A resource-cap failure cannot count as a successful rejection.

The supplied fresh replay is under `fresh-extracted/`; its aggregate receipt is `fresh-extracted/logs/replay.json`. `replay-receipts.json` summarizes this run. `inputs-before.json` and `inputs-after.json` bind the read-only inputs, and `packet-manifest.json` lists source hashes. No proof of Part B or root acceptance is included.
