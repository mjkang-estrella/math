# Reproduction

Use the pinned Lean 4.34.1 toolchain:
`/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin`.
No network, lake operation, mathlib build, or shared cache is required.

Extract `source-only.zip` to a new directory INSIDE the assigned lane, then run:

```sh
cd fresh-extracted
./replay.sh
```

For a stopped replay, use `RESUME=1 ./replay.sh`. The driver invalidates all cached success stamps when any Lean source changes; otherwise it skips a module only when both successful Lean/checker stamps and its compiled output exist. `module-order.txt` fixes the order. Every Lean invocation compiles just one explicit source module with `-M3500 -DwarningAsError=true`; every leanchecker invocation names exactly one explicit module. Import dependencies are built by previous processes. A failed module stops the driver. Resume never increases limits.

`guard.sh` sets lane-local TMPDIR and caches, MALLOC_ARENA_MAX=2, affinity to CPUs 0 and 1, CPU time 120 s, wall time 140 s, and an RSS watchdog at 6 GiB. It waits for its wrapped process and leaves no worker running. Every Python utility must also be invoked through this guard, with its actual script path. The resource caps are fixed and must not be raised after failure.

Each module has full compiler/checker logs and separate elapsed-time/peak-RSS files. `Endpoint.lean` prints transitive axioms for the conditional endpoint, controls, and plane correspondence. `Audit.lean` inspects metadata of declarations belonging to every lane module, rejecting forbidden safety, partiality, implementation, external, assumption, or generated-recursion metadata. `scan.py` performs the independent source scan. Run it via `./guard.sh python "$PWD/scan.py" "$PWD"`.

The archive contains source, replay/audit utilities, documentation, and numeric evidence; it contains no compiled Lean artifacts. The fresh extracted replay is independent of `build/` in the working directory. `results.json` records that extraction's actual results and per-module measurements. The frozen Lean sources can be compared against `source-manifest.sha256`. The development generators are retained in the lane as provenance only; reproduction uses the frozen sources and does not run discovery-lane scripts.
