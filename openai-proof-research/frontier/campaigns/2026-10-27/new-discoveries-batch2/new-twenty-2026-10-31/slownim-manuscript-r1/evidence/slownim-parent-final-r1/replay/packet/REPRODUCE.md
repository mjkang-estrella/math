# Reproduction

Pinned Lean: 4.34.1 at `/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin`.
Pinned read-only mathlib package root: `/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages`, mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Extract `source.zip` into a fresh directory inside this lane, cd there, then execute `./replay.sh`. No network, Lake build, shared cache writes, or toolchain installation is needed. `modules.txt` gives the dependency order. Each process handles exactly one module. After each successful Lean compilation the driver invokes `leanchecker MODULE` with that explicit module. Check `logs/Audit.lean.log` for the endpoint axiom list and local metadata audit, and `logs/source-scan.log` for the source scan.

Every Lean process passes `-M3500 -DwarningAsError=true`. Every Lean/leanchecker process runs through `run.sh`: two CPUs (0,1), CPU 120 seconds, wall 140 seconds (two-second forced-kill grace), process-group RSS watchdog at 6 GiB, `MALLOC_ARENA_MAX=2`, and lane-local TMPDIR and cache. The watchdog is joined on exit. No Python is needed. Independent modules are deliberately not parallelized.

The driver is resumable: per-module stamps bind the complete source set, watchdog and module order. If interrupted, rerun the same command; successful modules are skipped only if that binding agrees. For a genuinely fresh replay use a new extraction with no build or logs directories. The source archive contains no compiled files, dependency packages, or prior replay stamps.

The metadata audit covers all declarations with the SlowNim360653 namespace in their name, including any private generated declarations. It rejects unsafe/partial declarations, `_unsafe_rec` names, implementation-replacement and external attributes, and local axioms. The audit module itself uses Lean command metaprogramming solely to inspect the environment; its diagnostic strings necessarily mention prohibited metadata. It adds no declarations to the mathematical namespace. The source scan excludes that audit diagnostic file and checks every mathematical module. Manual inspection of Audit.lean is additionally required; the endpoint axiom closure is printed independently.
