# Round 7A replay

All writes and build products must remain in the assigned round-7A lane.
Run `bash scripts/replay7a.sh` from the source directory. It compiles each
module separately with -j1 -M3500 -DwarningAsError=true, then invokes
leanchecker with that explicit module. `RESUME=1 bash scripts/replay7a.sh`
resumes completed markers. Resume only after unchanged dependencies; remove
build/ for an independent fresh run.

For a fresh extraction, create a new empty subdirectory of this lane, unzip
source.zip there, then run its scripts/replay7a.sh. The script locates itself,
so build, logs, TMPDIR and caches remain in the extracted directory. Every
Lean, checker and Python call passes through scripts/capped.sh: two CPUs,
120 CPU seconds, 140 wall seconds, aggregate process-group RSS watchdog at
6 GiB, MALLOC_ARENA_MAX=2. No checker invocation omits its module argument.
Mathlib package files and the Lean 4.34.1 toolchain are read-only external
inputs at the exact paths in scripts/env.sh.

The audit uses allowOpaque := true, all generated local declarations as
seeds, recursive types and values, inductive companions and _unsafe_rec
companions; it verifies closure before writing audit.tsv. report7a.py checks
allowed axioms and reports local metadata separately from upstream metadata.
The manifest checks all 45 frozen modules before and after. Numerical checks
include n = 3,4,5,6 for the binary identities and inherited negative controls.
Logs use unique nanosecond names and preserve failures as well as successes.

`source.zip` contains source and replay scripts only, with relative safe paths.
The frozen round-6A and round-4B archive hashes are recorded in results.json.
`bridge-imports.sha256` pairs each of the 20 common round-4B module digests
with the corresponding lane source digest; all pairs must agree. The copied
bridge modules have their own `bridge-before.sha256` manifest. Source-only
packing also checks both frozen archives against the supplied source files.

Validation artifacts in the lane: logs/replay7a-local.out is the serial local
run, logs/replay7a-fresh.out is the independent empty-directory extraction
run, replay-fresh/logs/ contains its complete per-process logs, and
audit.tsv contains the full dependency-closure metadata. module-final.sha256
and module-fresh.sha256 compare the actual replayed Lean sources. The early
base-only log ends with the inherited round-6A reporter's manifest-count
assertion (37 versus the new 45); the corrected round-7A driver and reporter
replace it and must both finish successfully. Development failures remain
in logs/ rather than being deleted.
