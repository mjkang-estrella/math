# Reproduction

Pinned Lean 4.34.1 binary:
`/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean`.
Read-only mathlib package path and all dependency paths are in scripts/env.sh.
Mathlib pin: d13f23b723b8a846827a245b89c10fc7d3f11612.

Every invocation below occurs inside the lane, sequentially. Each check.sh call
runs Lean with -j1 -M3500 -DwarningAsError=true, then leanchecker with that
explicit module name, both under capped.sh. The wrapper limits CPU to 120 s,
wall to 140 s, RSS to 6 GiB, taskset to CPUs 0,1, and MALLOC_ARENA_MAX=2. TMPDIR
and XDG_CACHE_HOME are lane-local. It waits for both the job and RSS monitor.
No tool-option probes are used.

1. `scripts/rebuild.sh` rebuilds modules.txt in dependency order; successful
   source hashes are recorded in build/*.ok, making interruption resumable.
2. `scripts/check.sh ChordModel3Audit > logs/audit-build.log 2>&1` generates
   audit.jsonl. It uses allowOpaque := true, walks the endpoint's whole import
   closure, inventories all generated declarations, and asserts exact set
   equality with the audited names. Local forbidden metadata or transitive
   axioms cause an error. Upstream metadata is reported separately.
3. `scripts/capped.sh python3 -I scripts/regression.py` independently tests
   every labelled pairing and side vector through five chords and every chord
   deletion. It tests both the ±1 law and the C-half-edge swap normalization.
   It also executes three negative controls. This is evidence, not a Lean proof.
4. `scripts/capped.sh python3 -I scripts/package.py` creates a source-only zip
   and extracts it to a new fresh-extraction directory, checking safe paths.
5. In fresh-extraction, run `scripts/rebuild.sh > logs/rebuild.log 2>&1` after
   creating logs/, and `scripts/check.sh ChordModel3Audit > logs/audit-build.log 2>&1`.
   All objects then originate in the new extraction; LEAN_PATH uses its build/.
6. In the main lane run `scripts/capped.sh python3 -I scripts/results.py`.
   It verifies every source against the fresh extraction, all 41 inherited
   sources against the frozen archive, every fresh successful build receipt,
   and the full audit and metadata counts, then writes results.json.

The source archive contains the audit tool as ChordModel3Audit.lean, separate
from the 46 formal modules in modules.txt. All inherited sources remain unchanged.
Replay logs are retained locally, outside the source-only zip.
