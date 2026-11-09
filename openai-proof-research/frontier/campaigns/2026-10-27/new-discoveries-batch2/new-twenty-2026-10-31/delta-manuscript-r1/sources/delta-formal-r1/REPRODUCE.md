# Resumable capped replay

Lean: `/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean`, version 4.34.1 as specified by the assignment. Read-only mathlib package root: `/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages`; required mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612. These upstream objects are trusted dependencies, not bundled into the source archive. No dependency installation or network access is performed.

Extract `source.zip` into a NEW directory inside this lane, then run `bash scripts/replay.sh` from that extraction. The default replays everything. `bash scripts/replay.sh --resume` resumes modules bearing successful replay markers and newer oleans. Resume assumes unchanged earlier sources/dependencies; use a fresh extraction after modifications. Do not run two replay drivers concurrently.

Each module is compiled in a separate process using `lean -M3500 -DwarningAsError=true`, followed by `leanchecker MODULE` in another process. Every Lean and leanchecker invocation passes through `scripts/cap.sh`: taskset CPUs 0 and 1, CPU 120 seconds, wall 140 seconds, RSS group watchdog at 6291456 KiB, MALLOC_ARENA_MAX=2, lane-local TMPDIR and cache. Core dumps are disabled. No limit is raised on failure. The driver stops immediately on failure and preserves logs. The wrapper reaps both the process and its watchdog. `modules.txt` is the authoritative dependency order.

Python is not needed for replay. Source generation used the same capped wrapper with `python -I`, and read only the supplied data JSON. The discovery scripts were never executed. The source archive includes the already generated Lean modules, so root does not need any other lane to rebuild the proof modules.

`Audit.lean` scans the metadata of all declarations in this lane's namespaces and rejects unsafe/partial declarations, implementation replacement, external linkage, unsafe-recursion names and added axioms. It also prints the conditional endpoint's transitive axioms. The source scan is performed separately and logged. Only propext, Classical.choice and Quot.sound are permitted.

The endpoint is explicitly CONDITIONAL. A successful strict replay confirms the closed pieces and the conditional implication; it does not discharge the residual hypotheses or constitute acceptance.

## Handback checkpoint

The final archive lists 609 modules. Serialized fresh replay checked 131 modules, ending at Closure107. AuditPartial was additionally compiled and checked separately (logs/AuditPartial.log and logs/AuditPartial-checker.log). The metadata audit covers the closed prefix, not the uncompiled remainder. The wrapper's temporary pause hook was removed and no target/watchdog remains running. `bash replay-r1/scripts/replay.sh --resume` recompiles AuditPartial and resumes Closure108; full replay has not finished.

source.zip was amended after initial extraction only in the audit sources and manifests, not in any of the 131 replayed modules. The initial archive hash is retained in logs/replay-initial-archive.sha256. A full strict replay of the delivered final archive is outstanding. All original caps remain fixed.
