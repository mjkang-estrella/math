# Reproduction

The source-only archive is `schrijver-source-r5.zip`; `source-archive.sha256` binds it. Extract it into a fresh empty lane-local directory. Run:

```
python3 -I scripts/replay.py --resume
```

The runner verifies SOURCE-MANIFEST.json, builds every module serially in outputs/modules.json dependency order, and runs leanchecker on each module. Only successful receipts for the same packet and existing output permit resumption. It uses Lean 4.34.1 at /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin and the read-only pinned mathlib cache at /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages (d13f23b723b8a846827a245b89c10fc7d3f11612).

Build flags: -j1 -M3500 -DwarningAsError=true. Each expensive subprocess has affinity to at most two available CPUs, CPU limit 120 seconds, wall limit 140 seconds, managed private RSS ceiling 6 GiB, MALLOC_ARENA_MAX=2, and lane-local TMPDIR and caches. Unique full logs and JSON resource receipts are retained. There is one heavy process at a time. Seven negative controls must fail by kernel decision, not by import errors.

`ClosureAuditRound5` audits every declaration in the endpoint's exact local import closure, including generated declarations; `AuditRound5` audits all mathematical source modules, including every frozen module and inherited audit module. Both reject unsafe or partial flags, _unsafe_rec companions, implemented_by, extern, and transitive axioms other than propext, Classical.choice, Quot.sound. The source archive excludes build outputs and replay logs; actual fresh-replay logs are delivered in fresh-extraction-r5/logs.

`scripts/package_r5.py` packages sources and creates a fresh directory; do not rerun it against an already-existing fresh-extraction-r5. `scripts/audit_r5.py` generates only the two new audit modules. No frozen source is modified by either script.
