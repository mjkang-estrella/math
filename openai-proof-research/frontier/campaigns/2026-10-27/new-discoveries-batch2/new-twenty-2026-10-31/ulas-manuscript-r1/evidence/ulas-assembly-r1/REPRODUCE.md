# Resumable serial replay

Lean binary: /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean (4.34.1).
Read-only mathlib packages: /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages, pinned to d13f23b723b8a846827a245b89c10fc7d3f11612.

From this lane, the commands below resume the existing fresh extraction. Each driver stage waits for its preceding process; do not run stages concurrently.

```bash
python3 -I scripts/replay.py "$PWD/fresh-replay" build
python3 -I scripts/replay.py "$PWD/fresh-replay" checker
python3 -I scripts/replay.py "$PWD/fresh-replay" audit
python3 -I scripts/replay.py "$PWD/fresh-replay" controls
```

For an independent replay, extract ulas-source.zip into a NEW EMPTY subdirectory of this lane and substitute that directory for fresh-replay. The archive contains only Lean sources, replay source scripts and the module-order manifest. Safe relative paths are checked by package.py. It includes 43 src modules and all 11 inherited control sources. No build products are used during extraction. Run the top-level driver above, or the identical archived scripts/replay.py with its own extraction directory as target. Keep all extraction paths inside this lane.

The build driver invokes lean -j1 -M3500 -DwarningAsError=true -o for every module in dependency order. Completed modules have logs/build-NAME.done markers. Checker and audit stages have their own completion markers. After changing a source, use a NEW extraction; completion markers assume unchanged archive bytes. Failed processes never create completion markers. Every invocation retains unique .log, .stderr and .result.json files. Failed attempts remain in the record.

Each heavy process runs under taskset -c 0,1, a 120 second CPU limit, timeout 140 seconds (with a 2 second forced-termination grace), MALLOC_ARENA_MAX=2 and scripts/bounded.py monitoring RSS at 6 GiB. Every Lean invocation uses -M3500. TMPDIR and XDG_CACHE_HOME point inside the target. Processes are strictly serial. Python bytecode writing is disabled or Python runs with -I; no network or mutable upstream cache is needed.

The audit script is instrumentation under scripts/, not a new inherited mathematical module. It imports UlasFinal5 and exports eight serial hash shards of every kernel declaration and all imported-module metadata. It includes opaque bodies with allowOpaque := true, generated declarations, unsafe/partial flags, _unsafe_rec companions, implemented_by, extern, and dependency edges. The analyzer proves set equality between the audited closure and the union of constNames for the import closure, computes all transitive axiom sets to a fixed point, and distinguishes LOCAL modules from upstream. Compiler IR-only extra names are inventoried separately. All LOCAL flags must be clear and LOCAL transitive axioms must lie in {propext, Classical.choice, Quot.sound}; upstream metadata is reported, not hidden or treated as a failure of unused proof dependencies.

Controls reproduce all eight packet *Negative*.lean examples, including false +2 even valuation, wrong colour convention, and nonexistent equality at m = 15. They must fail with a type mismatch. The three older negative-*.lean controls are preserved and also rerun. Controls are never imported by UlasFinal5 and do not produce accepted modules.

Audit summary: fresh-replay/logs/audit-summary.json. Full declaration exports: fresh-replay/logs/declarations-0.jsonl through declarations-7.jsonl. Per-declaration transitive axiom inventory: audit-summary.json.transitive-axioms.jsonl. Endpoint #print outputs, including theorem types and axioms, appear in build-UlasFinal5-*.log.

This is an implementation handback, not acceptance. Root independently replays and adjudicates.
