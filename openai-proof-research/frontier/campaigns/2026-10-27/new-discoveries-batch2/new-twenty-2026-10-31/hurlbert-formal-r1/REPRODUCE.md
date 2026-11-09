# Reproduction

Run from this lane directory. All writes must stay here. The source archive `proof-source.zip` contains only five .lean sources and module-order.txt; no binaries or executable scripts. The supporting scripts in scripts/ are outside that archive and readable for review.

Dependencies: Lean 4.34.1 at /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin; read-only mathlib packages at /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages, pinned mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. scripts/env.sh sets the matching PATH and LEAN_PATH. This trusts supplied prebuilt upstream oleans; it does not rebuild mathlib or independently implement Lean's kernel.

To repeat in a new extraction directory:

```bash
scripts/capped.sh python3 -I -B "$PWD/scripts/extract.py" replay-root
scripts/replay.sh replay-root
```

The extractor checks the exact file whitelist, size cap, no duplicate names and byte equality with reviewed src/ before writing a previously nonexistent lane-local directory. Build order is Hurlbert, Endpoints, Control, Inventory, AllAxioms, recorded in module-order.txt and inside the archive. The replay driver compiles one module per process, then invokes `leanchecker MODULE` explicitly for that module. Every Lean invocation uses `-j1 -M3500 -DwarningAsError=true`. It stops at the first failing build/checker and retains full stdout/stderr and status lines in logs/EXTRACTION-NAME/.

After a resource interruption, resume at the first unfinished module, preserving earlier successful extracted oleans:

```bash
scripts/replay.sh replay-root Control
```

This recompiles and checks Control, Inventory and AllAxioms. Do not resume past an unsuccessful dependency. A fresh full replay starts at Hurlbert, the default. Source changes require regenerating the source archive and a new fresh full replay, not just a resume.

Every Lean, leanchecker and Python process runs through scripts/capped.sh: CPU 120 seconds, wall 140 seconds (2-second termination grace), affinity to two allowed CPUs, aggregate process-group RSS watchdog at 6 GiB, MALLOC_ARENA_MAX=2, and lane-local TMPDIR and cache. The wrapper reaps its watchdog before returning. Heavy processes are sequential. Do not invoke leanchecker without an explicit module or increase caps after a failure.

Inventory checks all 23 MathDB356266 declarations, including generated proof declarations, for unsafe/partial status, axiom declaration kind, implementation overrides, external implementations and unsafe recursion names. AllAxioms explicitly prints both requested endpoint axiom sets, then traverses the transitive axiom dependencies of every local namespace declaration and fails on anything outside propext, Classical.choice and Quot.sound. scan.py scans all extracted Lean sources for forbidden proof/declaration tokens after excluding strings and comments. The audit's own error strings mention forbidden features but do not use them.

To regenerate the archive after an authorized source change:

```bash
scripts/capped.sh python3 -I -B "$PWD/scripts/package.py"
```

The original Hurlbert.lean must keep its supplied hash. `make_control.py` records the untrusted, reproducible rank-table generation from the printed CDG word; the formal positive control independently checks the resulting table.
