# Replay of the r3 partial certificate

The packet has no literal refutation endpoint. Extract contact-r3-source.zip
into a NEW EMPTY directory inside this lane, then run:

```bash
LEAN_BIN=/path/to/lean-4.34.1-linux/bin/lean \
LEAN_PACKAGES=/path/to/pinned/.lake/packages \
python3 -I -B scripts/replay.py
```

Use Lean 4.34.1 commit 5045d0056413266e57c625dcd7c365b10e377c52 and mathlib
revision d13f23b723b8a846827a245b89c10fc7d3f11612 with its cached dependencies.
The two environment variables select read-only toolchain/package locations.
No package fetching or installation occurs. Existing local oleans, ileans,
ir files or a build directory cause refusal. Python runs isolated with
bytecode disabled. Temporary paths are inside the extraction's logs.

The driver sanitizes source, sequentially compiles 13 modules with
`-j1 -DwarningAsError=true`, invokes leanchecker separately on every module,
and runs eight expected-failure controls. A killed process or a nonstandard
negative-control exit is a failure. Each call has at most two CPUs, CPU
120 seconds, wall 140 seconds, a sampled aggregate private RSS watchdog at
6 GiB and MALLOC_ARENA_MAX=2. Every receipt keeps the resource samples.
Only one heavy process runs at a time; no background worker survives replay.

AuditR3 enumerates ALL local environment constants by owning module, including
private and compiler-generated names. It records module, unsafe/partial flags,
full expression-DAG type and opaque-inclusive value (`value? true`) and
transitive axioms. Only propext, Classical.choice and Quot.sound are permitted.
Generated names, including any _unsafe_rec companion, are not filtered out.
The independent audit_inventory.py validates all DAG references, declarations,
flags and axioms, writing replay-logs/audit-inventory.json. AuditR3's direct
full log is replay-logs/audit-r3.dag. Earlier audit modules are retained intact.
Large stdout logs are losslessly gzipped and replaced by an archive pointer.

The complete.json receipt binds all module source hashes. For the submitted
packet the final extraction is work/extracted-02; its full replay-logs are
retained in this lane. Successful replay validates ONLY the partial theorems
in the correspondence table. See GAPS.md for the exact next lemma.
