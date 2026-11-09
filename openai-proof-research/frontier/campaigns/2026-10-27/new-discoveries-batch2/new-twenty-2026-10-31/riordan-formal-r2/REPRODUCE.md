# Replay

Run from this lane:

    python3 -I scripts/replay.py

This creates a new empty, uniquely named lane-local directory and safely extracts 338258-infinite-family-source.zip. It builds the 20 proof modules serially in dependency order, then the preserved Audit and new StrongAudit tooling modules, using Lean 4.34.1 with -j1 -M3500 -DwarningAsError=true. It then runs leanchecker separately on all 22 modules and checks three deliberately false controls. A control must fail compilation. Full, uniquely named logs and JSON resource receipts are under logs/.

To resume an interrupted replay, pass the absolute path to its fresh directory:

    python3 -I scripts/replay.py /absolute/path/inside/this/lane/fresh-TIMESTAMP

The driver checks archive identity and extracted source bytes and resumes the recorded build/check steps. For an independent clean rebuild omit the argument. Do not edit previously built sources when resuming. The latest fully completed extraction is recorded in latest-replay.txt. replay-state.json records individual build, checker and negative-control outcomes.

The source archive contains only Lean source, with flat safe paths. It contains no olean or supplied compiled code. All original 18 proof modules and the original archive's auxiliary Audit.lean are preserved byte-for-byte. frozen-before.json and frozen-after.json include all 19 original Lean source files, making the freeze check stronger than the required 18 modules.

scripts/lean.py sets LEAN_PATH to the selected extraction and the read-only caches under /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages. The mathlib pin is d13f23b723b8a846827a245b89c10fc7d3f11612. The binary directory is /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin. Upstream mathlib is trusted rather than rebuilt.

scripts/run.py limits each expensive process to two allowed CPUs, 120 CPU seconds, 140 wall seconds, MALLOC_ARENA_MAX=2 and a sampled process-group RSS ceiling of 6 GiB. Virtual address space is 12 GiB to accommodate mapped caches. RSS sampling is not a cgroup hard limit. Temporary and cache paths are lane-local. Only one expensive process runs at a time. Logs are never overwritten.

StrongAudit inventories every generated and ordinary declaration from all 20 local proof modules in the endpoints' import closure. It then traverses every type and kernel body dependency, including upstream declarations, and audits the resulting transitive closure. It verifies that every seed and every dependency edge lies in the audited set; traversal inserts only seeds or dependencies, establishing equality. It rejects unsafe/partial declarations, _unsafe_rec companions and disallowed axioms throughout that closure, and runtime replacement attributes in local declarations. It inventories upstream extern and implemented_by attributes separately: upstream kernel primitives such as Nat.add carry runtime attributes, but their kernel bodies, rather than external execution, are used by these proofs. The resulting counts and full declaration inventory appear in the StrongAudit log. This is a declaration-dependency closure audit, not a rejection of unrelated metaprogramming declarations elsewhere in imported mathlib modules.

The false controls are: the original polynomial's infinite identity at j = 7; the value h 6 after deleting odd part 7 from the defining set; and the claim that xR has zero odd part. Their source files are under scripts/ and are copied into the extraction after the successful builds. They are deliberately excluded from the successful source archive.
