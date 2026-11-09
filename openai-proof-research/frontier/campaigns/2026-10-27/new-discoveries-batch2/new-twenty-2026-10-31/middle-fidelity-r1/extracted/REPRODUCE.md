All commands must be run within this lane. No network, git, lake build, or dependency writes are needed.

Pinned Lean: /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean (4.34.1).
Pinned read-only mathlib package directory: /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages, mathlib commit d13f23b723b8a846827a245b89c10fc7d3f11612.

The serial driver is:
    bash scripts/replay.sh "$PWD/fresh-extraction" "$PWD/fresh-extraction/build"

It is resumable: rerunning rebuilds each module serially, preserves uniquely named logs, and checks every module with an explicit leanchecker module argument. Compilation uses -j1 -M3500 -DwarningAsError=true. Every Lean, leanchecker and Python process is launched through scripts/run.sh. The wrapper uses two CPUs (0,1), MALLOC_ARENA_MAX=2, CPU 120 seconds, wall 140 seconds, and a process-group RSS watchdog at 6 GiB. Temporary files and caches are lane-local. No heavy process runs concurrently.

scripts/package.py constructs a source-only zip, verifies safe member paths, extracts into a newly created empty fresh-extraction directory and checks byte equality. It deliberately fails if that extraction directory already exists. The existing fresh extraction is retained for root review; use a new lane-local destination to repeat packaging. Launch Python only via scripts/run.sh and python3 -I.

MiddleAudit traverses the complete module import closure of MiddleFinal, including generated declarations. It checks that its audited declaration set equals the import-closure declaration inventory. It inspects types and values with allowOpaque := true, metadata, and transitive axioms. LOCAL checks forbid unsafe, partial, axiom declarations, _unsafe_rec, implemented_by and extern, and permit only propext, Classical.choice and Quot.sound transitively. Upstream metadata is reported separately, not subjected to a false claim that all of mathlib's compiler/runtime declarations are safe.

audit.jsonl contains a row for every declaration. scripts/report.py independently checks inventory/dependency coverage, reports LOCAL and upstream metadata, hashes sources, and writes results.json. The audit module's import closure is exactly the proof closure; the audit's own metaprogram is validation tooling. leanchecker checks that module too.

The three negative modules are intentionally invalid and must fail. The independent Python regression computes both minima by literal subset enumeration through cardinality 4 and checks source conventions, explicit witnesses and negative examples.

scripts/generate.py records the small-certificate generation method. Frozen Lean sources are authoritative; replay does not need to regenerate them. Each generated certificate is independently checked in Lean; Python is not a proof oracle.
