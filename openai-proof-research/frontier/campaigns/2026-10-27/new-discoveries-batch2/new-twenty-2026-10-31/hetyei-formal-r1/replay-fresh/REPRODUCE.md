# Reproduction

Extract source-only.zip into a fresh directory INSIDE hetyei-formal-r1, then run `bash replay.sh` from the extraction. To resume an interrupted unchanged extraction, run `bash replay.sh --resume`. Do not run multiple drivers concurrently. Receipts are bound to the full source/driver manifest; after changing anything, update the manifest and perform a new extraction.

The pinned distribution is /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux. Its version is Lean 4.34.1. The read-only mathlib package cache is /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages, pinned mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. No download or lake invocation is needed.

module-order.txt lists every module. Each is compiled in its own capped process with lean -j1 -M3500 -DwarningAsError=true, then checked in a separate capped process with leanchecker and an explicit module argument. The PATH shim also supplies -j1 and -M3500 to any Lean subprocess invoked by leanchecker.

capped.sh applies taskset to CPUs 0 and 1, CPU 120 seconds, wall 140 seconds, MALLOC_ARENA_MAX=2, and an RSS watchdog at 6 GiB. The watchdog sums the process tree and is joined after every call. TMPDIR, XDG_CACHE_HOME and all generated outputs are extraction-local. One heavy process runs at a time. No Python is needed. Full logs and receipts remain in logs and receipts.

Audit prints endpoint/control/range axiom lists and inspects every local declaration including generated companions for forbidden safety metadata, unchecked recursion companions, implementation redirection and extern attributes. It also checks transitive axioms of every local declaration against the three-name allowlist. The final source scan rejects proof placeholders and forbidden evaluation escapes. Audit itself contains strings naming the forbidden metadata for inspection purposes.

The completed fresh-extraction replay is retained at replay-fresh. Development artifacts remain in logs and tmp; successful extracted logs are authoritative for the final source manifest. Root must independently replay and review statement fidelity before acceptance.
