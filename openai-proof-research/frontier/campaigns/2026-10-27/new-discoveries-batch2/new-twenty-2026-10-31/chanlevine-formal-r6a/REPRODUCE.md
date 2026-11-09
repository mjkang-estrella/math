# Reproduce the partial certificate

Use Lean 4.34.1 at /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin and the read-only mathlib packages at /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages, revision d13f23b723b8a846827a245b89c10fc7d3f11612.

From the lane run `python3 -I scripts/package.py` once. This verifies all 29 frozen hashes, writes the source-only archive, checks safe paths and extracts into a fresh empty lane-local directory. For the delivered extraction run `python3 -I fresh-extraction/scripts/replay.py --resume`. Without --resume every module is rebuilt. Receipts are keyed to the full source manifest; every compilation and leanchecker gets a unique retained log.

The driver builds all 36 modules in dependency order using strict warning-as-error compilation and leanchecker per module. It audits CountR6Controls' entire local module import closure, all generated declarations and transitive type/value dependencies. The Lean audit constructs exactly the reachable declaration set and checks all dependencies are included, with only the three permitted axioms. Python verifies the local module set independently against source imports and counts the audited declaration records. The instrumentation audit module itself is excluded from theorem seeds.

Five intentionally invalid Lean files must fail: wrong rotation, missing rotor factor, using either conditional endpoint without arguments, and wrong parity. Exact isolated Python checkers run with the same process caps. Logs include /usr/bin/time resource measurements. The cap script serially monitors each child process group for wall time and aggregate RSS and applies CPU affinity and RLIMIT_CPU.

Finally `python3 -I scripts/finalize.py` writes results.json from the extracted replay, checks frozen/source/archive equality and reports LOCAL separately from UPSTREAM executable metadata. Development reused inherited immutable compiled dependencies; the delivered fresh replay starts without any inherited build files.

The endpoints are conditional on two OPEN Props. A successful replay does not prove MathDB 338887.
