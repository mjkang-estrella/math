# Reproduction

Lean: /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean, version 4.34.1.

Read-only packages: /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages. The parent lake-manifest.json records mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. No dependency was modified or downloaded.

From a fresh extraction INSIDE this lane, create logs, tmp and cache directories, make scripts/*.sh executable, and run `bash scripts/rebuild.sh`. It compiles modules in strict dependency order with -j1 -M3500 -DwarningAsError=true, then exports the entire declaration metadata and checks the endpoint import closure. The rebuild resumes at the first changed/missing module and recompiles later modules. The wrapper retains uniquely named full logs, pins at most two allowed CPUs, sets CPU 120 seconds and wall 140 seconds per call, and uses a 6 GiB RSS watchdog. TMPDIR and XDG_CACHE_HOME are local to the extraction.

Run `bash scripts/checkers.sh` to call leanchecker on explicit module names, serially. Do NOT call leanchecker with only --help: this version ignores that unrecognized flag and scans its search path.

`python3 -I scripts/numeric.py` is an independent diagnostic regression against the read-only cached exact table. It computes the full unpruned top-max table through 20, the elementary recursion through 130, and four negative controls. Its generated certificate module is untrusted until compiled. It does not prove any combinatorial bridge. The fresh source replay does not require running this generator.

`StackSortAudit.lean` examines types and all values with allowOpaque := true, including all generated kernel declarations. Compiler extra symbol names are inventoried separately: they do not have ConstantInfo metadata when absent from the logical environment. scripts/check_audit.py independently reconstructs the import graph rooted at StackSortFinal and checks exact set equality against every module-record kernel constant name. Compiler-only symbols are inventoried separately. It then traverses each endpoint's constant dependency graph, checks transitive axioms, and reports LOCAL versus upstream metadata separately. Upstream compiler implementation metadata is reported, not confused with local declarations or with logical axioms.

The source archive contains Lean source, scripts, documentation and numeric trace, with only relative safe paths. No compiled objects are packaged. Replay logs and audit artifacts remain separately in this lane. Read results.json for the actual completed validation results and the resource exception.
