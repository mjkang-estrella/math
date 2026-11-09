# Replay and limits

This is a partial certificate-elaboration experiment. No command here proves the unconditional endpoint. `EndpointAttempt.lean` is a preserved failed full-endpoint experiment. Generated files not listed in `replay-modules.json` are unvalidated obligations, not certified theorems.

Run `bash run.sh` from this directory. The replay serially rebuilds the four byte-identical inherited mathematical modules and the successful generated local-rule modules listed in `replay-modules.json`, then runs the declaration audit. It does not run the failed full-endpoint experiment or silently accept uncompiled generated files.

Lean is the pinned 4.34.1 executable, SHA256 e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550. All nine package revisions are in `pins.json`; Mathlib is d13f23b723b8a846827a245b89c10fc7d3f11612. There is no download, update, git command, or compiler substitution. Each Lean invocation uses the inherited `lean_guard.py`: -j1 -M2700, warningAsError=true, autoImplicit=false, sampled group RSS2800MiB, CPU210, wall230, no separate AS cap. Guards sample every 40ms; overshoot between samples is possible. Caps are never raised.

All non-Lean Python, generation, packaging, hashing, and verification run through `/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py`, with OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1, fixed AS/group RSS512MiB, CPU210, wall230. The inherited dedicated Lean launcher is the explicit no-AS exception; launching Lean under the 512MiB helper would impose the forbidden extra AS cap.

`source-only.tar.gz` uses sorted member paths, uid/gid0, mode0644, mtime0 and gzip mtime0. It excludes compiled own artifacts. A fresh extraction under `fresh-replay/` is rebuilt using exactly the same strict settings. The final manifest excludes itself and the final verification receipt; a separate guarded final verification occurs after substantive writes.
