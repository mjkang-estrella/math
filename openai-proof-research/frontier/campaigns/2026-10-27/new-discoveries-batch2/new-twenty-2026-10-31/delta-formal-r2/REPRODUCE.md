# Round 2 reproduction

All commands run from the round 2 lane. No network or dependency installation is used. Lean is /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean (4.34.1). Read-only package root is /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages, with required mathlib pin d13f23b723b8a846827a245b89c10fc7d3f11612.

Extract source.zip into a NEW directory INSIDE this lane and run `bash scripts/replay.sh`. The 634-module modules.txt is the dependency order. Every module compiles separately with `lean -M3500 -DwarningAsError=true`, then `leanchecker MODULE` in its own capped process. `--resume` skips only successfully marked modules with oleans newer than their unchanged source. After source or dependency changes, use a new extraction. Never run two drivers concurrently.

`scripts/replay-prefix.sh` replays the 46-module prefix closing the new bridges, chain obstruction, single-premise endpoint and partial audit. It does not compile the canonical certificate. `scripts/replay-certificate.sh START END` replays the indicated closure chunk interval, default 108 through 581, and assumes earlier dependencies already exist in that extraction. No inherited object is a fresh replay receipt.

Each wrapper uses taskset CPUs 0 and 1, CPU 120 seconds, wall 140 seconds, an RSS process-group watchdog at 6291456 KiB, MALLOC_ARENA_MAX=2, lane-local TMPDIR and XDG_CACHE_HOME, and disabled core dumps. Limits are never increased. Python generation used this same wrapper. No Python is necessary for replay. Explicit-module leanchecker calls are mandatory. Both the target and watchdog are reaped before the wrapper returns.

To request a controlled stop, create STOP_REPLAY at the lane root. Drivers stop only after a module has compiled and passed leanchecker, with exit75; remove the file before resuming. No process should remain at handback. The currently recorded frontier is in results.json and logs.

Run `bash scripts/source-scan.sh` for the forbidden proof-token/declaration scan. Metadata audits additionally reject local unsafe/partial declarations, added axioms, implementation replacement, external linkage and unsafe recursion metadata. Only propext, Classical.choice and Quot.sound may occur in the printed axiom lists. The full original Audit and added Round2Audit require the entire certificate and endpoint dependency chain. Round2AuditPartial covers only its imported proof prefix.

`logs/original-lean-byte-check.log` verifies all 609 original Lean modules against round 1's source manifest. The source archive contains only sources, manifests and replay scripts, with no generated Lean objects. Experimental unsuccessful approaches are excluded from its module list and archive. Development resource incidents, including a possible brief overlap between two failed development checks, are disclosed separately; they are not strict-replay receipts.

The archive may contain an unchecked generated unconditional endpoint. Read results.json and SUMMARY.md before interpreting status. This lane does not self-accept.

The inherited closure objects in replay-r2/build have no round2 `.ok` markers. Consequently `bash replay-r2/scripts/replay.sh --resume` recompiles that inherited prefix as well as completing the remaining modules; it does not falsely treat those copied dependencies as a round2 fresh replay. This is the recommended single-command full resume from the delivered extraction. A new extraction of source.zip with `bash scripts/replay.sh` remains the cleanest complete replay.
