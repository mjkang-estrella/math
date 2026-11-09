# Strict capped replay

Use Lean 4.34.1 from /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin. Read-only mathlib and companion packages are in /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages. Mathlib HEAD is d13f23b723b8a846827a245b89c10fc7d3f11612 (read directly from .git/HEAD, without invoking git).

Extract source-only.zip into a fresh directory within the assigned lane, enter it, and run `./replay.sh`. The script uses one module per Lean process, followed by leanchecker with the explicit module name. It sets -M3500 and -DwarningAsError=true on every Lean compilation. Module order is Base, Bridges, CountBase, S00 through S19, T00 through T20, Counts, Controls, Endpoint, Audit.

Every heavy command passes through capped.sh: two CPUs (0,1), inherited CPU limit 120 seconds, timeout 140 seconds with a two-second forced-kill grace, a process-group RSS watchdog at 6 GiB, MALLOC_ARENA_MAX=2. The watchdog samples aggregate process-group RSS every 0.1 seconds and kills the whole group on a breach. TMPDIR and XDG_CACHE_HOME are extraction-local. The trap terminates and reaps the watchdog at command completion. /usr/bin/time -v records per-call usage in the logs. No concurrent heavy processes are started by these scripts.

After interruption, `RESUME=1 ./replay.sh` skips modules having a strict success marker. Use this only in the same extraction with unchanged sources and dependencies; otherwise start fresh. Success markers are written only after both compilation and explicit-module leanchecker pass. A nonzero command aborts the driver. Limits must never be raised after failure.

Audit.lean prints the endpoint and control axioms, and checks namespace-local declaration metadata for unsafe or partial definitions, compiler implementation substitutions, extern declarations, generated unsafe recursion, and new axioms. It throws an error on any flag. The lexical source scan excludes Audit.lean because it names the forbidden metadata it is testing. All mathematical source files are scanned. Audit.lean itself must be read as the checking program, rather than as a mathematical assumption.

The development full-import and unsplit count failures are preserved in logs; they are not part of the final source packet. Root should inspect SUMMARY.md, results.json and replay/ logs before deciding acceptance. No acceptance is claimed here.
