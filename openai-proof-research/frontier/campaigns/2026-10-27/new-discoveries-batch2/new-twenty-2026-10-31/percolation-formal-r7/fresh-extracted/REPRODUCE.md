# Strict reproduction

Use the fixed Lean 4.34.1 installation named in TASK.txt. No network is used. Extract source-only.zip safely into a fresh directory inside this lane, rejecting absolute paths and parent components. Verify `sha256sum -c source-manifest.sha256` there.

Run `RESUME=1 BUDGET=55 bash replay.sh` repeatedly until all ordered modules finish. BUDGET is a wall budget checked between modules; each started module may finish after that chunk budget. Every compiler and checker is separately bounded. The driver checks rolling source and compiled-output hashes before skipping a successful module. A failure stops replay.

The guard imposes process-group RSS 6 GiB, affinity CPUs 0 and 1, CPU 120 seconds, wall 140 seconds, MALLOC_ARENA_MAX=2 and extraction-local temporary and cache directories. Every Lean invocation includes -M3500 and strict warning checking. Each leanchecker invocation names exactly one module. Python calls use the same guard, `python3 -I -B` and a real script path. Run one heavy process at a time.

Successful totals in module-times.json exclude failures and development runs. Full logs preserve those failures. AuditR7 imports every ordered proof module and audits local declaration metadata, including the expression builder. EndpointR7 prints the transitive axiom list. The source scan rejects forbidden executable tokens after stripping strings and nested comments.

The archive contains source only, without compiled artifacts. The round 5 inherited archive remains a separately preserved historical packet and is not silently counted as freshly rebuilt. Root decides acceptance.
