# Strict reproduction

Use Lean 4.34.1 at /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin. No network is used. Extract source-only.zip into a new directory inside this lane, rejecting absolute paths and parent components. Check `sha256sum -c source-manifest.sha256`.

Run `RESUME=1 BUDGET=55 bash replay.sh` repeatedly until every ordered module has passed. BUDGET is checked between modules; a started module may finish beyond the chunk budget. One compiler and one explicit-module leanchecker run serially per module. An exclusive flock prevents overlapping drivers. Successful stamps are skipped only if rolling source hashes and compiled-output hashes match. A failure stops replay.

Each process has affinity CPUs 0,1, CPU limit 120 s, wall limit 140 s, process-group RSS watchdog 6 GiB, MALLOC_ARENA_MAX=2 and local tmp/cache directories. Every Lean invocation uses -M3500 and -DwarningAsError=true. Never increase a limit after failure. Every Python call must likewise use guard.sh and a real script path, with python3 -I -B. For example: `bash guard.sh scan python3 -I -B scan.py "$PWD"`.

AuditR8 imports every delivered proof module and checks local metadata, including the expression builder, for local axioms, unsafety, partial definitions, extern bindings, compiler implementation substitutions and generated unsafe recursion helpers. EndpointR8 prints the endpoint axiom closure. Source scan strips strings and nested comments before checking executable forbidden tokens.

The archive is source only. Module times exclude failures, development and shell/watchdog overhead. Historical inherited.zip remains a separate byte-identical archive. Acceptance is for root to determine.
