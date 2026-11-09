# Round 6 replay

Use Lean 4.34.1 and the read-only pinned mathlib package roots in scripts/env.sh (mathlib d13f23b723b8a846827a245b89c10fc7d3f11612).

Run `bash scripts/validate.sh` from the extracted packet directory. It strictly serially builds and leanchecks all modules in modules.txt. Each compiler uses -j1 -M3500 -DwarningAsError=true. Each leanchecker receives its explicit module argument. Build success markers contain source hashes; after editing a source, delete its marker and downstream markers before replay. Fresh extraction contains no build products or markers.

Every Lean, leanchecker and Python process must run through scripts/capped.sh: two CPUs (0,1), CPU 120 seconds, wall 140 seconds, 6 GiB sampled RSS watchdog, MALLOC_ARENA_MAX=2, lane-local TMPDIR and cache. Run only one driver at a time. The wrapper waits for and reaps both the command and watchdog. Logs have unique nanosecond names. Do not invoke leanchecker without a module.

Run `bash scripts/controls.sh` for expected-failure controls, then `scripts/capped.sh python3 -I scripts/regression6.py` for independent numerical checks. Those checks are not proofs. Chord6Audit audits the complete endpoint import closure, including generated declarations and opaque proof bodies; it checks exact equality with the imported module inventory and writes audit6.jsonl. LOCAL and upstream metadata totals are reported separately in results.json.

The source archive is chord6-source.zip. It includes all 144 frozen modules and the Chord6 additions, scripts, module order, controls and documentation, but no object files. inherited-before.sha256 binds all frozen modules; `sha256sum -c inherited-before.sha256` checks their bytes. The input packet SHA-256 is 6be45630fee1ea460e8c66b5ae23a831bcc41ba85108afbb1f38f396dc9dd1ec.

The endpoint is Chord6Final to obey the binding Chord6*.lean naming rule. It is conditional on three independent Props. Replay and audit success are not acceptance. Root decides.
