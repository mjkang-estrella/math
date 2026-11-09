All commands run from this review lane. Do not run heavy commands concurrently.

1. The supplied source archive was extracted into the initially empty packet/.
2. Inspect packet/scripts/run.sh, watch.pl, lean.sh, prep.py and replay.sh.
3. Run `(cd packet && bash scripts/replay.sh) > logs/replay-driver.log 2>&1`.
4. Run `bash packet/scripts/run.sh python3 -I scripts/enumerate.py > logs/enumeration.log 2>&1`.
5. Run `packet/scripts/lean.sh --root=. -o packet/build/Sanity.olean Sanity.lean > logs/sanity-compile.log 2>&1`.
6. Run `LEAN_TOOL=leanchecker packet/scripts/lean.sh Sanity > logs/sanity-checker.log 2>&1`.
7. Run `perl scripts/scan.pl packet/src/*.lean > logs/forbidden-scan.log`.
8. Rehash inputs.list (sha256sum each absolute path) into inputs-after.sha256;
   rehash pinned Mathlib/Tactic/Bound/Attribute.lean into upstream-bound-after.sha256.
9. Run `bash packet/scripts/run.sh python3 -I scripts/finalize.py > logs/finalize.log 2>&1`.

The Lean executable is the exact 4.34.1 executable in the task brief. All Python,
Lean and leanchecker calls use the RSS/CPU/wall/affinity-capped runner.
The packet's replay checks explicit module arguments and all 47 modules,
including the six audit modules. It also requires four negative controls to fail.
This is this review's replay evidence, not root's decisive acceptance replay.
