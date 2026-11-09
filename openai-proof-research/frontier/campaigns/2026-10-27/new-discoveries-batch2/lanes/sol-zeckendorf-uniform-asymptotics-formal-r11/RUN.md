# Bounded reproduction

From this lane, `sh run.sh` serially compiles the eighteen mathematical modules and runs the name-aware standalone full-body audit. Every helper invocation goes through the fixed helper_guard.py path in run.sh with OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1. The helper guard has fixed512MiB AS/groupRSS, CPU210s, wall230s. The serial Lean child uses -j1 -M2700, warningAsError=true and autoImplicit=false, groupRSS2800MiB, CPU210s, wall230s; runner.py records attempted source, output and resource receipt for every call.

Invoke `python "$G" python certify.py pack`, then `python "$G" python certify.py replay`, with G the helper guard path from run.sh. Replay extracts source-only.zip into replay/fresh and checks archive hashes before/after. It compiles all source-only modules serially, repeats the full-body audit and removes all compiled artifacts in the lane. Pins and input bindings are checked before/after.

After writing implementation-receipt.json and failures.json, invoke guarded `certify.py manifest`. Then invoke guarded `certify.py verify` separately. MANIFEST.json excludes itself and verification-receipt.json. Do not modify manifested files after final verification. Existing replay/fresh is intentionally not overwritten; use a fresh copy of the packet for another full replay.
