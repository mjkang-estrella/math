# Reproduction

Run from this lane. Use `python3 -I -B` for every Python invocation; the `-B` is required even with `-I`.

Numerical diagnostics (one at a time):

    python3 -I -B scripts/limited.py NEW_NAME python3 -I -B scripts/matroid_certificate.py
    python3 -I -B scripts/limited.py NEW_NAME python3 -I -B scripts/seaweed.py exhaustive 13
    python3 -I -B scripts/limited.py NEW_NAME python3 -I -B scripts/seaweed.py random
    python3 -I -B scripts/limited.py NEW_NAME python3 -I -B scripts/perm_components.py 9
    python3 -I -B scripts/limited.py NEW_NAME python3 -I -B scripts/covering.py

Use a fresh log name for each invocation. The retained logs are the original complete outputs, not just selected successes. Historical Lean generation scripts explain the attempts; the final `.lean` files and source manifest are authoritative.

The module order is Bases, Cases0 through Cases7, Endpoint, Final, Audit. The final packet contains only these local Lean sources. `scripts/package_replay.py` documents safe allowlisted extraction, sanitization, sequential capped strict compilation, and `leanchecker` for every module. Its archive and extraction paths are deliberately exclusive, so a rerun must use fresh lane-local paths and log names. The completed replay uses replay-final/build. Do not reuse its oleans as a substitute for a fresh rebuild. `scripts/replay_run.sh BUILD_DIRECTORY lean ...` and `... leanchecker MODULE` set the pinned upstream package search path without changing dependencies.

Accepted axioms: propext, Classical.choice, Quot.sound only. No native_decide, ofReduceBool, sorry, admit, added axioms, unsafe declarations or implementation redirection is allowed. Audit.lean checks every local namespace declaration and its transitive axioms/metadata, including generated declarations.
