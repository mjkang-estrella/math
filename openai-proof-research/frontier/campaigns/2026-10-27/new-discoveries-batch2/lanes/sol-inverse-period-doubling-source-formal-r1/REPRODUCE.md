# Reproduction

Extract source-only.zip into an empty directory and run `bash REPLAY.sh`.
This reuses only the fixed installed Lean binary and the pinned package cache;
no previously built lane module is on LEAN_PATH. The replay directory is first
in LEAN_PATH and every mathematical module is built serially in dependency order.
It then runs Audit.lean. Source archives contain no .olean/.ilean artifacts.

The fixed binary SHA and all nine package pins are in packet/pins.json.
The package revisions are the recorded manifest pins, with selected source files
checked against immutable original/copy hashes; this is not a separate git checkout
verification. No git command was used. Administrative manifests are snapshots only.

Generic Python, hashing, copy/extraction and verification use the user-specified
absolute helper_guard.py, with OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
PYTHONDONTWRITEBYTECODE=1 and fixed AS/groupRSS512MiB CPU210 wall230.
Lean invocations use the frozen dedicated cube-formal guard to honor the explicit
no-extra-AS Lean exception, RSS2800MiB CPU210 wall230 and no cap raises.
The RSS ceiling is sampled every40ms, not a claim of an unsampled kernel hard limit.

After writing the final manifest, run the separate verify.py through that original
helper guard. Its receipt binds manifest/archive hashes and original/copy checks.
