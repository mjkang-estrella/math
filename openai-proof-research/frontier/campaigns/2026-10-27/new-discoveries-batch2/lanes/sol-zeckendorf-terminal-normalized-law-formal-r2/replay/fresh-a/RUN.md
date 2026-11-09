# Strict serial replay

All Python invocations must run through the fixed helper guard with
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1.
The absolute guard is
/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py.

The helper stays at AS/group RSS512MiB, CPU210s, wall230s. Only runner.py's
serial Lean child uses the explicitly authorized exception: -j1 -M2700,
group RSS2800MiB, CPU210s, wall230s, warningAsError=true, autoImplicit=false.
The pinned compiler hash is checked on every invocation. No package is edited.

From this lane, guarded `python certify.py replay` extracts source-only.zip
twice into fresh-a and fresh-b (those directories must initially be absent).
Each replay compiles Literal, Terminal and Law in that order, then runs
Inventory.lean and Audit.lean. It verifies all archive source hashes before
and after, all nine package revisions, exhaustive declaration inventory,
type/body transitive safety and axiom closure, and deterministic diagnostics.
It removes owned compiled objects. Receipts/logs persist for all attempts.

For a manually extracted source-only.zip: guarded `python runner.py -o
Literal.olean Literal.lean`, then the same command for Terminal and Law,
then guarded `python runner.py Inventory.lean` and `python runner.py Audit.lean`.
The archive is source only and uses immutable installed package object caches.
It does not rebuild mathlib or certify upstream truth or package working-tree
cleanliness. All nine immutable revision pins are compared with the original
formal project's manifest without invoking git.

After all delivery writes: guarded `python finalize.py manifest`, followed by
a separate guarded `python finalize.py verify`. MANIFEST.json excludes itself
and verification-receipt.json. No other final writes follow verification.
