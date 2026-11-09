# Serial guarded replay

All Python/helper executions use the absolute fixed guard:
/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py
with OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1.
Run from this lane: `python GUARD python certify.py pack`, then the same with
`replay`. Substitute the absolute guard path above for GUARD.

The helper has AS/group RSS 512MiB, CPU210s, wall230s, unchanged. Only runner.py's
serial Lean child has the explicit approved exception: j1, M2700, sampled
process-group RSS2800MiB, CPU210s and wall230s. warningAsError=true and
autoImplicit=false. The compiler SHA is checked on every invocation. Group RSS
is sampled every 40ms; unsampled transients are not ruled out.

For an extraction, compile Literal, Terminal, Law, Cells in order through
guarded `python runner.py -o NAME.olean NAME.lean`; then run guarded runner.py
Inventory.lean and Audit.lean. Installed pinned package object caches are used.
No package rebuild or upstream-truth audit is asserted. All nine package
revision pins and the original package manifest are checked without git commands.

Inventory enumerates EVERY actual origin in all four mathematical modules,
including private/generated declarations and instances. It traverses both
types and bodies transitively. Unsafe definitions abort; every partial is
explicitly flagged REJECTED, and audit.json records the resulting HOLD. The
inherited words._unsafe_rec prevents a strict PASS despite byte preservation.
Audit #checks each actual declaration and #prints its complete axiom closure.
Only propext, Classical.choice and Quot.sound are allowed.

certify.py replay freshly extracts source-only.zip twice, checks source hashes
before/after, compiles and audits serially, compares deterministic diagnostics,
and removes owned compiled objects. Archive entries use fixed timestamps and
permissions. certify.py is orchestrated from the lane, not from inside the
archive, because scientific bindings deliberately refer to immutable evidence
outside the source-only mathematical archive.

After all delivery writes, run guarded `python certify.py manifest` and then
a SEPARATE guarded `python certify.py verify`. MANIFEST.json excludes exactly
its own top-level path and the final verification-receipt.json. No delivery
writes follow that verification.
