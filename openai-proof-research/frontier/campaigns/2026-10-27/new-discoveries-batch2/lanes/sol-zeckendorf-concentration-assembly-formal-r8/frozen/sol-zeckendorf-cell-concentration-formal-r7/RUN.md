# Reproduction

Environment: OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1. All Python operations run through the unchanged helper_guard.py at the exact path in run.sh. Helper caps: AS/group RSS512MiB, CPU210s, wall230s. The approved Lean child uses the separately authorized serial j1, M2700, groupRSS2800MiB, CPU210s, wall230s; runner preserves failures and source snapshots. No cap raises from those approved values. warningAsError=true, autoImplicit=false.

Pinned compiler and package paths are absolute in runner.py; compiler hash and all nine package revisions are checked. Source order:

    Literal Terminal Law Cells Product Prefix Marks Boards Injection Abundance Tail Concentration

In a clean extracted source-only.zip directory, compile serially using `bash run.sh -o NAME.olean NAME.lean` for each module in that order, then `bash run.sh Inventory.lean` and `bash run.sh Audit.lean`. This reproduces the proof and exhaustive origin/type/body safety audit. Remove the resulting compiled files after inspection. Inventory/Audit are metaprogram audit instrumentation, not mathematical proof origins. Every declaration in all twelve mathematical origins, including private/generated declarations, is inventoried by Lean Name and module origin. Unsafe AND partial safety are hard rejected on every owned declaration and every transitive type/body dependency; only propext, Classical.choice and Quot.sound axioms allowed.

Parent packet operations: guarded `python certify.py pack`, then in a SEPARATE guarded call `python certify.py replay`. Replay makes replay/fresh exclusively by source archive extraction, checks the deterministic archive hashes, serially compiles all twelve modules and both audits, compares complete declaration/axiom inventories, and removes all own compiled objects. Then guarded `python certify.py manifest`; finally a SEPARATE guarded `python certify.py verify`. Full parent verification needs the immutable originals/frozen references at paths in bindings and immutable-references; the source-only Lean replay needs only pinned tools/packages. Administrative files are immutable local snapshots, not requirements on later shared originals.

MANIFEST.json excludes itself and verification-receipt.json. The final receipt binds its hash. source-only.zip has fixed file timestamps, order and permissions, excludes compiled files and historical evidence trees, and includes per-file SHA-256 archive-files.json. This packet reports partial scientific completion regardless of successful verification.
