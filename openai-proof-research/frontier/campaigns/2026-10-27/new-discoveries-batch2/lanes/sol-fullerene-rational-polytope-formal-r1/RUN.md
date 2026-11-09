# Reproduction

Run from this lane. Set OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 for every command. Prefix every Python invocation with `python ../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py`.

`python runner.py -o Literal.olean Literal.lean`, then InstanceG and InstanceH in that order, then `python runner.py Inventory.lean` and `python runner.py Audit.lean`. The runner pins the compiler hash, j1, M2700, warningAsError=true and autoImplicit=false; its isolated compiler child has the preauthorized AS exception and group RSS 2800 MiB / CPU210 / wall230 caps. The fixed helper guard is unchanged at AS/group RSS512MiB / CPU210 / wall230.

`python package.py` creates the deterministic source-only archive. `python replay.py` extracts it into a fresh lane-local directory, compiles serially, audits all actual mathematical module declarations and their transitive types/bodies, and removes extracted compiled artifacts. It intentionally refuses an existing fresh directory.

`python check_geometry.py` checks exact rational certificates, without importing those checks into Lean. `python finalize.py` writes the final manifest; a separate `python verify.py` invocation checks it and original/copy scientific bindings. Administrative files are snapshots only. No command grants acceptance or changes counts.
