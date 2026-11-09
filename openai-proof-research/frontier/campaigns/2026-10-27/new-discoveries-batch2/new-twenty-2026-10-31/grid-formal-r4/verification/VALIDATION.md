# Round 4 validation

See replay-report.json for exact inventories and metadata totals, and
verification/replay-report.json for the fresh extracted replay.

Every source is compiled strictly and serially with Lean 4.34.1, -j1,
-M3500 and -DwarningAsError=true, then checked with leanchecker naming that
module explicitly. Every Lean, checker and Python process uses scripts/run.sh:
2 CPUs, CPU 120 s, wall 140 s, MALLOC_ARENA_MAX=2, and a 6 GiB RSS watchdog
summing the process group. All temporary and cache directories are lane-local.

Audit4 imports the endpoint closure with opaque bodies visible and includes
generated declarations. It compares the complete declaration inventory and
audited set in both directions, including a separate exact endpoint closure.
LOCAL declarations are rejected for unsafe, partial, axiom, _unsafe_rec,
implemented_by or extern metadata, and for any transitive axiom outside
propext, Classical.choice and Quot.sound. Upstream metadata is reported
separately and is not asserted to have zero flags. The endpoint and the
closed classification theorem's own axiom lists are reported independently.

Four inherited negative controls must fail: false exceptional lattice iso,
non-equitable partition, false free-vertex claim and reversed order.
The frozen-before and frozen-after manifests cover all 23 inherited modules.
No incomplete development attempt is used as validation. Round 4 is not
acceptance: MainOrbit is still an explicit unproved Prop premise.
