# Round 3 validation

The final status is recorded in results.json and replay-report.json. This is
a partial conditional certificate; no self-acceptance or discovery credit.

Audit3 inventories 253265 declarations in the endpoint import closure and
checks equality of the inventory and audited sets in both directions. It
audits opaque bodies and includes generated declarations. There are 163 LOCAL
declarations across the 20 theorem/definition modules. LOCAL metadata has zero
unsafe, partial, axiom, _unsafe_rec, implemented_by or extern flags. All LOCAL
transitive axioms, including the new obstruction theorem and endpoint, lie
in {propext, Classical.choice, Quot.sound}.

Upstream metadata is reported separately: 298807 upstream declarations in the
auditor environment, with 712 unsafe, 3626 partial, 15 axiom, 3594 _unsafe_rec,
365 implemented_by and 964 extern flags. These are upstream library/runtime
metadata, not new local trusted assumptions. The endpoint's own transitive
axioms are only the three permitted ones. Do not confuse the upstream metadata
inventory with the endpoint dependency axioms.

Fresh replay takes place in verification/, extracted from the source-only zip.
All module compiles and checker calls are serial with unique full logs.
Four negative controls cover a non-equitable partition, a false free-vertex
claim, reversed refinement, and a false exceptional lattice-isomorphism claim.

The first fresh replay attempt stopped at GridBasic's checker because the
checker could not locate the lean executable. The runner was fixed to export
PATH and LEAN_SYSROOT. LEAN_SYSROOT also prevents the checker's internal
unflagged --print-prefix invocation; the configuration is explicit thereafter.
LEAN_NUM_THREADS=1 is exported as well as the -j1 command option.
Development compilation errors and manually stopped attempts are retained in logs.
No source is admitted on the strength of an interrupted or failed call.

The archive, frozen-source manifests and source-only fresh-replay checks are
included. The original 13 modules were not edited.

The first corrected fresh replay PASSED: all 23 modules compiled and passed
leanchecker, the Audit3 inventory sets matched, and all four negative controls
failed as intended. Source hashes were checked against the frozen 13-module
manifest. The final source archive is also extracted into final-packet/ and
replayed there; the final report is final-packet/replay-report.json.
