# T212M public release preparation — not a final release

This scaffold selects 96 exact public files from six frozen packets and four exact parent dispositions. It contains no final gate, final archive, manuscript verdict or acceptance. The final manuscript reviewer anchor is null. The final assembler deliberately refuses every invocation, including a forged ALL_REVIEW_GATES_PASS. Later final implementation must bind the actual reviewer report, limits, manifest and parent adoption to externally supplied hashes; merely changing a status or supplying a string must not unlock it.

The whole target remains: every nonatomic Borel law on finite nonnegative iid square-lattice weights, almost surely no bigeodesic simultaneously over all paths, without moments or direction, conditional on the stipulated pinned source. Source212 already pays every finite min-of-four second-moment law; only the infinite class is additional. No unconditional conjecture-resolution or priority claim. Accepted=false, published=false, count_change=0.

`public-selection.json` is the explicit deterministic allowlist. Every packet-owned selected byte is bound to its frozen manifest; parent dispositions have exact separately bound hashes. The preparation manifest's external hash authenticates this allowlist and helper code. Selection is not a wildcard release policy. Frozen manifests include unselected records for provenance; those entries do not cause private bodies to be included. Source receipts identify third-party bodies but do not distribute them.

Included: full manuscript public LaTeX/PDF and provenance, author derivation modules, source identities and reading limits, independent proof/contribution reports, original formal v1, separately labeled reviewer Independent.lean and its report, and parent dispositions. Excluded: all primary/source bodies, private caches, compiled Lean/dependency caches, and write-in-place review drivers. The public manuscript contains the precise DH/AH proof-use and generalized-kernel crosswalk requiring manuscript review.

## Reproducible staging

Supply the external preparation manifest hash independently:

```sh
python3 -B prepare.py --anchor EXTERNAL_PREPARATION_SHA256 --campaign /absolute/campaign/path --output /var/tmp/t212m-public-stage
python3 -B reproduce.py --anchor EXTERNAL_PREPARATION_SHA256 --stage /var/tmp/t212m-public-stage --tectonic /path/to/tectonic --output /var/tmp/t212m-pdf-replay
python3 -B reproduce.py --anchor EXTERNAL_PREPARATION_SHA256 --stage /var/tmp/t212m-public-stage --lean /path/to/lean --cache /path/to/pinned/packages --output /var/tmp/t212m-lean-replay
```

Outputs must be new. The stage is marked PREPARATION-NOT-RELEASE and is not a publishable archive. PDF uses fixed epoch and cached TeX resources; Lean verifies the selected pins and compiler and builds copied modules. Dependencies and compiler remain trusted, not rebuilt. Reviewer Independent.lean is separate evidence: its source and execution receipt are selected, but the original formal builder does not run it. Do not represent a v1-only replay as reviewer-supplement reproduction.

Future ZIP specification is sorted POSIX member names, no directory entries, fixed timestamp 2026-10-18 00:00:00, Unix regular-file 0644 permissions, DEFLATE level9, fixed create_system3 and empty comments. `assemble.py` exposes metadata construction but refuses final assembly until a new independently anchored final-gate implementation is prepared. No ZIP is emitted now.

## Coverage and rights

Original formal v1: 14 support declarations and 17 controls. Its Fin4 examples instantiate segment lemmas, not infinite escape/tail theorems. Reviewer supplement: 60 separate reviewer constants including infinite-graph nonvacuity, a metric-uniform threshold and hypothesis-deletion controls. Full stochastic FPP theorem, coherent infinite rays, cap construction, labels, Busemann limits and splicing are not formalized. Index-uniform tail cutoff still uses external coercivity. Retain formal review O4's scanner/cache and trusted-toolchain limits.

Author Myeongjin Kang, no affiliation. Original prose CC BY4.0, original code MIT; manuscript LICENSE.md supplies terms. Frozen review evidence preserves its source identity and reviewer role. Primary works retain original authorship and are not relicensed or selected. Compilation, hashes and finite controls are not mathematical verification.

## Adaptation

Design compared with t117q-release-v3 README and assemble.py. This is a fresh T212M-specific selection and guarded staging implementation, not a renamed T117Q gate. Unlike that completed release, manuscript closure is absent and final assembly remains disabled. Current proof, contribution and scoped formal dispositions are adopted parent records; none substitutes for the pending manuscript gate.
