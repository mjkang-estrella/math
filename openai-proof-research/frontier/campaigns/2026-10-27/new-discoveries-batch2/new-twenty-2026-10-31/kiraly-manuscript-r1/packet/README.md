# Candidate 388087: portable replay packet (DRAFT, 2026-10-31 PDT)

No acceptance or novelty certification. The exact original Lean file is preserved, SHA-256
1370129f56ef40e2dc317a8cf12ef8d7ed1a0e77eb4d6374d182ee9d4ddcddbb.

Requires Python 3.9+, Lean **4.34.1** (compiler commit
5045d0056413266e57c625dcd7c365b10e377c52), and the already-built external
packages in `lake-manifest.json`, with their exact pinned revisions. Mathlib is
**d13f23b723b8a846827a245b89c10fc7d3f11612**. All nine package checkouts, URLs and
revisions are listed in that manifest. The Cli checkout has no built library in
the current cache; the Mathlib import closure does not require one. Missing
optional package libraries are logged; missing imports still fail compilation. There is no bundled mathlib or dependency
object cache and this packet is not an offline standalone distribution.

From any fresh extraction, run (paths can contain spaces):

```sh
python3 replay.py --dependency-root '/path/to/pinned/.lake/packages' \
  --lean '/path/to/lean-4.34.1/bin/lean' --output './replay-output'
```

Alternatively set KIRALY_DEPENDENCY_ROOT and KIRALY_LEAN. An optional
`--leanchecker /path/to/leanchecker` runs that tool on the resulting module.
The script checks package revision metadata read-only, replaces inherited
LEAN_PATH with paths derived from the configurable root, uses two Lean threads,
promotes warnings to errors, compiles fresh theorem bytes and audits both
#print axioms outputs. It does not modify any dependency directory. Outputs
and logs go only to the selected output directory. Use a new output directory
for a fresh replay; no old theorem olean is included in the archive.

The recorded replay uses the current prebuilt cache. It does NOT establish a
fresh build of Lean/mathlib from downloaded source. To recreate dependencies
elsewhere, obtain Lean 4.34.1, obtain each repository at its manifest `rev`, and
build matching libraries (or obtain a trusted matching cache), preserving the
package-name layout under dependency-root. This source-build path was not
executed here. Revision checks do not authenticate the prebuilt object bytes.

`KiralyCounterexample.lean` contains all certificate literals and the proved-sound
checker: no generator or JSON is needed by Lean. `certificate.json` is useful
explanatory data. `inspect_certificate.py` checks it against the Lean literals,
prints its tree statistics and supplies a deterministic data-only checker.
It is supplementary verification, not a replacement for Lean.

The endpoints are KiralyClutter.counterexample and
KiralyClutter.kiraly_conjecture_false. Definitions of the blocker, covering
polyhedron, extreme-point integrality and choice property are in that file.
Only propext, Classical.choice and Quot.sound are permitted. The original
comment saying the 36 sets form the whole blocker is not a theorem of this file;
only their membership is used. Minimal nonideality and classification are not
formal conclusions. No edits to the frozen theorem have been made.
