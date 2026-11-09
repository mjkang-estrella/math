# Offline reproduction

All commands run in the extracted dossier directory. Write only there. Python is invoked with isolated mode and a real script path. No network, solver, Lean, lake, leanchecker, git or browser is needed for the dossier checks. The guard uses at most two available CPUs, CPU 120 s, wall 140 s, an RSS sampler at 6 GiB, a stronger 6 GiB address-space ceiling, and MALLOC_ARENA_MAX=2. Run commands serially in the foreground.

```bash
python3 -I -B guard.py "$PWD" recompute python3 -I -B recompute.py "$PWD"
python3 -I -B guard.py "$PWD" build python3 -I -B build_paper.py "$PWD"
python3 -I -B guard.py "$PWD" render pdftoppm -r 100 -png paper.pdf final-page
```

The recomputation uses only dossier data, verifies geometry, controls and every one-point deletion to stability, regenerates byte-exact DIMACS, rechecks all RUP additions and counts supplied replay measurements. It overwrites recomputation.json and recomputed.cnf. Rendering requires system Poppler. The PDF builder uses the included ReportLab dependency and fonts; Python must have Pillow, as this host does. No pip installation is required. The manuscript source is paper.md; build_paper.py is the layout source. PDF timestamps may vary; mathematical outputs are invariant.

Verify ordinary file bytes against MANIFEST.json. The manifest excludes itself, ZIPs and post-packaging receipts to avoid circular hashes; exact coverage is recorded. ZIP sidecar manifests list every member with its byte hash. archive-receipt.json binds the ZIP files. The full dossier excludes ZIPs and temporary directories, so it does not recursively embed its companion archive.

The Lean archive is an explicit external dependency. Its absolute original path and required SHA-256 are in packet-reuse-receipt.json. To repeat only its safe-extraction and source-manifest test:

```bash
python3 -I -B guard.py "$PWD" packet-test python3 -I -B verify_packet.py "$PWD" /absolute/path/to/source-only.zip
```

The packet test rejects unsafe names, symlinks, duplicate names and oversized members, verifies all 847 manifest entries, checks 830 ordered modules and removes its lane-local extraction tree. It never runs archive scripts or Lean. The archive is reused byte-identically; do not rebuild or rezip it. Only its documentation and module-order.txt were retained from extraction. Certificate JSON is separately included as computational data, not as a copied Lean packet.

Actual Lean replay instructions are preserved under packet-documentation/REPRODUCE.md solely as documentation for a separately authorized replay. This task explicitly forbids running them. The supplied developer replay is not a fresh manuscript-lane replay. Root replay and registry-refresh status is in root-status.json.

Historical preparation scripts prepare.py, finish_build.py and stage_dossier.py document staging in the original campaign tree. They are not fresh-dossier installers and need not be rerun. verify_paper_numbers.py audits historical encodings against the original external campaign files; the portable recomputation covers all final mathematical data. Frozen original paths in inputs-before.json and supplemental/source-copy receipts permit provenance comparison on the original host.
