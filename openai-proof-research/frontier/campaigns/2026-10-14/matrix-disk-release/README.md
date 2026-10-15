# Matrix disk rigidity: local publication package

Read `STATUS.md` first. The frozen, independently reviewed paper is
`../matrix-disk-manuscript/output/pdf/main.pdf`; its TeX, references, source
map, exact checkers, licenses and all eleven rendered pages accompany it.
Author: Myeongjin Kang, no affiliation. Original paper/prose: CC BY 4.0;
original code: MIT. Third-party rights remain intact.

From an extracted archive's root:

```sh
python3 -I frontier/campaigns/2026-10-14/matrix-disk-release/verify_bundle.py
```

This checks every bundled project file against its SHA256 and byte length,
then runs the 17-check and 16-check exact arithmetic programs in a temporary
copy. It verifies that their outputs equal the frozen receipts. It does not
verify the infinite-dimensional analytic arguments or certify novelty.

To typeset, install Tectonic 0.17.0 and, inside `matrix-disk-manuscript`, run:

```sh
tectonic --keep-logs --outdir output/pdf main.tex
```

A fresh installation may need network access for TeX dependencies. The
existing PDF is the exact reviewed artifact; a regenerated PDF need not be
byte-identical. The historical manuscript validator needs `pdfinfo` and
the original relative project layout, which this archive retains. Run it
only in a copy, since it writes validation and output manifests. Its status
strings describe manuscript preparation, not the later review decision.

No Lean source is represented as verified in this release. GLM's separate
finite scalar variance implementation remains under development. Even a
verified finite identity would not formalize the Hilbert-valued integral,
Fatou passage, boundary convergence, resolvent or geometric arguments.

To assemble again from the research checkout:

```sh
python3 -I frontier/campaigns/2026-10-14/matrix-disk-release/assemble.py /new/path/package.zip
```

The assembler refuses to replace an existing archive. It uses an explicit
allowlist, verifies the frozen manuscript and review receipts, and records
the captured bytes. It excludes downloaded third-party manuscripts, Lean
caches, active agent outputs and unrelated workspace files. Historical
source/input manifests can refer to excluded third-party or antecedent
files; those are provenance references, not promises of bundled content.
`BUNDLE-MANIFEST.json` is the authoritative list of included files.
