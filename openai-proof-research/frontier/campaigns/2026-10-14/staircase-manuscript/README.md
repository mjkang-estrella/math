# Integral regular summand in the staircase Specht cube

Myeongjin Kang, no affiliation. Manuscript dated 2026-10-15.

`main.pdf` is a six-page standalone research note. Its theorem covers every integer m >= 1, the ordered tensor v_R tensor v_R tensor v_C, a split integral regular orbit, and every commutative unital base ring. The proof is entirely in the paper. Finite computations and internal review verdicts are not mathematical premises.

## Build and reproduce

Python 3.9 or later, with assertions enabled, suffices for the controls. No third-party Python packages are needed. Run from the package root:

```sh
python3 -B support/reproduce.py
python3 -B support/verify_package.py
```

The first command runs the two copied controls in a disposable directory under `checks/`, compares their complete stdout bytes with the preserved expected outputs, and writes `checks/reproduction.json`. It also checks the equivalence of the two retraction formulas on all 512 basis triples for m=2 and all six position permutations. Source checkers and expected outputs are never changed. The new equivalence check is implementation support, not an independently reviewed proof.

The manuscript uses standard LaTeX packages and an inline bibliography; BibTeX is unnecessary. With Tectonic and Poppler on PATH:

```sh
python3 -B support/build.py
```

In this implementation the compiler is `/tmp/frontier-typeset/tectonic`; pass `--tectonic /path/to/tectonic` if needed. The script builds a copy in `checks/build-work/`, copies the resulting PDF to `main.pdf`, saves logs and extracted text under `checks/build/`, and renders every page under `checks/pages/`. Rebuilding may change PDF metadata and bytes. Reproduction is the same source, theorem and layout, not a promise of bit-identical PDF generation across tool versions. The frozen PDF's exact bytes are recorded by the manifests.

## Provenance and scope

- `source-to-claim.md` and `source-to-claim.json`: exact source interfaces, labels, hashes, attribution, and dependency limits.
- `attribution-response.md`: response to every contribution-review condition.
- `support/PROVENANCE.md`: origin and independence limits of the copied checkers.
- `input-manifest.json`: immutable inherited input inventory, including internal reading copies. `checks/input-audit.json` authenticates all 41 entries and 13 source-contract slices.
- `formal-scope.json`: full Lean proof absent; no formal coverage certificate attached. Parent integration and independent manuscript review remain pending.
- `metadata.json`: exact scope and handoff status. This directory awards no acceptance and changes no count.
- `RIGHTS.md`, `LICENSE-PROSE`, `LICENSE-CODE`: rights and license boundaries.

## Public package boundary

`staircase-manuscript-public.zip` is built from the explicit allowlist in `public-files.json`. It contains the paper, original documentation, code, expected results, and provenance hashes. **It excludes the entire `inputs/` tree, all third-party primary PDFs and TXT extractions, and all internal review snapshots.** External primary copies are local reading copies only. References supply links; the archive grants no rights over those linked works.

The complete work directory is an internal audit bundle and is not the public package. Do not distribute it recursively. The public archive is prepared for parent review only; nothing has been uploaded or published.

`public-manifest.json` hashes the allowlisted payload. `output-manifest.json` inventories the full handoff except itself and `SHA256SUMS`; `SHA256SUMS` also hashes that output manifest. These exclusions avoid circular hashes. `support/freeze.py` regenerates these records and the deterministic ZIP only after verification and page inspection. `verify_package.py --with-inputs` additionally checks the local reading copies, which are deliberately absent from the public ZIP.
