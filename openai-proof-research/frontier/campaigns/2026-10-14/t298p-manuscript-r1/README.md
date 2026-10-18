# T298P manuscript for independent review

**Author: Myeongjin Kang.** No affiliation stated. This package contains a complete 18-page mathematical paper and its single-file LaTeX source. It presents the unchanged target: two bounded self-adjoint elements with finite strict ordinary microstates/nonmicrostates free-entropy gap, and the source-specialized liminf transfer with k=2^32 and n=2^64+1. It does not assert W*-generation.

- Paper: `output/pdf/main.pdf`.
- Complete editable source: `main.tex` (no external included manuscript sections or bibliography file).
- Reviewer completion/required attribution mapping: `required-item-map.md`.
- Source and review anchors: `inputs.json`; interpretation and role boundaries: `provenance.md`.
- Reading limits and unreviewed literature leads: `reading-limits.md`.
- Build, extraction, visual, and arithmetic receipts: `validation/`.
- Rights: `LICENSE-PAPER.txt` (original prose/LaTeX CC BY 4.0), `LICENSE-CODE.txt` (original code MIT), `THIRD-PARTY.md`.

## Integrity verification

Obtain the SHA256 of `MANIFEST.json` from the external handoff; a hash stored beside its own manifest would not be an external anchor. From this directory run:

```bash
python3 -I -B verify.py --anchor EXTERNAL_MANIFEST_SHA256
```

This command is read-only. It checks exact sealed membership, safe paths, regular single-link files, sizes and SHA256. The only excluded top-level directory is `tmp/`, for transient builds and renders. All other files must be in the manifest. The manifest itself is covered by the external anchor. This verifies bytes, not mathematics, novelty, or acceptance.

If the original local repository and private source copies are available, also authenticate the referenced inputs:

```bash
python3 -I -B verify.py --anchor EXTERNAL_MANIFEST_SHA256 --repo /path/to/openai-proof-research
```

The manuscript can be read and rebuilt without those private copies. Replaying their authentication requires that repository context; original papers are not redistributed here.

## Rebuild and render

Requirements: Python 3, Tectonic with its TeX bundle, and Poppler (`pdftotext`, `pdfinfo`, `pdftoppm`). This follows the repository's existing Tectonic fresh-directory workflow. The recorded build used `/tmp/frontier-typeset/tectonic`; that machine-local default is not a bundled dependency. Supply the installed compiler path explicitly on another machine.

```bash
python3 -I -B build.py --tectonic /path/to/tectonic --output tmp/rebuild
pdftoppm -r 90 -png tmp/rebuild/main.pdf tmp/rebuild/page
```

The output directory must not already exist. `build.py` copies the complete source into it, fixes `SOURCE_DATE_EPOCH=1792281600`, runs Tectonic, and writes the PDF, log, extraction, PDF information, and a receipt with source, binary, and PDF hashes. A fresh second build here was byte-identical to the delivered PDF. Exact reproduction on another installation requires matching compiler and TeX bundle; the recorded compiler binary hash is in `validation/build-receipt.json`. The TeX bundle is not vendored, so universal bitwise reproduction is not claimed.

The final build reports no warnings. All 18 pages were rendered and opened for visual inspection. The render hashes and observations are in `validation/visual-review.json`; transient page images are excluded from the seal. Extracted text and layout checking complement, rather than replace, visual inspection.

## Local arithmetic and integrity controls

```bash
python3 -I -B check_arithmetic.py
python3 -I -B controls.py --anchor EXTERNAL_MANIFEST_SHA256
```

The first checks exact finite dimension/logarithm cancellations, the k^4 energy denominator, the k^-2 heat multiplier, and a scalar finite-gap example. It does not test the analytic hypotheses. The second copies the sealed package under `tmp/`, tests one positive and eight negative cases plus the declared transient exclusion, confirms that the verifier writes no files, then removes its temporary copies. It prints JSON only. The recorded controls were run against a provisional manifest before adding their receipt; the final seal includes the same unchanged verifier/control code and all final payloads. A post-seal replay was also run and checked; its output is transient to avoid circularly modifying the sealed receipt.

## Mathematical and review scope

The pinned source theorem is stipulated. The classical entropy interfaces are stated and cited, including the omitted-proof boundary for Shlyakhtenko Theorem 4.1 in arXiv v1. The frozen proof review reports PASS_FULL_T298P; the separate contribution review reports SUBSTANTIAL conditional on correctness. These are provenance for the earlier frozen packet, not this manuscript's independent review. All nine optional proof presentation repairs and all four required attribution/comparison items are incorporated.

The companion Lean package contains four support declarations and four counterexample controls only; the analytic theorem is not formalized. The optional orbital/dimension/free-mutual-information primary-body screen remains incomplete and is expressly disclosed in Section 8.3. There is no claim of worldwide priority, useful numerical epsilon, or low-dimensional witness. This author package does not accept or count the result.
