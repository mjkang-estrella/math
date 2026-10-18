# T117Q manuscript v1

Author implementation by Myeongjin Kang, no affiliation. This packet is ready for a separate manuscript review; it makes no acceptance or campaign-count decision.

The manuscript is `main.tex`, with the final 16-page `main.pdf`. It preserves the frozen all-complex-Hilbert-space, genuine-negative-type, ordered uniform first-pair-average theorem with exponent 9/2. There is no dimension, separability, rank, efficient-construction or rationality restriction. Source truths at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated. The manuscript proves the new matrix and assembly operations and credits each geometric input in Appendix A.

Independent input dispositions: PASS_FULL_T117Q; contribution r1 SUBSTANTIAL and r2 SUBSTANTIAL survives with required positioning now implemented; PASS_SCOPED_T117Q for exactly 31 support and 15 control declarations. These are distinct input reviews, not a manuscript verdict or literature-priority finding. `editorial-crosswalk.md` maps their requested changes. The formal packet is unchanged; all metric/Gaussian/design/fractional-power/per-chart-input and infinite-dimensional steps remain outside Lean.

## Reproduce the PDF

From this directory, use a previously nonexistent directory outside this sealed packet:

```sh
python3 -B build.py --output /var/tmp/t117q-manuscript-rebuild-UNIQUE
```

The builder uses `/tmp/frontier-typeset/tectonic`, records its version/hash, fixes SOURCE_DATE_EPOCH, and extracts PDF text and metadata. It may obtain missing TeX support files from the Tectonic cache/network; the author builds did so. It is not claimed hermetic. Source and final PDF hashes are in `validation/build-receipt.json`. The final build had no warnings, unresolved references, missing glyphs or overfull/underfull boxes. `validation/visual-qa.json` binds all 16 inspected renderings to this PDF. Earlier failed-layout build logs and source snapshots are retained honestly; their defects do not describe the final PDF.

## Integrity

Obtain the 64-hex manifest anchor from the external parent message; do not trust a value supplied by this directory itself.

```sh
python3 -B verify.py --anchor EXTERNAL_SHA256
python3 -B integrity_controls.py --anchor EXTERNAL_SHA256
```

The verifier checks exact directory and file membership, size/hash, root and ancestor links, payload links, nonregular objects and hardlinked files, including the manifest. Only the root manifest is omitted from its own membership. Controls run on disposable `/var/tmp` copies; the source packet is read-only. Their outcomes prove identity checks, not mathematics. `validation/integrity-controls.json` records controls on the preliminary seal; final anchored controls are replayed externally.

## Provenance and distribution

`input-provenance.json` authenticates selected copies against externally supplied source/review manifest anchors, and matches the nine selected pinned source Git blobs to the complete preprints tree. It does not claim a whole-family inventory or audit source truth. `reading-limits.md` and `external-read-inputs.json` delimit exact primary passages personally read for this manuscript. Earlier author/reviewer reading is attributed, not automatically inherited.

Original manuscript prose is CC BY 4.0; original code is MIT. See `LICENSES.md`. The intended public deliverables are the original manuscript, PDF, author scripts and audit/provenance documents. `private/` contains third-party source bodies, private author iterations and PNG QA renders; it is ignored and must never be staged or released. External primary bodies remain in their existing immutable private packets. The local manifest authenticates private membership for local review only. Input reports/code retain their own authorship and licenses. No upload, staging or commit was performed by this author agent.
