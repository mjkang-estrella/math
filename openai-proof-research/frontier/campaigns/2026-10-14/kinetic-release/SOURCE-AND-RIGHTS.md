# Sources, retrieval and rights

The immutable upstream truth pin is OpenAI/math commit
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Its theorem truth is stipulated for
this project; this package does not independently audit it.
`../kinetic-manuscript/source-H.json` retains ten exact upstream paths, pinned
raw GitHub URLs, SHA256, Git blob SHA1, byte lengths and documented read extents.
`source-map.md`, `source-map.json`, `references.tex` and the repaired proof's
source notes explain which interfaces are credited and which deductions are
new. No source text is silently relicensed.

The ten raw H files are deliberately omitted. In a disposable manuscript copy,
the existing verifier can retrieve and authenticate them transiently:

```sh
python3 verify_sources.py --fetch --project-root /nonexistent
```

It uses the exact pinned URLs from `source-H.json`, checks SHA256, size and
Git-blob SHA1, writes only a temporary directory under the copied manuscript,
then removes the downloads. This network-dependent source retrieval is
optional; it was not rerun by package preparation. The standalone bundle
verifier needs no source cache or network access.

`../kinetic-contribution-r1/sources.md` retains the bounded external-literature
screen with arXiv versions, direct URLs, available PDF/extract hashes, precise
read extents and limitations. It includes BGSS arXiv:2008.10403v2 and
arXiv:2201.04514v1, DHM arXiv:2408.07818v3, and the other comparisons actually
opened by that reviewer. Those historical reading records are evidence of the
screen performed then; preparation claims no new literature search. External
raw papers and text extracts are not bundled.

For a full historical run of the manuscript's `verify.py`, additionally
restore the original `sources/preprints-tree.json` (SHA256/length in
`excluded-inputs.json` and `inputs.json`) and place all ten H files at their
listed project paths. The tree index is a historical GitHub API snapshot;
regenerating a semantically equivalent tree may not reproduce its JSON bytes.
It must come from the original authenticated snapshot to pass that historical
hash check. The other 43 input records are selected in the explicit allowlist.
Run in a disposable copy because historical verification rewrites validation
and control receipts. Some other historical review runners have additional
source or machine-local paths; retaining their source does not assert that
they run in an extraction without those dependencies. Use the standalone
verifier and `rebuild_lean.py` for this package's documented portable checks.

Myeongjin Kang is the author, with no affiliation. Original paper/prose is
CC BY 4.0; original Python and Lean code is MIT. Included copied programs keep
their copyright/license notices. The upstream corpus, external literature,
Lean compiler, mathlib and other dependencies retain their own rights and
licenses. No third-party raw paper or dependency cache is included under the
author's licenses. The reviewed PDF and all 19 QA page PNGs are intended author
assets. The formal-review output manifest still records an old `.olean`; that
binary is explicitly excluded in `excluded-inputs.json`, with its Lean source
and fresh-compilation evidence retained.
