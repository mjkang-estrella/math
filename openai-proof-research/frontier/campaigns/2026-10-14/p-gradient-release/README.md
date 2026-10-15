# Local draft archive assembly

Run from the `openai-proof-research` root:

```sh
python3 frontier/campaigns/2026-10-14/p-gradient-release/assemble.py /tmp/p-gradient-draft.zip
```

The output path must not already exist. The assembler captures the selected
source bytes, checks the manuscript and formal validation hashes, checks
all four original proof-review inputs, and rejects concurrent input changes.
It writes an explicit draft label, a SHA256 manifest, reproducibility
instructions, and a ZIP containing the manuscript, formal sources/pins and
relevant authored reviews. It reads no credentials and makes no network calls
or submissions. Third-party papers and dependency caches are not bundled.
Original paths are retained so the Lean project and most research links work
on extraction; links to excluded source scans remain external references.

The first assembly at context commit `4f302a5a` succeeded with 50 project
files. Its disposable `/tmp/frontier-typeset/p-gradient-draft-check-1.zip`
had SHA256 `cab52943d11cbc1d9a20c1f3399739f73a6679d5dd8a3a728ba01917f337f509`.
The parent extracted it to a new temporary directory, checked every file's
length and SHA256 against its manifest, and ran both round-1 and round-2
review scripts there; both exited 0. This demonstrates archive integrity
and script portability, not the analytic theorem or a clean-machine Lean
build. The previous Lean build/axiom audit remains separately recorded.

This temporary archive precedes the active manuscript consolidation and
must be regenerated after the final manuscript gate. The assembler always
labels its output DRAFT; it cannot declare acceptance or publication.
Author names, affiliations, license and external identifiers remain unset.

## Completed manuscript gate and portable verification

The fresh independent manuscript gate now returns PASS with no required
repair, for the same frozen PDF. Its authored review files and all 27 page
and contact-sheet images are now included. Downloaded third-party reading
PDFs and text extracts are excluded through an explicit review allowlist.
The assembler checks the review's output hashes and reviewed input hashes
in addition to the earlier receipts. Historical pending-review banners
inside the frozen manuscript are superseded by the included parent gate
disposition without changing the reviewed proof bytes.

The reviewed 100-file archive passed a clean temporary extraction, manifest
verification and both algebra checkers. An intentionally corrupted manuscript
was rejected before those checkers ran; see `package-check.json`. Run:

```sh
python3 -I frontier/campaigns/2026-10-14/p-gradient-release/verify_bundle.py
```

from an extracted bundle. For Lean, use the pinned lake commands in the
bundle README. The original review runner records its original local
toolchain/cache paths and is retained as evidence, not a portable installer.
Package checks do not certify the analytic proof. The publication draft
still needs the user's authorship/license metadata before public release.

After consolidation, the parent checked all frozen source/PDF/receipt hashes
and inspected all six final contact sheets (21 pages). The assembler now
includes the exact appendix diffs and both recorded build logs. A second
disposable archive, `/tmp/frontier-typeset/p-gradient-consolidated-check-1.zip`,
contains 59 project files, SHA256
`014f6b5ae62d0c64286f17435ec41912370fb3fe6e5f16a5dfb6494848b1ef5a`.
Its captured-byte integrity check passed. It is still a draft; final manuscript
review and publication metadata remain outstanding. Page renders remain in
the repository as visual-QA evidence rather than inside the draft ZIP.
