# Commands actually run (in order; abbreviated paths)

Root: `/home/mj-kang/Documents/Dev/math/openai-proof-research`.
`C = frontier/campaigns/2026-10-14/fresh-structural-discovery-r3`,
`D = frontier/campaigns/2026-10-14/poly-zp-proof-r1`. Python 3.14.7.

1. Authentication of the frozen handoff:
   `sha256sum $C/candidate.md` -> `e3f4c65e...cbabcc` (20103 bytes);
   `sha256sum $C/seal.json` -> `75df70d9...9684e4`.
2. Candidate verifier (read-only): `cd $C && python3 -B verify.py`
   -> PASS, 79 inputs, 12 outputs, 39 pinned blobs, receipt SHA256
   `fa29613888a882122bfb65afbc7f0410a50c1b93b711361d06e5c8c4f6a68e32`.
   Stdout frozen as `receipts/candidate-verify-stdout.json`.
3. Independent blob cross-check: Python one-off computing Git blob SHA1 of each
   of the 39 rows of `$C/retrieval-upstream.json` and comparing with the
   project's own `sources/preprints-tree.json` -> 39 rows, 0 mismatches.
4. Tamper tests on disposable copies `cp -a $C $D/scratch/copy`:
   (a) append one byte to `checks.json`; (b) add `extra.txt`;
   (c) weaken one assertion in `checks.py`. Each run of `python3 -B verify.py`
   exited 1 with, respectively, `file authentication failed: checks.json`,
   `inventory mismatch: ['extra.txt']`, `file authentication failed: checks.py`.
   Stderr kept in `receipts/candidate-tamper{1,2,3}.stderr` (tracebacks show
   the since-deleted scratch path). The copies and `scratch/` were deleted.
5. Literature lead:
   `curl -sSL -A 'Mozilla/5.0' -D headers.txt -o upenn-dissertation-06a689f2.pdf
   'https://repository.upenn.edu/bitstreams/06a689f2-8398-4072-8b8b-1e398d8986ce/download'`
   in `$D/private/literature`, then `pdftotext -layout` and `pdfinfo`.
6. Independent checks: `cd $D && python3 -B checks/adversarial.py > checks/adversarial.json`
   (about 11 s), then a second run piped to `cmp - checks/adversarial.json`
   -> identical (deterministic).
7. Inventories: a one-off Python here-document (not stored as a program, so
   no sealing mode exists in this directory) hashed every file of `$C` in
   place and the three `private/` files into `inputs-manifest.json`, every
   other own file into `outputs-manifest.json`, and both manifests into
   `seal.json`.
8. Final check: `cd $D && python3 -B verify.py` -> PASS; `git status` showed
   no change outside `$D`.
