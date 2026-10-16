# B8C contribution review round 2

Myeongjin Kang; no affiliation. Original prose CC BY 4.0; code MIT.
Third-party rights retained privately.

Read review.md for the disposition and operation-comparison.md for the
primary-body comparison. Mathematics PASS_FULL_B8C is retained from r1;
contribution UNRESOLVED and counted=false. This is not an acceptance,
a dimension-eight counterexample, a manuscript or a formal certificate.

primary-reading-source-contracts.md specifies actual reading extents and
limits. findings-checkpoint.md was saved before packaging. original-scope.md
is byte-identical to the frozen author scope. active-review-contract.md
records current authority; historical briefs do not change ownership.

manifest.json lists exact owned payload files and directories, roles, sizes
and SHA256. It excludes only itself and seal.json to avoid circular hashes;
those two metadata outputs are explicitly named, and seal.json authenticates
the manifest. The seal's SHA256/size are reported OUTSIDE this directory in
the final handoff. It is not a signature or a proof of truth.

inputs/external-baseline.json inventories 71 observed originals: the 35-file
author package, 30-file r1 package, pinned source identity/catalogue files,
original historical brief, and context originals. Exactly 69 fixed external
files remain future references; AGENTS and parent disposition instead use
internal byte-identical snapshots. Live ledger/tasks are never required by
future verification. Their observations are preserved internally. The exact
external sealed directory sets are retained without duplicating archives.
New primary bytes and web-reader excerpts/derivatives are separately frozen
in inputs/primary-records.json. A URL is provenance, never a future hash gate.

Inspect verify.py, authenticate it through the manifest/seal, then run:

    python3 -I -B verify.py --seal-sha256 EXTERNALLY_REPORTED_SHA256

The external anchor is REQUIRED. Verification authenticates each metadata
layer before parsing payload, rejects unsafe/duplicate paths and JSON keys,
symlinks, bytecode, special files, missing/extra members, changed inputs, and
mismatching Git blobs against the complete catalogue. An audit hook forbids
writes, network and subprocesses inside the verifier. It executes no research
code, no diagnostics, and makes no mathematical/novelty judgment.

verification-controls.json records positive, wrong-anchor and missing-anchor
controls. unchanged-input-receipts.json records unchanged observed originals.
Final replay also checks no protected byte changed. No uploads/publication,
shared edits, staging, commits, nested agents, count change or Lean occurred.
