# Reproduction and trust boundaries

Work from this directory. Do not execute the archived verify.sh in this manuscript task: Lean, lake and leanchecker are prohibited here. No Lean command was run by this lane. The original archive is retained byte-identically; its instructions document a later authorized formal replay, using designated cached dependencies, rather than a self-contained upstream rebuild.

## Offline ordinary checks

Run these one at a time, without background jobs:

```
./scripts/run python3 -B scripts/check.py
./scripts/run python3 -B scripts/extensions_check.py
./scripts/run python3 -B scripts/lower.py
```

The first verifies both graphs, the complement and all 56 unordered cut/side certificates. The second exhaustively tests separating subsets to produce 216 cuts for the six order-nine colorings. The third finds the two alternate paths used in the complement lower-bound proof. The six common-neighbor witnesses in the paper are directly checkable from its complete neighborhood table. independent-check.json and extension-check.json retain the outputs. The manuscript table was checked entry-for-entry against the certificate JSON in scripts/finish.py.

The raw MathDB line includes its original terminating newline. `sha256sum -c mathdb-346167.sha256` checks the exact bytes, not reserialized JSON. The frozen raw line's open status is historical metadata, not a present novelty certificate.

## Repeating the preserved computations

The independent review scripts and catalogue are under evidence/review/. Running a script there writes only into that copy. For example, from evidence/review/:

```
../../scripts/run python3 -B scripts/independent.py candidate candidate-rerun.json
../../scripts/run python3 -B scripts/independent.py extensions9 extensions9-rerun.json
../../scripts/run python3 -B scripts/independent.py atlas atlas-rerun.json
../../scripts/run python3 -B scripts/brute-candidate.py
```

Use one command at a time. The last command overwrites the local COPY of brute-candidate.json. Preserve delivered outputs before rerunning. The catalogue sweep is bounded by the supplied watchdog; a cap exit is not a completed enumeration. This lane did not rerun that sweep. Catalogue completeness and graph-isomorphism coverage rely on McKay's public enumeration. The review's source, output histograms and original logs are included. scripts/collect.py and scripts/root_status.py are provenance collection scripts and should NOT be rerun against the delivered snapshot: they intentionally record before-state evidence and copy read-only original lanes.

## PDF source and rendering

manuscript.md is the editable paper; scripts/render.py is its ReportLab renderer. This lane fetched verified PyPI wheels with ordinary TLS verification, because system Python lacked ReportLab and pip. The exact wheels are retained in assets/wheels/ and bound by the manifests. No account or browser was used. scripts/deps.py records this network setup procedure but is not needed for offline reproduction.

Use Python 3.15 on Linux x86_64, the retained ReportLab 5.1.0, Pillow 13.0.0 and charset-normalizer 3.5.2 wheels, plus the three retained fonts. The Pillow wheel is platform-specific. To prepare an offline installation, extract the wheels into a lane-local .deps directory using Python zipfile, after checking their manifest hashes. Set PYTHONPATH to that directory. The current lane already has this local environment. Then run:

```
PYTHONPATH="$PWD/.deps" TMPDIR="$PWD/tmp" ./scripts/run python3 -B scripts/render.py
./scripts/run pdftoppm -scale-to 1500 -png rainbow-counterexample-draft.pdf qa/page
```

Poppler is needed only for rendering. PDF metadata includes the creation time, so byte-identical PDF reproduction is not promised. Inspect every rendered page after edits. qa/receipt.json binds the delivered PDF and all five final inspected PNGs. Font files are copied from the system; their byte hashes are included. No generated source or asset needs to be written outside this lane.

## Integrity, extraction and formal receipts

input-before.json and input-after.json bind all 693 files in the two frozen evidence lanes plus the ruling. root-input-before.json and root-input-after.json bind the two root receipts first available during preparation. Their paths are relative to the campaign parent directory; original lane files were never modified. integrity-receipt.json records equality. evidence-copy-manifest.json maps bundled evidence to frozen input hashes. The root receipts report PASS, not acceptance; the root paper read is still required.

safe-extraction-receipt.json records the original packet hash and every extracted regular-file hash. Before extraction, all archive names were checked for absolute paths, parent traversal, duplicate names and all symlinks/hardlinks or special files were rejected. Extraction used Python tarfile's data filter; every extracted file was then compared against its archive member. No Lean was run. safe-extraction/ retains this source-only test extraction.

MANIFEST.sha256 binds the dossier payload except itself, the archive receipt and the ZIPs. SOURCE-MANIFEST.sha256 separately binds paper sources, fonts and wheels. archive-receipt.json binds and tests the two ZIPs. A ZIP cannot contain its own final digest; the full archive contains the payload manifests, and its receipt remains external. Verify both ZIP CRCs and the recorded SHA-256 before using them. Do not treat hashes as a replacement for mathematical or statement-fidelity review.

## Resource and conduct limits

scripts/run imposes a two-CPU affinity, 120 CPU seconds, 140 wall seconds, sampled aggregate 6 GiB RSS watchdog, zero core dumps and MALLOC_ARENA_MAX=2. Sampling is not a hard cgroup memory limit. Only one heavy process was run at a time. Lane-local TMPDIR and no Python bytecode were used for authoring/dependency work. No Lean, lake, leanchecker, git, browser, child agent, upload, publication, external message, account action or shared ledger edit was performed. All created files are inside this lane. No jobs remain at handback.
