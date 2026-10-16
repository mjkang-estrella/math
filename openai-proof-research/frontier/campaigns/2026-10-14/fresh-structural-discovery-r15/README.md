# Fresh structural discovery r15

Myeongjin Kang; no affiliation. Original prose CC BY 4.0
(https://creativecommons.org/licenses/by/4.0/). Original verifier code MIT;
its full license is in the file header. Third-party source reading copies
are private and retain their original rights. No publication or submission.

Read candidate.md, original-scope.md, refinement-checkpoint.md and
pencil-checkpoint.md for the full assertion, proof checkpoints and gap.
source-contracts.md, screening.md and primary-comparison.md distinguish
actual reading, stipulated upstream truth and contribution limits.
Status: UNRESOLVED_FULL_LR. Campaign count 4/10 unchanged.

The seal.json SHA256 must come from the external terminal/final report.
First hash-authenticate seal.json against that external value, then
manifest.json against seal.json, then verify.py against manifest.json.
Inspect verify.py BEFORE executing it. Its only required argument is the
external seal hash, for example:

    python -B verify.py EXTERNALLY_REPORTED_SEAL_SHA256

The verifier writes no files and reads no live external source/context.
It rejects a wrong anchor, altered scope/status, extra/missing files,
extra/missing directories (including empty ones), symlinks, altered sizes/
hashes, or pinned Git-blob mismatch. It checks integrity, not mathematics,
novelty, primary comprehension or source truth. It neither runs research
code nor imports any code from retained third-party sources.

manifest.json specifies exact payload membership/roles/sizes/SHA256 and
all directories. seal.json binds that manifest, metadata names and counts.
These two metadata files complete the exact owned inventory. The detached
external hash anchors seal.json without a circular self-hash. inputs/context
contains internal snapshots of mutable context. inputs/context-before.json,
inputs/history-references.json and unchanged-source-receipts.json are
historical observations only; future live files are never rebound by the
verifier. Large historical directories were not copied or replayed.
