# r115 packet

Start with [report.md](report.md), then the five operation-level screen notes and [reading.md](reading.md). There is no frozen candidate and no nominee.

`public/` contains original research prose and an original integrity verifier. `private/` contains pinned upstream/third-party evidence and acquisition receipts under their original rights. Do not publish those bodies as original work. No new license for them is asserted. A successful verifier checks bytes and provenance consistency, not mathematics, priority or contribution.

Run the verifier with the packet path and a manifest SHA256 obtained from the separate handoff/FINAL anchor, never from within the packet itself:

    python -B packet/public/verify.py --packet packet --expected-manifest-sha256 EXTERNAL_FINAL_HASH

The manifest and report hashes are recorded outside the packet. Final-anchor copied controls and the unchanged-original comparison are also outside it.
