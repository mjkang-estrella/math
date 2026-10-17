# B8C independent manuscript review r1

Verdict: **PASS_MANUSCRIPT** for the entire diam(X)=sqrt(2), b(X)=9 assertion. See review.md, reading-limits.md, visual-review.json, reproduction.json and status.json. No manuscript repair, narrowing, campaign count change or publication action. The reviewer authored the separate scoped Lean support but not this manuscript; this packet does not issue an independent formal PASS.

The authenticated manuscript seal is 4f3f038684c6359be5e4e63b990d5485b11eb33ffe7c5c1ec5aa15a37173d1f2. Its 11-page PDF SHA256 is 870941e2499b3005f13063694ce183d3c77fdbea6ead1263a3c3e49dd58a517b. A fresh reviewer-owned build reproduces those PDF bytes. All eleven rendered pages were visually inspected, not merely text-extracted.

## Independent verification

Supply the review seal's SHA256 from the parent report, not from an untrusted local value:

    python -I -B verify.py --seal-sha256 EXTERNALLY_SUPPLIED_REVIEW_SEAL_SHA256

The verifier is read-only. It binds exact file/directory membership, all payload hashes, the manuscript's externally anchored inventory, four predecessor packages, 45 explicit manuscript dependencies, additional immutable reading inputs, rebuilt source/PDF identity, exact Appendix replay identity and all visual page receipts. It rejects missing/extra files, symlinks and a wrong anchor. The audit hook denies writes, subprocess execution and sockets. It does not execute mathematical scripts, rerun Lean, prove mathematics or certify novelty. No files may be added to this sealed review directory.

For a fresh typesetting replay, create a new scratch directory OUTSIDE the sealed package. Copy only rebuild/main.tex and rebuild/support/build.py into that directory, preserving the support/ subdirectory. Then run the copied helper:

    python -I -B support/build.py --tectonic /tmp/frontier-typeset/tectonic

The helper writes only in that new copy. It sets SOURCE_DATE_EPOCH=1792108800 and uses Tectonic --only-cached. Compiler Tectonic 0.17.0 SHA256 a98aa59ad5c1df39a6c9e56cbfc5088f2b11d6c179c0130b97998e4bd46a46da; output identity and page counts are in rebuild/checks/build-receipt.json. pdfinfo/pdftoppm/pdftotext are required. The exact Appendix script can be replayed from the read-only manuscript support/example_10_2_bounds.py, with stdout saved OUTSIDE the sealed package and compared to appendix-replay.json.

All formal coverage is scoped: the human theorem's geometry/topology, actual geometric F/O production, compactness, Bessel inequality and diameter attainment remain outside Lean. The formal-support independent gate belongs to a separate reviewer. Mutable parent records are snapshots only, not future-state constraints. Original prose CC BY 4.0/code MIT, author Myeongjin Kang, no affiliation; third-party rights retained.
