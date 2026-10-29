# Source packet: subunit Rényi threshold

Research manuscript. Independent final review, bounded freshness refresh and root acceptance pending; credit zero. No acceptance or registry update is included.

Run from a freshly extracted source tree, with Python 3.14.8, ReportLab 4.4.10, Pillow 13.0.0 and charset-normalizer 3.5.2 available. These are external renderer dependencies, not local compiled proof artifacts. The exact renderer, zlib, fonts and executable hashes are in toolchain.json. Font assets are included. Python's ZIP compression and ReportLab invariant mode give identical bytes on this pinned toolchain.

    python3 component/helper_guard.py python3 verify.py /absolute/new/output-directory

This verifies the complete source manifest, rebuilds paper.pdf and packet.zip, and invokes the unchanged component verifier for a fresh isolated full Lean replay. The output directory must not exist. Compare hashes to the delivery provenance. No local .olean or cache is shipped. The upstream pinned compiled Mathlib installation is an external dependency whose .olean/private/server companions are checked exactly by the inherited verifier. Rebuilding on a different renderer or compression implementation is not claimed byte-identical.

component/ is the exact immutable expanded source component. component-source.zip is its unchanged deterministic original archive. Eight inherited mathematical modules and all three endpoint-extension modules are unchanged. The exhaustive import-all FullAudit covers 104 actual declarations in eleven mathematical modules, including generated helpers; only the standard three axioms are permitted. manifests and receipts are integrity evidence, not mathematical assumptions.

Use paper.txt and build_paper.py to rebuild the paper alone; use pack.py to repack the source tree. Generated outputs must be outside this source tree. The packet intentionally carries no generated paper.pdf. The delivery separately supplies it.

evidence/ preserves the source-attribution proof, independent preliminary review, current-prior and registry closure reports, root decisions and replay receipts. Bulk survey inventories are not copied. The formal component embeds the official v3 HTML and original proof. Source and novelty limits, historical failures, and tool setup failures are summarized in SOURCE-ATTRIBUTION.md and failures.md. This packet adds no acceptance or global historical priority claim.
