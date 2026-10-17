# Reproduction and audit boundaries

First verify the ZIP or clean extraction with the externally supplied manifest and final-gate hashes:

    python3 -B verify_bundle.py /path/to/release --manifest-sha256 HASH --gate-sha256 HASH

This portable command checks every archived byte and exact membership. It establishes identity, not mathematical truth or novelty. Read the manuscript and independent reviews for the arguments.

The manuscript is at frontier/campaigns/2026-10-14/complex-projector-borsuk-manuscript-r1/. In a writable copy, run its standard-library exact Appendix A certificate with:

    python3 -I -B support/example_10_2_bounds.py

This checks only the explicitly compared non-SIC example. The main theorem is proved analytically, without numerical minima. Build the PDF in that writable copy with:

    python3 -I -B support/build.py --tectonic /path/to/tectonic

Tectonic 0.17.0, cached TeX packages and Poppler are the recorded environment; --allow-network can provision missing TeX packages. Inspect every rendered page after a fresh build. Original build and all-page QA records are preserved.

Lean support is at frontier/campaigns/2026-10-14/complex-projector-borsuk-formal-v1/. Copy it to a writable directory. Provision exactly Lean 4.34.1 commit 5045d0056413266e57c625dcd7c365b10e377c52 and all lake-manifest.json package revisions, including mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. With an explicit pinned dependency cache, run:

    python3 -B rebuild.py --lean /path/to/lean --cache /path/to/packages
    python3 -B mutations.py --lean /path/to/lean --cache /path/to/packages

The runners freshly compile the four Lean sources and expose the trust in precompiled dependency objects. A normally provisioned Lake project is also supplied. No compiler or dependency objects are bundled.

Historical input/provenance verifiers in the source, manuscript and review folders authenticate the original full research workspace and can require private reading inputs or sibling packets absent from this public subset. They are preserved as evidence, not advertised as portable archive entrypoints. Use the top-level verify_bundle.py for independent portable identity checking; the displayed mathematical/PDF/Lean commands do not require private source PDFs. Internal reviews and scope are fixed by FINAL-GATE.json.

The formal review retains project-owned snapshots under its historical private/ directory; these contain original support code and review records, not third-party reading PDFs.
