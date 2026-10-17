# Verification and reproduction

FINAL-GATE.json binds all four adopted internal review gates. Supply its separately delivered hashes when checking an archive or a clean extraction:

    python3 -B verify_bundle.py /path/to/archive.zip --manifest-sha256 HASH --gate-sha256 HASH

The portable verifier checks exact membership, hashes, fixed scope/source identities, gate labels and actual bound review-manifest bytes. These are identity checks, not proofs of mathematics. Authenticate the archive before executing its code.

The deterministic assembler uses sorted regular-file entries and fixed timestamps:

    python3 -B assemble.py --gate FINAL-GATE.json --gate-sha256 HASH --output /outside/extraction/reassembled.zip

Byte-identical reassembly is tested in the recorded Python/zlib environment. Cross-version compression identity is not assumed. Generated files must stay outside the clean extraction.

## Manuscript

In a writable copy of frontier/campaigns/2026-10-14/cm275-manuscript-r1, run:

    python3 -I -B support/build.py --tectonic /absolute/path/to/tectonic

The recorded compiler is Tectonic0.17.0, with cached TeX packages and Poppler tools. SOURCE_DATE_EPOCH=1792108800 fixes timestamps. The default build uses the offline cache; --allow-network explicitly permits fetching missing packages. It creates output/pdf/continuum-coulomb-qma.pdf and renders all ten pages. After a source change, inspect every page. The release check compares an unchanged-source PDF byte for byte and every new page hash with the sealed visual-review record; the public manuscript subset need not duplicate page rasters.

## Lean support

In a writable copy of frontier/campaigns/2026-10-14/cm275-formal-v1, provide Lean4.34.1 and the nine pinned dependencies from lake-manifest.json, including mathlibd13f23b723b8a846827a245b89c10fc7d3f11612:

    python3 -B rebuild.py --lean /absolute/path/to/lean --cache /absolute/path/to/packages --output .replays/public-build

The cache contains the pinned Git checkouts and their precompiled .lake/build/lib/lean objects. The runner checks dependency revisions/cleanliness and compiler identity, then compiles all own source/audit files in a fresh temporary directory. It executes the author controls, false-goal rejections and actual failure-wrapper tests. No old CM275 object is used. These finite statements do not formalize the full continuum theorem.

## Source inventories and release controls

Original full-workspace manifests/verifiers may require omitted private reading copies or sibling packets. Their historical inventories are preserved; use verify_bundle.py for the selected public subset. Original source URLs, hashes and reading limits identify external inputs without redistributing their bodies.

release_checks.py runs against a completed archive with --archive, --manifest-sha256, --gate-sha256, --work and --tectonic. Its work directory must be new. It tests changed/missing/extra entries, symlinks, wrong verdicts/anchors, pending-gate rejection, deterministic reassembly and fresh PDF/page reproduction. Final receipts state the actual tested archive. Compiler/library objects remain outside the release.
