# Verification and reproduction

Supply both hashes from the release receipt delivered outside the archive:

    python3 -B verify_bundle.py /path/to/archive.zip --manifest-sha256 HASH --gate-sha256 HASH

The same command accepts a clean extraction directory. It checks every byte, exact file/directory membership, all final verdicts and dependency anchor bytes; changed/missing/extra/symlink/pending-gate inputs are rejected. Hash identity is not mathematical proof. This entry point is portable and uses Python's standard library only. Verify before executing other archived code.

Deterministic reassembly from a clean extraction:

    python3 -B assemble.py --gate FINAL-GATE.json --gate-sha256 HASH --output /path/outside/extraction/reassembled.zip

Do not place the output or bytecode inside a supposedly clean extraction. Fixed ZIP timestamps, regular modes, sorted names and compression settings give byte-identical reassembly in the tested Python/zlib environment. Cross-version zlib byte identity is not claimed. The assembler requires all four exact PASS verdicts and refuses a pending gate even with a recomputed hash.

## Manuscript

In a separate writable copy of frontier/campaigns/2026-10-14/cdf098-manuscript-r1:

    python3 -I -B support/build.py --tectonic /absolute/path/to/tectonic

Recorded environment: Tectonic0.17.0, cached TeX bundle, Poppler pdftoppm/pdftotext/pdfinfo, SOURCE_DATE_EPOCH=1792108800. No network is needed with the cache. The explicit optional --allow-network flag can provision missing TeX packages. Inspect all nine rendered pages after changes; the sealed manuscript review contains the byte-identical fresh rebuild and all-page visual QA. The release check rebuilds unmodified extracted source and compares PDF/page bytes to that evidence without claiming a new visual review of changed material.

## Scoped Lean support

Copy frontier/campaigns/2026-10-14/cdf098-formal-v1 to a writable directory. Provision Lean4.34.1 commit5045d0056413266e57c625dcd7c365b10e377c52 and all nine revisions in lake-manifest.json, including mathlibd13f23b723b8a846827a245b89c10fc7d3f11612. The explicit cache must contain the pinned package Git trees and their precompiled .lake/build/lib/lean objects. Run:

    python3 -B rebuild.py --lean /absolute/path/to/lean --cache /absolute/path/to/packages --output .replays/public-build
    python3 -B mutations.py --lean /absolute/path/to/lean --cache /absolute/path/to/packages --output .replays/public-mutants

These compile the four local Lean sources afresh in a temporary directory and remove their objects. They do not use old CDFLocal/Controls objects or rebuild dependencies. The ordinary Lake project is also supplied. Runtime/compiler/standard-library/dependency-cache trust and exact formal exclusions are recorded. No Lean rebuild was repeated merely for packaging because the layout and source bytes are unchanged; the independent formal review's fresh build is preserved.

Optional finite proof diagnostics, from the extracted root:

    python3 -B frontier/campaigns/2026-10-14/cdf098-proof-r1/checks/cdf098_check.py

This combines exact Fraction arithmetic, finite seeded graph samples, floating-point scale diagnostics and two explanatory preset flags. It is not a universal graph or theorem certificate.

## Historical verifiers and private input limits

Original full-workspace verifiers remain unedited. They can require omitted third-party reading inputs, full original inventories and sibling packets, so they are NOT the portable archive entrypoints. Use top-level verify_bundle.py for this selected public subset. Source/primary receipt URLs and hashes permit separate retrieval subject to their rights; no third-party body is bundled. Original antecedent read limits are preserved. Historical formal-review private/formal is a project-owned snapshot, explicitly retained with its original source/control/log identities.

The bundled release_checks.py can test another archive in a new working directory outside a clean extraction, using --archive, --manifest-sha256, --gate-sha256, --work and --tectonic. It checks extraction, reassembly, corruption/membership/gate controls and the unchanged PDF rebuild. Its mutations affect only its new work directory. Internal review and integrity checks imply neither external peer review nor worldwide priority.
