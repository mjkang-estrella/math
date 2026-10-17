# Verification and reproduction

All four reviews are adopted in FINAL-GATE.json. Supply the separately delivered manifest and gate hashes to authenticate the portable archive:

    python3 -B verify_bundle.py /path/to/archive.zip --manifest-sha256 HASH --gate-sha256 HASH

The same verifier accepts a clean extraction. It checks exact file and directory membership, hashes, verdict labels, fixed source/scope anchors, and the actual bytes of bound review manifests. This establishes identity, not mathematical truth. Use the portable verifier before executing archived code.

The deterministic assembler uses explicit selected original payloads, fixed timestamps and sorted regular-file entries. A completed gate is required even if someone recomputes a hash over a pending gate. Both independent review anchors are explicitly adopted in the release helper. Reassembly uses:

    python3 -B assemble.py --gate FINAL-GATE.json --gate-sha256 HASH --output /outside/extraction/reassembled.zip

Byte-identical ZIP output is tested within the recorded Python/zlib environment; cross-version compression identity is not assumed. Keep generated outputs and bytecode outside a clean extraction.

## Manuscript

In a separate writable copy of frontier/campaigns/2026-10-14/ts132-manuscript-r1, run:

    python3 -I -B support/build.py --tectonic /absolute/path/to/tectonic

The recorded compiler is Tectonic 0.17.0, with cached TeX packages and Poppler tools, SOURCE_DATE_EPOCH=1792108800. The default build is offline; --allow-network explicitly permits fetching missing packages. Inspect all nine rendered pages after source changes. The release checks compare unchanged-source PDF and page bytes against the adopted independent review.

## Scoped Lean support

In a writable copy of frontier/campaigns/2026-10-14/ts132-formal-v1, provision Lean 4.34.1 commit5045d0056413266e57c625dcd7c365b10e377c52 and the nine dependency revisions in lake-manifest.json, including mathlibd13f23b723b8a846827a245b89c10fc7d3f11612. The cache includes pinned Git trees and their precompiled .lake/build/lib/lean objects. Then run:

    python3 -B rebuild.py --lean /absolute/path/to/lean --cache /absolute/path/to/packages --output .replays/public-build
    python3 -B mutations.py --lean /absolute/path/to/lean --cache /absolute/path/to/packages --output .replays/public-mutants

These compile the current task sources in an isolated temporary directory, using no old TSLocal or Controls objects. They reuse dependency objects, which remain a disclosed trust boundary. The full Boolean theorem is not formalized. The ordinary Lake project and exact conditional interfaces are retained.

## Historical verifiers and omitted inputs

Original workspace verifiers are preserved without rewriting their inventories. They can require omitted third-party snapshots and original sibling packets; they are not portable public-subset verification commands. The top-level verify_bundle.py is the intended portable archive entrypoint. Source and primary receipt hashes/URLs permit separate rights-respecting retrieval. The selection excludes all private/input snapshot directories at preparation time; the two complete original review packages and parent adoption receipt are selected explicitly.

The adapted release_checks.py exercises a completed archive in a new working directory with --archive, --manifest-sha256, --gate-sha256, --work and --tectonic. It checks corruption, membership, symlink, wrong-verdict and pending-gate rejection, deterministic reassembly, and the fresh unchanged-source PDF rebuild. The separate release-check receipt reports the actual tested archive and all resulting controls.
