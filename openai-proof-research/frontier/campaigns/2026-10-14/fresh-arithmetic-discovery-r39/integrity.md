# Integrity and reproduction

The immutable external manifest SHA256 must come from the parent handoff, not be recomputed and trusted from the packet itself. Run:

    python /absolute/path/to/packet/verify.py EXTERNAL_MANIFEST_SHA256
    python /absolute/path/to/packet/control-tests.py EXTERNAL_MANIFEST_SHA256

The verifier checks original invocation ancestry before any resolution, recursively lstats entries, rejects symlinks, hardlinks, FIFOs and other nonregular entries, and requires exact file and directory inventories. Nested manifest.json files are rejected. It also authenticates the complete tree, source-family selection, all64 non-PDF source blobs,14 retained primary bodies and associated available text extractions, and the unchanged frozen scope.

The13 copied controls comprise canonical baseline, unchanged copy, payload alteration, deletion, extra file, extra empty directory, root symlink, ancestor symlink, hardlink, FIFO, nested manifest, adversarial self-reseal and wrong external anchor. Rejections are checked by both returncode and diagnostic reason. Scratch copies live inside a temporary child of this packet to avoid the earlier per-user /tmp quota; that child is excluded from copied trees and removed on exit. The canonical baseline is checked before creating scratch. Do not inspect the canonical inventory concurrently while controls are running. Control output must remain outside the frozen packet; no output file is written by default.

verify.py and control-tests.py are adapted from the same author's r38 exact-inventory support, not new mathematical work. They do not create seals, invoke a proof checker or establish contribution. There are no finite numerical mathematics diagnostics in this structural argument. Formal interfaces are prospective only.

Private files are retained solely for source authentication and reviewer access and are excluded from Git/releases. The public receipt hashes identify them without redistributing their bodies. No content from a future proof/contribution review is included.
