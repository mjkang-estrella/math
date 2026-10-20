# Read-only artifact reproduction

The handoff supplies complete detached SHA256 anchors for FINAL.json,
MANIFEST.json and REPORT.md. Obtain those anchors from the handoff, not
from a local sidecar. MANIFEST.json covers every other regular file in
this r102 root, every payload directory and their modes. REPORT.md is
outside that manifest; FINAL.json binds both its hash and the manifest
hash. FINAL is anchored externally. No file or directory is silently
excluded as scratch, hidden, ignored, pycache or large.

Before executing code, inspect verify.py and confirm it matches the
externally anchored manifest. Then run from any directory:

    python -B /absolute/path/to/fresh-arithmetic-discovery-r102/verify.py \
      --root /absolute/path/to/fresh-arithmetic-discovery-r102 \
      --final-sha256 FULL_FINAL_SHA256_FROM_HANDOFF \
      --manifest-sha256 FULL_MANIFEST_SHA256_FROM_HANDOFF \
      --report-sha256 FULL_REPORT_SHA256_FROM_HANDOFF

The verifier only reads and prints. It checks detached anchors, exact
payload file/directory inventory and modes, copied input bindings, the
immutable frozen scope, and pinned raw source bodies against the complete
tree/Git blobs/SHA256s. It does not contact a network, modify originals,
execute upstream code or assign any mathematical gate. The three outside
anchor files are checked as regular files and by bytes, not by mode.

controls/results.json records nine copied preseal fixture cases: clean,
modified payload, missing source, unexpected hidden file, symlink, mode
change, modified outside report, wrong external FINAL anchor, and a forged
reseal with unchanged external anchors. The last eight are rejection
controls. controls/run_controls.py is retained for inspection; do not run
it inside the sealed original root because it deliberately writes copies
and a receipt. The production verifier is the read-only reproduction path.

The controls compared the entire then-existing author tree before/after,
and the 14 named external originals used as context/history. This is not
a whole-workspace or historic external-state snapshot. The ordinary
verifier verifies retained copies, so later edits to mutable parent
ledgers do not redefine its mathematical premises or invalidate source
reproduction. Source PDFs and search bodies remain private under their
original rights. This is a local research handoff, not a portable release.
