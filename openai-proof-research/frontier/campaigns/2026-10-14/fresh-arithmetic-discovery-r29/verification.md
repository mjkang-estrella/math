# Verification and sealing contract

The parent receives two SHA256 anchors externally: manifest.json and verify.py. Supply both explicitly to verify.py and controls.py. The verifier never writes or reseals. It checks its executing bytes, packet verifier bytes and manifest against those external anchors; then checks exact files/directories, content hashes/sizes, ancestor/root/nested symlinks, hardlinks, nonregular files and nested manifest.json files. Self-resealing an edited packet cannot satisfy the old external manifest anchor.

Default verification includes all retained private bodies. --public-only expects the complete private directory to be absent and checks the exact public package; third-party bodies must not be committed or released. --source-tree PATH additionally authenticates every pinned non-PDF source/companion receipt against the canonical complete preprints-tree.json, including exact family completeness. It is incompatible with --public-only.

Run diagnostic.py separately to reproduce diagnostic-result.json. Run controls.py with the same two anchors to reproduce controls-result.json; it copies into /var/tmp and leaves the source packet untouched. Its18 cases include positive/public-only and adversarial mutations. The first provisional inventory was used only to test the verifier before recording these control results; the final inventory includes the results and is rerun afterward. No source or theorem-scope change occurred during sealing.

No program output, checksum, finite diagnostic or integrity control is an independent mathematical proof, substantiality verdict, formal theorem certificate or release authorization.
