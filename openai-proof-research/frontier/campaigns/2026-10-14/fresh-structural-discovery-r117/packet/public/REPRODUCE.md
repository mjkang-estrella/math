# Read-only verification

Run from the owned r117 directory with **detached values supplied by the parent or final handoff**, not values discovered inside the packet:

```sh
python packet/public/verify.py --packet packet --finalhash MANIFEST_SHA256 --reporthash REPORT_SHA256
python packet/public/finite_checks.py
python packet/public/run_controls.py --packet packet --scratch control-scratch --finalhash MANIFEST_SHA256 --reporthash REPORT_SHA256
```

Both hash arguments are mandatory; there is no self-anchoring default. Authenticate verify.py independently using the external anchors or trusted copy. The exact inventory includes directories and rejects symbolic links, hardlinks and special files. It checks all payload sizes/SHA256, selected upstream Git blobs and URLs against sealed complete-tree entries, primary PDF/text identities and the public source register. The full13223-entry tree is not copied/replayed; its parsing receipt and identity are sealed. Current external repository/history bytes are not needed or revalidated. No network is used.

Controls copy the packet into the explicitly chosen scratch directory outside packet/, test positive and negative cases against the detached final anchor, rerun the bounded rational diagnostic, then compare all original file hashes. They write only temporary copies and stdout. The external final-controls.json preserves their results. Self-resealed tampering is checked using the **original** detached hash. The separate report anchor is outside the packet. These checks authenticate bytes, not proofs or substantiality.
