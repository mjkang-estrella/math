# Verification scope and replay

The read-only verifier requires an externally supplied SHA256 for MANIFEST.json:

    python -B verify.py --expected-manifest-sha256 EXTERNAL_ANCHOR

It inventories exact files and directories, including empty directories, rejects root/payload symlinks, hardlinked regular files, FIFO/nonregular nodes and nested manifests, and checks every payload digest. It separately binds the original-scope digest,20 selected canonical source blobs, raw pinned URLs and4 primary PDF/text identities. The manifest is not its own trust anchor.

checks/integrity-controls.json records13 copied intermediate-packet controls, with both acceptance/rejection and expected failure-reason substrings checked. The scratch copies were removed. The final manifest is generated after these results and all final records are present; final positive and wrong-anchor runs are emitted outside the packet, avoiding post-seal edits.

checks/extraction-replays.json records4 successful pdftotext -layout byte replays. checks/matrix-diagnostics.json records only finite floating-point algebra checks, not a proof or formal gate. Source blob identities and private bodies are local; no third-party body is to be published.

For the numerical diagnostic, replay with a Python environment containing NumPy:

    python -B checks/matrix_diagnostics.py

The author used NumPy2.5.3. Tiny floating-point residuals are reported with tolerances in the script. The exact mathematical assertions are justified by candidate.md, not by those residuals. No independent proof, contribution or formal PASS is implied.
