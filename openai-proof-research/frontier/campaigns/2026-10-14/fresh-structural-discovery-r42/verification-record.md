# Verification record

The deterministic rank diagnostic was replayed with python -B and its parsed JSON exactly matched the saved finite output. It tests only the displayed rational matrices at degrees1–4.

Thirteen copied intermediate-packet controls passed: positive copy; wrong external anchor; changed report; changed original scope; missing payload; extra file; extra empty directory; root symlink; payload symlink; hardlinked payload; FIFO; nested manifest; and self-resealed mutation under the original external anchor. Temporary copies were removed. These controls do not mutate the final payload and establish no mathematical theorem.

After adding the control result and this record, MANIFEST.json is regenerated. The final read-only positive verification and wrong-anchor rejection are run separately, and their external manifest SHA256 is delivered to the parent outside this packet. That externally supplied hash is required; a hash printed inside an untrusted packet is not an external anchor. Exact inventory includes private source bodies for local authentication, not release permission.

Reproduce: python -B verify.py --expected-manifest-sha256 <caller-supplied external anchor>. Optional --root names another packet location. The verifier rejects symlinks, nonregular nodes, regular-file hardlinks, extra/missing paths including empty directories, nested manifests, any byte/size/hash mismatch, altered original scope and source receipt/blob discrepancies. It makes no independent proof, novelty or formal-verification assertion.
