# Validation scope and execution notes

`../checks.py` is a standalone exact finite diagnostic with a fixed seed and no external Python dependencies. `checks.json` records its output. It does not implement or validate the full directed-cycle conjecture.

All seven private primary PDF/layout-text pairs and the CC raw-text extraction replayed byte-for-byte. Nine canonical source Git blob identities were matched to the complete pinned tree. The private directory is ignored by Git.

The strict inventory harness was copied from r51 and adapted to this packet. Its first positive-copy attempt failed correctly because shell output redirection created the future result file before copying, violating the sealed inventory. That empty artifact was removed, and the unchanged controls were rerun with stdout captured in memory and written only after completion. All13 controls then passed. This was a harness-ordering correction; no inventory rule was weakened.

The copied controls run against an intermediate manifest before their own result is added. The final packet is resealed and checked separately with its externally reported anchor; the verifier also rejects the all-zero anchor. Integrity results do not imply proof or contribution acceptance.
