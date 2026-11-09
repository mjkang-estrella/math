# Capped runnable checks

From the lane directory, prefix every Python command with:

`OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py`

Then `python check_exact.py` for the exact rational comparisons, or `python work.py diagnostic` for bounded floating diagnostics. The guard fixes AS/groupRSS512MiB, CPU210s and wall230s; no cap raises. Retrieval commands in work.py are bounded and only target arXiv API/PDF endpoints. Do not rerun denied routes.

After all writes, `python finalize.py` builds manifest.json excluding itself and verification-receipt.json from its contents (the finalizer script IS included); then separately run `python verify.py`. No file other than verification-receipt.json should be written after manifest creation. Administrative snapshots are verified as saved snapshots only. Reused immutable history copies are verified against inherited fixed hashes, with originals compared when present.
