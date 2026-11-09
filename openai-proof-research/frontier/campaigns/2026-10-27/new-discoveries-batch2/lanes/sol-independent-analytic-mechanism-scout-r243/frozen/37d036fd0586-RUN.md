# Exact capped replay

From `/home/mj-kang/Documents/Dev/math`, run each command with the literal prefix below (one guard invocation per command):

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-wide-algebra-scout-r222/report_helpers.py replay
```

This runs `cube.py`, `cube_route2.py`, `cube_reduce.py`, `verify_math.py` and `genius_check.py`, retaining their exact stdout/stderr and exits in checks.json. CPU210s, wall230s, address space512MiB and sampled process-group RSS512MiB remain fixed; no cap raises. The entire replay takes seconds under these limits. Helpers use the installed stdlib only; PDF extraction used installed pdftotext. No random external seed: route2 uses seed222.

For finalization use the identical prefix, replacing the final `replay` argument first with `manifest`, then in a **separate guard invocation** with `verify`. This writes provenance/source map and finalmanifest, then verifies every listed file, original scientific report, retained PDF/text hash and all1,596 immutable history refs. Administrative files are snapshot-only; their live originals are not required to stay fixed. The manifest deliberately excludes itself and verification-receipt.json. Replay mutates check outputs, so run it before making the final manifest. Do not rerun network retrieval or denied historical routes for replay.
