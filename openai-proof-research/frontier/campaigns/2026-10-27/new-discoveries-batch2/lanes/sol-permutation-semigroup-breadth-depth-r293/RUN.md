# Capped replay

Run only from this lane. Every invocation uses the unchanged fixed guard, AS/groupRSS512MiB, CPU210s, wall230s, and the required environment. Do not run helpers directly or raise caps.

```bash
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python independent_checks.py
```

The same prefix may run checks.py, boundary_window.py, chambers.py 8, and vertices.py, in that dependency order. Checks are exact integer/rational computations. independent_checks.py independently recomputes all505 passing Apéry certificates by membership DP and rechecks every strict H8 chamber/residue case. Its coverage limitation is explicit in independent-result.json.

Replays rewrite result artifacts. After any changes, run finalize.py under that prefix to regenerate the manifest, then run verify_integrity.py under the prefix as a **separate invocation after all other writes**. The verifier alone writes verification-receipt.json; the manifest excludes itself and that receipt. Integrity PASS is not acceptance or a conjecture proof.

Do not rerun retrievals by default. access.json records exact successful URLs and chronology. No Google or previously denied route is authorized. Eight extra source families are body-screened, with no fresh-result claim; ancillary fetched PDFs do not enlarge that count.
