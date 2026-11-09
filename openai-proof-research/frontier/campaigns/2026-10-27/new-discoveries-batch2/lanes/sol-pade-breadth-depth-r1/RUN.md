# Fixed-cap replay

Every command below uses AS512MiB, sampled process-group RSS512MiB, CPU210s, wall230s in the assigned guard, without cap raises. Environment: OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 (guard also pins other BLAS thread variables).

From this lane run, substituting SCRIPT with checks.py, product_route.py, report.py, finalize.py, verify.py:

`OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python SCRIPT`

checks.py uses exact integer-scaled coefficients and independent Fraction checks at n≤12; scope odd m≤39,n≤400. product_route.py independently convolves q_m(z)q_m(-z), checks its closed coefficient formula, then exact-inverts to w160 for odd m≤19. These bounded programs do not prove the source conjecture. checks took about9.4s and21MiB sampled groupRSS; product standalone about0.12s and12MiB. Extraction/request helpers remained well below caps. Source retrieval is optional and must respect access exclusions; no retry of denied routes. Do not rerun report/finalize after final verification without producing a new manifest/receipt.

finalize.py hashes every lane file except finalmanifest.json and verification-receipt.json. verify.py is a separate guarded invocation after writes; it checks local manifest and immutable external references and independently recomputes bounded coefficient signs and the exact even-product obstruction. Receipt records verification outcome and manifest hash; it is intentionally outside its manifest.
