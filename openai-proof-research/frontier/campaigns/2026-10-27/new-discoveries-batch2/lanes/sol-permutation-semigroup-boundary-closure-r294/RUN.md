# Exact runnable checks

From the repository workspace root, use this prefix for EVERY Python/helper invocation, with the script path below appended:

```
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python
```

All script paths share the prefix `openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-permutation-semigroup-boundary-closure-r294/`.

1. `arrangement.py`: independent rational vertical slabs, exact face sign-vector equality, exhaustive line segments/vertices and full degree<=8 positive prefixes. PASS:2823 faces,4395 interior edges,46/32 retained boundary strata. Final successful run wall22.92s, sampled peak39,813,120 bytes.
2. `lines.py 12`: all ten one-dimensional support arrangements. PASS: surviving segment counts5,9,6,4,6,4,4,4,4,10 in listed support order. Wall4.21s, peak27,750,400 bytes. These are necessary-prefix results only.
3. `symbolic.py`: lattice equation and initial congruence tables; AP universal identity checked against direct Boolean DP on530 parameter pairs. PASS wall0.28s.
4. `apery.py`: two further exact Apéry identities checked against direct DP on322 pairs each; ALL twelve primitive a>=12 ratio vertices evaluated by an independent direct DP until a+5 consecutive reachable values guarantee the tail. Seven family passes/five failures. PASS wall0.36s.
5. `finalize.py`: binds downloaded PDF/text bytes, failures and provenance, then creates manifest excluding itself as a manifest entry and excluding the receipt. This script IS included as an ordinary file in the manifest; only manifest.json and verification-receipt.json are excluded.
6. `verify.py`: SEPARATE guarded process after all other writes. Rechecks every manifest entry and exact file set, frozen original/copy bindings, fresh retrieval hashes/text hashes, unchanged ledger counts and historical report hashes. Writes only verification-receipt.json. Inspect that receipt for the final status.

The guard enforces512MiB address space and sampled process-group RSS, CPU210s/wall230s, no cap raises. It also sets BLAS-family thread limits. No guard limit was hit. The first independent arrangement attempt failed its comparison assertion and was repaired; see failures.json. The resource wrapper's metrics were returned in tool output, not silently treated as mathematical evidence. Retrieval failures/access limits are recorded in access.json/body-access.json and failures.json; no403/429/challenge occurred and none was retried.

Running mathematical scripts again rewrites results; if doing so, regenerate manifest and then run verify.py separately. Do not rerun freeze.py against a changed predecessor and silently overwrite the original bindings. No solver above searches a bounded k range for source-family membership.
