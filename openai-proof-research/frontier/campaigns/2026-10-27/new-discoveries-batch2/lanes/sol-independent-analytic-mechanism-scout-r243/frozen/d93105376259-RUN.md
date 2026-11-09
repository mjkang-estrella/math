# Reproduce bounded exact checks

From repository root, run:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-fresh-family-wide-scout-r218/checks/finite_fields.py
```

Requires Python3 and sympy (installed). Fixed primes3,5,7,11; no network. Guard fixes address-space and sampled process-group RSS512MiB, CPU210seconds and wall230seconds. Do not increase caps. Prior run exit0, sampled RSS about49MiB,1.2seconds. Finite exact arithmetic supports only the stated instances. Rerun changes results file bytes and requires fresh final manifest/verification. Original input freeze/reference bindings and HTTP receipts are retained separately.
