# Independent integrity verification

Run from the repository root:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python3 frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python3 -B frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-mathdb-primary-qualified-breadth-r436/verify.py
```

The guard retains fixed 512 MiB address space/group RSS, 210 seconds CPU and 230 seconds wall caps. No upstream verifier is executed. `verify.py` never writes upstream receipts. The exact payload manifest excludes only `manifest.json` and `final-receipt.json`. `seal.py` is a guarded packaging helper, not the independent checker; do not reseal a payload to hide a verification failure. Mathematical/prior clearance is not asserted by a PASS.
