# Reproduction

Every command below runs from this lane directory with `OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1`, under the fixed guard `G=../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py`. The guard sets AS and sampled group RSS to 512 MiB, CPU to 210 s and wall to 230 s. No caps were raised.

```sh
python3 -I $G python3 -I scripts/fetch.py $PWD NAME URL      # one per receipts/access.jsonl entry, single attempt
python3 -I $G pdftotext -layout downloads/<name>/body extracted/<dir>/<file>.txt
python3 -I $G python3 -I scripts/checks.py check-results.json  # diagnostics only
python3 -I $G python3 -I scripts/finalize.py                   # freeze-after + manifest
python3 -I $G python3 -I scripts/verify.py                     # separate verification -> verification-receipt.json
```

The initial freeze was an inline guarded Python call. It copied the inputs and wrote receipts/freeze-before.json at 2026-10-30T12:57:36Z, before any scientific reading. checks.py ran with exit 0, peak group RSS 11.4 MB, wall 0.60 s.
