# Bounded replay

From this lane, run the following commands. Every Python/helper/retrieval/hash/edit operation uses the specified external guard; no cap increase. Network retrieval is optional and should not be repeated on parked failures.

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python ../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python checks.py
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python ../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python verify.py
```

checks.py uses rational arithmetic only, no external packages. It checks finite graph identities and exact polynomial quadrature values. Its assertions do not certify the universal wavelet source question or worldwide novelty. verify.py independently checks source/history bindings and final manifest, then writes only verification-receipt.json. Re-running checks.py deterministically reproduces its manifested output.
