Run from this shard. Dependencies are standard Python plus SciPy for poset diagnostics. Imports use existing installed packages; no dependency edits/installations were performed.

```
timeout 150 taskset -c 0,1 python extract.py
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 timeout 110 taskset -c 0,1 python poset_diagnostic.py
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 timeout 110 taskset -c 0,1 python poset_flow.py
timeout 12 taskset -c 0,1 python poset_local_weights.py
timeout 100 taskset -c 0,1 python game_diagnostic.py
timeout 100 taskset -c 0,1 python game_grid.py
timeout 100 taskset -c 0,1 python chordal_diagnostic.py
timeout 140 taskset -c 0,1 python history.py
timeout 70 taskset -c 0,1 python build_results.py
timeout 30 taskset -c 0,1 python verify.py
```

`fetch.py` and `registry.py` reproduce live network requests, not immutable receipts; do not overwrite this pass's dated receipts to simulate their historical reproducibility. Network resources and heads can change. Both have finite CPU/address-space and request-time limits, fetch.py uses at most2 workers and has outer240-second wall cap. No403/429 retries are implemented.

A first poset invocation lacked NetworkX; the final script uses existing SciPy sparse matching instead. Failed Lean version subprocess logs are retained as build-results.log and build-results-final.log; the final builder uses the actual successful earlier version observation and records both later failures. All final diagnostics exit successfully. No mathematical proof is certified by these external scripts. Logs contain full program output, including bounded no-gap findings, not all intermediate game states or graph certificates.
