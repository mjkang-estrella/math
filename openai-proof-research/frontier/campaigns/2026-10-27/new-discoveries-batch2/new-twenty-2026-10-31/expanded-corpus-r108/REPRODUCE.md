# Reproduction

All paths below are relative to this lane. The Lean distribution and pinned external mathlib cache are the ones specified in TASK.txt. `./run.sh` produces the source-only packet and an empty-directory extracted replay, strict compilation, all-declaration axiom audit and leanchecker verification. Full compiler/checker output is retained in replay/. Resource wrappers retain full stdout/stderr and JSON receipts under logs/.

The diagnostic executables are compiled from the retained header-free C sources with the supplied `leanc -O3 -o scripts/NAME scripts/NAME.c`. No package installation is needed. The host has no g++ and the bundled bare clang could not locate stdio.h; those failed initial compile commands were superseded by the supplied leanc with explicit libc prototypes. C++ draft source is retained as development history; `penney.c` is the executed source.

Use `python scripts/limited.py LOGNAME COMMAND ARGS...` for each independent call. The wrapper pins the process tree to two available CPUs, inherits CPU 120-second limits, enforces wall 140 seconds, samples process-group RSS against 6 GiB, and permits 64 GiB address space. This is a sampled guard, not a cgroup guarantee. The first diagnostic receipts used only launched-process RSS monitoring and 12 GiB address space; their JSON names identify that limitation. The final extracted replay uses process-group sampling. The task's resource limits continue to apply if manually reproducing a script outside the wrapper.

Executed diagnostic commands:

```
scripts/penney 14
scripts/penney 16
scripts/thue 2000000
python scripts/thue_sparse.py
python scripts/circulant.py 50
python scripts/circulant_search.py 40
python scripts/circulant_exhaustive.py
python scripts/certificate.py
python scripts/reduced.py
python scripts/near_bipartite.py
python scripts/hadamard.py
python scripts/garvan.py
python scripts/prime_distance.py
scripts/partitions 50000 outputs/partition-parities.bin
python scripts/progression.py
python scripts/progression_source.py
```

The original sparse Thue–Morse recursion run failed at Python's default recursion limit; the corrected source raises it and `logs/thue_sparse_fixed.*` contains the completed run. The two progression scripts intentionally differ: one tests the defective MathDB p²-inverse wording and the other the intended source's signed p-inverse convention. Failed literal tests receive no credit. The 200 near-bipartite LPs use floating HiGHS solutions and do not certify exact optimality. All other reported arithmetic diagnostic checks use integers; none is a mathematical theorem until semantically certified. Only the circulant order-15 endpoint is formally certified here.

The source-only ZIP contains Circulant.lean, Bridge.lean, Endpoint.lean and Audit.lean, with no local oleans. `scripts/replay.py` removes only this lane's replay directory, extracts the ZIP afresh and compiles dependencies in order. External cache locations are read-only. The final manifest hashes bind all deliverables; regenerate it after any edit.
