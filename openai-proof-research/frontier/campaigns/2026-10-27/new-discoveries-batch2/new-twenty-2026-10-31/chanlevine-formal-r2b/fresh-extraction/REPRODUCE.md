# Reproduction

The source archive contains seven frozen modules and six new Sem modules, plus scripts and these notes. Extract into an empty directory beneath this lane only. Run:

```
python3 -I scripts/replay.py --resume
```

The script compiles in strict serial dependency order using pinned Lean 4.34.1, `-j1 -M3500 -DwarningAsError=true`, then runs leanchecker on each module. Receipt fingerprints permit resuming only the identical source set. All per-process logs have unique names.

The resource wrapper restricts affinity to CPUs 0 and 1, CPU time to 120 seconds, process-group RSS to about 6 GiB and wall time to 140 seconds. TMPDIR and caches are lane-local, and MALLOC_ARENA_MAX is 2. No network or package mutation is used.

SemAudit enumerates all declarations, including generated declarations, in the local import closure of SemRegression (which imports SemFinal), then traverses every referenced type/body and inductive constructor, including upstream dependencies. The replay independently recomputes the graph closure from logged roots and edges and checks exact set equality. Every visited declaration has unsafe, partial, implemented_by and extern flags logged. Target transitive axioms are checked against propext, Classical.choice and Quot.sound. Flagged upstream dependencies, if any, are reported explicitly; they are not silently excluded.

Four expected compilation failures detect a wrong canonical weight, empty Hamiltonian cycle, incomplete vertex coverage, and omission of the explicit recurrence residuals. The copied reviewer SCC algorithm independently compares the literal finite state graph to the facing-pair counts for n = 3 through 8 and m = 1 through 3.

Use the exact remaining Prop statements in SemFinal.lean and SemWords.lean. Only canonicalTest is unconditional. Root must not assemble an unconditional endpoint from these conditional theorems without closing every residual.
