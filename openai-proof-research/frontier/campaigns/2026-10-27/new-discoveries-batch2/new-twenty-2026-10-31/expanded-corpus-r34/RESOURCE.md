# Resource and reproducibility notes

All computations were serial and process-affined to CPUs 0,1. No uncontrolled exponential search or background job remains. The finite domains and outputs are explicit; scripts are diagnostics, not formal certificates.

- intake.py: twenty corpus files scanned, forty exact raw lines extracted; command wall budget 110s, rg timeout 80s. Actual intake was 1.63s. This initial inexpensive intake had no explicit address-space limit; do not mistake it for a managed-memory expensive search. No history tree copied. Full selected statements in statements.txt; history output in history-search.txt. intake-receipt.json records all chunk hashes.
- fetch.py: serial HTTP with per-request 25s timeout, wall180s, RLIMIT_AS2GiB, CPU90s. Complete successful responses retained in sources/. Dated URL/status/byte-hash receipts in fetch-receipts.json. No fabricated hashes for failed responses.
- diagnostics.py: wall110s, CPU100s, address space1GiB, CPUs0,1. Full output diagnostics.log. Exact determinants use integer permutation expansion. Products limited to sixteen vertices; 28 factor pairs. Exit0.
- dominator.py: wall90s, CPU80s, address space1GiB, CPUs0,1. Full output dominator.log; all four finite domains completed, exit0. Enumerates canonical proper set partitions, not all color label permutations; sinks explicitly exempt for diagnostic purposes.
- dominator.cpp: retained attempted equivalent C++ source. Compilation was capped at wall20s, CPU15s,1GiB; failed immediately because `g++: command not found`. No C++ executable exists or was run. Python was used instead. The initial failed command wrote an empty dominator.log before the Python run replaced it with completed output; the complete failure is recorded here.
- registry-fetch.py: wall45s, CPU30s,1GiB; serial20s request timeouts. AIM403 was not retried. whataifound200 response retained. registry-fetch-receipts.json records both.
- finalize.py: wall30s, serial, CPUs0,1; inexpensive hash/reconciliation pass, exit0. finalize.log complete. Generates exactly40 ID-keyed results and checks all twenty inventory-manifest chunk hashes. Re-running can update mutable administrative snapshot hashes; it does not touch those ledgers.

Example replay, from project root, with L set to this lane's absolute path:

    timeout 110s taskset -c 0,1 python "$L/diagnostics.py" > "$L/diagnostics.replay.log" 2>&1
    timeout 90s taskset -c 0,1 python "$L/dominator.py" > "$L/dominator.replay.log" 2>&1
    timeout 30s taskset -c 0,1 python "$L/finalize.py" > "$L/finalize.replay.log" 2>&1

Python resource limits are set inside the mathematical diagnostic scripts. No Lean compilation occurred because every investigated route was either excluded or incomplete. There is no sorry-bearing dummy endpoint.
