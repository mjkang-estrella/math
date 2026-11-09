# Sym6: deep decimal pins for the 60 sym3-open 111132 configurations

This bounded computational continuation owns exactly the 60 open keys in
`verification/highdim/sym3/summary.json`: k=5: 2, k=6: 40, k=7: 16,
k=8: 2. Here k counts far digits; the certificate dimension is k+1.
It does not settle the general multiplicative-persistence conjecture.

All writes are confined to `verification/highdim/sym6/` and this note.
Python runs as `bash -c 'ulimit -v 8000000; python3 -I ...'`, using only
the standard library, at most ten workers, commands below thirty minutes,
and atomic configuration/checker checkpoints. No git commit is made.

The generator, precomputed search accelerator, checker, low-position cover
auditors, and initial continuation/replay/finalization scripts are copied
from sym5. The generator and copied checker are unchanged. The adapted
driver loads the exact sym3-open assignment and sym3 certificate library.
Every retained certificate, including inherited files, must receive a fresh
direct invocation of `verification/highdim/sym5/check_sym5.py`.
The independent original `verification/indep4/check_sym_F.py` is used directly
for depths at most three. Deep certificates use the independent F5 checker
only after `verification/indep5/NOTE_F5.md` exists and reports passing tests;
otherwise their absolute paths are listed in `sym6/deep_pin_certs.txt`.

The decimal-pin proof is the sym5 proof: for t=v2(K), qmin>t, and
0<=d<=qmin, every domain point satisfies
`X/2^t = K/2^t (mod 5^d*2^max(d-t,0))`.
The generator explicitly partitions every omitted low position before using
a larger qmin. Empty positions and every distinct remaining coefficient
value form separate branches; no position is fixed twice. The copied
independent cover auditor replays containment, and finite short-length
smooth enumeration covers lengths below the terminal floors.

Equal-coefficient positions are unordered within each group, while distinct
coefficient groups are independent. The copied sym3 ordering audit checks
every coefficient word and its inverse assignment to increasing position
ranks. A complete candidate is counted closed only after certificate checks,
full low-position/v2 coverage, and finite exception and size-leaf filtering.
Incomplete and budget-limited covers remain open.

## Executed results

- k=5: 2 closed, 0 open; 2 closures require a deep pin in the retained library; 0 independently checked covers.
- k=6: 38 closed, 2 open; 38 closures require a deep pin in the retained library; 0 independently checked covers.
- k=7: 13 closed, 3 open; 13 closures require a deep pin in the retained library; 0 independently checked covers.
- k=8: 0 closed, 2 open; 0 closures require a deep pin in the retained library; 0 independently checked covers.

Total: **53 closed, 7 open**, with **53 deep-pin closures**.
Deep-pin counts mean that the retained certificate library does not provide a complete depth-at-most-three cover. Every deep tree was also tried with the same tree at depth three; successful downgrades received a fresh original-F replay. This does not claim that another depth-three proof is impossible.

Fresh direct checker results on all original retained/search certificates: `{'M': {'PASS': 24057}, 'F': {'PASS': 43}, 'F5': {}}`.

Depth-three same-tree attempts: `{'FAIL': 990, 'PASS': 23024}`; original-F results including successful downgrades: `{'PASS': 23067}`.

Closure certificates: 23942; retained deep closure certificates: 938.

**Independent deep-pin replay is pending.** At the final availability check, F5 did not have the required readiness note reporting passing tests. Counts use direct sym5 checks and independently replayed covers; they do not imply F5 confirmation. `deep_pin_certs.txt` lists all deep search certificates, and `closure_deep_pin_certs.txt` lists the retained closure subset.

Ordering audit: **PASS**, all 60 configurations and 6095 coefficient words. Coverage: **53 complete, 7 incomplete**.

`coverage_audit.json` records every case, its complete cover or missing-domain diagnostics, all coefficient-ordering counts, and the finite exception bound. `slice_domain_audit.json` verifies every checkpointed slice against its retained certificate domain and hash. `v2_inventory.json` independently lists all canonical v2 branches, including those in open cases. No incomplete cover is counted closed.

Finite smooth scan: `{'label': 'COMPUTED', 'Lmax': 34, 'smooth_points': 57913, 'members': []}`. All size-leaf solutions were filtered back to their original digit configurations.

Kill-type ledger dependency totals: `{'prime_coset': 47081, 'decimal_tail_coset': 47081, 'mod8_parity': 47081, 'unaligned_sumset': 1139}`; stored witness references: `{'aligned_prime_reference': 927020, 'unaligned_sumset_reference': 10010}`.

Copied arithmetic and partition controls: `{'result': 'PASS', 'planted_instances': 168, 'class_prime_tests': 10752, 'wrong_kills': 0, 'edge_cases': {'k>t0': 80, 'k=t0': 20, 'k<t0': 68}, 'k_gt_qmin_rejected': 'decimal pin depth', 'misdivided_modulus_rejected': 'false prime kill at 0', 'partition': {'result': 'PASS', 'cases': 72, 'labelled_points': 780, 'discarded_fixed_collision_branches': 60}, 'position_partition': {'result': 'PASS', 'cases': 72, 'canonical_points': 585}}`.

- `search_pin4_10.json`: 60 attempts, `{'BUDGET': 40, 'COMPLETE_PENDING_CHECKS': 20}`, 527.409 worker seconds.
- `search_pin5_30.json`: 40 attempts, `{'COMPLETE_PENDING_CHECKS': 17, 'BUDGET': 23}`, 968.783 worker seconds.
- `search_pin6_180.json`: 17 attempts, `{'COMPLETE_PENDING_CHECKS': 10, 'BUDGET': 7}`, 1804.198 worker seconds.
- `search_pin6_60.json`: 23 attempts, `{'COMPLETE_PENDING_CHECKS': 6, 'BUDGET': 17}`, 1143.750 worker seconds.

Every still-unfinished configuration received the next stage. Completed slices from unfinished configurations were retained and checked too; partial trees were never emitted. OPEN means a bounded search did not produce a checked complete cover.

Reproduction from the repository root (each command bounded below thirty minutes):

```sh
timeout 1200 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym6/continue_sym2.py search --stage pin4_10 --seconds 10.0 --workers 10 --pin-digits 4 --position-slices --precompute --schedule 2,3,5,2,3,2,7 --extra-floor 0 --modulus-digits 90 --depth 280'
timeout 1200 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym6/continue_sym2.py search --stage pin5_30 --seconds 30.0 --workers 10 --pin-digits 5 --position-slices --precompute --schedule 2,3,5,2,3,2,7 --extra-floor 2 --modulus-digits 100 --depth 320'
timeout 1200 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym6/continue_sym2.py search --stage pin6_60 --seconds 60.0 --workers 10 --pin-digits 6 --position-slices --precompute --schedule 2,3,5,2,3,2,7 --extra-floor 2 --modulus-digits 120 --depth 400'
timeout 1200 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym6/continue_sym2.py search --stage pin6_180 --seconds 180.0 --workers 10 --pin-digits 6 --position-slices --precompute --schedule 2,3,5,2,3,2,7 --extra-floor 2 --modulus-digits 160 --depth 600 --mixed-dimensions'
timeout 600 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym6/test_sym5.py'
timeout 1500 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym6/replay5.py --workers 10 --seconds 900 --brute 11 --downgrade'
timeout 600 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym6/prune_ablations6.py'
timeout 600 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym6/audit_search_domains6.py'
timeout 900 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym6/finalize5.py'
timeout 600 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym6/seal6.py'
```

Evidence under `verification/highdim/sym6/`: `assignment.json`, `summary.json`, `coverage_audit.json`, `ordering_audit.json`, `v2_inventory.json`, `kill_usage.json`, `checks5.json`, `checks5_journal.jsonl`, `test_results.json`, `source_hashes.json`, `manifest6.json`, `input_*.json`, `search_*.json`, `closure_certs.txt`, `deep_pin_certs.txt`, `closure_deep_pin_certs.txt`, `certs/`, and `k3_certs/`. All passes are fresh direct CLI invocations; no inherited checker PASS was reused. Source hashes verified unchanged. No git commit was made.
