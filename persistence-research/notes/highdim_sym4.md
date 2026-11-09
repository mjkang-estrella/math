# Sym4: continuation of the final 134 sym2 configurations

Status labels: **COMPUTED** means an executed finite experiment; **PROVED
(checked)** requires both direct checker replays and a complete slice cover.
An unfinished search or cover remains **OPEN**, irrespective of partial kills.
This effort does not settle multiplicative persistence.

## Scope and execution constraints

The assignment is exactly `sym2/summary.json`'s 134 open keys: 133 for target
14112 and `32:11|9,9,9`. The source uses dimension k=1+number of far digits:
target 14112 dimensions 5,6,7,8,9 have 13,47,51,20,2 assigned keys, respectively;
target 32 has dimension 4. These are the counts in the task's context, despite
its phrase "free far digits". Actual far-digit counts are one smaller.

Writes are confined to `verification/highdim/sym4/` and this note. Required
scripts were copied from sym2, whose files are read only. Python commands use
`bash -c 'ulimit -v 8000000; python3 -I ...'`, only the standard library, at most
12 search/check workers for this effort, and commands bounded below 30 minutes.
Each completed configuration and certificate is checkpointed atomically. No
git commit is made.

## Improvements and soundness

**PROVED. Hybrid refinement.** The original nd-sym method already stores a
separate coordinate/group for every distinct coefficient, and a multiset only
within each repeated coefficient. `gen_precomputed.py` now makes the singleton
tuple axes explicit, retaining multiset axes for repetitions. For multiplicity
h of parent residue b modulo M, child residues are all combinations with
replacement of h elements of {b+Mt:0<=t<f}. Taking the Cartesian product of
those choices, the singleton axes, and the L axis gives every child exactly
once. No permutation exchanging distinct coefficients is identified. All
coefficient orderings are therefore included. This is an implementation and
search-speed experiment, not an additional symmetry reduction or kill type.

**PROVED. Prime supply.** `prime_supply.py` searches divisors of 10^d-1 for every
1<=d<=60, first removing known factors, then using bounded Pollard rho. Factors
above 2^64 that only pass a probable-prime screen remain explicitly unresolved;
only candidates <=10^14 enter the new supply. Candidate orders are reduced by
factoring p-1. Supply assertions are search hints: the two required certificate
checkers independently prove primality and recompute orders for every used
prime. In a cyclic prime-field group, |<3,7>|=lcm(ord(3),ord(7)), so its index is
(p-1)/that lcm. Both that index and decimal order are recorded. With tail
constraints, ranking uses the size of the actual allowed union of cosets;
small <3,7> index alone does not imply a strong exclusion test.

**PROVED. Tail-aware witness ranking.** Existing arithmetic witnesses are
ranked by (p-1)/(h*number of allowed cosets), then by smaller p. Cache keys
include M and both exact-or-free exponent signatures, and caches are private
to one K/qmin generator. The same accepted prime, sumset and exact-size tests
are retained; changing witness order changes neither their meaning nor their
soundness. Prime-period and forbidden-residue caches inherit the sym2 argument.

**NEEDED CHECKER EXTENSION: decimal tails beyond three digits.** The required
`sym/check_sym.py` explicitly requires `0<=pin_digits<=min(3,qmin)`; the
independent `indep4/check_sym_F.py` has the same cap. No certificate here uses
pin_digits>3, and neither checker is edited. For a future extension, a depth
j<=qmin would use D=5^j*2^max(j-v2(K),0) and all pairs of powers of 3 and 7
modulo D. The congruence follows because every variable decimal term is
divisible by 10^j, including 10^L. Both checkers would need cap changes and
independent tests of period/pair enumeration, parity interaction, resource
limits, and rejection when j>qmin. This argument alone does not authorize an
unchecked certificate.

**PROVED. Refinement scheduling.** Any sequence of positive integer refinement
factors partitions a parent class into all its symmetric lifts. Trying factors
2,3,5 before the expensive factor 7 changes only search order. Checkers derive
the child factor from the stored moduli and independently enumerate every
omitted lift; acceptance never trusts a supplied schedule or heuristic.

## Coverage and ledger policy

For an original configuration X=10^L+K+sum(c*10^q), K=9*S_low-1, the original
positions are pairwise distinct with 3<=q<L. A fixed-v2 terminal slice requires
qmin>v2(K); all offending low positions and the remaining high tail must be
covered. Stronger-floor searches additionally require a finite scan of all
shorter lengths. Only full nd-sym certificates accepted by both original
checker entrypoints, with unchanged file/checker hashes, may discharge a
slice. Reused sym2 pieces must be directly replayed by both checkers too.

The copied `audit_coverage.py` retains the independent enlarged-domain cover
algorithm. Distinct-fixed-position and position-partition alternatives retain
their separate sym2 independent replay. Open covers have explicit missing
obligations; no partial cover counts as a closure. `audit_orderings.py` enumerates
every distinct coefficient word and its inverse group assignment.

`kill_usage.json` will list each retained/reused certificate's prime witnesses,
exact decimal orders, aligned versus sumset references, exact-size leaves,
tail/mod8 dependencies, hashes and checker outcomes. No new arithmetic kill
type is introduced. Results are appended after bounded searches and replays.

## Executed results

**COMPUTED; closures PROVED (dual-checked cover).** Counts below use dimension k=1+far digits, matching the sym2 count convention.

- Target 32, k=4: 0 closed, 1 open, 1 assigned.
- Target 14112, k=5: 4 closed, 9 open, 13 assigned.
- Target 14112, k=6: 16 closed, 31 open, 47 assigned.
- Target 14112, k=7: 18 closed, 33 open, 51 assigned.
- Target 14112, k=8: 1 closed, 19 open, 20 assigned.
- Target 14112, k=9: 0 closed, 2 open, 2 assigned.

Exact newly closed keys:

```text
14112:101|9,27,54,54,72
14112:101|9,9,9,54,54,72
14112:103|9,18,45,54,54
14112:105|9,9,9,18,54,54
14112:121|9,9,9,18,54,54
14112:13|9,18,45,54,54
14112:15|9,18,27,54,54
14112:15|9,9,9,18,54,54
14112:161|9,18,18,27,54
14112:1|9,54,54,63,72
14112:1|9,9,45,45,54,54
14112:201|9,9,9,45,54,54
14112:205|9,9,9,9,54,54
14112:211|9,9,9,18,54,54
14112:215|9,9,9,54,54
14112:21|9,9,9,45,54,54
14112:23|9,9,9,18,54,54
14112:25|9,9,9,9,54,54
14112:261|9,9,9,9,18,54
14112:263|9,9,45,54
14112:303|9,18,18,54,54
14112:331|18,18,54,54
14112:51|9,9,9,18,54,54
14112:5|9,9,18,27,54,54
14112:5|9,9,9,9,18,54,54
14112:601|9,18,18,54,63
14112:601|9,18,27,45,54
14112:601|9,9,27,54,72
14112:601|9,9,9,9,54,72
14112:605|9,9,18,27,54
14112:605|9,9,9,45,54
14112:605|9,9,9,9,18,54
14112:610|27,45,45,54
14112:611|9,9,9,18,18,54
14112:615|9,9,9,18,54
14112:63|9,18,18,27,54
14112:63|9,9,18,45,54
14112:63|9,9,9,18,18,54
14112:663|9,9,18,45
```

Direct original-checker results: {'M': {'PASS': 15442}, 'F': {'PASS': 15442}}. All 15442 retained/reused certificates were invoked as original CLI entrypoints, without importing or patching either checker. The replay orchestrator only schedules subprocesses. Both use a brute box through L=10; declared solution lists agree.

Certificates: 15265 new (13950460 bytes total; largest 318114 bytes), 177 reused sym2 pieces, 15265 certificates used by complete new covers. Reused pieces remain in their original locations and were replayed anew.

Coverage: {'OPEN': 95, 'CLOSED': 39}. Every closure passes the independently replayed unordered/v2 slice cover; open configurations retain explicit missing-domain reasons. The baseline v2 inventory contains 229880 terminal obligations across all 134 keys. All 12795 distinct coefficient orderings pass the inverse-group bijection audit. Inventory completeness is not a closure claim for the open configurations.

Finite exception scan: {'label': 'COMPUTED', 'Lmax': 28, 'smooth_points': 32831, 'members': []}. All declared size solutions are also filtered back to the original decimal configuration and target in the coverage auditor.

Hybrid comparison: {'result': 'PASS', 'hybrid_cases': 42, 'labelled_lifts': 68895, 'witness_order_comparisons': 432, 'deeper_decimal_pins_used': False}. The independent small-box slice tests additionally pass 72 labelled cases (780 points) and 72 position-partition cases (585 canonical points).

Search stages:

- `search_floor235.json`: 132 attempts; {'BUDGET': 95, 'COMPLETE_PENDING_CHECKS': 37}; 3138.421 worker seconds; reasons {"Budget('modulus')": 11, 'COMPLETE_PENDING_CHECKS': 37, "Budget('wall alarm')": 84}.
- `search_period50.json`: 11 attempts; {'BUDGET': 11}; 153.439 worker seconds; reasons {"Budget('modulus')": 1, "Budget('wall alarm')": 9, "Budget('nodes')": 1}.
- `search_tailrank235.json`: 134 attempts; {'BUDGET': 132, 'COMPLETE_PENDING_CHECKS': 2}; 2629.335 worker seconds; reasons {"Budget('modulus')": 2, 'COMPLETE_PENDING_CHECKS': 2, "Budget('wall alarm')": 130}.

Prime search: all d=1..60 attempted; 32 added primes, 1621 total supply entries. A separate trial-division and exact-order audit accepts all 32 new entries (`prime_supply_audit.json`). `prime_search.json` reports unsplit or large probable cofactors; no complete factorization claim is made. `prime_ranking.json` records decimal orders and subgroup indices. Added-prime witnesses actually present in retained certificates: []. The targeted period-50 pass yielded no complete cover; no closure gain is attributed to the larger supply.

Ablation on the two first-pass successes (same 25-second bound, <=8 workers):

- `14112:263|9,9,45,54` / tailrank: COMPLETE_PENDING_CHECKS, 2.708 s, 501550 lifts, 490 nodes.
- `14112:663|9,9,18,45` / supply: COMPLETE_PENDING_CHECKS, 4.133 s, 606311 lifts, 570 nodes.
- `14112:263|9,9,45,54` / supply: COMPLETE_PENDING_CHECKS, 4.182 s, 501550 lifts, 490 nodes.
- `14112:663|9,9,18,45` / tailrank: COMPLETE_PENDING_CHECKS, 4.837 s, 606311 lifts, 570 nodes.
- `14112:263|9,9,45,54` / schedule: COMPLETE_PENDING_CHECKS, 6.727 s, 903549 lifts, 718 nodes.
- `14112:663|9,9,18,45` / schedule: COMPLETE_PENDING_CHECKS, 9.005 s, 1061350 lifts, 801 nodes.
- `14112:663|9,9,18,45` / baseline: BUDGET, 25.0 s, 2068447 lifts, 4782 nodes.
- `14112:263|9,9,45,54` / baseline: BUDGET, 25.0 s, 1583041 lifts, 3291 nodes.

All complete ablation certificates are retained and dual-checked too. These two selected cases test attribution of the observed successes; they are not an unbiased performance benchmark.

Kill-type dependency ledger: {'prime_coset': 15442, 'decimal_tail_coset_k3': 15442, 'mod8_parity': 15434, 'unaligned_sumset': 351, 'exact_size': 12}; closure-only dependencies: {'prime_coset': 15265, 'decimal_tail_coset_k3': 15265, 'mod8_parity': 15263, 'unaligned_sumset': 290, 'exact_size': 10}. Reference counts distinguish aligned prime tests, unaligned sumsets and exact-size leaves; decimal-tail/mod8 dependencies are conservatively recorded whenever enabled. No kill type beyond Agent F's audited types is used.

Needed checker extension remains pin_digits>3 up to qmin. It was not used. Other open-case budget or modulus failures are search limitations, with full traces in stage JSON files; they imply no impossibility theorem.

## Reproduction

```sh
timeout 600 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym4/continue_sym2.py search --stage tailrank235 --seconds 20 --workers 12 --schedule 2,3,2,3,5,2 --precompute --modulus-digits 72 --depth 250'
timeout 900 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym4/continue_sym2.py search --stage floor235 --seconds 30 --workers 12 --schedule 2,3,5,2,3,2,7 --extra-floor 2 --position-slices --precompute --modulus-digits 72 --depth 250'
timeout 180 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym4/continue_sym2.py search --stage period50 --seconds 15 --workers 12 --schedule 2,5,5,3,2,3,7 --selection period50_selection.json --precompute --modulus-digits 72 --depth 250'
timeout 1500 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym4/replay_dual.py --workers 12'
timeout 300 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym4/audit_coverage.py'
bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym/check_sym.py verification/highdim/sym4/certs/tailrank235/K2366_q3_c9_9_45_54.jsonl 10'
bash -c 'ulimit -v 8000000; python3 -I verification/indep4/check_sym_F.py verification/highdim/sym4/certs/tailrank235/K2366_q3_c9_9_45_54.jsonl 10 --json'
bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym4/finalize.py'
bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym4/verify_manifest.py'
```

The exact driver loaded at the start of the first two searches is preserved in `source_snapshots/continue_sym2_initial.py`; its hash matches both input ledgers. Later driver edits corrected the reconcile/check/audit entrypoints for sym4 and did not change the search path. `prepare_evidence.py` verifies this snapshot and the assignment source hash.

Main files: `summary.json`, `coverage_audit.json`, `v2_obligations.json`, `ordering_audit.json`, `dual_checks.json`, `dual_journal.jsonl`, `kill_usage.json`, `prime_search.json`, `prime_ranking.json`, `hybrid_test_results.json`, `ablation_results.json`, `input_*.json`, `search_*.json`, and `certs/`. All are under `verification/highdim/sym4/`. The manifest binds these and this note; logs are excluded.
