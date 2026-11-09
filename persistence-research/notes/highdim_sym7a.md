# Sym7a: adaptive position peeling on the 33 sym5-open configurations

This is a bounded computational continuation for target 14112, not a proof
of the general multiplicative persistence conjecture. The input is exactly
the 33 open names in `verification/highdim/sym5/summary.json`: dimension 6:
1; dimension 7: 12; dimension 8: 18; dimension 9: 2. All writes are confined
to `verification/highdim/sym7a/` and this note; no commit is made. Python
commands use `bash -c 'ulimit -v 8000000; python3 -I ...'`, stdlib only,
at most ten workers, per-command timeouts below 30 minutes, and atomic
certificate/configuration/checker checkpoints.

## Exhaustiveness proof

A state `(K,C,p)` represents all original assignments with as-yet unassigned
positions at least p, together with the fixed assignments at positions below
p accumulated in K. Equal coefficients form an unordered multiset. Original
positions are globally distinct, including between different coefficient
groups, and all are strictly below L. At position p there is either no far
coordinate, or precisely one coordinate with coefficient c for one of the
distinct values c remaining in C. These mutually exclusive cases are:

* unused position: `(K,C,p+1)`;
* occupied position: `(K+c*10**p,C minus one copy of c,p+1)`.

There is one occupied branch per distinct coefficient value, not per
labelled copy. Thus repeated copies cannot both occupy p, and every original
assignment follows exactly one branch. Ordering the coefficient branches by
multiplicity changes only traversal order. Each split preserves
`X = 10**L + K + sum(c*10**q)` exactly. Iterating raises every remaining free
coordinate to the eventual floor p'. This includes the branch in which all
copies of a chosen group avoid p; proceeding through the other groups
produces the unused-position branch.

A terminal certificate may safely enlarge the original slice by forgetting
fixed assignments: its remaining free coordinates are distinct, at least
its certified qmin (which must be <= p'), and below L. Fixed positions are
all below p'. For L >= p', every absorbed position remains strictly below L.
For L < p', forgetting fixed assignments or raising the lower bound for L
could lose points. The audit therefore scans ALL original configurations
through `Lmax = max_state(p'-1)`, independently enumerating every 2,3,7-smooth
number below `10**Lmax`. Certificates cover the complementary long lengths.
This also handles an empty remaining multiset, where the certificate domain
requires L >= qmin rather than L greater than a remaining coordinate.

Every child recomputes `t0' = v2(K')`; no inherited valuation is assumed.
The generator is invoked only when `p' > t0'`. If that inequality fails,
peeling continues. This terminates for these finite multisets: along any
infinite path, only finitely many occupied decisions occur, after which K
is constant and p eventually exceeds its finite valuation. Computational
budgets can stop earlier, producing explicitly OPEN leaves.

For `k <= qmin <= p'`, every variable term, including `10**L`, is a multiple
of `10**k`. Dividing `X == K' mod 10**k` once by `2**t0'` gives
`Y == K'/2**t0' mod (5**k * 2**max(k-t0',0))`. The sym5 generator and checker
implement exactly this pin. When enabled, the separate mod-8 pin also
requires `qmin >= t0'+3`. No certificate extends the allowed pin depth.

## Search and verification policy

The generator, precomputation caches, checker copy, supply and original
coverage modules are copied from sym5. Originals are not modified. The
copied checker is an archival reference: actual certificate replays invoke
`verification/highdim/sym5/check_sym5.py` AND
`verification/indep5/check_sym_F5.py` directly as CLIs with brute L <= 11.
No checker code is imported into the generator or replay driver. Both full
verdicts, commands, certificate/checker hashes, times and resource outcomes
are retained in `dual_checks.json` and `dual_journal.jsonl`.

The search tries easy low-dimensional states before peeling, defers costly
high-dimensional low-floor trees, and uses factor order 2,3,5,2,3,2,7 before
adaptive signature-based refinement. This uses the sym4/sym5 lesson of
growing useful small-prime richness before factor seven. Tail-aware actual
coset size ranks auxiliary witnesses. A bounded second supply experiment
examines primes with 2,3,5,7-smooth p-1, emphasizing a factor of five and
manageable decimal order. Supply metadata is only a hint; both original
checkers independently verify every used witness.

`audit7a.py` imports neither the search driver nor either checker. It
reconstructs the root from each assignment and independently demands the
exact unused branch and one occupied branch per distinct coefficient at
every split. It checks reachability, recomputes all valuations, checks
terminal full-domain containment, binds both checker passes to the current
bytes, compares declared solutions, and filters any solution back to the
original decimal configuration. Missing or resource-limited leaves remain
OPEN. The finite partition controls compare independent direct enumeration
of original assignments with peeled assignments, including multiplicities,
changed valuations, position collisions and short L.

Results are appended after the bounded runs and the complete direct replay.

## Executed results

Counts below refer only to the 33 assigned sym5-open configurations, all for
target 14112. **1 closed, 32 open.**

| Dimension | Assigned | Closed | Open |
|---|---:|---:|---:|
| 6 | 1 | 1 | 0 |
| 7 | 12 | 0 | 12 |
| 8 | 18 | 0 | 18 |
| 9 | 2 | 0 | 2 |

The closure is `14112:623|9,9,9,18,54`. Its retained cover has
21 directly dual-checked certificate domains. Closure pin depths:
`{'6': 6, '7': 7, '5': 6, '4': 2}`. OPEN records explicitly retain unresolved
slices; no smooth member was discovered, and no claim of impossibility is
made for those 32 configurations.

**Direct checker results:** sym5 `check_sym5.py`: **2041/2041 PASS**;
independent `check_sym_F5.py`: **2041/2041 PASS**. Both were invoked
directly on every retained certificate, with brute bound 11 and 8,000,000 KiB
virtual-memory limits. No large-memory exception was needed. No current
certificate/checker hash is stale, and no FAIL, TIMEOUT or pending result is
used. Original source hashes and byte-identical archival copies are checked.

**Coverage:** PASS for the exhaustive partitions in all 38
recorded trees: 4576 states and 1424 peeling splits.
The accepted complete cover closes the dimension-6 configuration. Every other
cover retains an explicit OPEN leaf. The finite controls passed 84 cases /
1,260 canonical points, with exact equality and disjointness against direct
original-assignment enumeration. The separate finite scan through length
26 enumerated 26455 smooth
numbers and found **zero matching members** across the assigned configurations.
The auditor independently reconstructs split children rather than trusting
the driver's claimed coverage.

Certificate depths are `{'6': 231, '7': 1755, '5': 28, '4': 2, '8': 25}`. The ledger records every
auxiliary prime reference, supplied order annotation, aligned versus sumset
prime leaf, exact-size leaf, valuation, pin setting, digest and dual-check
status. Full independently recomputed arithmetic statistics and any declared
solutions are retained in the checker records. Kill-reference totals:
`{'rest_references': 200146, 'sumset_prime_leaves': 3529}`. A rest reference denotes a witness listed at a
refinement; it is not a claim of that many distinct killed classes.

The bounded supply search considered 4348 candidates and added
128 primes to the 1,621-entry copied supply. Added-prime
witness references in retained certificates: `{'2160001': 3, '24001': 3, '160001': 3, '13230001': 3, '420001': 1, '21001': 1}`. No closure
gain is attributed to the expanded supply: the successful dimension-6 cover
was obtained before that experiment. The targeted dimension-7 floor-8 run
still leaves `(K=188, C=[9,9,18,27,54,54], qmin=8)` unresolved. Its final attempt
stopped at the five-million-lift cap; floor-7 attempts also hit modulus or
lift limits. This is a search limitation, not a counterexample or rejection
of position peeling.

### Checkpoint and cache incident

The first implementation assumed workers inherited the prepared certificate
library. This Python version uses a different default multiprocessing start
method, so the library was absent inside workers. The first pass still
constructed sound peeling covers, but later uncached runs regenerated some
files. The audit detected 122 stale hash-bound checker records.
The correction selects an explicit fork context, publishes certificates
immutably with atomic hard links, and requires matching hashes when deciding
whether to skip a replay. All affected current files received fresh direct
replays; all 2041 final file hashes now match both PASS records. The incident
and obsolete hash records remain in `stale_hash_incident.json` and the
append-only checker journal. Final `dual_checks.json` is the authority.
The corrected cache was exercised in `peel8cached`: all 104 terminal
certificates were reused and the single unresolved root was reattempted.

### Search stages

| Stage | Configurations | Candidate covers | Open | Worker seconds |
|---|---:|---:|---:|---:|
| search_peel7 | 33 | 1 | 32 | 2858.408 |
| search_peel8cached | 1 | 0 | 1 | 12.315 |
| search_peel8five | 1 | 0 | 1 | 120.000 |
| search_pilot7 | 1 | 1 | 0 | 14.730 |
| search_root7five | 1 | 0 | 1 | 58.591 |
| search_root7long | 1 | 0 | 1 | 67.935 |

Candidate covers are search output only; the counts above use direct dual
replay plus the independent coverage and finite scan. Search failures never
emit partial certificate trees. All 33 received the full initial bounded
pass. Later experiments deliberately targeted the almost-complete dimension-7
cover rather than claiming an exhaustive larger-budget pass.

### Reproduction and continuation

The final driver defaults to the original sym5 adaptive refinement cycle.
Use `--rich-five` to select `(2,3,5,2,3,5,2,7)` instead. The sole generator
diff is a search-order option; the certificate format and arithmetic kills
are unchanged. `gen_sym_baseline.py` preserves the byte-identical sym5 source.
Initial stages before the cache fix are retained as historical checkpoints;
rerunning with a fresh stage name uses the corrected cache and can perform
different amounts of work within the same wall-clock budget.

```sh
# A new bounded all-assignment continuation, using existing immutable files:
timeout 1200 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym7a/run7a.py --stage resume7 --floor 7 --seconds 90 --slice-seconds 3 --workers 8'
# The targeted floor-8 / factor-five experiment, using a fresh stage name:
timeout 300 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym7a/run7a.py --stage resume8five --key "14112:21|9,9,18,27,54,54" --floor 8 --seconds 120 --slice-seconds 25 --workers 1 --schedule 2,3,5,2,3,5,2,7 --rich-five'
# Run after search completes; do not exceed ten combined search/replay workers:
timeout 1500 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym7a/replay7a.py --workers 8 --timeout 300'
timeout 180 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym7a/audit7a.py'
timeout 180 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym7a/report7a.py'
```

Main evidence under `verification/highdim/sym7a/`: `summary.json`,
`coverage_audit.json`, `kill_ledger.json`, `dual_checks.json`,
`dual_journal.jsonl`, `research_stats.json`, `closure_certs.txt`,
`partition_controls.json`, `source_hashes.json`, `prime_supply_audit.json`,
`tree_*.json`, `input_*.json`, `search_*.json`, and `certs/`.
`manifest7a.json` binds the final note, scripts, ledgers, inputs, trees, and
all certificates. No original sym5/indep5 file was modified and no commit
was made.
