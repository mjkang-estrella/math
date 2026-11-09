# Sym3: target 111132 continuation

This effort owns exactly the 210 `SKIPPED (k=...)` configurations in
`verification/highdim/hd2/results_t111132.json`: 124 at k=5, 66 at k=6,
18 at k=7, and 2 at k=8. The earlier 122 closures are outside this assignment.

**COMPUTED** denotes executed finite computation; **PROVED (checked)** requires
a complete slice cover, two direct checker PASS results for every component,
and the finite short-length exception scan. BUDGET remains open. No claim here
settles the persistence conjecture.

Tools were copied from sym2 into sym3, without changing their source files.
The adapted driver uses the original nd-sym format and arithmetic kills.
It invokes `verification/highdim/sym/check_sym.py cert.jsonl 11` and
`verification/indep4/check_sym_F.py cert.jsonl 11 --json` directly as separate
isolated subprocesses, without importing or wrapping either checker.
All Python invocations use `bash -c 'ulimit -v 8000000; python3 -I ...'`.
Search stages are limited to 1500 or 1740 seconds, with at most 12 workers and a
checkpoint after every configuration. Completed certificate trees are atomic;
partial trees are not saved. Cross-stage reuse references existing files.
No legacy certificates are duplicated. Writes stay within sym3 and this note;
no git commit is made.

Equal-coefficient positions form multisets. Distinct coefficient groups remain
independent, so all distinct coefficient orderings are included. The separate
`audit_orderings.py` enumerates all 10160 coefficient words across the 210 cases
and checks their bijections with grouped position ranks.

Coverage reuses copied `audit_coverage.cover` and the sym2 distinct-position and
position-partition refinements. Each fixes every low-position possibility and
retains the high tail before using a checked certificate. The finite smooth
scan covers lengths below terminal certificate floors. Checker solution lists
are compared and filtered back to the original digit configuration.

For a configuration `(S,R)`, the equation is
`X=9n=10^L+(9S-1)+sum(c*10^q for c in R)`, with pairwise distinct
`3<=q<L`. A certificate at `(K,R,qmin)` uses `t0=v2(K)` and requires
`qmin>t0`, so every point in its domain has `v2(X)=t0`.
The stronger-floor search decides positions `p=3,4,...`. At each position,
either the digit is 1, or one distinct remaining coefficient value `c` is
fixed there: replace `K` by `K+c*10^p`, remove one occurrence of `c`, and
advance `p` once. It stops only at `p>=max(3,v2(K)+3)`.
This partitions every original placement, never fixes a position twice, and
makes the mod-8 pin valid on every terminal certificate. If an original length
ends before that floor, the finite scan through the maximum floor minus one
includes it. The independent coverage replay may also use a lower-floor
checked certificate wherever its domain contains the entire remaining branch.
Open configurations retain explicit missing-domain diagnostics and are not
claimed to have complete slice coverage.

## Final executed results

**COMPUTED:** Newly closed/open counts for this assignment:

- k=5: 122 closed, 2 open, 124 assigned.
- k=6: 26 closed, 40 open, 66 assigned.
- k=7: 2 closed, 16 open, 18 assigned.
- k=8: 0 closed, 2 open, 2 assigned.

Both direct checkers PASS on all 18734 retained certificates, with brute L<=11. Their complete solution lists agree. No checker failure or timeout is counted as a closure.

**PROVED (checked):** Every counted closure has a full slice cover built only from hash-bound certificates accepted by both direct checkers, together with the finite short-length scan and the complete filtered size-leaf solution lists.

Coverage: 150 complete configurations; 60 incomplete. Every case has its coverage result, failed-cover diagnostics if open, and distinct ordering count in `coverage_audit.json`. Closed cases include the exact certificate list, coverage method, finite bound, and filtered members. No open case is claimed covered.

The ordering audit passes all 210 configurations and 10160 words. The finite exception scan checks 36367 smooth integers through 29 digits and finds 0 members in closed cases.

Certificates occupy 12924285 bytes, with zero duplicate domains. No legacy certificates were copied.

The first launch of precomputed24 briefly overlapped broad8 and was stopped immediately, before it produced a checkpoint or retained certificate. This transient exceeded the intended 12-worker cap; later search/check pools ran sequentially with at most 12 workers. The interrupted launch log is retained separately.

Checkpointed stages:

The supply-B 180-second pass was intentionally stopped at its saved checkpoint after the target-specific notes identified the need for the larger prime supply. The final supplyD180 pass uses the existing supply_D.json as an untrusted search aid. Primality, decimal orders and every kill are still independently recomputed by both direct checkers. Completed files from the interrupted pass are retained and checked; unsaved partial trees are discarded. The pre-supply driver is frozen in inputs/.

- `search_broad8.json`: 210 configurations, {'BUDGET': 201, 'COMPLETE_PENDING_CHECKS': 9}, 1662.582 worker seconds.
- `search_high_positions180.json`: 10 configurations, {'BUDGET': 6, 'COMPLETE_PENDING_CHECKS': 4}, 1225.725 worker seconds.
- `search_high_positions72.json`: 164 configurations, {'COMPLETE_PENDING_CHECKS': 87, 'BUDGET': 77}, 6912.165 worker seconds.
- `search_precomputed24.json`: 201 configurations, {'COMPLETE_PENDING_CHECKS': 37, 'BUDGET': 164}, 4432.381 worker seconds.
- `search_supplyD180.json`: 73 configurations, {'COMPLETE_PENDING_CHECKS': 13, 'BUDGET': 60}, 11804.04 worker seconds.

Evidence:

- `assignment.json`: source hash and exact 210-case assignment.
- `summary.json`: closed/open keys, counts, members, stages and full per-case coverage.
- `standalone_checks.json` and `check_journal.jsonl`: exact direct commands, certificate hashes, both checker results.
- `coverage_audit.json` and `ordering_audit.json`: slice/short-length and ordering coverage.
- `kill_usage.json`: per-certificate kill dependencies, stored reference counts, exact prime orders and F-checker actual kill classifications.
- `certs/`: compact nd-sym JSONL proof trees; `input_*.json` and `search_*.json`: budgets and checkpoints.
- `manifest.json`: SHA-256 evidence manifest.

Reproduction (repository root; each bounded command below 30 minutes):

```sh
timeout 1500 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym3/continue_sym3.py check --workers 12'
timeout 1500 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym3/continue_sym3.py audit'
bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym3/audit_orderings.py'
bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym3/finalize_sym3.py'
bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym3/verify_manifest.py'
```
