# Sym7b: adaptive position peeling for the seven sym6-open 111132 cases

Scope: precisely the seven keys in `verification/highdim/sym6/summary.json`'s
`open` list: far-coordinate count k=6: 2; k=7: 3; k=8: 2. This is a bounded
computational continuation, not a proof of the general persistence conjecture.
All writes are confined to `verification/highdim/sym7b/` and this note. No git
commit is made. Only the standard library is used; every Python invocation is
wrapped in `bash -c 'ulimit -v 8000000; python3 -I ...'`. Individual exceptional
replays may use the explicitly permitted 30000000 limit. Runs are configured
for an aggregate budget of eight workers, and every command is bounded below
thirty minutes. Search and checker ledgers checkpoint atomically between results.
At one transition the next six-worker search pool was started before the
previous pool had fully exited, briefly exceeding the intended pool allocation.
The new pool was stopped, and `recover.py` reconciled completed journal entries
and atomic certificate files before resuming. `recovery.json` records the three
recovered states. Later transitions require confirmed process completion.

## Exhaustiveness and the leading-position boundary

For a configuration let

    X = 9n = 10^L + K + sum(c_i * 10^q_i),   K = 9*S_low - 1,

where L is the number of decimal digits of n, the far positions q are distinct,
3 <= q < L, and coefficients c=9(d-1) for non-one digits d. Equal coefficients
form unordered groups; different coefficients remain independent.

A peeling state (K', C, p) represents the original assignments consistent with
the choices below p, with all still-free positions >= p. Its full arithmetic
certificate, when present, may cover a larger domain, which is safe. At position
p there is either no far coordinate, or exactly one far coordinate: distinctness
forbids two occupants. If p is empty the successor is (K', C, p+1). If its
coefficient is c, the successor is

    (K' + c*10^p, C with ONE copy of c removed, p+1).

There is exactly one branch for every distinct coefficient remaining, not one
branch per labelled copy. Thus these branches are disjoint and exhaustive on
canonical original assignments. In group language this is the proposed test:
one copy sits at p versus all copies in the group exceed p, applied to all
groups. Once a position is decided, it is never revisited, so fixed positions
are distinct and no remaining position can collide with them. Every original
assignment, including every ordering of distinct coefficient groups, has a
unique route. Merging identical (K',C,p) states preserves containment.

The leading exponent L is NOT a far coordinate. An occupied branch requires
L>p; an empty branch advanced to p+1 can omit L=p. We do not silently discard
these points. The coverage auditor sets B to at least every state floor and
proves the tree cover for L>B. A separate exhaustive enumeration of all
2,3,7-smooth n<10^B checks every original configuration of length L<=B.
This also covers the empty-group boundary L=p, and allows safe comparison to a
certificate whose no-free-coordinate domain permits L=qmin. The finite scan
and all exact-size-leaf solutions are filtered against the original decimal
configuration and target product 111132.

After EVERY occupied branch, t0' is recomputed as v2(K'), never inherited from
the parent. A certificate is used only when qmin>t0', qmin<=p, and
pin_digits<=qmin. If the new valuation is too large, peeling continues or the
state remains explicitly OPEN at the run's depth bound. The optional mod-8 pin
additionally requires qmin>=t0'+3. Certificate checkers independently derive
t0' from the constant; the certificate does not store a trusted valuation.
For legal pin depth d, X=K' mod 10^d holds throughout the terminal domain,
including q=qmin=d. Dividing once by 2^t0' gives the sym5 congruence

    X/2^t0' = K'/2^t0' (mod 5^d * 2^max(d-t0',0)).

## Implementation and validation policy

The generator, precomputed generator, checker snapshot, supply, finite-scan and
position-control modules, and ordering auditor are copied from sym6 without
modifying their sources. `source_hashes.json` binds the originals and F5's
checker/readiness note. `peel.py` is a new adaptive driver. Existing certificates
are search hints only: any chosen certificate is copied locally and receives
fresh direct command-line invocations of BOTH
`verification/highdim/sym5/check_sym5.py` and
`verification/indep5/check_sym_F5.py`. No inherited PASS is accepted. The latter's
`NOTE_F5.md` now reports passing deep-pin tests and independent replay results.
Every generated certificate is replayed, including certificates belonging to
incomplete configurations. No unfinished generator tree is emitted.

The original scripts remain unchanged. The local generator later received one
memory-only optimization: its inverse join now uses `residues7.get(key, ())`
instead of indexing a `defaultdict`. Indexing inserted an empty list for every
missing residue, exhausting the 8 GB search cap at depth nine. A missing lookup
contributes no pairs in either implementation, so the arithmetic and pair order
are unchanged. `gen_sym_before_lookup.py` and `gen_sym.py.diff` identify the exact
change. `lookup_controls.json` reports 48 comparisons with 12,908 identical
ordered pin pairs, including the valuation/depth edge cases. The deeper retry
then stayed within memory and stopped at its recorded lift budget. Both original
arithmetic checkers are still invoked directly, without this optimization.

An inherited K=89, qmin=6, dim=8 certificate passed M but exhausted F5's memory
even at the permitted 30 GB cap. It is archived under `withdrawn/`, with both
direct checker records in `withdrawn.json`, and is excluded from every closure.
Its leaf was replaced by exhaustive position peeling; any unresolved replacement
leaf keeps the configuration OPEN. Other memory-limited certificates receive
individual 30 GB replays. Successful results are merged only with matching
certificate and checker hashes; all failed attempts remain in the journals.

`audit_peel.py` does not import the driver, generator, or either arithmetic
checker. It reconstructs every expected successor from the recorded parent,
checks equality of the entire child map, verifies every root against the exact
assignment, requires all states reachable, and checks certificate containment,
hashes, and both direct checker results. Its small-box control independently
enumerates canonical original tuples, including empty groups, repeated groups,
occupied floor positions, and changes in v2. The separate copied ordering audit
checks every coefficient word and inverse grouping.

A closure requires a complete audited tree, two passing arithmetic checks for
every certificate in that tree, no finite-scan member, and no original-configuration
member among size-leaf solutions. Incomplete, timed-out, or resource-limited
obligations remain OPEN. `kill_usage.json` records each certificate's witness
references and proof dependencies; search failures are retained in
`search_journal.jsonl`, and checker failures/timeouts in `checks_journal.jsonl`.

## Executed results

| Far digits k | Assigned | Closed | Open |
|---|---:|---:|---:|
| 6 | 2 | 1 | 1 |
| 7 | 3 | 0 | 3 |
| 8 | 2 | 0 | 2 |

Total: **1 closed, 6 open**, among exactly the seven assigned sym6-open configurations.

Closed key(s):
- `111132:21|9,18,54,54,54,72`

Every remaining key is explicitly OPEN:
- `111132:10|9,18,18,18,18,54,54,54`: 40 unresolved terminal obligations.
- `111132:10|9,18,18,54,54,54,72`: 27 unresolved terminal obligations.
- `111132:1|9,18,18,18,18,54,54,54`: 16 unresolved terminal obligations.
- `111132:1|9,18,18,54,54,54,72`: 5 unresolved terminal obligations.
- `111132:205|9,18,18,54,54,54`: 3 unresolved terminal obligations.
- `111132:601|9,18,18,18,18,54,54`: 17 unresolved terminal obligations.

**Direct arithmetic checks: M 2042/2042 PASS; F5 2042/2042 PASS on all retained certificates.**
This includes 63 freshly replayed inherited certificates and certificates from incomplete configurations. No inherited verdict was reused. The pin-depth histogram is `{5: 4, 6: 438, 7: 740, 8: 858, 9: 2}`.

One additional inherited candidate is withdrawn: M passed, but F5 returned `MemoryError` at the permitted 30 GB cap. It is archived under `withdrawn/`, excluded from the retained totals, and its former proof leaf was replaced by position peeling. The replacement has unresolved leaves, so it does not close that configuration. Six other F5 certificates exhausted the standard 8 GB cap and all six passed fresh direct 30 GB replays. All failed attempts and exact commands remain in the checker journals.

**Coverage:** the exhaustive split audit is **PASS**, with 1366 checked split nodes and 3516 reachable states. Exactly 1 configuration cover is complete and dual-checked; 6 covers are incomplete. There are 108 explicit unresolved leaves, and no incomplete cover is counted closed.

The independent small-box controls pass: 175 cases, 2135 canonical points; 2074 legal deepest-pin checks and 61 cases that require further valuation peeling. The ordering audit passes all 1685 coefficient words for all seven configurations.

Fresh finite scan: `L <= 26`, 26455 smooth n, **zero original-configuration members**. All exact-size-leaf solutions were also filtered against the original digit configurations; none is a member.

Kill-ledger enabled-feature totals: `{'decimal_tail_coset': 2042, 'mod8_parity': 964, 'unaligned_sumset': 721, 'prime_coset': 2042}`. Witness references: `{'prime_witness_references': 2277632, 'unaligned_sumset_references': 13480}`. These are dependencies of the recorded proofs, not claims of minimal necessary pin depth.

All frozen original source hashes and the assigned-input hash verify unchanged. The only local generator change is the tested lookup optimization described above. No git commit was made.

### Bounded search checkpoints

| Stage | Emitted certificates | Budget-limited | Other errors |
|---|---:|---:|---:|
| peel6 | 407 | 103 | 0 |
| peel7 | 303 | 91 | 0 |
| peel8small | 409 | 16 | 0 |
| pin8high | 106 | 16 | 0 |
| finalsmall | 716 | 6 | 0 |
| k6pin9 | 2 | 1 | 0 |
| replace_large8 | 22 | 1 | 0 |
| replace_root9 | 0 | 0 | 1 |
| replace_root9_get | 0 | 1 | 0 |

The table counts newly emitted/checkpointed results of completed stages. It excludes copied library hits and three results recovered at the interrupted transition; those files are all included in the retained replay totals. Search errors never emit partial certificates. The first depth-nine K=89 attempt exhausted memory; the read-only lookup retry passed initialization and stopped at its smaller lift budget.

### Reproduction and evidence

Every exact direct checker command, time, memory cap, certificate hash, checker hash, stdout, and result is in `checks.json` and `checks*_journal.jsonl`. `checks_large.json` preserves the withdrawn candidate's 30 GB failure; `checks_rescue*.json` record the six successful memory rescues. Search parameters, complete trees, and interrupted recovery are in `tree.json`, `search_*.json`, `search_journal.jsonl`, and `recovery.json`. Do not rerun `peel.py init` on an existing evidence directory unless intentionally rebuilding it.

From the repository root, hash-bound replay and audit commands are:

```sh
timeout 1500 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym7b/replay.py --workers 6 --seconds 300'
timeout 180 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym7b/audit_peel.py'
timeout 60 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym7b/audit_orderings.py'
```

The replay command skips an existing PASS only when both hashes match; those PASS records were all produced by fresh direct invocations during this continuation. Individual large-check commands use the recorded 30000000 cap and remain below thirty minutes.

Main files under `verification/highdim/sym7b/`: `summary.json`, `verification_status.json`, `coverage_audit.json`, `ordering_audit.json`, `kill_usage.json`, `checks.json`, `checks_large.json`, `checks_rescue*.json`, `checks_late.json`, `tree.json`, `assignment.json`, `lookup_controls.json`, `withdrawn.json`, `source_hashes.json`, `manifest.json`, `certs/`, and `withdrawn/`. The manifest binds this note and every retained certificate.
