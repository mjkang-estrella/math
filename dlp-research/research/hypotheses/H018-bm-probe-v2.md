# H018 BM probe v2: one declared fixture-only extension

2026-10-08. Implementation/review authorized by root; numerical execution is
NOT yet authorized. Immutable v1 artifacts at commit `124dba5` remain intact.
This document authorizes no subsequent extension or automatic rerun.

## Reason and exact scope

The v1 attempt exhausted 96 fixture-order tests using 71,755 events, before
controls or feature sampling. Its recorded pre-JSON elapsed time was
0.029313264996744692 seconds. This is a public fixture-selection failure,
not a negative feature result or a hardware-performance claim. The original
result remains `experiments/H018/initial_results.json`; do not overwrite it.

Root explicitly permits one extension of the PUBLIC curve search from
b=1,...,4 to b=1,...,8 at the same p=8191, with up to 273 order tests.
No secret, feature output, or changed feature criterion selected this family.
Every repeated setup and failed test is charged again. Stop at the first
eligible fixture. If this attempt fails, park this diagnostic.

## Frozen operations

Use `experiments/H018/bm_probe_extension.py`, reusing the immutable v1 meter,
field/group/BM implementations, primitive-w search, controls, and feature
sampling. The only duplicated algorithm is the short fixture-selection driver
with its differences annotated; no second arithmetic/BM framework.

1. Instantiate the v1 meter and, BEFORE new algorithmic work, set phase
   `prior_diagnostic` and charge `tick('prior_run_events', 71755)`.
2. Recertify p by trial division. Enumerate and trial-divide ALL odd candidates
   in [8011,8373], skipping q=p with a charged comparison. Rebuild the prime
   list; do not load it as advice from v1. Assert its length is 39 using one
   separately charged comparison. A mismatch invalidates this freeze.
3. Try b=1,...,8 in order on y^2=x^3+x+b. Charge the discriminant check and
   evaluation at x=-1; skip if the latter is zero, because (-1,0) is rational
   2-torsion. Thus b=2 is rejected on paper, not from an observed feature.
4. Keep the original point rule: x=0,...,15, first nonzero-y point found using
   eleven squarings for h^2048, verify y^2=h, and choose min(y,p-y).
5. Test the recertified q values in increasing order on that point, with at
   most 273 tests globally in this attempt. A nonzero G with [q]G=O and
   2q>8373 certifies the full prime order by Hasse. q=p remains excluded.
6. Re-factor q-1 and certify the first primitive w in 2,...,33, or stop
   inconclusively. Use the same first eligible G and w rules as v1.
7. Run the original controls BEFORE feature streams: length-16 planted
   1+2w^i+3w^(2i), with complexity 3 and recurrence validation; then the
   length-at-most-64 fixed LCG (seed 18018, multiplier 1664525, increment
   1013904223, modulus 2^32), stopping at complexity 32. It is not an iid null.
8. Generate at most 128 shared samples P_i=[w^i]G. The four Fq-valued features
   remain centered x; centered y; (Y^2-X^3-X-b)/p modulo q; and
   center_p(-x/y) modulo q. Run the same four BM streams, stopping each at
   finite-prefix recurrence LENGTH L>=64. No root/log extraction or feature
   tuning. Preserve prefixes, discrepancies, L traces, samples, and partial
   update status exactly as in v1.

Here X,Y are centered integer representatives in Fp. The kappa quotient is an
exact integer division; the formal-parameter inversion is in Fp. The odd full
prime-order orbit has neither O nor affine y=0. All arithmetic, exceptional
group cases, tests, dynamic array work and trace writes remain charged.

## Global resources and precise paper ledger

The cumulative event cap remains **1,000,000**, including v1's 71,755.
Therefore this process has at most **928,245 new events**. There is no separate
fresh million-event budget. Carry is one explicitly labelled prior-run event
category, not misattributed current curve arithmetic.

Root explicitly increases the authorized aggregate wall allowance from one
60-second process to **120 seconds across TWO processes**, each independently
guarded at 60 seconds. This is a declared one-time increase, not an invisible
timer reset. Record the original elapsed observation, current elapsed time,
and their labelled sum; neither observation implies a hardware speed claim.

The event unit and administrative exclusions are unchanged from v1: bounded
word/modular arithmetic, comparisons, bit operations, dynamic array accesses,
and trace fields are counted. Meter internals, protocol/source/result SHA-256,
JSON parsing for provenance, and JSON formatting are administrative; their
wall time is included. Prior JSON must not provide any curve or prime-list
input to the algorithm. No inverse, log, random-function, or full-orbit table.

| Phase | Maximum/reservation |
| --- | ---: |
| Prior v1 diagnostic carry | 71,755 |
| Repeated setup, primality/factoring, point searches | 35,000 |
| New count-39 assertion | 1 |
| At most 273 order tests, including each test record | 210,483 |
| Primitive-w certification | 25,000 |
| At most 127 sample scalar multiplications | 36,703 |
| Normalization, features, sample/curve checks | 35,000 |
| Four BM streams | 400,000 |
| Both controls and validation | 35,000 |
| Other current bookkeeping | 20,000 |
| Cumulative paper total | **868,942** |
| Remaining cumulative reserve | **131,058** |

The tighter scalar bounds are PAPER bounds on the existing code, not the
observed v1 maximum. Its general-a doubling costs at most 25 events; addition
including the equal-point branch at most 37. For an ell-bit positive scalar,
mask scanning and loop overhead cost at most 30+2ell. Below 8192, excluding
8191, q has at most 12 set bits: 12 doubles, 11 additions and 56 overhead
give 763 events, plus eight record/count events =771. From 8192 to 8373 there
are 13 doubles and at most seven additions, yielding a smaller bound. Thus
273*771=210483. For w<=31, at most four doubles/four additions plus 40 overhead
give 288; w=32,33 give smaller bounds. The next outer-loop comparison is also in the orbit phase, so its full
reservation is127*(288+1)=36703.

The 400k BM bound uses the aggregate discrepancy/update coefficient-iteration
bound, paid copies, inversions, trace and initialization, as documented in the
unchanged v1 implementation. Coordinate normalization and controls each keep
their reviewed 35k allocations. The one new length assertion has a separate
one-event phase so it is not omitted from the total. All phase overruns must
be reported, even if the hard cumulative cap has not been reached.

## Provenance, reporting, and interpretation

Report SHA-256 of this protocol, the extension source, v1 source, v1 protocol,
and prior output. Pin all three v1 artifacts to their independently audited
SHA-256 values, rejecting even jointly altered source/protocol/output. Validate that prior output describes the 71,755-event
fixture failure with no completed controls/features, and that its recorded
source/protocol hashes match the immutable artifacts. A provenance mismatch
invalidates this attempt; do not silently substitute a new prior run.

Report cumulative and current event totals separately, with cumulative phase
and kind tables and a clearly isolated `prior_diagnostic` phase. Preserve
uncommitted BM-update markers on interruption. Retain partial certificates
only under the same validated-control/committed-trace conditions as v1.

Numerical execution, if separately approved, must use `python3 -B` to avoid
bytecode files. This implementation/review authorization permits AST parsing
only, not importing or running the probe. Root and independent Sol review
precede any execution; no git, state, or v1 artifact changes are authorized.

A reached threshold excludes global sparse-power count t<64 for that exact
feature/fixture/generator. Failure to reach it remains unresolved. This does
not certify a sparse identity, asymptotic randomness, all coordinate methods,
or a full-range ECDLP improvement. Verified improvement remains NONE.
