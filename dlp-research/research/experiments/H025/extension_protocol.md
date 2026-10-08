# H025 unchanged-B exact scaling extension — pre-run protocol

2026-10-08. Root adopts native Sol's completed continuation proposal with the
explicit stopping/output rules below. Independent static review is required
before the sole execution. No import/self-test/numerical run has occurred.
Initial coverage_probe.py,protocol.md,initial_results.json remain byte-for-byte
unchanged. This is a fixed scalar-coverage falsifier, not an EC solver/benchmark.

## Question and parameters

Does unchanged B save at least5% exact uniform-target generated keys against
BOTH the declared GWZ-style control and the H019 signed two-family schedule
at each of32771,65537,131071 in that order? M=floor(sqrt(q/2)) is respectively
128,181,255, covering M mod3 classes2,1,0. Expanded primality certification
must pass; a failure is inconclusive with no substitution. No empirical
phase model or asymptotic claim is being tested. Primes were selected before
extension data to increase sizes and cover these gcd classes, not tune B.

Per prime run in fixed order:
1. control: b=(0,1,2),c=0,s=(1,M,-(M+1)); positive prefixes.
2. two: b=(0,1),c=0,s=(1,-ceil(sqrt(2q))); positive prefixes.
3. B: b=(1,2,4,8), c_i=floor(q/73)*b_i² modq,
   s=(M,-(M+1),M+2,-(M+3)); original alternating centered prefixes.

All use original h=max(1,floor(floor(log2q)/16)), block h(2h+1), cyclic
families, main keycap=floor(3ceil(sqrt(q))/block)*block and early full coverage.
At these orders h=1 and block=3. The two-family schedule covers every scalar
by its usual index bound and therefore needs no stronger fallback; it is allowed
the same cap, with its actual peak use reported separately. Its useful input,
infinity and same-family signed matches are retained identically. This wrapper
is not an assertion of exact published constants or equal total memory.

Use original all-q prior; supplied logical O,G,Q records; zero-key initial
coverage0,+1,-1; both signs for every nonzero denominator; direct infinity;
complete-block inspection; cached expanded inverses; roots/primality expanded;
no comparison against cleared main records in fallback. On main miss the
original complete two-family fallback/overshoot/clearing rules apply. First
scalar-discovery and block-survival sums must reconcile. No narrowed secrets,
random samples, unpriced lookup oracle, A, shift tuning or replacement runs.
Attribution among shifts/centering/family count is deferred, not claimed.

## Gate and exact early rejection

After both controls complete at q, set T=19*min(N_control,N_two). B passes at
that order exactly when20*N_B<=T. The joint validation requires all three.
After each COMPLETE B block, if20*partial_survival_numerator>T, the final mean
cannot pass because every remaining survival term is nonnegative. Before
reporting rejection check the censored identity

    partial_survival_numerator
      = sum(discovery_cost[k] if already discovered else generated_keys).

The three initial hits have discovery cost0. The recorded array uses cost+1,
with0 for undiscovered. A failing check is inconclusive. A verified strict
lower-bound violation stops the ENTIRE extension immediately with status
rejected: later primes are not run and are explicitly untested. It is sufficient
to reject this all-three finite gate, not B at every size or asymptotically.
Earlier full passes and all partial case/block evidence are retained. Equality
is a pass condition; it must not cause early rejection. If no rejection occurs,
all cases must complete correctly to report passed. There is no success claim
from partial samples or an incomplete control. Early rejection can also occur
at completed fallback blocks and includes all paid main key costs.

## Bounded execution and artifacts

The initial preregistered finite gate passed for B. That justifies ONE larger
exact falsifier before expensive EC implementation. Root authorizes a global
50M-event budget including an explicit426964 prior-run debit. No per-case
reset. Initial1M was a first-run default, not a permanent ceiling. This fixed
extension's completion below50M is NOT certified; observed initial speed only
motivates feasibility. Cap exhaustion is inconclusive and cannot be retried
by resetting the budget. Independent static review must check instrumentation
and new stopping logic before execution.

Use H018's unchanged Meter/Field/prime_trial source and original event convention.
Only this extension process sets the configurable event cap50M and internal
work-time limit55s, reserving output time inside an external60s timeout. The
prior debit is one labeled charge and does not pretend those events were rerun.
Export both total including debit and debit amount. Hash source, original source,
H018 dependency and this frozen protocol. No mutation of initial files.

Command, from dlp-research:

```sh
timeout 60s python3 -B research/experiments/H025/extension_probe.py > research/experiments/H025/extension_results.json.gz
```

Output is lossless deterministic gzip of compact JSON, retaining all scalar
first-discovery arrays and block traces. JSON/compression/hashes are administrative
with wall time covered externally, not solver operations. Internal cap/error
retains partial arrays/pending blocks and exits2; completed pass/rejection exits0.
An outer timeout or corrupt/truncated artifact is inconclusive. Never promote
an unverified pending block or incomplete artifact into a rejection result.

## Full-work interpretation accompanying any result

Use findings/H025-frontier-cost-bridge.md. For main B ordinary arithmetic use
Cx*E[main keys] plus k(2M+S) times the sum of first-family-block reach
probabilities. Price fallback separately by its reach-weighted ordinary keys,
clearing, setup and support; no extra B fork is charged to fallback. Report
shared-initializer requirements, two center arrays per B family, support/scratch,
lookup/storage, exceptional dispatch and verification as remaining costs.
Do not use limiting2.5M+S at k=ell=1 or charge four independent shifted SCMs.

For hypothetical primitive weights, the remaining5% margin against each control
is .95*ordinary_control-ordinary_B, before the explicit omitted-cost difference.
Positive margin merely bounds allowable remaining work. No measured EC field,
curve family, CPU/GPU rate, bit-cost, equal-total-memory or full-solver improvement
is established by any scalar gate outcome. Negative finite evidence closes this
validation attempt; it is not a universal lower bound. No broad Lean machinery.

Pre-run review correction: output lists planned primes, wholly untested primes
and the stopping prime explicitly. It records and checks frozen hashes of the
initial source, protocol AND results, binding the426964 debit to the preserved
artifact. These hashes/metadata are administration; the equality assertion is
charged after the prior-run debit. A provenance mismatch is inconclusive.
