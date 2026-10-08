# W023: actual fresh-run checks for the frozen query programs

Verdict: **independently reproduced finite execution evidence**, harness review PASS.
Author: coordinator Astra. Reviewer: native Astra `/root/encoding_review`.
Frozen scripts/word_query_checks.lean SHA256:
`ba9f60eba3462952680f7f871274f372c817f24dd2d39b3e0704f94eaee2b5b9`.
Uses committed WordQueryCode hash
`362e4ea41199bcbbaa11f8cb050e416ba757a173fc46c715b1bf3cb060182a82`
and unchanged WordRun hash
`72ced59f481e8aef7f3340f918fa3d24ce8e9ff7ceb497d356f3cf31238b76e6`.

## Hypothesis and scope

The two actual typed programs are predicted to execute the W018 packing/search
paths correctly under fresh charged setup. Wrong output, fault/exhaustion at F,
wrong prefix state, altered source, mismatched trace counts or failed fuel
boundary assertions falsify the hypothesis on a tested input. This is compiled
Lean evaluation of the actual WordRun runner, unlike W018's Python model.
It is still finite testing, not a kernel correctness/cost theorem.

329 paired datasets passed. The complete bounded data domains are:
(W,m,k)=(7,0,0), (7,0,7), (7,1,0), totaling257 datasets. Every payload/query in
those domains is covered. The remaining72 are targeted duplicate, absence,
maximal-value, full-width, maximal-m and M=U cases; no exhaustive claim for
those domains. Every dataset is checked against actual common admission and
typed key/payload/query ranges and is nondecreasing. Sorting/header agreement
remain preconditions; their host test checks are not guest instructions.

For each program and dataset the harness calls fresh run twice: once at the
common F and once at I+a, where a=6L+26m+42 is the exact-prefix hypothesis.
The latter must exhaust in guest state at PC86 with all32 registers and the
entire heap equal to the independently specified prefix state. Prefix equality
is observed from these actual states and compared traces; PC is not invented
as a trace field. Each prefix opcode and setup/access count is checked.

At F, both must halt with the specified output, preserve source bits/register0,
and have exact predicted used/remaining, guest attempts, probe/equality count,
halt count and completed accesses. Sequential output uses the first matching
entry of the input; binary output/probes use existing verified IndexedLookup
as an independent host oracle. Neither oracle result is given to the guest.
Duplicate payloads need not agree between programs. Their actual full-run trace
prefix must equal the separately executed fresh prefix trace.

Two empty-table full runs and sixteen boundary reruns check zero fuel,
pre-setup/setup boundaries, first guest step, exact prefix boundary, just before
halt, exact halt and extra-fuel terminal stability. In total the final suite
executes **1334 fresh runs and455341 setup/guest trace events**. These event
counts are actual Result.used sums, not the number of host implementation steps.

## Commands, results and development failures

Exact command from dlp-research (the file uses #eval, not --run):

```
timeout 60 ./scripts/lake.sh env lean scripts/word_query_checks.lean
```

Final suite exited0 and printed PASS. Independent reviewer inspected the exact
frozen harness and reran it once with exit0. Output is archived as
research/findings/W023-word-query-results.txt, SHA256
`869e02137c40d1c868f4b5e0dd88668d5fbc912e2110e6c1d6b7ed747a6d13a1`.
The three counts and complete-domain scope match exactly. An initial nine-dataset suite passed36 fresh runs/19085 events. Adding one
independent rerun of the final suite gives929767 total events for this bounded
wave, below1M. No additional execution is needed without a new defect/change.

The initial compile rejected reserved identifier prefix; it was renamed
prefixRun. During suite expansion, three type-inference attempts for nested
shape iteration failed before evaluation; an explicit pair-type ascription
resolved them. No runtime assertion failed. Lean's refusal to evaluate terms
with elaboration errors was respected: no #eval! or proof escape was used,
and no heartbeat/time/event limit was raised.

## Remaining obligations

Generic admitted-input correctness, no-fault invariants, full prefix termination
and state-based split, actual deterministic search refinement, F sufficiency
and trace-derived comparison proofs remain open. Manual count formulas now have
finite runtime evidence, not universal proof. No winner/crossover, hardware,
whole-BSGS or ECDLP speed claim is made. This is packed-table search under common
full packing; it says nothing about streaming/lazy alternatives or unavoidable
preprocessing. Source preparation and host test/oracle computation are excluded
from the frozen guest model, as already declared by W016.

Reviewer qualification: prefix checks cover all registers/heap cells and all13
opcode counts; full-run checks cover selected counters plus aggregate/access
counts, not every individual opcode. Source/r0 preservation is observed at the
prefix and halt, not at every intermediate state. Fuel boundaries use the empty
profile only. These are the intended finite checks, not global invariants.
No blocker was found and no source change or additional rerun was needed.

Integrated `./scripts/check.sh` passed363 theorem audits and build/smoke checks
with the W024 module. The runtime script is separately executed by the command
above; it is not silently included in the ordinary check script.
