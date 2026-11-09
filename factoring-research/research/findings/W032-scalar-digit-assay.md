The W032 scalar-digit implementation passed the preregistered finite diagnostic
in its **single permitted run**. All **155 cases completed**, including all 131
unit cases and all five independent matrix controls. There was no formula or
implementation mismatch, and no stopped, failed, or unstarted case. **Verified
complete factoring improvement: NONE.** The disposition is **inconclusive on any
factoring gain**; the finite implementation and identity screen passed.

Execution began 2026-10-09 04:58:19 UTC (2026-10-08 in the project timezone).
The complete assay used **19,964 of 20,000 events**, leaving 36, and
**0.26432903797831386 seconds** from the external launcher's start through child
exit, against the fixed 60-second cap. The child recorded 0.2352843099506572
seconds before final result serialization. Use the larger external duration for
the complete run. The process returned 0; stderr was empty. No pilot arithmetic,
rerun, post-result source change, or cap increase occurred.

The [frozen brief](W032-scalar-digit-assay-evidence/brief.txt),
[protocol](W032-scalar-digit-assay-evidence/protocol.md), and
[expanded case list](W032-scalar-digit-assay-evidence/cases.json) specify the
algorithm, exact execution order, event granularity, reference work and rejection
conditions. All 19 input/source payloads were frozen before execution. The
[pre-run manifest](W032-scalar-digit-assay-evidence/freeze-manifest.json) was
externally SHA-256 anchored before launch as
`97a99ab6760c9c838d32e9204687cc1a98a4c5efd76a0a681b21177de9c3eef1`.
Its ten input snapshots include the required project instructions, full parent
W032 protocol, W031 parent disposition and reviewed trace interface. Its other
nine payloads are the six Python sources, full brief, protocol and exact cases.
Static compilation before freeze executed no candidate/reference arithmetic.

The candidate performs scalar quadratic-pair powering by a left-to-right binary
loop, with the leading bit initialized to (z,1). Pair squaring uses four modular
products and two additions; multiplication by (z,1) uses three products and two
additions. The N=143 loop has seven squarings and four base multiplications;
N=323 has eight and three. Public modulus/digit powers and (-4)^n are computed
once per N and charged. Reference inverses are also globally cached and charged.
There is no polynomial jet or literal N-step exponent loop. Known factors enter
only the reference configuration and factor classification, never candidate.py.

All unit records retain canonical A, B and V, the exact A/N² quotient and
remainder, normalization operands, all four digits and gcds, formula values,
identity outcomes, factor properties, per-case event vectors and widths. The
[full results](W032-scalar-digit-assay-evidence/results.json) include every index;
the [completed record stream](W032-scalar-digit-assay-evidence/records.jsonl)
contains the same 155 records. V is null and digits are empty for the prescribed
initial-factor and a=0 branches, rather than fabricated normalization values.

For the complete N=143 domain, the 143 input cases separated into 120 units,
22 proper initial gcds and the single a=0 skip. The initial proper factors were
11 in 12 cases and 13 in 10 cases. These are separate from digit results. For
each digit below, counts are **gcd=1 / proper gcd / gcd=N**, over the 120 units:

- d1: **120 / 0 / 0**.
- d2: **107 / 13 / 0**; proper factors were 11 five times and 13 eight times.
- d3: **99 / 21 / 0**; proper factors were 11 fourteen times and 13 seven times.
- d4: **109 / 11 / 0**; proper factors were 11 eight times and 13 three times.

There were 41 distinct unit inputs with at least one proper digit gcd. Digits
3 or 4 supplied a proper gcd at 30 distinct unit inputs, of which 28 had no
proper d2 gcd. Overlap is retained: the individual digit counts must not be added
and presented as distinct successful inputs. As a concrete later-digit example,
N=143,a=2 produced V=4964645729805987512, digits (24,67,13,28), and gcds
(1,1,13,1). This is an exploratory finite observation, not a selection rule.

For the twelve fixed N=323 inputs, eleven were units and a=17 returned the
ordinary initial factor 17. Over the eleven units, in the same count order:

- d1: **11 / 0 / 0**.
- d2: **8 / 3 / 0**; all proper factors were 17, at a=5,13,47.
- d3: **9 / 2 / 0**; factor 19 at a=7 and factor 17 at a=31.
- d4: **9 / 2 / 0**; factor 17 at a=3,23.

These were seven distinct unit inputs with a proper digit gcd; the four higher
digit inputs were disjoint from the d2 inputs in this fixed list. The list is a
public fixed holdout, not a statistical sample. No unit digit in either group
had gcd=N. The a=0 initial gcd=N was retained as a skip, never a proper factor.

Each of the 131 units passed A divisible by N², V mod N²=1, the d1 identity,
the exact integer quotient (a²+r)/24, the d2 identity and the d1 unit-gcd check.
Canonical ranges and factor divisibility checks also passed. Every unit produced
all four digits before the formula controls ran, even after a proper digit gcd.
The five prescribed N=143 matrix cases a=1,2,3,5,7 all matched A. The reference
uses ordinary dense 2×2 matrix binary multiplication of [[2z,-4],[1,0]], without
Delta or calls to the pair routine. It multiplies the trace by the modular
inverse of 2; it does not integer-halve canonical trace residues. For example,
the a=1 trace is the odd integer 51027994965054826532099, and its correct modular
half is 281176135495309669539353. Scalar arithmetic and the Python interpreter
are shared between representations; this is not a second integer-arithmetic
implementation or a symbolic proof.

The [event stream](W032-scalar-digit-assay-evidence/events.jsonl) contains every
charged event, operands/results, trial and scope, and widths. Total charges
separate as follows:

- Administrative frozen-input/control checks: **21**.
- Candidate public setup: **104**.
- Reference setup: **27**.
- Candidate case work: **13,600**.
- Reference case work, including all matrix controls: **6,212**.

Peak operand width was **92 bits**, peak explicit unreduced intermediate width
**184 bits**, and peak result width **92 bits**. The descriptive sum of squared
maximal event widths was 120,571,911. The complete scoped event vector is retained
in results.json and stdout.txt; individual case vectors are in each record.
Normal N=143 unit cases used 144 events, the five matrix cases 293 each, N=323
unit cases 145 each, and nonunit/skip cases eight each; setup is additional.

A modular multiply/add/subtract is one fused arithmetic-plus-reduction event;
divmod is one event returning both quotient and remainder. Gcd and inverse are
one event each with opaque internal Euclidean operations. Power and extraction
stages and named control predicates receive additional events. Python iteration,
logging, hashes, instrumentation counters and output summarization are covered by
the wall measurement rather than a Python-instruction event count. Internal
gcd/inverse intermediate widths are not measured. **These events are not bit
costs**, and no speed comparison against trivial gcd screening, trial division,
or a factoring implementation was performed. No all-input claim or complexity
claim is supported by this finite assay.

The [post-run integrity audit](W032-scalar-digit-assay-evidence/integrity-audit.json)
confirmed all 19 frozen payload hashes and sizes remained unchanged, record-stream
equality with results.json, contiguous event IDs, and exact agreement of the log
count/vector with the recorded 19,964 events. This was a file/ledger audit only;
candidate and reference numerical functions were not invoked again. The
[launch marker](W032-scalar-digit-assay-evidence/RUN-ONCE.json) and
[external execution result](W032-scalar-digit-assay-evidence/execution.json)
retain the one-launch guard, timestamps, wall duration and return status.

The [delivery manifest](W032-scalar-digit-assay-evidence/delivery-manifest.json)
lists the complete report and all evidence payloads with SHA-256 and byte sizes.
It excludes only itself and its
[hash anchor](W032-scalar-digit-assay-evidence/delivery-manifest.sha256), avoiding
self-reference. The same final manifest hash is emitted externally at handoff.
The delivery contains 31 inventoried payloads plus those two inventory files,
33 files total. No shared solver, Lean, STATE or task file was edited; no install,
commit, recursive delegation or shared project check was run.

The next parent action is evidence intake alongside the already-assigned symbolic
W032 audit. Exact later-digit carry structure and a paid, useful input-selection
or success argument remain open; small-domain proper gcd counts resolve neither.
The separate live W031 normalized-prime-screen task was not duplicated. Shared
project checks remain with the parent if required after intake. This assay is
finished and must not be rerun or tuned under this preregistration.
