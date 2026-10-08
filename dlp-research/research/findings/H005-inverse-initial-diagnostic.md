# H005 I1: completed first cost falsifier

Status: completed frozen run and independent recorded-data audit PASS. The paper
all-admitted-target group-call extension below passed independent review. No improved ECDLP algorithm, asymptotic result or hardware speed
estimate follows. Native Sol implemented, native Astra reviewed math/protocol/source,
Claude Opus separately reviewed cost/evidence; root alone executed and integrates.

## Frozen evidence and command

From dlp-research, root ran ONCE:
`python3 research/experiments/H005/inverse_walk.py --output research/experiments/H005/inverse_initial_results.json`
Exit0, complete: all73 offsets, signed-BSGS reference and exact metadata aggregation.
No warmup or cap reset. Total822726 instrumented events, below the unchanged1M cap.
Recorded0.22977526602335274 seconds includes diagnostic work, NOT an ECDLP throughput
benchmark. No GPU calibration or inference to large fields.

Source SHA256 `968c1886389556eda86478f3c2f26a6741b2b908053dde5e182456f3173f1731`.
Pre-run amended protocol SHA256
`ee3425fd9f15021f1e6e76031f5da525ec091ba8d29bcd77a5f3a6978ff71f75`.
Raw JSON84864 bytes SHA256
`151564f18a315d81d6a88ade8daca0ce2804438691ffb6a02113bada5ec2e616`.
The raw record says complete and its full category/total reconciliation passes;
the independent reviewer verified those assertions without an EC rerun.

The curve is y^2=x^3+28x+27 over F59, full prime order73;
G=(34,35), Q=(4,47), inherited from previously recorded H002 seeds7,19.
Both algorithms actually verified the recovered scalar70. This was not supplied
as advice. It means Q=-3G: the signed reference matched immediately at giantindex0.
This favors the fixed-target reference; do NOT present the experiment as a
uniform-secret comparison. The separate bound below addresses this only in the
explicit group-CALL metric for the same tiny curve/implementation.

## Observations and explicit cost scope

62/73 attempts succeeded:59 useful cycles,2 identity hits,1 minus-generator hit.
11 attempts timed out; no zero-denominator-cycle outcome occurred. Failed-attempt
costs enter the expectation. Per-attempt transition counts are in the raw artifact; peak
candidate dictionary18 records versus reference7, with setup/temporary records
separately described by the source. No physical peak-RAM measurement.

For S=62, reported candidate expected work is one-time setup plus sum of all
attempt vectors/S plus the explicitly modelled rejection sampler divided by
success probability. Before the run, root additionally froze one restart-wrapper
loop and one caller outcome check per attempt: add73/62 to each of comparisons
and loop_iterations in the RAW source expected vector. Raw source expectations
are retained unchanged with this exclusion explicit. The table includes those
corrections where relevant; these are not new executed diagnostic events.

| Event category | Candidate expected complete solve | Reference complete solve |
| --- | ---: | ---: |
| Group addition calls | 4179/31 | 17 |
| Field inversions | 3707/31 | 15 |
| Field multiplications | 51564/31 | 204 |
| Field additions | 4721/31 | 16 |
| Field subtractions | 17584/31 | 76 |
| Field reductions | 73869/31 | 296 |
| Comparisons, corrected | 236741/62 | 454 |
| Loop events, corrected | 58609/62 | 105 |
| Lattice reduction iterations | 4703/62 | 0 |
| Dictionary reads | 815/62 | 8 |
| Dictionary writes | 745/62 | 7 |
| Answer verifications | 1 | 1 |

Do not add categories into a CPU price: inversion/group calls have their actual
field operations counted separately, and the event model omits Python allocation,
hashing, exact arbitrary-precision bit work and hardware transactions. Candidate
point tuple hashing and reference x-key creation are not calibrated. The reference
has8 point_key_formations whereas the candidate has0 in that specific counter;
there is no claim of dominance in literally every named instrumentation category.
The candidate already loses the group/field arithmetic comparison with score and
most integer costs omitted. It has no smaller dictionary peak in this instance.

## Paper extension: group calls for every admitted nonzero target

This generalizes the specified algorithm's target input for analysis; only the
one frozen target was executed. Keep curve, G, score, T=18 and implementation
fixed. For k in1..72, binary scalar multiplication calls group addition
c(k)=popcount(k)+floor(log2(k)) times. A zero scalar calls it zero times.
The simple upper bound c(k)<=13 suffices; c(70)=9.

For any nonzero Q=kG, uniform r makes Q+rG uniform on the same subgroup. Therefore
the entire point-path, stopping-time, known-hit and first-repeat distributions are
unchanged. Coefficient a_t=2^(-t) means the repeat's zero-denominator status depends
on the time gap, not k or r. Thus success remains62/73. Initial[r]G call count
averages over all r, even though its correlation with success may change. Include
all attempts in E(C)/u, so that correlation does not alter this argument. Setup
and transition call distributions remain fixed. A successful solve performs one
verification with c(k) calls. Consequently

`E[group_calls_candidate(k)] = 4179/31 - 9 + c(k) = 3900/31 + c(k)`.

The signed reference uses6 baby additions,2 stride additions, at most6 giant
updates and one verification. Hence for every such k,

`group_calls_reference(k) <= 14 + c(k) <= 27`.

Since3900/31>14, the candidate has strictly more expected group calls for every
admitted nonzero target, regardless of the reference's early stopping position.
Admission excludes Q=O. If both algorithms add the natural direct-zero shortcut,
that input is a tie; no strict-all-target claim is made for it.

This is a finite implementation-specific group-call result. Group calls include
identity shortcuts and doubling, and do not all have equal physical cost. It
establishes no uniform-target field-operation/runtime bound, no extrapolation
beyond this curve, no lower bound on other halvings/restart policies/timeouts,
and no exclusion of rational-reconstruction steering in general.

## Disposition and next step

Park this frozen direct-halving implementation under the predeclared first-gate
policy; the independent raw-evidence audit passed. No larger run, new seed,
timeout tuning or random-score experiment is funded by this loss. The unbatched
reference can itself be improved by known arithmetic, so beating it would not
have established a new state of the art anyway. Significant reopening requires
a concrete changed mechanism with a paid prediction, not another parameter sweep.

Best supported complexity remains the classical square-root reference with
known automorphism constants and charged tradeoffs. Verified improvement: NONE.
Next conclusion-changing work is independent H005 hybrid proposals and skeptical
review of the recent-result bridge report; no broader Lean machinery is needed
for a losing finite candidate. Commands, all failures and remaining limits are
retained so this negative can guide future selection rather than be hidden.

## Independent recorded-data audit

Native Astra /root/encoding_review ran a metadata-only assertion script, exit0.
All73 records, hashes, phase/category/total reconciliation, sampler/expectation
fractions, complete/partial flags, wrapper correction and comparisons passed.
It found745 total transitions; useful-cycle returns have length5 in42 successful
attempts and length7 in17 attempts. These are outcomes, not59 distinct cycles.
The separate paper group-call argument passed with the nonzero-target caveat.

Root inspected and retained the exact already-run body as
`research/experiments/H005/audit_recorded.py`, SHA256
`546ce644fc09e01e9487f76cf146fe7c56fca5f3ea6238949ef157181f96afef`.
Reproduction from dlp-research: `python3 research/experiments/H005/audit_recorded.py`.
Auditor originally ran `python3 /tmp/h005-recorded-audit.py`, exit0. Root did not
rerun the elliptic-curve experiment or reset any budget. This audit recomputes
only retained metadata and integer count formulas, not elliptic-curve trajectories.

Final repository check:
`./scripts/check.sh > /tmp/ecdlp-h005-results-check.log 2>&1`, exit0. No new Lean
theorem or Audit change. This command did not rerun the H005 experiment; the
source, amended protocol and raw data remain at the audited hashes.
