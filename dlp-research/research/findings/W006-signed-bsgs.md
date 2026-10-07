# W006: signed-block BSGS constant-factor candidate

Date: 2026-10-07. Status: finite experiment and arithmetic support independently
reviewed and accepted within their stated scope. No accepted calibrated speedup,
complete Lean signed-algorithm proof, or tape result.

## Hypothesis and known prior work

Can using negation pairs reduce dominant BSGS additions on the fixed W004
synthetic cases after charging construction, sign handling and canonical keys?
This is a known constant-factor opportunity, not a novel attack or an exponent
change. Falsifiers: any failed scalar, canonical alias/sign error, uncharged
construction that reverses comparison, or no useful saving under a justified
later cost calibration. The last criterion is not resolved by API counters.

Primary source retrieved: Galbraith, Wang and Zhang, [Computing elliptic curve
discrete logarithms with improved baby-step giant-step algorithm](https://www.aimsciences.org/article/doi/10.3934/amc.2017038?viewType=HTML),
Advances in Mathematics of Communications 11(3), 453–469 (2017), DOI
10.3934/amc.2017038. The journal abstract and Table 3 distinguish known
negation-based constants, average versus worst cases, and heuristic/conjectural
entries. They do not certify this implementation or a hardware result. The
ePrint PDF `https://eprint.iacr.org/2015/605.pdf` returned403 to coordinator; the
journal full-HTML link reached a login page. No claim of reading the full paper.

## Implemented protocol

Store jG for 0<=j<m, canonicalizing affine y to min(y,p-y) with an infinity tag
through W004's point-key function. Store the signed j identifying that canonical
representative. Require 1<=m<=q and 2(m-1)<q to exclude distinct signed baby
indices that alias modulo q. A canonical target residual also returns a sign.
On key match, combine signs and return (i*(2m-1)+signedDigit)%q.

Build the table by m additions, obtaining mG and remembering (m-1)G. One extra
addition forms (2m-1)G; one negation forms the giant stride. Start with Q, then
add that negated stride between queries (subtract the positive (2m-1)G).
Number of queries allowed:
ceil((q+m-1)/(2m-1)). The intended interval coverage is
[-(m-1), (B-1)*(2m-1)+(m-1)], containing [0,q-1]. This coverage argument and
sign recovery passed independent review. Sol's alternative proposal shifts
centers by m-1 and must charge the offset; it is not the implementation here.

Compare ordinary sorted BSGS at m=ceil(sqrt(q)), signed BSGS at the same m,
and signed BSGS at m=ceil(sqrt(q/2)). These m values depend only on public q,
not the target secret. Build and sort anew for every target. All 365 scalars on
the five W004 coordinate curves are tested; no interval restriction or sampling.

## Observations

Command: `timeout 60 python3 scripts/signed_bsgs_experiment.py` redirected to
`/tmp/signed-bsgs-provisional.json` for inspection. First run passed all scalars
in all three variants, with 100988 instrumented events. No failed tests so far.
Counter units: group-add API calls, lookup comparisons (equality and ordering
aggregated), sort comparisons, negation API calls, canonical y-order tests.

At q=199 the ordinary maximum additions were28 versus signed same-m22 and
signed smaller-table21. Smaller-table signed maxima also include21 negations,
20 canonical order tests,77 lookup tests and21 sort tests, versus ordinary
1 negation,0 canonical tests,111 lookup tests and44 sort tests. These per-field
maxima need not occur at one scalar and must not be added to report a measured
worst-case total. The smallest q=7 case has5 maximum additions in all variants;
it remains part of the dataset. Counter totals over all secrets are also emitted.

Counters do NOT include field-operation internals, tuple comparison internals,
key construction, index accesses, allocations, register operations or peak byte
memory. An event sum is a workload guard, not a calibrated runtime estimate.
Storage is m entries plus merge-sort temporaries. The prior W004 ordinary engine
is reused with the same sorting/lookup semantics; newly counted negations are
explicit. No claim this experiment implements the proposed W005 RAM ledger.

## Independent work and remaining steps

Read-only Opus design/cost reviewer launched BEFORE code was implemented:
request `ecdloop-w3-negation-design-opus-20261007-r1`; task ID
`node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-w3-negation-design-opus-20261007-r1`.
It is reviewing the mathematical protocol and literature applicability, not
yet the later Python source. A separate code/cost review is required before
accepting the experiment. No positive empirical ratio will be called a new
asymptotic algorithm, or practical recovery feasibility.

## Arithmetic support and conditional cost interpretation

Coordinator added `Research/SignedCoverage.lean`. `covers` proves for all
q>0,m>0,d<q that some i<blocks(q,m), j<m satisfy d=i*(2m-1)+j or
d+j=i*(2m-1). Here blocks=(q-1+(m-1))/(2m-1)+1, equal to the script's formula
under these positive hypotheses. `no_nonzero_signed_alias` proves that a,b<m
with (a+b)%q=0 and 2*(m-1)<q forces a=b=0. Neither proves coordinate canonical
key correctness, the Python algorithm, or a cost bound.

`timeout 60 ./scripts/lake.sh env lean Research/SignedCoverage.lean` initially
failed on a Nat division-lemma argument name and inconsistent unfolding of a
modulo term in omega. Giving the quotient inequality its explicit expected type
and keeping modulo expressions consistently folded fixed both. Full
`./scripts/check.sh` subsequently passed 72 audits/29 build jobs; 14 screened
files includes the separate in-progress OrbitArithmetic module, not yet part
of these audited claims. Only allowed logical dependencies were reported.

Durable experiment command:
`timeout 60 python3 scripts/signed_bsgs_experiment.py > research/findings/W006-signed-results.json`.
It passed after adding explicit prime/discriminant validation for the fixed
curve constants; event count remained100988. Thus the data do not depend on
an unarchived temporary file.

For illustration WITHOUT assigning hardware weights, summing each event class
over every q=199 scalar gives signed-smaller minus ordinary differences:
-1073 additions, -3478 lookup tests, -4577 sorting tests, +2925 negations and
+2925 canonical y tests. Under a hypothetical linear ledger with fixed costs
A,L,S,N,C for these classes, the signed total is smaller iff
1073*A+3478*L+4577*S > 2925*(N+C). This is an inference from the measured vectors,
not a calibrated performance result. It applies to sums over all targets (or
uniform-secret means in this finite set), not worst-case summed maxima.
Uncounted operations could change the comparison.


## Completed independent implementation review

Native Astra `/root/encoding_review`: qualified PASS, no code/proof blockers.
Standalone OrbitArithmetic/SignedCoverage compile commands and the signed
experiment passed. Regenerated JSON exactly matched the archived100988 events,
and the q=199 difference vector matched. Reviewer checked sign combination,
modular recovery, stride construction, preprocessing pertarget and no secret
access. It requested the stride wording correction (now says ADD negated stride).

Supplementary unarchived cyclic-group tests were reported: orders1..30, all
admissible m,4840 scalar cases,203176 events,285 expected guard rejections,
zero failed tests; independent add/neg call counters matched instrumentation.
They cover control flow/even orders/self-negation, not EC arithmetic proofs.

## Completed independent design review and resolved disagreements

Opus task `ecdloop-w3-negation-design-opus-20261007-r1` completed with no
mathematical blocker and a known constant-factor interpretation. Its literature
review reports retrieving an archived copy of ePrint2015/605 and distinguishes
average-tuned paper constants from worst-case tuning, and from combined-addition/
shared-inversion variants NOT implemented here. Coordinator has not independently
retrieved that full archived paper; its own source evidence is the journal
abstract/table recorded above. No block-computation constants are used.

Opus proposed reducing the loop cap to ceil(q/(2m-1)) by modular coverage,
and a closed-form first-hit index, retaining m+1 setup additions. The present
larger cap is safe and does not make valid-target runs perform those extra
iterations. Native Astra independently reviewed these boundary statements:

- The tighter B=ceil(q/(2m-1)) is correct and minimal under the strict-span
  restriction. First hit is i=0 for d<=m-1 or d>=q-m+1, otherwise
  floor((d+m-1)/(2m-1)); the worst is B-1. These are reviewed derivations,
  not additional Lean theorems or changes to the archived experiment.
- Opus's 'one extra block' overstates rounding: the old bound is equal OR one
  larger. At q=7,m=3 both are 2; at q=3,m=2 they are 2 and 1.
- Strict span 2(m-1)<q is sufficient, not necessary for distinct canonical keys.
  At q=2,m=2, identity and the self-inverse point have distinct keys despite
  2(m-1)=q. Retaining the stronger restriction is sound.
- Storing the actual baby point is unnecessary here: the canonical point plus
  signed index suffices. Opus reviewed an earlier design, not the later source.
- m=ceil(sqrt(q/2)) remains a public-parameter tuning rule. No exact optimality
  theorem is established here. Astra found no counterexample through q=300 to
  its minimizing the narrow equal-addition objective m+ceil(q/(2m-1)); neither
  that observation nor this tuning proves optimality for arbitrary cost weights.
- An alternative m+1 setup counts doubling as one addition and assumes the
  public generator is available. It gives no field-operation cost result.

Astra reported a supplementary, unarchived arithmetic sweep of q=1..300,
all strict-span widths and all scalars: 4,533,775 cases, no failures. It is
independent reviewer evidence, not a coordinator-reproduced artifact, a Lean
proof, or a measurement of tape transitions. The durable five-curve dataset is
unchanged. Future source changes require another implementation review.
