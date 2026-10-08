# W019: literature corrections and a composite-ring counterexample

Status: **verified limited negative result**. Native Astra independently reviewed
the disposition and reproduced the finite probes; qualifications below retained.
This record dispositions the preserved Grok report and the Factory Fable audit;
it does not accept either report wholesale. Original reports remain unchanged.
No new ECDLP attack, general Smart implementation, or cryptographic claim.

## Supported finite negative finding

The original prototype's jac_add is **not a general elliptic-curve addition
routine over Z/43²**. On y²=x³+4x+2, take Jacobian coordinates P=(1,1,43)
and Q=(1,1,86). Both satisfy the curve equation and have unit Y. Converting to
ordinary projective coordinates (XZ:Y:Z³) and normalizing Y=1 gives distinct
valid points (43:1:0) and (86:1:0). The discriminant is nonzero modulo43.

The prototype returns (86:1:0) for P+Q and (172:1:0) for Q+P, after the same
unit normalization. Distinct normalized projective coordinates mean distinct
points. Elliptic-curve addition is commutative, so both outputs cannot implement
it. The field-oriented equality branch mistakes two different formal-neighborhood
points for identical inputs and doubles the first. This falsifier does not need
a claim about the exact formal logarithm or the correct value of the sum.

Coordinator artifact: research/artifacts/W019-ring-commutativity-check.py,
SHA256 `7580cc4628a2e8cf352e6b12923c3e43cc2566ae5746ba05c0491baf5bdd7144`.
It imports the unchanged historical prototype and asserts nonsingularity,
both equations, unit normalization and the two exact outputs. Four add/double
counter increments are separate from408 mixed operations in the imported demo.
Output is retained in W019-ring-commutativity-results.json. First execution passed.
Exact command:

```
timeout 60 python3 research/artifacts/W019-ring-commutativity-check.py
```

This counterexample is outside the sampled original smart_dlp multiplication
path. It does not falsify the six correct p43 results or show a wrong returned
secret in those samples. No all-input guarantee for the prototype is established.

## Reproduced lift experiments and their limits

Factory's preserved probe code, independently inspected/run by coordinator,
prints the following finite results using the unchanged prototype primitives:

- Fixed curve lift a=0,b=2 at p61:0/61 changes of the tested G point's x-lift
  recover scalar7. All61 b-coefficient lifts fail all six listed secrets.
- Changing a to61*k: for scalar7, only k=0 fails among0..60. The specific
  a=61,b=2 lift recovers all six tested secrets1,2,3,7,11,30.
- At p43,a=4,b=2, the tested b-lifts fail scalar7 only at k=33.
- Factory's larger E1 example reproduces tP=860,tQ=473 and the incorrect
  addition result1720. The commutativity test above independently avoids
  reliance on its claimed expected formal-log sum1333.

These are sampled finite observations, not a proof of uniqueness of a bad
isomorphism class, of a1/p failure law, or of correctness for all trace-one
curves/lifts/scalars. Changing the curve lift changes this concrete p61 result;
a blanket failure of the trace-one method is unsupported. Higher precision alone
has not been tested or ruled out for every possible variant.

The point-add counter is mixed: it increments in affine operations as well as
Jacobian routines.408 is not408 Jacobian additions. Factory's ring probe prints
228 Jacobian increments for the twelve sampled smart_dlp calls and467 total in
its later reset probe; the lift probe prints10999. Independent AST instrumentation
of the original increment sites finds278 Jacobian-category and130 affine-category
increments, exactly408. Factory's228 omits two ordinary smart_dlp calls (16 each)
and the HPL call (18); its assertion that all remaining increments were affine
is false. These are separate counters
with resets/import demos, not a complete uniform cost model. Thus the report's
'<11k total' wording is not adopted. Wall times are uncalibrated diagnostic text,
not performance evidence. No complete resource comparison follows.

## Literature/model corrections accepted by coordinator

The fixed-power target in Goals.lean is stronger than o(sqrt(q)). The function
sqrt(q)/log(q) separates the two asymptotic criteria. Finite trends prove neither.
An automorphism orbit set is not automatically a quotient group: in Z/5,
1 and4 share a negation class, yet adding1 gives classes2 and0. Ordinary generic-
group bounds cannot be applied to orbit cardinality without a suitable model.
`descriptionBits` needs an actual size bound; it does not itself exclude tables
or parameter/encoding advice. A uniform fixed program is a distinct restriction.

Coordinator inspected the actual retrieved primary text passages, in addition
to Factory's audit. Bernstein–Lange–Schwabe PKC2011 section3 explicitly conditions
its average iteration estimate on heuristics. Its cycle overhead is not a
numerical per-input bound for arbitrary implementations or BSGS. Its stated
curve restriction and asymptotic batching assumptions must accompany field-op
estimates. Primary source: https://www.iacr.org/archive/pkc2011/65710132/65710132.pdf
(local pkc.txt passages165..225 and280..317).

Shoup Theorem1 gives an O(m²/p) success-probability bound under its random-
encoding/random-target generic-oracle model. The report's explicit constant
came from a secondary lecture, not this theorem. No generic-plus-automorphism
lower-bound theorem is proved here. Source: https://www.shoup.net/papers/dlbounds1.ps
(local shoup-collapsed.txt158..178).

Semaev2004 explicitly proposes a conditional relation-generation route over
prime fields; its efficient bounded-root solver is missing from that proposal.
That is not proof of inapplicability or refutation. Small delta0 box tests do
not refute a positive-delta asymptotic. Diem2011 discusses this gap and develops
a separate extension-field result. This is a statement about these papers,
not a current exhaustive novelty survey. Sources: https://eprint.iacr.org/2004/031
(local semaev.txt214..254); https://doi.org/10.1112/S0010437X10005075
(local diem-comp.txt160..198).

## Audit disagreements and source provenance

The local diem.pdf/diem.txt are actually Koike on mean-curvature flow; coordinator
read the title. Only diem-comp.txt is the claimed Diem text. File names are not
source verification. HTML bot challenges retained under PDF names are not papers.
Bulk downloads/extracts are not committed. SafeCurves figures, original nine-
secret BSGS experiment and summation-box counts remain unverified here.

Factory's uniform-coordinate-division example starts from a triple scaled by
nonunit p. Such a triple is not thereby a valid projective representative;
merely satisfying the polynomial equation is insufficient. It shows unreliable
normalization of an invalid triple, not a second valid-point counterexample.
The E1 commutativity counterexample above uses unit Y throughout.

Factory's implication that stripping yields None/zero and therefore cannot
return a wrong result is insufficient: a zero tQ may pass when tP is invertible.
The sampled path had no stripping hits; that observation is not a universal
path-invariant proof or a no-false-positive theorem.

Factory's proposed next experiment is **not accepted**. With m babies0..m-1,
the existing project uses span2m-1. A2m+1 stride needs a different endpoint/table
convention and coverage proof. An asymptotic constant-factor estimate does not
force every input's ratio into[1/sqrt(2)-epsilon,1], and a ratio outside that
interval does not demonstrate a counting error. Independent reviewer calculated
from existing q7 code: ordinary m3 versus signed m2 costs3 versus4 additions
for d2, and5 versus3 for d6. The signed path includes its extra stride-forming
addition; these per-input ratios are legitimate. No new full experiment was run.
W006/W012/W015 already supply
stronger all-scalar signed-baseline evidence and exact coverage; repeating nine-
secret tests would not advance the research.

Factory's misc probe recomputes136 f3 zeros/no discrepancies on rational-x
triples over F17 and the reported tiny orbit indices. Those are local algebra
checks, not a relation finder. Its beta is defined from [lambda]G.x, so the x
coordinate equality is by construction; the nontrivial printed checks are
lambda's polynomial, equal y and beta³=1. It does not test beta!=1 or contain
the reported embedding-degree exponent checks; do not claim those reproduced.

## Reproduction and research process

T3 request `ecdloop-w8-literature-audit-fable-20261008-r1`; complete task ID in
W019-fable-audit-report.md and STATE. Native Astra `/root/encoding_review` is
independently reviewed this report with the parent objections supplied, returned
PASS for the limited counterexamples/disposition, and rejected the broad claims.
The coordinator accepted the counter correction and narrow normalization wording.
No model was asked to endorse its own report as an independent reviewer.

Original Factory probes are archived byte-for-byte in research/artifacts as
W019-fable-probe-{ring,lift,misc}.py. They retain their original absolute temporary
import path and are unmodified evidence. To reproduce from dlp-research:

```
mkdir -p /tmp/w019-audit
cp research/artifacts/W019-smart-original-unverified.py /tmp/w019-audit/proto.py
timeout 60 python3 research/artifacts/W019-fable-probe-ring.py
timeout 60 python3 research/artifacts/W019-fable-probe-lift.py
timeout 60 python3 research/artifacts/W019-fable-probe-misc.py
```

Coordinator ran each after reading its code; all exited0 and numeric outputs
matched the reports, with qualifications above. Output snapshots are retained
in findings/W019-fable-{ring,lift,misc}-results.txt. The probe timings are not
expected to reproduce byte-for-byte. Prototype remains explicitly unverified;
none of these files is integrated into Lean or used as a solver correctness proof.
Next: retain the failed general-ring refinement as a negative result and continue
actual baseline cost verification; no new candidate algorithm is accepted here.

The reviewer retained the AST counter instrumenter unchanged at
research/artifacts/W019-counter-split.py, SHA256
`1bce57fbea4804420aad96a61dd3f191258776acbd33ed552b4e55166c9df36a`.
Coordinator inspected and reran `timeout 60 python3 research/artifacts/W019-counter-split.py`;
output W019-counter-split-results.txt reproduces130/278/408. Instrumentation
adds category counters at the original increment sites, leaving mathematical
operations and inputs unchanged; this is classification of an existing counter,
not a complete cost semantics. No original prototype code was repaired.
