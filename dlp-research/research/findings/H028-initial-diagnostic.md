# H028 first frozen diagnostic: correct finite behavior, no work gain

2026-10-08. The single preregistered run COMPLETED with exit0, no cap/error.
This is synthetic correctness and finite accounting evidence, not a benchmark
or whole-solver speedup. Independent saved-artifact audit by native Sol passed.

## Reproduction, provenance and review

Executed ONCE from dlp-research:

    timeout --signal=TERM --kill-after=2s 60s python3 -B research/experiments/H028/key_probe.py --execute > research/experiments/H028/initial_results.json

No warmup, tuning, continuation or rerun. Unified exec session49497 completed0.
Global guard10M events/55seconds internal,60seconds external.
Observed3,351,990 modular-RAM events, with phase and category sums identical.
Reported pre-JSON elapsed~0.999seconds is only this diagnostic's local elapsed
time, NOT EC throughput, candidate solver timing or hardware calibration.

SHA256:
- source: a4823976f4071d0a9ea9d66b804dcca8d3e67f09e19dc5b8c841c5aad7e3d452
- frozen protocol: 80ac3028caacf43227a90e9503dcf065beca99d94077c6b171d9d7412ae01a04
- H018 support: 0865eac9be57655ec1ddde3d76f2aba79bff91ea5384110a7d2205041a764da7
- result: ad1be2e8b2a444b21c9da8e4c7335123cb756a72001cd6bf055c5a707fd2e8e0
Result size3,561,077bytes. Source hash unchanged after execution.

Native Astra implemented only key_probe.py. Root inspected coefficient,
polynomial and grid source, parsed syntax with ast.parse (no import/execution),
and identified dataflow/accounting corrections before the first run. NEW Sol
partial and final source reviews checked the handed-off hash and explicitly
approved ONE frozen run. Fixes before execution included actual candidate
infinity/cache data, shared center inversion, slope-numerator convention,
snapshot-array charges, partial allocation attachment, effective cap text,
actual forced dispatch/sign paths and per-case ledgers.

Accepted partial-output caveat: pending=None alone does not prove a block
finished; inspect its completed flag, retained slots/records and overall status.
No partial result was promoted here: all fixtures/cases completed.
Support import is controlled and side-effect-free; import errors precede the
main diagnostic handler. No such error occurred.

## Exact finite results

All8,500 group elements were enumerated, including8,496 nonidentity points.
Every stored point/transition, fixed addition-law checks, coefficient comparison,
signed-fibre identity and discriminant sum passed. Independent full rational
polynomial Miller constructions on the FIRST TWO fixtures agreed with the
binary coefficient method and had the required pole orders. Other fixtures
did not run polynomial expansion.

| q | M2 | S2 | c0 | exact rho=S2/(2(q-1)) | sum chi(Delta) |
|---:|---:|---:|---:|---:|---:|
|73|148|296|0|296/144|4|
|103|186|372|0|372/204|-18|
|271|542|1084|0|1084/540|2|
|8053|16004|32008|0|32008/16104|-100|

These values satisfy the already independently proved rho<=3. They do not
establish an asymptotic distribution or a typical rho~2 claim.

All12 fixed seed cases7,19,43 across four curves recovered the reference scalar17
after their specified blinding, with full-range coverage code. The candidate
does not read17 or the diagnostic orbit table. Fixed seeds are correctness
cases, not iid performance trials or exhaustive scalar recovery tests.

Aggregate complete-grid data:660records,251regular side pairs,13exceptional
pairs,51raw matches=24false+27genuine,73cached side reconstructions.
At q8053 the three false-match counts were3,1,0 and R was5,5,1.
The complete-grid diagnostic continues after first success; these are not
first-hit work measurements. Independent audit checked complete raw-pair sets,
all515 finite side descriptors, immutable archives and24 setup-Miller traces
(216steps), in addition to396 fixture binary trace steps.

Actual infinity-before-lookup and nonzero-h orientation paths were forced and
checked. HOWEVER c0=0 on ALL four fixtures: the nonidentity zero-key two-sign
path did NOT execute. Absence was explicitly reported; no point was fabricated.
That exception remains an executable coverage gap despite its source/proof review.

## Finite work screen: initialization already consumes the saving

The literal candidate performs two additional binary Miller setups per seed
case. Their non-inversion multiplication counts alone are54,62,78,130 at the
four sizes. Maximum regular-generation squarings saved in those cases are
14,14,30,110 respectively (one q103 case saves12). Thus, in any field weighting
with0<=S/M<=1 and nonnegative other costs, this candidate-specific setup alone
exceeds the ENTIRE available regular squaring credit. No false-refinement
upper bound was incorrectly used as a necessary rejection bound.

The recorded optimistic S/M=4/5,I/M=8,A/M=0 projection confirms it:

| q | extra Miller setup (units M) | regular squaring credit (units M) |
|---:|---:|---:|
|73|1014/5|56/5|
|103|1230/5|48/5 or56/5|
|271|1502/5|120/5|
|8053|2586/5|440/5|

This rejects arithmetic headroom for the tested literal finite configurations,
even before added reconstruction, canonicalization and table work. It does NOT
reject larger sizes, cheaper correctly charged setup, the archive-free variant,
or the proved collision bound. Setup is polylogarithmic while the hypothesized
generation saving scales with generated points. There was no executable matched
x-baseline run and therefore no measured end-to-end comparative timing.

## Independent result audit and disposition

NEW Sol artifact audit parsed saved output only; it did NOT rerun/import the
probe or collect new challenge observations. It reconciled hashes, counters,
stored curve transitions, coefficient traces and polynomial extractions,
all fibre/discriminant identities, record/match/cache sets, setup costs and
coverage limitations. Root independently checked the same hashes/aggregates and
all12 projected setup-versus-credit inequalities. Post-hoc analysis is separate
from the preregistered candidate/diagnostic event ledger.

./scripts/check.sh > /tmp/ecdlp-h028-source-check.log 2>&1 passed366 existing
audits before the numerical run; source unchanged. No Lean/Audit theorem was
added for H028. The general collision proof remains independently reviewed
paper mathematics, not a machine-checked EC refinement.

Best supported complete ECDLP reference remains square-root; VERIFIED COMPLETE
WORK IMPROVEMENT NONE. Next useful work is a sharply scoped matched full-solver
cost experiment or analysis at sizes where setup no longer trivially dominates,
with competent x baseline, real record/metadata/memory costs and explicit
applicability. Do not relabel this finite correctness pass or saved output-square
count as a breakthrough, hardware throughput, or practical full-size attack.
