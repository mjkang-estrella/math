# H031 literal cubic stream: exception-bound followup

Status: root paper derivation; independent native Sol checked the exception
counts, truncation and literal-formula scope. Final verdict: ACCEPTED for the
single literal P-only stream, with the qualifications below.
No experiment, source modification or Lean claim. This follows the limited
regular-operation screen in H031-coverage-screens.md, not a new representation
proposal. Its purpose is to close that screen's exceptional-step loophole.

## Fixed implementation and scope

Short Weierstrass curve over Fp with p>3, prime subgroup order q>3, Q=kG,
one stream with consecutive distinct indices
modulo q. Emit/inspect only P_i=iQ+i^3G, retaining D_i,E_i as working registers.
The old-value recurrence is P'=P+D, D'=D+E, E'=E+F, with
D_i=(k+3i^2+3i+1)G, E_i=(6i+6)G, F=6G.
Use the literal full-affine formulas from the initial card. Additional keys
from D,E, shifted/multiple streams, altered formulas or arbitrary repeated
restarts require different counting/cost analysis. This is not a theorem about
all cubic methods or all-memory-regime solvers.

## Counting exceptional addition-events

For distinct input indices in Fq, a nonzero polynomial of degree d has at most
d roots. The following are union bounds, so overlaps only improve the bounds.

- P+D: P=O has at most3 roots of i^3+ki; D=O at most2; P=+D or-D
  has at most3 roots each (leading coefficient1). At most11 exceptional events.
- D+E: D=O at most2, E=O at most1, D=+E or-E at most2 each
  (leading coefficient3!=0). At most7 exceptional events.
- E+F: E=O at most1; F!=O; E=+F or-F at most1 each
  (leading coefficient6!=0). At most3 exceptional events.

These events include infinities, tangent doubling and inverse-pair addition.
Thus at most21 addition-events among the three updates over ANY set of distinct
indices can be exceptional. At least3t-21 are regular during t emission updates.
The possible O(1) mismatch between number of updates and inspected outputs
only changes a constant. The initial identity/tangent cases are included.

## Arithmetic consequence to review

The literal regular affine formula executes2M+S outside inversion: one slope
product, one square, one ordinate product. Give all inversions, their batching,
exception dispatch, storage and setup away for a favorable lower bound.
Then t updates cost at least(3t-21)(2M+S); a negative right side is harmless.
For uniform full-range k, signed pair relations and direct infinity recover
at most t^2 scalar candidates among t inspected P keys. Identically true
equations supply no recovery. No extra guessing/verification queries are
granted. Let T be the number of inspected keys until valid recovery and
L=floor(sqrt(q)), and run until recovery or L inspected keys. An abandoned
unsuccessful shorter prefix does not inherit this work bound. Then E[min(T,L)] is the sum for t=0,...,L-1 of
Pr(T>t), which is at least sum(1-t^2/q)=(2/3)sqrt(q)-O(1).
This truncation uses fewer than q indices and needs no assumption of eventual
recovery or no wrap over an infinite run. Update/output offsets cost O(1).
The leading arithmetic coefficient is therefore at least
(2/3)(6+3s), s=S/M, versus H019's high-memory(2sqrt(2)/3)(2.5+s).
For0<=s<=1, the candidate difference after cancelling2/3 is
6+3s-sqrt(2)(2.5+s)>0: both its constant and slope are positive.

This closes the exception objection for the stated literal stream while even
ignoring inversion work. It remains an arithmetic comparison with square-root
memory, not complete wall time, hardware calibration or general impossibility.
No next experiment follows from a losing literal recurrence. A genuinely new
cheaper multi-output mechanism would need its own separately reviewed contract.

## Review record

Root requested native Sol `/root/h010_early_dependencies` to check polynomial
counts, update/output indexing, inspection of auxiliary keys, fixed-label
conditioning and the truncated stopping argument. No runs/imports/edits/children.
Independent review confirmed counts11/7/3. Explicit D-E and D+E polynomials
are k+3i^2-3i-5 and k+3i^2+9i+7. The E exceptional indices are-1,0,-2.
The reviewer confirmed truncation resolves later wrap/nontermination and
required the literal-standard-formula operation charge and P-only inspected
keys. Fixed extra branch recovery tests would add O(t) to the coverage count,
preserving the leading bound, but are not granted in the exact t^2 statement.
A free Q=O input dispatch adds one constant candidate, also leaving the leading
bound unchanged.
These qualifications are incorporated. No universal optimized-formula lower
bound or complete wall-time rejection is asserted.

Validation: `./scripts/check.sh > /tmp/ecdlp-h031-exception-check.log 2>&1`
passed exit0,366 existing audits. No new Lean theorem/Audit entry; the new
exception argument is independently checked paper mathematics only.
