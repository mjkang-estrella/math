# Preliminary review integration and current scope

The independent pi-detemple-preliminary-review report and provenance have been
read in full and copied into reviews/preliminary. Its final thread message was
read at position128. SOURCE/MATH/ELIGIBILITY pass as a preliminary candidate;
the bounded screen found no prior resolution. These are not a final formal or
manuscript review and do not change credit0 or the accepted24/30 tally.

## M1: actual checker defect corrected, originals preserved

The original check_certificate.py symbolically checks the second derivative of
24(x^4+a*x^2)(h-log x)-x^2+7/40-a. That expression agrees with sourceG only when
a=155/294. It omits c=7a/40-31/336 for general a. This was an avoidable checker
error; its old unrestricted symbolic-identity description is superseded here.

The current check is check_certificate_corrected.py, with its own output
corrected-certificate.json. It uses the full Q=x^4+a*x^2+c in BOTH the source
function and the h'' coefficient, and includes +c/x^2 in the expanded logarithm
contribution. SymPy proves its identity for arbitrary positive a,x. The original
checker and certificate are retained unchanged for review-byte provenance;
they are historical records, not the current general-a identity check.

The load-bearing rational product-rule certificate already used the full P, P',
P'', and its exact lower bound remains510221/1093750. Both the original numerical
check and the corrected one evaluate the full sourceG. The actual Lean proof
uses full sourceG for every parameter, cancels c ONLY at155/294 by exact rational
arithmetic, then transfers midpoint failure by parameter continuity. It never
imports the Python identity or assumes a derivative formula for general a.
Its21-declaration/3-module strict replay receipt is unchanged. Therefore no
mathematical, formal, or manuscript correction is required for M1.

## M2 and scope

The cubic-reciprocal sum estimate means sum_(n>=1) f(n)<=integral_0^infinity f(t)dt,
then add f(0)=8, giving10. All relevant coefficients and sign directions in the
explicit rational bound are correct.

For each fixed a<155/294 the unnormalized difference need not diverge positively
as x->0: its constant-log part tends24c log(4/3)<0. No all-a failure or persistence
as x->0 at a fixed interior a is claimed. The formal endpoint gives existence
of positive a STRICTLY below155/294, after fixing a boundary witness first.

The preliminary report's statement that there is no Lean endpoint concerns its
original25-file freeze only. FORMAL-ADDENDUM and the new final-review freeze
cover the completed literal21/3 endpoint and2-page draft. The specific rational
pair527/1000,1/50 remains a mathematical certificate, not a Lean endpoint.

## Novelty limits retained

All14 indexed citing works were screened, but only6 had primary bodies read by
the preliminary reviewer;8 were checked at title/abstract level. No absence of
the fraction155/294 in text, empty MathDB field, citation count, or registry search
certifies novelty. Final review should test the remaining closest bodies and
update the live source record where feasible. No worldwide-priority claim,
part(i) result, or exact replacement threshold is made.

Before any credit: NEW independent five-gate review of the current full files,
deterministic packet assembly, and a fresh extracted strict replay are required.
