# H030 — Coordinator intake of the exact-block construction

2026-10-08. **Submission consumed; independent review required.**
Verified complete factoring complexity improvement: **NONE**.

The constructive task factoring-h030-root-product-blocks-r1 is completed,
with no pending child runs. The coordinator read all 482 report lines and its
source notes, and verified all 12 frozen-input plus 21 delivery manifest entries.
The submitted report has SHA-256
f66360ee379188f50b83fb1f11fff43536aa3c2beb18c6a05118d4986b864581.
An identical H030-submitted-draft.md preserves the original before any later edits.
Artifact identities establish provenance, not mathematical correctness.

## Proposed result and scope

The selected exact Newton-cubic constructor specifies every outer/inner rounded
root using sufficient rational Bernstein certificates and bisection to explicit
short blocks. Its product routine clears denominator 6 by residue classes,
then uses ordinary monic product/remainder trees over every composite modulus.
Partial intervals, failed certification and the retained-record scan are charged.
The proposed complete bound remains M^(1/3)*poly(log M).

The claimed decisive obstruction uses J=[ceil(3M^(1/3)/4),floor(M^(1/3))].
For c(k)=ceil(2sqrt(Mk)), its integer second differences on J lie in
{-2,-1,0,1}. If a rational degree-D polynomial equals c on L consecutive
positions there, the submitted lemma gives L<=max(8,4D-6).
For D=3, covering J consequently requires Omega(M^(1/3)) explicit records.
A further argument with e listed exceptional positions gives L<=4D+9e+8,
and therefore an aggregate Omega(M^(1/3)) coefficient/exception count for
the specified dense representations.

The coordinator checked the proposed proof structure: root counts for a
nonconstant second-difference polynomial, curvature for a constant one, and
at most three affected consecutive triples per exception. These are provisional
checks, not acceptance or independent review. In particular, no conclusion
extends to implicit floors, sparse high-degree circuits, nonconsecutive blocks,
modular-only identities, implicit exceptions, RootProduct generally or factoring.
The report proposes no next experiment or new constructive primitive.

## Independent review obligations

Audit the exact certificate, all equality and short-block cases, denominator
clearing, composite-ring multiplication/remainders, arbitrary partial intervals,
full setup/query/space costs and sequential access. Re-derive the derivative
bounds, second-difference set, constant/nonconstant cases, low degrees, endpoints
of J, exception counting and the precise representation cost consequence.
Separate a valid upper bound from the proposed mandatory output lower bound.
Do not assume the polynomial equals the rounded sequence merely because it
approximates the underlying real root. Confirm the actual dense-output premise.

Check primary attribution for ordinary product trees and the existing Lehman
square-root-speedup question, with exact reading scope. Preserve the already
accepted H029/H004 reduction as a dependency; do not widen its interface or
introduce a factor/order oracle. All new deductions remain unaccepted pending
the review. No finite experiment, code change, Lean proof or larger sweep is
selected. H031 continues its separate constructive task.
