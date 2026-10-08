# H011 concrete fiber operations: candidate-specific cost screen

Proposer: native Astra /root/h006_structured_relation_ideas, completed distinct
operation report after the mathematical screen. Root records three concrete
mechanisms, not three discoveries. Independent native Sol cost review CONFIRMED the scoped calculations, with
qualifications integrated below; all claims here are scoped to the operations and distributions below. No new
experiment or implementation. Verified improvement NONE.

## 1. One-center known-anchor pair query

Build a dictionary K={s_i G} of L distinct numerically known-log points,
INCLUDING O if its column is removed; otherwise add one to the coverage count. For
R=aG+bQ, scan P in K and look up R-P. A hit with b!=0 yields
b*d=s_i+s_j-a and must be verified. Reflection fibers are disjoint pairs with
multiplicity, so cancelling all unknown point columns at one fixed center
leaves only all-known fibers or previously discovered useful equalities. A
point labelled aG+bQ is not numerically known-log when b!=0. O has scalar0,
and the double-center case uses invertibility of2 modulo odd q.

The pair-sum set has size at most L(L+1)/2. A fresh uniform R therefore hits
with probability at most that count/q. A failed literal full scan costs Theta(L)
point/look-up visits. When L² is much below q, failures alone give optimistic
work scale q/L; when L is comparable to sqrt(q), dictionary setup already costs
that much. Paid setup plus scan thus has square-root best-case envelope L+q/L.
This is NOT an established upper bound for every dictionary: duplicates and
rank/yield loss can only worsen it. Early successful return does not erase full
failed scans. Arbitrary caps or adaptive partial scans need a separate ledger.

Alternatively literally enumerate all unordered pairs, paying Theta(L²)
visits, then query the stored sums with uniform targets. Only for this literal
loop is L²+q/L² an optimistic necessary envelope. Distinct sums may number
M much less than L², and structured anchors can generate them without enumerating
all pairs. For an explicitly materialized DISTINCT-sum table, the appropriate
envelope is M+q/M, plus original-anchor setup; it is still square-root at best.
Storage is O(M) keys with one sufficient scalar witness per key, unless the
implementation deliberately retains all pair records. Neither duplicates nor
coverage prove universal L² preprocessing or storage. Factoring a named fiber
or replacing its row by function notation supplies no faster reporter.

## 2. Distinct-center reflection-word queries

Use operations P -> C_i-P with known affine labels C_i=a_i G+b_i Q, starting
from numerical anchors. Maintain vertex label P=A G+B Q. Exact point-key
collisions with different B recover d; equal-B identities are checked and do
not count as useful output. Every edge, coefficient update and lookup is paid;
V retained vertices occupy O(V) records, with all discarded work also charged.

Freeze ALL center coefficient pairs, scalar seeds and the finite word list
independently of the uniform secret d. Conditional on independent random coins,
each useful equality between two distinct resulting labels fixes at most one d.
A list of V labels succeeds for at most binom(V,2) secrets, before normalization
constants such as signs. Thus constant success needs V=Omega(sqrt(q)) explicit
vertices in this operation. Initial anchor records count toward V and setup.
Coordinate-conditioned centers, coefficient choices, word selection or an
implicit intersection algorithm are outside this elementary union bound.

The compact common function from the mathematical finding is constant across
rational inputs for fixed parameters. That blocks its value-only selector, not
all possible uses of the differing fiber partitions. A different useful query
primitive has not been supplied.

## 3. Complete a divisor from e-1 known anchors

Supply an effective rational pole divisor D0 of degree e with affine point sum
C=aG+bQ. Choose e-1 numerical anchors A_i and compute U=C-sum A_i. Then
sum[A_i]+[U]-D0 is principal. For explicitly listed supports, successive
line/vertical-line factors construct a straight-line certificate with O(e)
literal group-law steps; support overlaps and cancellations must be tracked.
This is known divisor-function machinery. Root opened
[Miller, Short Programs for Functions on Curves](https://crypto.stanford.edu/miller/miller.pdf),
whose algorithm constructs short function programs and whose genus-one step is
a line calculation. Exceptional evaluation points of such programs are not
free valid evaluations. Here the selection test only uses the explicit U.

The certificate does not determine log(U): it remains
 a+b*d-sum log(A_i). Search U in a numerical dictionary of size L. If the
anchors, dictionary AND b are fixed before a fresh independent uniform a,
so a is uniform conditional on all three, then U is uniform for every fixed d,
and a trial hits with probability L/q. Paid dictionary setup plus one event per
trial has necessary work scale L+q/L. Membership can be tested BEFORE building
the function certificate; its work is charged when performed, not asserted
unavoidable for failed membership trials. This optimization does not defeat
the dictionary/trial lower envelope. A new a
requires a compatible newly constructed/presented D0; the old fixed divisor is
not silently reused with a different sum. Constructing these divisors is paid.

At fixed b, collisions between residuals cancel d and are tautological. Varying
b permits birthday-type collisions, but the predeclared affine-label union bound
only applies when its independence assumptions hold. Demanding that ALL e zeros
are numerical anchors restores the original tuple-sum search; constructing a
function after finding the tuple merely certifies it.

## Rank and next decision

All three supplied operations reduce to paid pair/dictionary/collision selection
under their frozen rules; none supplies a faster primitive. The higher-degree
shared-fiber idea remains unpriced, not proved impossible: unknown-column
cancellation may leave nonzero known-point degree. Reopening requires an actual
anchored incidence generator with nonzero target coefficient and complete costs.
No generic Lean refinement or function-field engine is justified by these cards.

Root requested a NEW independent native Sol cost review, including the correction
that optimistic envelopes are not runtime upper bounds and ALL affine-word
coefficients must be secret-independent for the elementary union bound. The
initial mathematical review was a separate completed task, not this cost review.
No experiment/edits/children in reviewers. Shared records/commits root-only.

Independent review completion: native Sol checked the pair-coverage/full-miss
scan regime, secret-independent entire word family, explicit rational support
of the compact Miller certificate, and allowed lookup before certification. Root
integrated each qualification. These screens reject the named operations, not
arbitrary reporters or coordinate-conditioned samplers. All numerical logs and
point multiplicities are counted explicitly; affine labels are not secret logs.
Validation: `./scripts/check.sh > /tmp/ecdlp-h011-fiber-check.log 2>&1` passed
exit0 with363 existing audits; only Markdown changed afterward. No new Lean
claim/Audit entry, numerical run or new infrastructure.

Final table-scope correction: independent reviewer distinguished literal pair
enumeration from efficient construction of a structured distinct-sum set. Root
retains M+q/M for the latter and does not infer Theta(L²) visits/storage from
L anchor points alone. No change to the scoped square-root conclusion.

Uniform-shift scope: b is selected before a. Marginal uniformity of a is not
enough if b depends on a (e.g. b=a collapses for d=-1). Residual membership is
a per-target bound under the conditional sampler; reflection-word coverage is
instead an average-over-uniform-secret bound. These quantifiers are distinct.
