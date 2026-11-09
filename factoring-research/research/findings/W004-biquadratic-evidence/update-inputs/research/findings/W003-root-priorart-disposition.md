# W003 Lens B — coordinator disposition

2026-10-08. **Accepted with the completions and corrections below, at their
stated scopes.** Verified new complete classical factoring complexity
improvement: **NONE**. The research objective remains active.

The coordinator consumed all 905 lines of the
[independent review](W003-root-priorart-review.md), its source-inspection and
validation records, and the 572-line submission. All 76 initial review
snapshots and all 89 review delivery entries verify. The review SHA-256 is
`6d43e18fffacb8006b787240e0460443f8c3137992791ca18f8e47edc61b5eea`.
The original submission and [submitted snapshot](W003-root-priorart-submitted-draft.md)
remain identical, SHA-256
`2053748929ba399bf4e010fc0133ce12cd60d4c568745a44b06ae7a6c788f275`.
Original reports, intakes, source ledgers and manifests remain unchanged.
This disposition governs their historical provisional labels; it does not
retroactively claim that the original wording contained the repairs.

## Integer construction retained at the older bound

Accept the raw-word root-fiber reduction for odd moduli with at least two
distinct prime divisors after paid elementary cases. Repeated exponents are
allowed. Given a verified inner root independent of the hidden preimage x
conditional on R, the useful probability is exactly 1-2^(1-k). The outer law
includes rejected words, zero, proper nonunits, inner factors and inner roots.
The iid cold cost identity C/p requires p>0 and independence between trials,
not independence between cost and success inside one trial.

Retain the integer twist algorithm with the review's explicit finite parameter
rule and sequential execution schedule. For v=exp(sqrt(2 log N log log N)),
rational enclosures give an integer v<=B<2v without deciding an exact-real
integer boundary or consulting an analytic threshold. Prime enumeration and
small-prime gcds are charged. With h=pi(B), use T=16(h+1)B raw records,
retain full exponents of positive B-smooth residues R^epsilon m^2, and choose
one nonzero dependency using only residues, exponents and their order.

The proof must use the **entire geometric tape**, not just the retained list.
The permutation m -> h_R^epsilon m modulo N, extended by the identity on
out-of-range words, preserves all gcd decisions and makes the entire epsilon
vector independent of the transformed words. Consequently early stopping,
rejections, absence of earlier factors and dependency selection preserve the
fair odd-label bit. The root reconstruction is exact and uses verified units.
Conditioning additionally on m or epsilon would invalidate this argument.

Review section 5 supplies the needed rounding slack in Dixon's smooth-square
estimate. With r=ceil(log N/(2 log v)) and u=exp(log N/(2r)), multiset counting
and the divisor-weighted character partition give

    A >= sqrt(N)*[(3/2)/log N]^r,
    lambda_u >= A^4/(N^2*(log N)^2) >= 1/v

for sufficiently large continuing N. The positive 4r log(3/2) term absorbs
the ceiling error. Thus raw row admission is at least 1/(2B). The full-tape
binomial count, followed by the disjoint early-factor/completed-list events,
gives FACTOR-or-ROOT success greater than 3/8. This is a proved smooth-square
transfer with explicit premises, not an assumption that arbitrary integers
or number-field norms have a convenient smoothness distribution.

The retained matrix/provenance algorithm in review section 6 really has a
sequential cubic schedule, including rewinds, insertion and copying. It gives

    time per cold finite trial <= B^3 poly(log N),
    working space <= B^2 poly(log N).

Small continuing inputs have an explicit positive success tape; no unknown
threshold is an input to the program. The outer split probability is bounded
below by a positive constant for all sufficiently large continuing inputs,
with the finitely many remaining constants handled in the proof. Paid
preprocessing and recursion yield the complete expected upper bound
L_N[1/2,3sqrt(2)] and space L_N[1/2,2sqrt(2)]. These are conservative upper
envelopes, not matching lower bounds, timings or a new improvement over the
published rigorous Lenstra–Pomerance L_N[1/2,1] factorer.

The ROOT-only wrapper is also retained with its explicit composition: an
internally found factor is fully factored using the already defined splitter,
then known-prime roots, Hensel lifting and CRT are charged. It does not call
an unprovided same-modulus root oracle. An unbounded expected routine is not
automatically a finite-tape routine. For the latter, review section 7 caps
each node and prime-root call at n_0^2 attempts, proves o(1) total failure,
and counts all tape and work bounds. Use that explicit variant when a finite
cap is required. No deterministic polynomial-time prime-root claim is made.

## Field statements retained with corrections

1. **Abstract membership and modular recovery are distinct predicates.**
   Exhaustive actual field-square tests decide whether tau lies in the
   finite-list square-class image. Maintain a separate flag for a hit that
   passes the specified localization and unit tests. Full derivative gcd N
   can obstruct that recovery without proving that the abstract target is
   absent. When the required leading-coefficient and derivative images are
   units, the reviewed clearing proof makes every abstract hit recoverable.
   This qualifies original lines 372–380.
2. **Rational norms sometimes distinguish the extension-square bit.**
   For nonsquare alpha and the promise Q in K^* intersect K(sqrt(alpha))^*2,
   let b identify Q=z^2 or Q=alpha z^2. Then
   [Norm(Q)]=b[Norm(alpha)] in Q^*/Q^*2. If Norm(alpha) is nonsquare, it
   distinguishes b; if Norm(alpha) is square, it does not. Replace the
   unconditional loss-of-bit wording at original line 473 by this dichotomy.
   Review section 9's symbolic totally positive example verifies that the
   informative case exists. It gives no N,R-only field selector or yield.
3. **Clamp the small-R count.** Use a nonnegative cutoff U in the submitted
   loose bound, or use review equation R16 for arbitrary real U. On balanced
   distinct semiprimes a fixed L_N[2/3,c] cutoff covers at most N^(-1+o(1))
   of the unit-square law. This is an upper count, not an attained probability
   or a lower bound for every alternative encoding.

Accept the derivative order-multiplier proof, the actual field-square tests
and their conservative variable-width exhaustive-search envelope, with those
predicate distinctions. Review section 8 also gives explicit leading-coefficient
scaling for nonmonic fields and both twisted/untwisted integral radicands.
No maximal-order, inert-prime, discriminant-factorization or full square-class
oracle is granted. The localization never extends to the entire number field.

The norm necessity alpha in Norm(L^*) iff -1 in Norm(L^*), negative-real-place
obstruction, extension-square classification and norm size identity are
retained at their precise domains. Relative norm membership is not finite-list
target attainability. Square rational norm alone is not actual field
squareness without additional hypotheses. Known NFS selection and relation
laws have not transferred to arbitrary R or squared-coefficient row sampling.

## Disposition and next action

The source/reduction gate is complete. It supplies an explicit older-scale
integer construction and corrected algebraic constraints, with no improved
complete factoring bound and no numerical test selected. Primary theorem
comparisons are accepted at the inspected statement/algorithm scopes, not
as a new audit of every cited analytic proof.

The parent norm-certified quadratic law remains under its separate review.
It has Norm(alpha)=t^2, so it lies in the uninformative rational-norm case
of the corrected dichotomy. W004's frozen constructive follow-on proposes
paid distinct-field selection and concrete packet/descent identities; its
mixed-target supply remains the problem to solve. Neither pending work is
accepted by this disposition. See [W003 handles](../tasks-W003.json) and
[W004 brief](../hypotheses/W004.md); preserve their exact evidence and wait
for the corresponding task completions rather than duplicating live work.
