# H046 information fallback: literal batching and a dense scalar sieve

2026-10-09 UTC. Native Sol /root/h034_c4_implementation is the explicit
replacement for Factory Fable's failed public-information task, which returned
only 'Internal error: Agent error'. These are Sol's constructions, not Fable
results. Native Astra independent review completed; root checked
componentwise semantics and scalar polynomial identities.
Current ECDLP exponent1/2; verified complete-work improvement NONE.
No experiment, benchmark, new Lean claim or novelty claim.

## Direct-product batching is a particular implementation

For M shifts d_i, let Q_i=Q+d_iG. Apply the H046 half-orbit evaluator in the
product algebra R=F_p^M componentwise. It shares control flow and product-tree
topology; the target-independent A(G) can also be reused. This exactly
describes M ordinary evaluations, after dispatching any Q_i=O.

In this representation a ring addition/multiplication entails M coordinate
field additions/multiplications. The point sources, polynomial coefficients,
giant-centre evaluations, inversions and final products all remain paid for
each component. R has zero divisors: a nonzero vector is not necessarily a
unit. Exceptional point operations or zero denominators must be dispatched
componentwise, rather than inverted as if R were a field. Fixed exceptional
blocks can be evaluated directly as in the single-query construction.
Monic remainder-tree evaluation is valid over R; unrestricted interpolation
or division by an arbitrary nonzero ring element is not imported.
Consecutive query-point construction takes O(M) paid group operations; arbitrary
shifts may instead use separate paid scalar multiplications. Neither is free.

The literal invoice is soft-O(M*sqrt(q)) coordinate-field work and simultaneous
storage in field elements, with the one-time A(G) cost charged. Serializing
evaluations reduces peak storage to soft-O(sqrt(q)) but does not share their
target-dependent arithmetic. The explicit circuit performs M copies of its
coordinate arithmetic; a vector instruction is not free total work.

This is not a lower bound for all batch algorithms, alternative representations,
packed arithmetic, or hardware elapsed time. No concrete non-componentwise
shared evaluator with a competitive complete recovery invoice was supplied.
Shared software control alone is not that missing construction.

## Exact scalar-polynomial sieve

Suppose PAID queries return e_i=chi_q(k+d_i), where q is the prime SCALAR
order. If e_i=0, k=−d_i is known and is verified against Q. Otherwise e_i=±1.
Translate the sign semantically from the coordinate-field output ±1 to the
scalar-field elements ±1; there is no assumed field embedding F_p into F_q.
Put h=(q−1)/2 and define over F_q, not coordinate field F_p,

    F_i(Z)=(Z+d_i)^h−e_i.

For every scalar z, Euler's criterion shows F_i(z)=0 exactly when
chi_q(z+d_i)=e_i. Hence the roots of gcd_i F_i are precisely the scalars
consistent with all queried bits. They include the true k, but uniqueness
does not follow merely from the number of queries. Candidate extraction and
point verification are still paid.

Each nonzero-output polynomial splits over F_q into h distinct roots:
its derivative is h*(Z+d_i)^(h−1), nonzero at every root. Thus the gcd has
no extraneous extension-field roots or repeated-root complication in this
stated e_i=±1 case. This is an exact predicate, not an efficient decoder claim.

For a nonzero shift d, expand

    (Z+d)^h = sum_{j=0}^h binomial(h,j)*d^(h−j)*Z^j.

All h+1 coefficients are nonzero in F_q, because 0<=j<=h<q and d!=0.
Subtracting e can cancel the constant, leaving at least h nonzero coefficients.
Therefore the NAMED dense materialization strategy already writes Theta(q)
field coefficients for even one such shifted polynomial. Its query generation,
dense construction, gcd, extraction, storage and final verification are separate
costs. The unshifted case d=0 is sparse and does not establish a similar
materialization bound by itself.

The dense-input cost rules out an exponent improvement from this literal
strategy on growing q. It is not a complexity lower bound for succinct
polynomials, modular composition, implicit gcd, different predicates or other
recovery algorithms. A source of exact character bits alone does not make this
dense sieve fast.

## Decision

These two explicit strategies do not provide a competitive full solver.
The positive content is their exact semantics; the negative evidence concerns
their stated representations and operation schedules. The algebraic arguments
above are elementary derivations, not attributed discoveries. The fast
polynomial ingredients of the underlying evaluator are sourced in
H046-half-orbit-evaluator.md; no new backend runtime theorem is asserted here.
Sol also read [Bostan–Gaudry–Schost, Sections2.1–2.2](https://specfun.inria.fr/bostan/publications/BoGaSc07.pdf)
for the distinction between base-ring and effective-ring costs. Its selected-term
recurrence results do not automatically share target-dependent elliptic products.

Next decisive evidence: a specified non-componentwise shared query algorithm or
an implicit candidate-recovery operation, together with all paid queries,
preprocessing, bit/field costs, peak memory and success/verification terms.
No such operator was constructed in this bounded pass. No synthetic experiment
or general formal infrastructure is admitted on the strength of these screens.
