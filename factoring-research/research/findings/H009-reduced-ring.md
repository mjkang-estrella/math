# H009: reduced-ring batching retains dense intermediate work

Verified factoring complexity improvement: **NONE**. The finite sparse-collapse
hope is rejected on the preregistered sample. The characteristic-zero argument
below is a parent derivation awaiting independent review; it does not establish
a universal finite-ring or factoring lower bound.

## What was tested

The [protocol](../hypotheses/H009.md) audits W001-dynamics Card 4's existing
implementation: compute division polynomials for E_a: y²=x³+a*x+1 at (0,1)
in the quotient ring modulo A(T)=product(T-a_i), reducing each product.
The scalar index is 2^j, j=1,...,64. The test concerns a concrete recurrence,
not a new ECM algorithm or a smoothness experiment.

All 12 registered configurations completed: four moduli, two each at 32 and
48 bits, crossed with batch sizes 8,16,32. No generation shortfall, timeout,
error or unstarted configuration occurred. No sampled discriminant exposed a
nontrivial gcd. Each of the 684 stages with j>=8 had at least 90% nonzero
coefficients, meeting the registered 90%-of-stages rejection criterion.

All 768 stage polynomials agreed at every sampled parameter with the scalar
recurrence. The first four stages additionally agreed with unreduced exact
integer-polynomial computation followed by reduction. These checks validate
quotient arithmetic; the scalar reference shares the mathematical recurrence
and is not an independent proof of its elliptic-curve interpretation.

Every configuration performed 2,372 polynomial multiplications. At batch sizes
8,16,32 the summed input degree-slot volumes were respectively 37,732; 75,051;
148,965. These totals were the same for all four sampled moduli. The diagnostic
completed in about 2.57 seconds including generation and validation up to the
recorded timing sample. Final serialization occurs afterward and was covered
by the external 60-second cap. It used schoolbook polynomial arithmetic;
this is not a timing comparison against optimized ECM.

[Source](../experiments/H009/reduced_ring.py) and
[complete results](../experiments/H009/result.json) retain every N, curve
parameter, stage, counter and validation outcome. Source SHA-256:
`5aa885b9cbdc4dbcf4579bf08bf718eb89572ba997e491e85484ede75f59b97b`.
Protocol SHA-256:
`ec6e5ec96b2406b0f162715900a8e2460dd5d8c795f81e66eb816e7c6555a89d`.

## A restricted generic-density lemma

Let F be a polynomial over a characteristic-zero field, of degree D>=r and
leading coefficient c_D nonzero. Write the remainder modulo a generic monic
degree-r polynomial in the ordinary coefficient basis. Every one of its r
coefficients is a nonzero polynomial in the modulus coefficients.

To prove this, specialize the modulus to (X-u)^r with indeterminate u.
The remainder is the truncated Taylor expansion

    sum(k=0,...,r-1) F^(k)(u)/k! * (X-u)^k.

For i=0,...,r-1, its X^i coefficient has leading u term

    c_D * binom(D,i) * (-1)^(r-1-i)
        * binom(D-i-1,r-1-i) * u^(D-i).

Indeed, expand the Taylor terms and use

    sum(l=0,...,r-1-i) (-1)^l binom(D-i,l)
      = (-1)^(r-1-i) binom(D-i-1,r-1-i).

All displayed factors are nonzero in characteristic zero because D>=r.
Lower terms of F have strictly smaller u degree and cannot cancel this one.
Thus the coefficient cannot have been identically zero before specialization.
For any finite list of such F, the simultaneous nonvanishing conditions define
a nonempty algebraic open set. Although the proving specialization has repeated
roots, it does not restrict the conclusion to repeated-root moduli: the product
with the nonzero discriminant polynomial remains nonzero. Substituting generic
distinct parameters into product(X-a_i) gives the same generic conclusion.

For the stated division polynomials, degree F_k is (k²-1)/4 for odd k and
k²/4-1 for even k. Thus for k=2^j and j>=2, the degree is 4^(j-1)-1.
After O(log r) doubling stages, each named remainder is generically dense.
An implementation that materializes those stages therefore writes at least
r*(h-O(log r)) coefficient slots over a generic characteristic-zero field.
This counts actual intermediate output, not just the final degree or a short
description of an unevaluated recurrence.

The division-polynomial batching direction and its degree formula are prior
art. [Li–Wagstaff's primary poster](https://www.cerias.purdue.edu/news_and_events/events/symposium/2004/posters/pdfs/FFT-ECM.pdf)
describes simultaneous curve-parameter evaluation;
[Li's dissertation abstract](https://docs.lib.purdue.edu/dissertations/AAI3263600/)
records degree, construction and complexity analysis. Their existence is not
evidence that an additive-cost primitive has been supplied here. The remainder
lemma above is a direct derivation, not a claim of novelty.

## Cost conclusion and boundaries

The implemented recurrence has O(h) fixed-size groups of quotient-ring
operations, with ordinary dense polynomial multiplication/reduction cost
P(r,n) at input bit length n. Its honest upper cost is roughly h*P(r,n),
plus batch-polynomial construction, parameter generation, gcds and extraction.
Calling a degree-r ring multiplication one scalar operation hides the factor
under investigation. FFT multiplication can improve P; it does not remove the
number of materialized stages. The measured coefficient volumes confirm this
work on the frozen sample.

The characteristic-zero lemma alone does NOT establish generic density for
every composite modulus: nonzero integer polynomials can vanish after reduction,
and high-degree polynomial functions over finite fields can collapse. It also
does not bound how soon a successful ECM run stops. No all-input modular lower
bound or asymptotic ECM success theorem is being inferred from it.

This rejects sparse coefficient trimming as the tested escape. It leaves open
a different algorithm that computes the final product without materializing
each recurrence state, but no such algorithm was constructed. A compressed
circuit, a norm symbol, or fast final multipoint evaluation is not that algorithm.
Reopen only with an explicit transformation and complete construction/query cost;
do not repeat the same recurrence at larger batch sizes as a search for novelty.

As with other standalone diagnostics, a hard external kill before final writing
would lose in-memory partial rows; no such kill happened here. Coefficient-volume
counters do not meter all bit operations, memory traffic, or setup. Hidden factors
are used only by tiny corpus generation and never passed to the evaluator.
