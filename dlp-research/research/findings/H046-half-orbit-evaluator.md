# H046 signed half-orbit product: a square-root evaluator, not a faster solver

2026-10-09 UTC. Proposal/derivation: native Astra /root/h007_additive_relations.
Root independently expanded the addition formula, checked block indexing and
degree bounds, and read the primary multipoint-evaluation source. Paper result,
not Lean-certified, executed, timed or a claim of novelty. No new experiment.
Current ECDLP exponent1/2; verified complete-work improvement NONE.

## Scope and exact output

Let E/F_p be a nonsingular short Weierstrass curve y²=f(x)=x³+a*x+b,
p>3, with G of odd prime order q, and Q=kG. Dispatch Q=O directly.
Write N=(q−1)/2. H045 gives the exact identity

    A(Q)/A(G) = chi_q(k),   A(P)=product_{j=1}^N y(jP),

where chi_q is the SCALAR Legendre symbol, represented by field elements ±1.
It is not a field-coordinate character. Every factor is nonzero because the
subgroup has odd order. The product retains ordinate signs.

H045's elementary O(q) sequential strategy is a valid upper bound, not a
necessary cost. This record supplies the previously missing explicit
soft-O(sqrt(q)) single-query construction. It uses standard techniques, not
an improved ECDLP algorithm.

## Rational block function

For U_i=iQ=(a_i,b_i), put D_i=X−a_i. In F_p(E), the addition formula is

    y(T+U_i)
      = −Y + (Y−b_i)*(2X+a_i)/D_i − (Y−b_i)^3/D_i^3
      = (A_i(X)+Y*B_i(X))/D_i^3,

with Y²=f(X) and

    A_i = −b_i*(2X+a_i)*D_i² + 3*b_i*f(X) + b_i³,
    B_i = −D_i³ + (2X+a_i)*D_i² − f(X) − 3*b_i².

Root checked this by expanding (Y−b_i)^3 and reducing Y²=f(X).
The degrees are deg A_i<=3 and deg B_i<=1: the cubic and quadratic terms
in B_i cancel. This is a rational-function identity, with actual values at
removable representation singularities handled below.

Set m=ceil(sqrt(N)). Form the product of these m rational functions using
balanced product trees, representing the numerator by a pair (A,B). Multiplication
uses

    (A+YB)*(C+YE) = (AC+f*BE) + Y*(AE+BC).

There is no inversion in this quadratic function-field computation. Induction
gives numerator degrees <=3m and <=3m−2, respectively. The denominator is

    D_m(X)=product_{i=1}^m (X−a_i)^3,   deg D_m=3m.

Thus F_m(T)=product_{i=1}^m y(T+iQ)=(A_m+YB_m)/D_m can be formed in
O(M_p(m)*log(m+1)) field operations, where M_p(d) prices degree-d polynomial
multiplication over F_p and satisfies standard regularity bounds.
At −iQ the i-th factor has a genuine pole of order3; the other factors take
nonzero finite values. The representation also vanishes in its denominator
at +iQ, where cancellation makes the desired product regular. Do not blindly
divide there.

## Complete coverage and exceptional centres

Let L=floor(N/m), r=N−Lm. For j=0,...,L−1 the complete block at T_j=jmQ
covers indices jm+1,...,(j+1)m. Generate the baby points and the giant
centres by ordinary group additions, preserving known ordinates.

- Compute block j=0 directly because its centre is O.
- If present, compute block j=1 directly: T_1=mQ is a removable singularity
  of the displayed rational representation.
- For j>=2, jm>m and jm+i<q for all i<=m, since (j+1)m<=N.
  Hence jmQ cannot equal +iQ or −iQ. All displayed denominators are nonzero.
- Compute the tail of r<m points directly.
- When fewer than two complete blocks exist, direct enumeration suffices.

The repair work is O(m) point/field operations. Standard identity/doubling/
tangency dispatch is used in point generation; an affine addition formula is
never applied at a zero denominator. Desired factors are never zero or infinity.

Multipoint-evaluate A_m,B_m,D_m at the remaining giant abscissae; combine
A_m(x(T_j))+y(T_j)*B_m(x(T_j)), divide by D_m(x(T_j)), and multiply the block
values and repaired factors. Arbitrary-point evaluation suffices; arithmetic
progression of the abscissae is neither asserted nor needed.

## Paid invoice and source scope

For m=ceil(sqrt(N)), product formation, evaluation, baby/giant generation and
repairs take soft-O(sqrt(q)) field work, with soft-O(sqrt(q)) field storage
using conventional product/remainder trees. Point generation/normalization
and nonzero divisions are charged. One transparent choice is affine generation
with O(m+N/m) separately paid inversions; it adds their actual polylog(p)
cost and does not make them unit-cost multiplications.

A conservative bit interpretation uses effective F_p polynomial multiplication
and evaluation, plus O(m+N/m) field inversions and ordinary point operations.
With standard fast arithmetic this is soft-O(sqrt(q)*log(p)) bit work/storage;
the soft notation suppresses logarithmic factors in q and p, and no concrete
runtime or small constant is asserted. Input validation and group-order
certification are outside this promised-instance evaluator, not silently proved.

The fixed product A(G) can be computed by the same construction and reused.
For a cold single target, charge it as well, plus the final division.
No inverse table over secret values is used.

Primary ingredient: [Bostan–Gaudry–Schost, Section2.1 and effective-ring
model in Section2.2](https://specfun.inria.fr/bostan/publications/BoGaSc07.pdf).
The paper states ordinary polynomial multiplication/evaluation bounds and their
space/bit models. Its arbitrary-point evaluation costs O(M(d)*log(d)) with
O(d*log(d)) field storage. The elliptic ordinate block construction here is our
application of those ingredients, not a theorem quoted from the paper.
Special arithmetic-progression speedups are unnecessary. No novelty claim.

## Why this does not change the ECDLP estimate

This implementation explicitly generates square-root-scale many points/
coefficients for ONE scalar-character value. No favorable finite full-work
constant against a complete solver is established. Multiple known public
multiples cQ merely give chi_q(c)*chi_q(k), not independent information.

For a shifted target Q'=Q+dG, the i-th factor becomes

    y(T+iQ+i*dG).

Its displacement depends on i; it is not evaluation of the old F_m^Q at one
common translated argument. The fixed A(G) denominator is reusable, but the
target-dependent product and giant evaluations cannot be declared free/shared.
Literal separate-query use pays the construction for every query. Combining
that invoice with the named H045 shifted-Legendre recovery strategies supplies
no exponent gain. Those strategies are upper bounds, not recovery lower bounds;
nor does this implementation's size bound arbitrary alternative circuits.

Next decisive paper gate: a SPECIFIC shared computation for shifted targets
with a complete recovery and memory invoice that can beat the matched baseline.
No such mechanism was supplied in this pass. No implementation, experiment,
or broader Lean refinement is warranted merely for this square-root-cost bit.
