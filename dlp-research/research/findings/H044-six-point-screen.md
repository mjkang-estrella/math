# H044 six-point determinant: exact predicate, no fast selector

2026-10-09 UTC. Native Sol /root/h034_c4_implementation independently
proposed this limited representation after the recorded Opus API failures.
Native Astra /root/h007_additive_relations independently verified the criterion
and counterexample. Root checked primary mathematical references. This is
standard elliptic divisor geometry, not a new algorithm or novelty claim.
No executable experiment, implementation, Lean claim or H034 cap reset.
Best supported exponent remains 1/2; verified improvement NONE.

## Exact statement and proof

Let E/Fp be a smooth short-Weierstrass curve y²=x³+ax+b, p>3, with origin O.
Let P1,...,P6 be distinct finite rational points. Form the six-by-six matrix
whose i-th row is

    v(P_i) = (1, x_i, y_i, x_i², x_i*y_i, x_i³).

Then det(v(P_i))=0 if and only if P1+...+P6=O.

The displayed functions have distinct pole orders 0,2,3,4,5,6 at O and
no other poles. They are independent, and Riemann–Roch gives dim L(6O)=6,
so they form a basis. A singular evaluation matrix supplies a nonzero function
in L(6O) with these six distinct zeros. Degree of a principal divisor is zero,
so its divisor is exactly P1+...+P6−6O. Conversely, if the group sum is O,
that divisor is principal, giving a nonzero function in the evaluation kernel.
The divisor-class identification of E with Pic0 gives the equivalence.
The matrix is over Fp, so singularity over an algebraic closure already gives
a nonzero kernel over Fp; no additional rationality assumption is hidden.

The underlying Riemann–Roch and Pic0 facts are in
[Milne, chapter I, section 4, Proposition 4.10 and Theorem 4.13](https://www.jmilne.org/math/Books/ectext6.pdf).
Root read these passages, including the arbitrary-field discussion. The proof
above specializes those facts to the explicit six-function basis; it was
independently checked on paper and has not been formalized in Lean.

Repeated points invalidate this plain evaluation test: duplicate rows make
the determinant vanish automatically. Prescribed multiplicities require
local-jet conditions instead. Infinity also requires a suitable line-bundle
evaluation instead of the displayed affine coordinates. Signed points include
their chosen ordinates; abscissae alone do not specify this relation.

If P_i=a_i G+b_i Q in a prime-order subgroup of order q, Q=kG, this exact
zero-sum relation gives k=−(sum a_i)/(sum b_i) mod q when sum b_i is nonzero.
Verify the recovered scalar. Arbitrary field weights in a linear dependency
of the evaluation vectors are not the integer coefficients of this divisor.

## Exact counterexample to ordinary dependency extraction

Let G have prime order q>28 and choose P_i=iG, i=1,...,7. All are distinct
finite points. Seven vectors v(P_i) in a six-dimensional Fp-space necessarily
have a linear dependency. But omitting point P_j gives group sum

    (1+2+3+4+5+6+7−j)G = (28−j)G != O.

Here 28−j ranges from 21 through 27. Thus every six-row minor is nonsingular
despite the weighted dependency among seven rows. This explicitly refutes
using an arbitrary Gaussian dependency as the desired six-point selector.
It is not a lower bound on other selection algorithms.

## Prior art and complete-work disposition

The relation-representation/selection distinction is known, rather than a
new hypothesis. Root read the definition of Problem L in
[Abdullah–Mahalanobis, section 2.1](https://gcc.episciences.org/7180/pdf): it asks
for a kernel vector with prescribed numbers of zero positions, not merely
any nonzero kernel vector. This source check identifies prior art only; its
other probability and complexity assertions are not adopted here. Earlier
project minor/poset reviews already cover that algorithmic route. This screen
does not reopen stopped proposal roles or repeat their construction work.

For six already-selected points, a direct group-sum test is also available.
No complete-work advantage of the determinant over that test is established.
Generating labelled points, choosing a useful subset, all failed choices,
matrix arithmetic, null scalar coefficients, memory and verification must
be charged. No fast subset selector emerged in this pass, so there is no
candidate-specific experiment or broad formalization to admit. A genuinely
different costed selector would be needed before revisiting the mechanism.

## Process and validation

Sol's final report added a separate elementary screen: for a quotient isogeny
phi with kernel containing <G>, Q=[k]G implies phi(Q+S)=phi(S) by the
homomorphism law. This specified point-value probe contains no k-dependence.
It does not exclude other isogenies or coordinate operators. Claims about
formal expansions need an explicitly compatible parameter; none is adopted
here beyond the point-value identity. The ordinary case q!=p suffices for
the usual separable quotient construction; constructing/evaluating the map,
extension points and any extraction remain paid.

Root checked the introduction of
[Bernstein–De Feo–Leroux–Smith](https://arxiv.org/pdf/2003.10118): square-root
Vélu gives a soft-O(sqrt(q)) field-operation upper guarantee for evaluating
the specified degree-q isogeny from a kernel generator. That is neither an
ECDLP decoder nor a lower bound. Sol reported an author-hosted PDF access
error and a successful arXiv read; root likewise used the primary arXiv PDF.
No complete gain follows from the scalar-independent probe.

Sol's source reads for the six-point screen were Galbraith sections 7.9 and
8.7 (author-hosted crypto-book/ch7.pdf and ch8.pdf). Root used Milne instead,
and Astra independently checked the proof and its exceptional cases. Sol
also notes feature construction is O(B) field operations after paid point
generation. Its remark about B^5 enumeration is not accepted as a complete
algorithm or bound without specifying the fixed target and lookup policy;
the six-point test alone leaves subset selection unresolved.

Both native reviews were read-only, without code runs/imports, children or
edits. Root's web reads used the linked author/primary sources; an initial
lookup of H006-mechanism-disposition.md failed because that filename does not
exist, and rg --files identified the actual earlier record names. No evidence
was inferred from that failed read. No numerical seeds or runtime measurements.

Existing Lean artifacts are unchanged. Validation command, for the integrated
checkpoint: ./scripts/check.sh > /tmp/ecdlp-h044-sixpoint-check.log 2>&1.
Its outcome is recorded in STATE; these checks do not certify this paper proof.
