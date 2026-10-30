# BBK full refinement: unsuccessful uniform continuation

Research date: 2026-10-29 UTC. Lane sol-bbk-full-refinement-r4. Credit 0.
No complete proof, no counterexample, no acceptance recommendation. No PROOF.md
or Lean certificate is supplied.

## Literal scope and dependency audit

The target is Banerjee–Bringmann–Keith, arXiv:2601.04014v1, Section 5,
Conjecture 5.1: every coefficient of

G(k,n) = product(i=0..n-1)(1-q^(2k-1+2i)) /
         product(i=0..n)(1-q^(2i+1))

is nonnegative, for every integer k>=1 and n>=0. The degree index ranges over
ALL nonnegative integers. The MathDB page's k>=0 and malformed quotient do not
override the primary source. Its claims of 2013 antecedents were not verified;
they are database metadata, not demonstrated chronology of this exact refinement.

Read root-bbk-handoff-r4/HANDOFF.md and scope-check.json as present in the
workspace (the supplied commit reference 946186c772 was NOT checked with git,
because git operations are prohibited). Read root-bbk-r1 failures,
pi-bbk-full-refinement-r3/PROOF-K4-K5.md, run1, run9, and first-batch
pi-discrete-discovery-r7/FINDINGS.md. Existing partial row certificates have
not been independently fully audited here.

For O_t=product(i=0..t-1)(1-q^(2i+1)), k>=2 gives exactly

G(k,n)=O_(k+n-1)/(O_(k-1) O_(n+1))=G(n+2,k-2).

Proof: the numerator of the original product is O_(k+n-1)/O_(k-1).
The denominator is O_(n+1); swapping the two denominator indices proves
symmetry. In particular k<=5 would transpose only to n<=3, conditional on valid
row proofs. k=1 is separately 1/(1-q^(2n+1)). The old run9 object is wrong:
it has an extra denominator factor 1-q^11. Literal k=6 has denominator
weights 1,3,5,7,9, period315, denumerant degree4. No new finite row was attempted.

## Primary-body literature comparison

Fresh primary bodies and retrieval receipts are in sources/ and retrieval*.json.

* Corteel–Savage math/0309108v1, 2003-09-05: Theorems 3 and 4 give odd/even
  truncated lecture-hall generating functions. Their numerators are Gaussian
  polynomials at xy, and there are TWO denominator Pochhammer blocks. At x=y=q,
  the Gaussian base is q^2, not an odd numerator block. This specialization
  supplies a positive different object. No identity eliminating the second
  denominator block to obtain G was found. This is a checked mismatch of the
  obvious specialization, not a proof that every use of lecture halls is impossible.
* Gatzweiler–Krattenthaler 2502.06032v3, 2025-11-20: Conjecture 1 concerns
  polynomial quotients with the SAME top index and SAME base. Its proved cases
  include lower-index gap at most3 and lower index2 (Theorem9). BBK(5.2)
  has different bases q and q^2 and G is generally not polynomial. Thus this
  is not a direct application. Their fake-Gaussian extension remains conjectural;
  no substitution into an unproved conjecture is used as a theorem.
* Chern–Wang 2601.19845v1, 2026-01-27: actual Theorem1.3 is
  (q^2;q^2)_n/(q;q^2)_n^2 positive, for integer n>=1. Corollary2.2 has
  denominator (q;q^2)_(n+1)^2. This corrects prior lane summaries that read
  the denominator as length2n. Lemma2.1 and its cancellation proof give an
  actual positive decomposition for that SQUARED-denominator object.
  Theorem1.2 concerns the sum over n. Neither statement by itself implies
  positivity of each summand G(k,n). No claim of a subsumer is made.

## Uniform recurrence route explored

For k>=1,n>=1, cancellation of adjacent numerator blocks proves

G(k+1,n)-G(k,n)
 = q^(2k-1) (1-q^(2n)) (q^(2k+1);q^2)_(n-1)/(q;q^2)_(n+1).       (R)

Indeed the ratio of the two G's is
(1-q^(2k+2n-1))/(1-q^(2k-1)); subtract one and cancel the latter factor.
A uniform nonnegative sign for the residual in (R) would prove the target
by induction in k, starting with G(1,n). We have NO proof of this stronger
residual inequality. Exact prefixes on 240 pairs (k=2..16,n=0..15), degree<=900,
check the algebraic recurrence and reveal no negative residual coefficient.
These are diagnostics only; n=0 is handled separately by equality of the rows.

Trying to advance by multiplication alone fails: in the symmetry-triangular
range, advancing a denominator weight9 to numerator weight13 requires the
factor (1-q^13)/(1-q^9), whose q^13 coefficient is -1. Existing G factors can
repair this; this is not a counterexample to G. Similarly a positive logarithmic
coefficient criterion fails: at (k,n)=(6,4), the coefficient of q^11 in
q G'/G is 1-11=-10. Neither shortcut proves the needed invariant.

## Generating-function denominator clearing: exact obstruction

Put Q=q^2 and

A_n(x)=sum(b>=0) (q Q^b;Q)_n x^b,
P_n(x)=(x;Q)_(n+1) A_n(x),
C_n(x)=P_n(x)/O_(n+1).

These are identities over rational functions in q, expanded formally in x.
The original product directly gives, for n>=1,

A_n(x)=A_(n-1)(x)-q Q^(n-1) A_(n-1)(Qx).

Consequently

P_n(x)=(1-x Q^n)P_(n-1)(x)
       -q Q^(n-1)(1-x)P_(n-1)(Qx),
P_0(x)=1.

Proof: factor off the final factor 1-q Q^(b+n-1) in each coefficient;
then multiply by (x;Q)_(n+1), canceling the initial or final factor as appropriate.
This proves by induction that P_n is a polynomial in x of degree<=n.
Also

sum(k>=1) G(k,n)x^(k-1) = C_n(x)/(x;Q)_(n+1).

A coefficientwise nonnegative C_n would give a uniform positive realization,
since the reciprocal denominator is a product of positive geometric series.
But the exact recurrence yields

P_1=(1-q)(1+qx),
P_2=(1-q)(1-q^3)
    +q(1+q^2)(1-q)(1-q^3)x -q^5(1-q)^2 x^2.

Thus

[x^2]C_2(x)=-q^5(1-q)/((1-q^3)(1-q^5)),

whose q^5 coefficient is -1. This is an exact algebraic falsifier of positivity
of the cleared generating numerator, not a numerical conjecture and not a
falsifier of BBK5.1. checks.py independently reproduces it using coefficients
of the original G, without the A/P recurrence. Any successful use of this
representation must control cancellation between different x degrees after
multiplication by the geometric denominator. No such uniform control was found.
This failed route is recorded solely to avoid spending another lane on the same
false sufficient condition; it earns no discovery credit.

## Strongest remaining objection and formal status

Every sign argument above either needs an unproved stronger invariant or fails
on an exact small obstruction. There is no partition injection, nonnegative
all-parameter decomposition, all-degree estimate, or substantive counterexample.
The numerical absence of negatives cannot fill this gap. The source5.2 residual
and the old divisibility/complete-intersection/q-Chu failures remain unresolved
or ruled out exactly as in the handoff; they were not recycled as discoveries.

A literal potential Lean endpoint would quantify k,n,m:Nat, require 1<=k,
and assert 0 <= PowerSeries.coeff m of the literal product of factors
(1-X^(2*k-1+2*i)) and the inverse/geometric factors at 2*j+1. Formal obligations
would include this definition's source identity, the product symmetry,
coefficient closure under nonnegative sums/products, and, decisively, an actual
unconditional uniform positivity argument. That last obligation is absent in
ordinary mathematics here. No Lean file, stub, sorry, or verified label is used.
Pin remains Lean4.34.1/mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
