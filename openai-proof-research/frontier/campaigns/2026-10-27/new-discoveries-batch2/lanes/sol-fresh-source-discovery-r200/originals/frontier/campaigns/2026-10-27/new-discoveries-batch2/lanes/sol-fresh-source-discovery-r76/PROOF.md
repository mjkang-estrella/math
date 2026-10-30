# Complete ordinary multiplicity theorem — UNCOUNTED / substantive HOLD

This file proves the full multiplicity assertion for the actual power-law series,
not the proposed stronger curvature statements. It also diagnoses the literal
existence quantifier. Neither an endpoint correction nor a routine classical
corollary is nominated for credit. No Lean or paper is authorized by this proof.

## Source and exact scope

Da Costa–Drmota–Grinfeld, *Modelling Silicosis: The Structure of Equilibria*,
arXiv:1901.10670v1, 30 January 2019; September 2019 accepted-manuscript copy
at Strathprints 70232, equations (3.1), (3.6), (3.10), Corollary 7, and Section 5
Conjecture on printed p18. Actual formulas and p18 rendering inspected.
Published DOI: 10.1017/S0956792519000329, EJAM31(6)(2020)950–967;
version-of-record body equivalence is not certified.

Let a>=0, b>-2, d0>0 be arbitrary real parameters. For integers i>=1 set

d_i=i^a+i^b, w_i=i^(b+1),
P_0(x)=1, P_i(x)=product_{j=1}^i x/(x+d_j),
H(x)=sum_{i>=1} w_i P_i(x), F(x)=H(x)/(x+d0).

Equilibria with positive quartz concentration are exactly F(x)=lambda, x>0,
where lambda=alpha/r>0. The other concentrations are then uniquely determined
by source (3.1). This proof covers the source's physical subfamily b<=a as well
as the displayed broader mathematical family.

**Theorem.**

* If b>a-1, F is strictly increasing from 0 to infinity: exactly one equilibrium
  for every lambda>0.
* If b=a-1, F is strictly increasing from 0 to 1, with 0<F(x)<1: exactly one
  equilibrium for 0<lambda<1 and none for lambda>=1.
* If b<a-1, F increases strictly to one maximum M>0 and then decreases
  strictly to 0. Every 0<lambda<M has exactly two equilibria, lambda=M has
  exactly one, and lambda>M has none.

Consequently the full at-most-two clause holds and uniqueness holds whenever
existence is possible in the first regime. The literal Section 5 wording
claiming an equilibrium for every lambda also at b=a-1 is false; this is an
ineligible endpoint/existence correction, not a substantive counterexample.

## 1. Convergence and analyticity

Since d_j>=1, on a compact subset of the complex right half-plane Re z>0,
there is q<1 with |z/(z+d_j)|<=q for every j. Indeed
|z+d_j|^2=|z|^2+2d_j Re z+d_j^2 >= |z|^2+2Re z+1.
Thus polynomially growing coefficients times P_i(z) form a uniformly absolutely
convergent analytic series. H and F are real analytic on (0,infinity).
For 0<x<=1, P_i(x)<=(x/(1+x))^i. The weighted geometric sum is O(x)
as x tends to zero, so F extends continuously with F(0)=0. It is positive for x>0.

Telescoping P_{i-1}-P_i=(d_i/x)P_i gives
sum_{i=1}^N d_i P_i=x(1-P_N), and hence sum_{i>=1}d_iP_i=x.
All limits here follow from the geometric bound; no asymptotic conjecture is used.

## 2. Strict monotonicity for b>=a-1

Put c=a-b and r_i=w_i/d_i=i/(1+i^c). The numbers
q_i(x)=d_i P_i(x)/x=P_{i-1}(x)-P_i(x) form a probability distribution
on the positive integers; its upper tails are Pr(N_x>i)=P_i(x).
Therefore H(x)/x=E[r_(N_x)]. Each P_i(x) is strictly increasing in x.

When c<=1, r(t)=t/(1+t^c) has derivative
[1+(1-c)t^c]/(1+t^c)^2>0 for t>0. Thus r_i is strictly increasing.
Tail summation (nonnegative increments, justified by monotone convergence) gives
E[r_(N_x)]=r_1+sum_{i>=1}(r_{i+1}-r_i)P_i(x).
It is strictly increasing and positive. Multiplication by the positive strictly
increasing factor x/(x+d0) shows F is strictly increasing.

For fixed K, Pr(N_x>K)=P_K(x) tends to 1 as x tends to infinity.
If c<1, r_i tends to infinity, hence E[r_(N_x)] tends to infinity:
for every K it is >=r_(K+1)P_K(x). Therefore F tends to infinity.
If c=1, r_i=i/(i+1)<1 and r_i tends to 1. The same tail argument,
with upper bound 1, gives E[r_(N_x)] tending to 1. Consequently F<1 and F tends
to 1. Continuity and strict monotonicity prove the first two cases.

## 3. Finite rational-basis sign variation lemma

For any finite real vector v let V(v) be its sign variations after deleting zeros.
Let d_1,...,d_N>0 be arbitrary (ordering is unnecessary), and let c_0,...,c_N
be arbitrary real numbers. Define

Q_N(X)=sum_{i=0}^N c_i X^i product_{j=i+1}^N(X+d_j).

Then the ordinary monomial coefficient vector of Q_N, in increasing degree,
has at most V(c_0,...,c_N) variations. Consequently, by classical Descartes'
rule, Q_N has at most that many positive roots, counted with multiplicity.

Here is a complete proof of the transformation claim. Let A_N be the matrix
whose ith column is the coefficient vector of X^i product_{j=i+1}^N(X+d_j).
A_0=(1). The identity
Q_N=(X+d_N)Q_(N-1)+c_N X^N
implies A_N=L_N diag(A_(N-1),1), where L_N is the lower bidiagonal matrix
with diagonal d_N,...,d_N,1 and all immediate subdiagonal entries 1.
Recursive substitution factors A_N into lower bidiagonal matrices embedded
in leading principal blocks and identity matrices elsewhere.

Each factor diminishes sign variations: its ith output is a positive weighted
combination of input entries i-1 and i (or a positive multiple of one input).
For every nonzero output choose an input contributor of the same sign.
The chosen input indices can be nondecreasing because their permitted sets
are {i-1,i}; equal selected indices have equal sign. Thus every alternation
of output signs requires an alternation in the input sequence. This proves
V(output)<=V(input), including zero inputs and cancellation. Applying this
successively proves the claim. Descartes' rule is classical, not a new lemma
or tool attributed to this lane. Its actual proof body is retained in
Albouy–Fu arXiv:1307.6842v1 Proposition 1, Section 2.

## 4. Infinite horizontal-level argument for b<a-1

Now c=a-b>1. The same function r(t)=t/(1+t^c) increases up to
(c-1)^(-1/c) and decreases afterwards, tending to zero. For every lambda>0,
the integer indices with r_i>lambda form an interval, possibly empty.
Thus the coefficients

c_0=-lambda*d0,
c_i=w_i-lambda*d_i=d_i(r_i-lambda), i>=1,

have at most two sign variations: a negative block, a positive block, a
negative block, ignoring zeros. Every finite prefix has at most two.
Define G_N(x)=sum_{i=0}^N c_i P_i(x). Its positive denominator is
D_N(x)=product_{j=1}^N(x+d_j), and D_N G_N=Q_N of Section 3.
Hence G_N has at most two positive zeros, counted with multiplicity.
The limit, locally uniform, is

G(x)=H(x)-lambda*x-lambda*d0=(x+d0)(F(x)-lambda).

**Important finite-tail correction:**
G_N=H_N-lambda*(x+d0)+lambda*x*P_N.
Using H_N-lambda*(x+d0) in place of G_N would be incorrect.

Also F(x) tends to zero at infinity. Indeed r_i is bounded and tends to zero;
Pr(N_x>K)=P_K(x) tends to 1. Given epsilon>0, choose K so r_i<epsilon
for i>K. Then E[r_(N_x)]<=max_i r_i*(1-P_K(x))+epsilon, which tends
to at most epsilon. Since F=x/(x+d0)*E[r_(N_x)], F tends to zero.

We next show that every strict superlevel set {x:F(x)>lambda} is an interval.
Otherwise choose x1<x2<x3 with F(x1),F(x3)>lambda>=F(x2).
Choose lambda' strictly between F(x2) and min(F(x1),F(x3)); this is positive.
Since F tends to zero at both ends, there exist 0<x0<x1<x2<x3<x4
with F(x0),F(x4)<lambda'. At these five points G for level lambda' has
alternating signs -,+,-,+,-. By pointwise convergence, the finite G_N have
these same five strict signs for all sufficiently large N. The intermediate
value theorem supplies four distinct positive zeros, contradicting Section 3.
This argument deliberately uses strict signs, not the invalid assertion that
real zero counts are automatically preserved under uniform limits.

F is therefore quasiconcave. Positivity, continuity and its zero end limits
imply attainment of a positive maximum. The maximizing set is an interval;
if it contained two points, F would be constant between them, contradicting
real analyticity and F(0)=0. Let x* be its unique point. Quasiconcavity implies
F is nondecreasing on (0,x*) and nonincreasing on (x*,infinity): for example,
x<y<x* implies F(y)>=min(F(x),F(x*))=F(x). Any equality on either side
would force a constant interval, again impossible by analyticity. Thus both
monotonicities are strict. The intermediate value theorem now gives exactly
two, one, or zero roots as asserted. This closes the full ordinary proof.

## Limits and falsifiers

No ordinary multiplicity gap remains. Curvature signs H''>=0 or H''<=0,
monotonicity of H'' in b, and analogous assertions for the comparison K-series
are NOT proved or nominated. A genuine source series with three positive
roots at one positive level would falsify the result; a finite positive-d
coefficient transform increasing sign variation would falsify the key lemma.
The bounded exact checks support the algebra, but are not this proof.

The strongest eligibility objection is the fully explicit classical bridge:
source telescoping + elementary positive bidiagonal factorization + classical
Descartes + elementary limiting/quasiconcavity arguments. No new generic
mathematical tool has been established. Root must adjudicate substantive
eligibility, source-version equivalence and bounded novelty before any further
investment. The literal endpoint correction is independently excluded.
