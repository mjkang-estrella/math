# Full target retained; no complete result

Credit 0. Counts remain 3/30 additional, 33/60 total. No acceptance authority.

## Exact source and quantified scope

Mihoković–Raïssouli, arXiv:2405.13618v2 (24 May 2024), Definition 1.1,
(1.1), (1.5), Example 4.6 and Conjecture 4.7, actual HTML bodies read.
https://arxiv.org/html/2405.13618v2
Latest arXiv abstract page reports v2. Related journal DOI
https://doi.org/10.2298/AADM240618001M ; journal issue page places it in
AADM20(1)(2026),1–23, posted28April2026. Actual journal PDF unavailable here:
DOISerbia timeout, publisher-linked pefmath timeout through web and certificate
hostname mismatch through urllib. No TLS bypass; journal equality not certified.

For each epsilon in {-1,+1}, set q=(5+epsilon sqrt17)/2 and p=-epsilon sqrt17.
For ALL distinct positive reals a,b, the conjecture asserts

    M(a,b) < B_p(M(a,B_q(a,b)), M(B_q(a,b),b)),
    B_r(s,t)=((s^r+t^r)/2)^(1/r),
    M(s,t)=(t-s)/(sqrt2 atan(log(t/s)/sqrt2)), M(s,s)=s.

The diagonal is excluded by the standard strict comparison convention; it
is not a counterexample. Both q are positive; both p are nonzero. This is
M2, a logarithm–arctangent mean, not the campaign's inverse-arcsinh family.
No exact MathDB number for Conjecture4.7 is asserted. Cached363173/4/5 refer
to neighboring L_alpha/S_alpha/M4 claims, not this one.

## Primary theorem and registry gate

The same source's Proposition2.3 only compares individual means; it does not
state the nested conjecture. Source Example4.6 already gives its local sixth
order sign. That sign gets NO credit. Raïssouli–Sándor2016 actual Theorems4.1,
4.2,4.4 and their proofs were read at
https://link.springer.com/article/10.1186/s13660-016-1212-z . The two generic
criteria concern arithmetic outer means, convexity/concavity, and a sandwich
by (A+B_r)/2. Their literal hypotheses do not immediately solve this target;
see the exact conjugation obstruction below. This does not clear all possible
classical subsumption.

Reuse authorized r7 complete registry trees and head receipts, retrieved
29October2026 04:39:40–44UTC: omega Problems and D5, OpenAI preprints, count
root and registry. The searched names/identifier do not locate a matching
problem or proof path. Generic 'stabiliz' hits concern unrelated groups,
codes and algebra. Paths are not full-text proof absence evidence. Live
public targeted search on29October found original and journal metadata,
no located resolution; this is bounded coverage, NOT novelty clearance.
MathDB affected route already403 and GitHub API rate-limited in preceding
lanes: neither traversed/retried. Current MathDB solution bodies unread.
Earlier Handelman/Matkowski cached leads were discarded on actual source
bodies: the former already says Theorem2 proves its Conjecture1, the latter
already supplies a counterexample. No work or novelty credited to them.

## Exact ordinary reduction

By symmetry and homogeneity, take (a,b)=(1,e^z), z>0. Define

 F(t)=log((e^t-1)/(sqrt2 atan(t/sqrt2))), F(0)=0,
 u=z/2+log(cosh(qz/2))/q,
 v=F(u), w=u+F(z-u),
 D(z)=log((exp(pv)+exp(pw))/2)/p-F(z).

Since 0<u<z, every expression is regular. Direct substitution gives
v=log M(1,e^u), w=log M(e^u,e^z), and D=log(R/M).
Thus the FULL source statement is exactly D(z)>0 for EVERY z>0 and BOTH
branches. No local or fixed-parameter result replaces that target.

Let H(t)=e^t/(e^t-1)-sqrt2/((t^2+2)atan(t/sqrt2)), H(0)=1/2;
let h=(1+tanh(qz/2))/2 and W=exp(pv)/(exp(pv)+exp(pw)). Differentiation gives

 D'(z)=W H(u)h + (1-W)[h+H(z-u)(1-h)]-H(z).       (*)

A sufficient still-UNPROVED uniform inequality is that the RHS of(*) is
nonnegative for all z>0, with strictness somewhere in each interval(0,z).
Even D'>=0 alone is not established. Exact equivalence D>0 above is the
weaker unresolved target; failure of monotonicity would not refute it.

## Failed shortcuts, with ordinary obstructions

1. Termwise derivative comparison fails: at z=0, u'=1/2, v'=1/4,
w'=3/4, F'=1/2. The first component is strictly smaller than F' near zero.
Only cancellation with the second weighted component can yield(*).

2. Neither global convexity nor global concavity of D is possible.
Removing the common t from numerator/denominator in F makes it real analytic
at0. Substituting its Taylor polynomial in the exact reduction gives

    D(z)=(11/11520)z^6+O(z^7), D(0)=D'(0)=0.

The arithmetic is reproduced exactly in Q(sqrt17) by check.py; it agrees with
source Example4.6 and is not a new local theorem. Concavity with D'(0)=0
would force D(z)<=0, contradicting the displayed positive coefficient.
For convexity, put c=2^(-1/q), k=sqrt2/pi and
 d=(1-c)/(sqrt2 atan(log(1/c)/sqrt2)). Then u-z ->log c,
 M(1,e^z)/e^z ->k,
 M(1,e^u)/e^z ->kc,
 M(e^u,e^z)/e^z ->d.
These follow respectively by log cosh asymptotics, atan tending to pi/2,
and continuity/homogeneity at(c,1). Consequently
 D(z)->log(B_p(kc,d)/k), a finite real number. A convex function on[0,infinity)
with any positive secant slope is unbounded above: its later secant slopes
are at least that positive slope. Here D(0)=0 and D(z)>0 for small positive z,
yet the limit is finite. Contradiction. Thus global convexity also fails.
This rules out two proof strategies, not the conjecture.

3. Direct power conjugation does not meet the closest2016 criteria.
Set T(X,Y)=M(X^(1/p),Y^(1/p))^p. It is again a homogeneous symmetric mean.
Conjugation turns the resultant into R(A,T,B_(q/p)). For p>0 the target is
T<R(A,T,B_(q/p)); for p<0 it is T>R(A,T,B_(q/p)).
For any symmetric analytic mean with expansion M(1-t,1+t)=1+A t^2+O(t^4),
Taylor substitution gives T(1-t,1+t)=1+[(2A+1-p)/(2p)]t^2+O(t^4).
Here A=1/3 (expand atan and atanh), so the coefficient is(5/3-p)/(2p).
For p=sqrt17 this is negative, excluding convexity required by2016Thm4.4
(and q/p<1 also has the wrong parameter direction). For p=-sqrt17,
Thm4.2's required lower sandwich T>=(A+B_(q/p))/2 fails already near the
diagonal: its quadratic difference coefficient is

    (10/3-p-q)/(4p)=-(5+3sqrt17)/(24sqrt17)<0.

These are exact nondegenerate nearby-input obstructions to the proposed
classical reduction, not to the source conjecture. They do not exclude other
comparison theorems, iteration methods, or more sophisticated subsumption.

## Validation and strongest objection

check.py uses exact rational quadratic-field formal series and verifies both
branches through degree6 and the component derivative limits. CPU35s,
address space512MiB, BLAS/OMP1; PASS. probe.py separately ran32 high-precision
finite diagnostics (z from.01 to10000); all supported the conjecture. Those
are explicitly NOT proof, interval certificates, or credit. No numerical
comparison is used in any ordinary obstruction above.

Strongest objection: all retained deductions are elementary transformations,
local source algebra or failed-route diagnostics. The decisive global
cancellation in(*) is completely missing. No complete ordinary proof or
admissible interior source refutation survived. No Lean, manuscript or
PROOF.md was started. No acceptance or novelty authority claimed.
