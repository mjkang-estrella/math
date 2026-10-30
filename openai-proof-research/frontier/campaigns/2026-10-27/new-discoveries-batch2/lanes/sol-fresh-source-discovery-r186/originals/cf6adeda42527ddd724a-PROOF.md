# Positive-parameter arcsinh concavity: ordinary proof candidate

Credit 0. The literal Lean endpoint compiles, with a fresh isolated replay
PASS (19 declarations, 5 modules, standard three axioms). Independent
source/math/eligibility review, acceptance-grade prior-art screen, paper and
final deterministic packet/extracted replay are still absent.
The old small-p refutation remains uncredited; this is an attempt to answer
the surviving positive-parameter question, not to relabel that refutation.

## Exact source target

Li Yin, Li-Guo Huang, Yong-Li Wang and Xiu-Li Lin, *A survey for generalized
trigonometric and hyperbolic functions*, Journal of Mathematical Inequalities
13(3) (2019), 833–854, DOI 10.7153/jmi-2019-13-58, Conjecture 5.1 on printed
p.847: for fixed 0<x<1, p -> arcsinh_p(x) is strictly concave on (1,infinity).
The defining integral is (1.14):

    A(p,x) = integral_0^x (1+t^p)^(-1/p) dt.

This is the narrower surviving formulation identified in the earlier
pi-arcsinh-concavity-preliminary-review, whose small-p witness did not answer
it. That review wrongly attributed the survey to other authors; the actual
title page gives the four names above. The original Baricz–Bhayo–Vuorinen,
Filomat 29(2) (2015), 303–313, Conjecture 2.4, used all p>0 and is false
there by the old uncredited witness. These source questions must be separated.

## Proposed stronger theorem

For every x>0, the literal integral A(p,x) is strictly concave on
(log(2)/2,infinity). In particular it answers the entire 2019 Conjecture 5.1.
No assertion that this is the optimal parameter interval for A is made.

## Proof

For u>0 define

    H(u) = log(1+u) - u log(u)/(1+u).

Writing r=u/(1+u) in (0,1) gives

    H(u) = -r log(r) -(1-r) log(1-r) >0.

Furthermore H'(u)=-log(u)/(1+u)^2. Thus H increases up to u=1 and decreases
afterwards, so H(u)<=H(1)=log(2). This is the elementary binary-entropy bound;
it is classical and is not claimed as a new tool or outcome.

Fix t>0, and put u=t^p, f(p,t)=(1+t^p)^(-1/p), ell=log f. For p>0,

    ell_p = H(u)/p^2,
    dH(t^p)/dp = -p (log t)^2 u/(1+u)^2,
    ell_pp = -2H(u)/p^3 -(log t)^2 u/[p(1+u)^2].

Consequently the exact second derivative is

    f_pp = f/p^4 * [ H(u)^2 -2p H(u)
                           -p^3 (log t)^2 u/(1+u)^2 ].

For p>log(2)/2, we have 0<H(u)<=log(2)<2p. Hence H(u)^2-2pH(u)<0,
and the final term in the bracket is nonpositive. Thus f_pp<0 for every
t>0 and every p>log(2)/2. No interchange of an improper integral and a
parameter derivative is needed: this proves strict concavity pointwise.

For distinct p0,p1 in this interval and 0<lambda<1, the strict pointwise
Jensen inequality holds for every t>0. At t=0 the integrand is exactly 1,
so the corresponding non-strict inequality holds there. Each integrand is
continuous on [0,x] for p>0. The Jensen gap is continuous and positive on
(0,x]; for instance it is positive at x/2. Its integral is therefore
strictly positive. Integration of the Jensen inequality proves

    A(lambda*p0+(1-lambda)*p1,x)
      > lambda*A(p0,x)+(1-lambda)*A(p1,x).

This is strict concavity on the stated interval. Since log(2)/2<1, it
implies exactly the 2019 source statement for 0<x<1 and p>1. Positivity
then gives the source's strict multiplicative Turan consequence for p>2.
This consequence is not a separate outcome.

## Strongest objections and unclosed gates

1. The calculation is short and elementary. It may be judged a routine
   generic reciprocal-lp-norm/entropy corollary. A concrete published theorem
   supplying this same diagonal-parameter result would exclude credit.
2. Filomat Theorem 2.6 already proves separate parameter concavity for
   arcsinh_(p,q). Separate concavity does not imply diagonal concavity: its
   mixed derivative is essential. The new derivation must not be advertised
   as following merely by putting q=p in a one-parameter partial derivative.
3. No independent final math/novelty/eligibility verdict exists. The initial
   web screen has not located an exact proof but does not certify absence.
4. The five-module Lean certificate now proves the literal SourceConjecture,
   and the stronger all-x theorem, without residual premises. Root fresh
   replay and all 19 printed types/axioms have been read. No manuscript or
   independent formal review exists yet; symbolic/numerical diagnostics are
   not the quantified proof.
5. This is one proposed family. The entropy lemma, derivative identity,
   extension to x>1, old small-p witness, and Turan consequence are uncounted.
