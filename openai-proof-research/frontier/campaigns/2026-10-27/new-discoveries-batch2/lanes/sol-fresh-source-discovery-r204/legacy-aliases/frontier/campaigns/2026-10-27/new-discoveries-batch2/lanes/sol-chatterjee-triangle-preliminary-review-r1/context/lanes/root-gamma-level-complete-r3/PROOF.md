# Strict convexity of Gamma-ratio level curves

Complete mathematical proof and literal Lean certificate; independent final
review and acceptance pending. Candidate credit 0; batch accepted tally 1/30.

## Source and exact scope

Garrappa–Gerhold–Popolizio–Simon, J. Math. Anal. Appl. 551 (2025), 129588,
Lemma 15 and Remark 16(a), actual journal PDF pages 12–13; arXiv:2410.11852v4.
The source defines h(x)>0 by Gamma(h)Gamma(h+2x)=2Gamma(h+x)^2, proves strict
convexity for x>=1, and asks for strict convexity on the whole positive axis.
The actual version of record is included and agrees with v4 at these passages.
Theorem 23 also uses this curve at x<1. No separate source complete-Bernstein
or non-real-zero conjecture is claimed solved. SOURCE-COMPARISON.md gives the
public repository URL and visual-read record.

We prove the following single-family strengthening: for every real c>1 and x>0
there is a unique positive h_c(x) with

    Gamma(h_c(x)) Gamma(h_c(x)+2x) / Gamma(h_c(x)+x)^2 = c.

The height h_c is strictly convex for x>0. All levels c, the old x>=1 case,
helper lemmas and classical tools are not separate outcomes.

## Series identity and levels

For 0<x<s set F(x,s)=log Gamma(s-x)+log Gamma(s+x)-2log Gamma(s), and
g(u)=-log(1-u^(-2)), u>1. Then

    F(x,s)=sum_(m>=0) g((s+m)/x).

Indeed use the classical finite log-Gamma approximants
z log N+log(N!)-sum_(m=0)^N log(z+m). In the combination defining F,
the log N and log(N!) terms cancel exactly; each remaining summand is
2log(s+m)-log(s-x+m)-log(s+x+m)=g((s+m)/x). The Bohr–Mollerup
log-Gamma limit gives the identity. This is an actual HasSum proof in Lean,
not an assumed Euler-product interface.

For m>=1, all terms are nonnegative and

    g((s+m)/x) <= x^2/((s+m)^2-x^2) <= x^2/m^2.

The first bound follows from -log(1-t)<=t/(1-t) for 0<=t<1; the second
uses (s+m-x)(s+m+x)>m^2. For each fixed x>0 this gives uniform convergence
of the tail on the entire interval s>x. The m=0 term is handled separately.
Thus F(x,.) is continuous and strictly decreasing there. At s down to x,
the zero term tends to infinity. At s to infinity, each term tends to zero
and the summable majorant gives a zero limit. The IVT gives a unique s>x
at every level log c>0. Put h_c(x)=s-x.

Taking logarithms of the positive Gamma ratio shows that this level equation
is exactly the displayed literal source ratio, so it gives its existence and
uniqueness without residual assumptions.

## Strict Jensen argument

Direct differentiation gives

    g'(u)=-2/(u(u^2-1)),
    g''(u)=2(3u^2-1)/(u^2(u^2-1)^2)>0, u>1.

Let x0!=x1 be positive, a,b>0, a+b=1. Write y_i=h_c(x_i), s_i=x_i+y_i,
X=a*x0+b*x1, S=a*s0+b*s1, A=a*x0/X, B=b*x1/X. The weights A,B are
positive with A+B=1 and, for each natural m,

    (S+m)/X = A*(s0+m)/x0 + B*(s1+m)/x1.

Apply convexity of g termwise. At least one of m=0 or 1 gives strict
inequality: equality of both corresponding pairs of arguments would yield
1/x0=1/x1 after subtraction. Summing the convergent series, with a strictly
positive gap at that index, therefore gives

    F(X,S) < A*F(x0,s0)+B*F(x1,s1) = log c.

Since F(X,X+h_c(X))=log c and F(X,.) strictly decreases, X+h_c(X)<S.
Subtract X to obtain h_c(X)<a*h_c(x0)+b*h_c(x1). This proves the theorem.

The argument is classical perspective convexity: x*F(x,s) is a sum of
x*g((s+m)/x), classical perspectives composed with affine shifts. The
weighted Jensen calculation is that standard proof, not a new tool.

## Formal endpoint and verification

Nine modules, 52 public declarations. `GammaLevel.SourceLevel` is literally
the positive real Gamma-ratio equation. `source_convexity : SourceConvexity`
quantifies every c>1 and produces a height defined for all positive x with
StrictConvexOn on Ioi 0. `source_remark16a` is the closed c=2 specialization.
`existsUnique_sourceLevel` separately certifies uniqueness. There is no
remaining series-identity, monotonicity, level-existence or Jensen premise.

`python3 verify_candidate.py` asserts the Lean binary version and SHA-256 and
all package pins, copies source only to a fresh temporary directory, builds
all modules with warnings as errors, and checks the public type/axiom reports.
The root replay passed with only propext, Classical.choice, Quot.sound; all
actual 52 type and axiom reports were read. Lean 4.34.1; Mathlib full revision
d13f23b723b8a846827a245b89c10fc7d3f11612. One copied series helper was renamed
to avoid a collision with an independent Euler helper; component-bindings.json
records that sole change. No local oleans are consumed by verification.

## Review correction, substantive objection, and limits

The preliminary review's assertion that the mechanism is not a perspective
sum was wrong. The independent r2 review explicitly reassessed the corrected
x*F perspective bridge and recommends eligibility; both reports are retained
unchanged under reviews/. The manuscript credits all classical machinery.

The strongest contrary case is that the exact Euler-product normalization,
perspective observation and two-shift strictness are short enough to be
judged routine. No published theorem about this curve or a subsuming strict
level-radius theorem was located in the bounded primary/citing/registry
screen. Independent final review must reconsider this objection, not inherit
eligibility from a prior verdict or from successful formalization.

No global priority guarantee, exhaustive MathSciNet/zbMATH search, or new
convexity machinery is claimed. Numerical checks are diagnostic only. No
external publication, upload, account mutation or MathDB edit has occurred.
