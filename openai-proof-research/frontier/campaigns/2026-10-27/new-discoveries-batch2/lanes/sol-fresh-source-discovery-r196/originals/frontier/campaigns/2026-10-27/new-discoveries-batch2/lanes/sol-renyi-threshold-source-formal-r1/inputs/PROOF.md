# Ordinary refutation of the proposed subunit Rényi threshold

Research only, 2026-10-29. No Lean, paper, acceptance or literature-priority claim.

## Literal target and hypotheses

Fu–Li, *A reverse entropy power inequality for i.i.d. log-concave random variables*, arXiv:2510.09206v3, printed page 2, paragraph after (1.2), proposes a constant p0 in (0,1) such that the increment hp(X+Y)-hp(X) for iid log-concave vectors is maximized by exponential vectors for p>=p0, and by cube-uniform vectors for 0<p<=p0. This is an unnumbered, explicitly suspected assertion, NOT their numbered Shannon Conjecture 1.1. Here hp(f)=(1-p)^(-1)log integral f^p. A counterexample in dimension one refutes the stated dimension-independent threshold.

We prove: for EVERY real p with 0<p<1 there is a finite a>0 such that, for independent copies Xa,Ya having the log-concave probability density

    fa(x) = ca exp(-x) 1_[0,a](x),   ca=(1-exp(-a))^(-1),

the increment hp(Xa+Ya)-hp(Xa) is STRICTLY GREATER than the corresponding increment for independent rate-one exponentials E,E'. All entropies involved are finite. Exponential increments are unchanged by translation and nonzero scaling, so choice of rate does not matter. Products give the same strict comparison in every dimension if desired, without separate credit.

## Exact integrals, including normalization

The density fa is log-concave in the usual extended-value sense: its support is an interval and its log is affine there. Its integral equals one. For 0<=s<=2a its self-convolution is

    (fa*fa)(s)=ca^2 exp(-s) min(s,2a-s),

and is zero elsewhere. This follows by integrating the constant ca^2 exp(-s) over [0,a] intersect [s-a,s]. Put

    J = integral_0^infinity exp(-ps) s^p ds > 0,
    Ja = integral_0^a exp(-ps)s^p ds
         + integral_a^(2a) exp(-ps)(2a-s)^p ds.

J is finite (an exponential dominates every power). Directly,

    integral fa^p = ca^p (1-exp(-pa))/p,
    integral (fa*fa)^p = ca^(2p) Ja.

Consequently the ratio whose logarithm, divided by 1-p, is the increment is

    Ra = ca^p p Ja/(1-exp(-pa)).

For E the corresponding ratio is R=pJ. We will prove Ja>(1-exp(-pa))J for all sufficiently large finite a. Since ca^p>1 and 1-p>0, this implies Ra>R and the required STRICT increment comparison. No comparison of separately upper-bounded entropies is used.

## The uniform tail mechanism for every fixed subunit order

Let D_a=J-Ja. Substituting s=a+u gives the exact, nonnegative deficit

    D_a=exp(-pa) integral_0^infinity exp(-pu)
         [(a+u)^p-(a-u)_+^p] du.                    (A)

For each fixed u>=0, the bracket tends to zero as a tends to infinity. For a>u this follows from the mean value theorem, because the derivative p t^(p-1) tends to zero. Also, for ALL a,u>=0,

    0 <= (a+u)^p-(a-u)_+^p <= (2u)^p.

If u<=a, apply (v+w)^p<=v^p+w^p with v=a-u and w=2u. If u>a, use a+u<=2u. The function exp(-pu)(2u)^p is integrable. Dominated convergence in (A) therefore gives

    exp(pa)D_a -> 0.

Since J>0, for all sufficiently large a we have D_a<exp(-pa)J, or equivalently Ja>(1-exp(-pa))J. This completes the every-real-p theorem.

## Explicit finite witnesses approaching order one

The preceding argument contains no numerical premise. For a directly specified cofinal sequence, take any integer n>=2 and set

    p_n=1-1/n,     a_n=2(48n)^n.

We verify the required inequality by elementary estimates. For a>=8192 and 1/2<=p<1, split the integral in (A) at u=a/2. On the first interval, the mean value theorem and p-1<0 give

    (a+u)^p-(a-u)^p <= 2pu(a/2)^(p-1).

Its integral against exp(-pu) is at most 2(a/2)^(p-1)/p. On u>=a/2, use the previous bound (2u)^p<=2u, valid because 2u>=a>=1. Bounding it further by 2u+1 and integrating gives

    exp(pa)D_a <= 2(a/2)^(p-1)/p
                   + exp(-pa/2)((a+1)/p+2/p^2).

For p=p_n,a=a_n, the first term is exactly 2/[p_n(48n)]<=1/(12n)<=1/24. Since a_n>=2*96^2>8192 and p_n>=1/2, the second term is at most

    exp(-a_n/4)(2a_n+10)
      <= 384(2a_n+10)/a_n^3
      <= 1152/a_n^2 < 1/24.

The exponential estimate uses exp(t)>=t^3/6, with t=a_n/4. The final strict inequality follows from a_n>=8192 and 24*1152<8192^2. Thus exp(p_na_n)D_(a_n)<1/12. Meanwhile

    J >= integral_0^1 exp(-p_ns)s^p_n ds
       >= exp(-p_n)/(p_n+1) > 1/6,

using p_n<1 and exp(1)<3. Hence D_(a_n)<exp(-p_na_n)J, exactly as needed.

Given ANY proposed p0<1, choose an integer n>=2 with n>1/(1-p0). Then p_n>p0, but the explicitly specified iid pair above beats every one-dimensional exponential pair at that order. This contradicts the full existential-threshold assertion; it is not an endpoint correction, a fixed favorable case of a positive conjecture, or a claim about p=1. We neither settle the Shannon conjecture nor identify actual optimizers at any order.

## Strongest mathematical objection and attempted falsifiers

The apparent objection is Fu–Li Lemma 3.7: exponentials majorized by the sum give the largest output hp among monotone log-concave inputs with the SAME INPUT h_infinity. This does not compare hp(output)-hp(input). Their normalization fixes the input maximum; our ratio retains the changing input hp, the factor ca^p, and the denominator 1-exp(-pa). Dropping that denominator reverses the conclusion. The convolution formula, (A), and the direction after division by 1-p are the decisive falsifiers. They have been rederived above independently of the numerical scan.

Classical entropy-comparison bounds for one density and Melbourne–Tkocz's difference inequality do not supply the reverse increment bound claimed in the source. A full classical subsumption/eligibility review is still required: the proof is elementary and uses a familiar truncated exponential family. No assertion that shortness itself demonstrates substantive eligibility is made.

There is no missing universal mathematical step in this ordinary proof. Current-prior semantic coverage, expert attribution/eligibility of the unnumbered assertion, and independent adversarial validation remain separate HOLDs.
