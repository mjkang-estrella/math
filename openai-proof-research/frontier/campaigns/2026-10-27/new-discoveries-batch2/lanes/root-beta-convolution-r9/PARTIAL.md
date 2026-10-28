# Incomplete-beta convolution: partial range only, credit 0

Date: 2026-10-28. This is root research, not a discovery nomination, not an
acceptance, and not a complete Lean certificate. Additional tally stays 1/30.

## Exact source and the genuinely missing part

D. B. Karp, *Normalized incomplete beta function: log-concavity in parameters
and other properties*, arXiv:1509.05120v1, Eq. (1), Eq. (6), Conjecture 2,
Lemma 1 and Corollary 1. Actual primary HTML was read on this date:
<https://arxiv.org/html/1509.05120v1>. Journal-body comparison is not done here.

Put h_b(t)=Gamma(t+b)/(Gamma(t+1)Gamma(b)), t>0. The series in Eq. (1)
is an **ordinary** generating function; there is no additional n! denominator.
The coefficient at x^k in the normalized product difference of Eq. (6) is

    psi_k = sum_(i=0)^k [h_b(a+alpha+i) h_b(a+beta+k-i)
                        -h_b(a+i) h_b(a+alpha+beta+k-i)].

All a, alpha, beta are positive, and k is any nonnegative integer.
Conjecture 2 asks for negativity when 0<b<1 and positivity when b>1.
**The source's own Corollary 1 already proves the entire 0<b<1 half**, citing
Kalmykov–Karp [10, Theorem 3]. The earlier root r6 completely-monotone
observation is thus a rediscovery of a result explicitly present in the
source, and remains uncredited. For b>1 the source proves the integer-shift
case alpha in N, beta>=alpha-1 (with beta>0). Those cases are also uncredited.

The argument below handles every positive real alpha, beta when 1<b<=2.
It leaves b>2 with arbitrary noninteger shifts unresolved. No claim that this
partial range itself is new to the literature is made; the derivation is a
short consequence of the source's Lemma 1 and strict Jensen concavity.

## Generic finite-convolution lemma

Let h:(0,infinity)->(0,infinity) be C^2 with h'>0 and h''<=0. Then the
displayed psi_k formed with h is strictly positive for all a,alpha,beta>0.

Proof. Set S=2a+alpha+beta+k and r(u)=h(u)h(S-u), for 0<u<S. Directly,

    r''(u)=h''(u)h(S-u)+h(u)h''(S-u)-2h'(u)h'(S-u)<0.

Define G(t)=sum_(i=0)^k r(t+i), for 0<t<S-k. It is strictly concave.
Reindexing i to k-i proves G(S-k-t)=G(t). In particular,
G(a+alpha+beta)=G(a). Since

    a+alpha = beta/(alpha+beta)*a
              + alpha/(alpha+beta)*(a+alpha+beta),

strict Jensen gives G(a+alpha)>G(a). These two values are exactly the
left and right convolutions in the coefficient definition. Every evaluation
lies in (0,S), including k=0. This proves the lemma.

## Applying the lemma for 1<b<=2

For 1<b<2, take c=b-1 in (0,1) and x=t+1. The source's Lemma 1 says

    [psi(x+c)-psi(x)]^2+psi'(x+c)-psi'(x)<0.

Multiplying by h_b(t)>0 identifies this with h_b''(t)<0. Also
h_b'(t)/h_b(t)=psi(t+b)-psi(t+1)>0 because the digamma is strictly
increasing on positive arguments (its trigamma series is positive).
Thus the generic lemma applies. At b=2, h_2(t)=t+1, so h'>0 and h''=0;
the same proof applies and in fact psi_k=(k+1)alpha beta.

## Why the same proof does not establish the remaining conjecture

At b=3, h_3(t)=(t+1)(t+2)/2 is convex. More decisively, for S=10,
the second derivative of h_3(u)h_3(10-u) at u=1/10 is 2953/100>0.
Consequently r, and even G for k=0, need not be concave on its entire domain.
This refutes that proposed sufficient proof route, **not** Conjecture 2.
Log-concavity of h alone cannot simply replace concavity in the proof.

An induction through h_(b+1)(t)=(t+b)h_b(t)/b has not been justified:
its convolution has additional index-dependent weights, so positivity of the
previous unweighted convolution is not enough. No theorem is claimed from
that recurrence. These are the precise remaining mathematical obstacles.

## Verification and limits

`check_partial.py` verifies the product second derivative symbolically, twenty
exact b=2 coefficient identities, and the exact b=3 obstruction. It also makes
90 high-precision numerical checks within the proved partial range; these are
diagnostics only. The argument above, not those finite checks, establishes
the partial statement. No full source-level Lean endpoint, manuscript,
independent review, novelty clearance or packet is claimed. No external action.
