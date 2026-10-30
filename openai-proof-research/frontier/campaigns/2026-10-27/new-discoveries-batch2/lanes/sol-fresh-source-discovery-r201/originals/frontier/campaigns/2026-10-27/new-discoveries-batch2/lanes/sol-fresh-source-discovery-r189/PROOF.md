# Full ordinary proof candidate: Guo's published Conjecture 2

This is an ordinary all-order proof for independent root adjudication. No Lean,
manuscript, novelty clearance or discovery credit is claimed.

## Exact source

Victor J. W. Guo, *On a conjecture related to integer-valued polynomials*,
Bull. Math. Soc. Sci. Math. Roumanie 66(114), no.4 (2023), 449–453,
published Conjecture 2, equation (4.1), p452. Actual publisher PDF:
https://bulletin.ssmr.ro/pdf/66-4/articol_8.pdf . It is Conjecture 4.1 in
arXiv:2003.12653v1 (23 March 2020); the journal retains the same quantifiers.
For every positive integer l,n and integer 0<=k<n, the claim is

    n^2 divides (2l-1)!! sum_{m=k}^{n-1}
                   (2m+1)^{2l-1} binom(m+k,2k) binom(2k,k)^2.

All binomials below have nonnegative upper argument; they are zero when the
lower argument exceeds it. Empty products equal one. The double factorial is
1*3*...*(2l-1). No prime, parity, bounded-degree, or asymptotic restriction is added.

## 1. Uniform denominator lemma

For every k,t>=0,

    k+t+1 divides 4^t (2t+1)!! binom(2k,k).                 (A)

Proof. Put d=k+t+1 and H=2t+1. Fix a prime p dividing d, and write a=v_p(d).
Let b be the largest nonnegative integer with p^b<=H. For each j with
b<j<=a, k mod p^j = p^j-t-1, since p^j divides d and p^j>H>=t+1.
Consequently 2(k mod p^j)>=p^j: indeed p^j>=2t+2. Thus

    floor(2k/p^j)-2floor(k/p^j)=1.

Every summand of this form for arbitrary j>=1 is either zero or one.
The factorial valuation identity

    v_p(binomial(2k,k))
       = sum_{j>=1}(floor(2k/p^j)-2floor(k/p^j))

follows by counting multiples of p,p^2,... in the factorials. It is at least
max(0,a-b). If p is odd, p^b is an odd integer <=H and appears among the
factors of H!! (for b=0 no factor is needed), so v_p(H!!)>=b. If p=2,
v_2(4^t)=2t>=b: the inequality 2t+1<=2^{2t} holds for t>=1 by induction,
and for t=0 we have b=0. Hence the valuation of the right side of (A) is
at least a, for every prime divisor of d. This proves (A), including t=0.

## 2. All-degree factorial-basis identity

Fix k>=0. Define integers a_{r,t}, r>=0, by a_{0,0}=1, zero outside
0<=t<=r, and

    a_{r+1,t}=(2k+2t+1)^2 a_{r,t}+a_{r,t-1}.

For an indeterminate z define P_0(z)=1 and
P_t(z)=product_{i=0}^{t-1}(z-(2k+2i+1)^2). The relation
z P_t=P_{t+1}+(2k+2t+1)^2 P_t proves inductively

    z^r=sum_{t=0}^r a_{r,t} P_t(z).                      (B)

For every m>=k, putting z=(2m+1)^2 gives

    P_t((2m+1)^2) binom(m+k,2k)
       =4^t (2k+2t)!/(2k)! binom(m+k+t,2k+2t).          (C)

When m<k+t a factor on the left is zero and the right binomial is zero.
Otherwise each factor of P_t is 4(m-k-i)(m+k+i+1), and cancellation
of factorials proves (C). Thus this is an exact identity at every summation
index, with no division by a potentially vanishing m-dependent factor.

## 3. Exact summation and integral coefficients

For q>=0 and n>q, telescoping gives

    sum_{m=q}^{n-1}(2m+1)binom(m+q,2q)
       =n(n-q)/(q+1) binom(n+q,2q)
       =n^2 (q!)^2/((q+1)(2q)!)
                      binom(n-1,q)binom(n+q,q).         (D)

For completeness, set G(m)=m(m-q)binom(m+q,2q)/(q+1).
G(q)=0 and G(m+1)-G(m)=(2m+1)binom(m+q,2q), since the numerator
after extracting that binomial is
(m+1)(m+q+1)-m(m-q)=(q+1)(2m+1).
When q>=n both the sum and the expression containing binom(n-1,q)
are zero, so the latter version of (D) remains valid.

Let S be the unmultiplied sum in the source claim and take r=l-1 in (B).
Using (C), followed by (D) with q=k+t, yields exactly

    S/n^2 = sum_{t=0}^{l-1} a_{l-1,t} 4^t
        [(2k)! ((k+t)!)^2/(k!^4(k+t+1))]
        binom(n-1,k+t)binom(n+k+t,k+t).                 (E)

The bracket can be rewritten as

    binom(2k,k) product_{i=1}^t(k+i)^2/(k+t+1).

Lemma (A) says that multiplication of this bracket by
4^t(2t+1)!! gives an integer. Since t<=l-1, (2t+1)!! divides
(2l-1)!!. Every coefficient in (2l-1)!! times (E) is therefore an
integer. The remaining a's and binomials are integers. This proves the
source divisibility for every l,n,k in its complete scope. No finite
checker is used as a premise. In particular l=1 and n=1 need no exceptions.

## 4. Complete classical-adaptation objection for root

There is a strong routine-adaptation objection, independent of shortness.
The source's published Lemma 3 and Theorem 2 already give (D) and the l=1
case via Catalan integrality. Chen–Guo arXiv:1412.5734v1, Section 4,
equations (4.1)–(4.2), explicitly proposes expansion of arbitrary powers
in a shifted factorial/binomial basis, and uses that to prove the weaker
mod-n congruences for all odd powers. Its actual proof body was read.
Here is the entire bridge from that classical mechanism to this endpoint:
use the monic Newton basis (B), cancel the paired factors as in (C),
apply the already printed telescoping identity (D), and remove all
denominators q+1 by the elementary prime-valuation estimate (A).
Equations (A)–(E), with their proofs above, complete this bridge for
every parameter, rather than merely suggesting it. The source does not
print (A), and the inspected Chen–Guo theorem has modulus n rather than
n^2; neither is asserted to be an earlier publication of this endpoint.
Root must independently decide whether this full bridge falls under the
campaign's routine classical-adaptation exclusion. No substantive PASS
is inferred from the printed open status. No exclusion is inferred from
length alone. Bounded historical novelty remains a separate HOLD.
