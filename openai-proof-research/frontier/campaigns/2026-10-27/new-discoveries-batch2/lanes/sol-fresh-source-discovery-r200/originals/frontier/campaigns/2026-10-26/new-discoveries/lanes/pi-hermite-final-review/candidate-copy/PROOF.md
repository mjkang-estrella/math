# Proposed full Hermite envelope theorem (MathDB 346243)

Status: complete proposed mathematical argument, NOT independently reviewed,
NOT formalized, credit 0. No novelty or priority claim. All classical ingredients
and the even-degree case are uncredited. An adversarial substantive-eligibility
and prior-art decision is required before investment in a discovery packet.

## Exact source and normalization

Guo--Liu, arXiv:2004.10441, Conjecture 1, Eq. (30), p.10; published
Commun. Theor. Phys. 73 (2021) 075002, Conjecture 1, Eq. (29), p.8,
DOI 10.1088/1572-9494/abf1dd. The actual published page was rendered and read.
Both use the physicists' Hermite polynomial
H_n(x)=(-1)^n exp(x^2) (d/dx)^n exp(-x^2).
The live MathDB record is retained with all activity arrays empty. That status
is source evidence, not evidence of novelty.

Set E=2n+1, C=2^n Gamma((n+1)/2)/sqrt(pi),
g(x)=(1-x^2/E)^(-1/2), and a=sqrt(E)(1-pi/(2E)).
The exact desired statement for every integer n>=1 and x>0 is

    |H_n(x) exp(-x^2)| <= C g(min(x,a)) exp(-x^2/2).

Write y(x)=H_n(x) exp(-x^2/2). It suffices to show

    |y(x)| <= C g(x)           (0<=x<sqrt(E)),              (B)
    |y(x)| <= C g(a)           (x>=0).                     (T)

Indeed 0<a<sqrt(E), so use (B) for x<=a and (T) for x>=a.
Below, a global bound (T) is obtained from classical Cramer--Indritz; the new
proposed part is the exact odd-degree coefficient in (B), not that classical
global estimate or the even-degree energy argument.

## 1. Energy and even degrees

The Hermite equation gives y''+(E-x^2)y=0. Therefore

    B(x)=(E-x^2)y(x)^2+y'(x)^2,    B'(x)=-2x y(x)^2.       (1)

In particular B is nonincreasing for x>=0. For even n, y'(0)=0 and
|y(0)|=C, by the standard half-integer Gamma identity. Thus
(E-x^2)y(x)^2<=B(x)<=E C^2 whenever 0<=x<sqrt(E), proving (B).

## 2. Two exact Wallis comparisons for odd degrees

For n=2m+1, change the sign of y if necessary so that y(0)=0 and
y'(0)=A=2(2m+1)(2m)!/m!>0. Then E=4m+3,
C=2^(2m+1)m!/sqrt(pi), and define

    gamma_m = A^2/(E C^2)
            = pi (2m+1)^2 binom(2m,m)^2 / ((4m+3)16^m),
    r_m = 2(4m+3)^2 / (2(4m+3)^2-1).

The classical Wallis limit gives gamma_m -> 1. Direct cancellation gives

    gamma_(m+1)/gamma_m = 1-1/[4(m+1)^2(4m+7)] < 1,

and, writing delta_m=gamma_m/r_m,

    delta_(m+1)/delta_m - 1
      = (176m^2+440m+247)
        / [4(m+1)^2(4m+7)^3(32m^2+48m+17)] > 0.           (2)

Since delta_m ->1 and is strictly increasing, gamma_m<r_m for every m>=0.
For m>=1, also gamma_m<=gamma_1=9pi/28<99/98, using pi<22/7.
The strict comparison to r_m is what will absorb the energy lost near zero.
Neither the Wallis limit nor this finite rational cancellation is claimed as
a discovery by itself.

## 3. Sine comparison on a short initial interval

Assume m>=1, so E>=7. Put x0=sqrt(2/E), q0=E-2/E>0,
c=sqrt(1-2/E^2), and u=sqrt(E)x. On 0<=x<=x0,

    (A/sqrt(E)) sin(sqrt(E)x) <= y(x)
      <= (A/sqrt(q0)) sin(sqrt(q0)x).                     (3)

Here is a positivity-safe proof, rather than an assumed comparison. There is
a positive neighborhood of 0 where y>0, since y'(0)>0. If its first positive
zero z were <=x0, variation of constants in y''+E y=x^2 y on [0,z] would give

    y(z)=A sin(sqrt(E)z)/sqrt(E)
         + integral_0^z sin(sqrt(E)(z-t)) t^2 y(t)/sqrt(E) dt >0,

because sqrt(E)z<=sqrt(2)<pi. This contradicts y(z)=0. Thus y is positive on
(0,x0]. The same formula gives the lower bound in (3). For the upper bound use
y''+q0 y=-(x0^2-x^2)y; its variation-of-constants integral is nonpositive,
since all its sine kernels have phase between 0 and sqrt(2)<pi.

## 4. Bound before x0

For 0<u<=sqrt(2), set

    M(u)=(1-u^2/E^2) sin(cu)^2.

It is increasing. Indeed logarithmic differentiation reduces this to

    c cot(cu) > u/(E^2-u^2).

Here c>9/10, cu<=sqrt(2)<pi/2, and cot is decreasing. Alternating Taylor
bounds give cos(sqrt(2))>=7/45 and sin(sqrt(2))<1, so the left side is
>7/50. The right side is <=(3/2)/(49-2)=3/94<7/50.
Consequently (3) and q=E-x^2 give

    q y(x)^2/(E C^2) <= gamma_m M(u)/c^2
      <= gamma_m sin(c sqrt(2))^2
      <= gamma_m sin(sqrt(2))^2 < (99/98)(49/50)=99/100<1. (4)

We used sin(sqrt(2))<=sqrt(2)(1-2/6+4/120)=(7/10)sqrt(2).
This proves (B) up to x0. Continuity covers u=0 without logarithms.

## 5. Energy loss at x0 and the rest of the bulk

From (1) and the lower bound in (3),

    B(0)-B(x0) >= (2A^2/E^2) integral_0^sqrt(2) u sin(u)^2 du.

On [1,sqrt(2)] we have sin(u)>=sin(1)>5/6, and
integral_1^sqrt(2) u du=1/2. The last integral is therefore >25/72>1/4.
It follows that

    B(x0) < A^2(1-1/(2E^2)) < E C^2,                    (5)

where the second inequality is exactly gamma_m<r_m from (2).
For x0<=x<sqrt(E), use (1) again to obtain
(E-x^2)y(x)^2<=B(x)<=B(x0)<E C^2. This completes (B) for all odd n>=3.

For n=1, y=2x exp(-x^2/2), C=2/sqrt(pi), E=3. Put v=x^2 in [0,3].
The squared assertion is pi v(1-v/3)<=exp(v). Since pi<22/7 and
exp(v)>=1+v+v^2/2, it suffices to note

    1+v+v^2/2-(22/7)v(1-v/3)
       =1-15v/7+65v^2/42 >0.

The last quadratic has positive leading coefficient and negative discriminant.

## 6. The clamped tail, with explicit classical attribution

Use the classical Cramer--Indritz inequality (DLMF 18.14.9):

    |H_n(x) exp(-x^2/2)| <= sqrt(2^n n!)    for real x.    (6)

No new-result credit is claimed for (6). Let S_n=(2^n n!)/C^2. Duplication and
log-convexity of Gamma give

    S_n=sqrt(pi) Gamma((n+2)/2)/Gamma((n+1)/2)
       <=sqrt(pi(n+1)/2).

Also g(a)^2=1/[pi/E-pi^2/(4E^2)]>E/pi. For n>=4,
pi^3(n+1)<2(2n+1)^2, hence S_n<g(a)^2, proving (T).
For completeness the displayed polynomial inequality follows by replacing
pi^3 by (22/7)^3, writing n=4+k, and observing that all coefficients of
2(2n+1)^2-(22/7)^3(n+1) in k are positive.

For n=3, S_3=3pi/4 and

    S_3/g(a)^2=(3pi^2/28)(1-pi/28)
       <(30/28)(25/28)=750/784<1,

using pi^2<10 and pi>3, so (6) again proves (T).

For n=2, direct differentiation gives
sup_(x>=0)|(4x^2-2)exp(-x^2/2)|=max(2,8exp(-5/4))<5/2.
The latter exponential bound follows from exp(5/4)>16/5 using four Taylor
terms. Meanwhile C_2 g(a)>2sqrt(5/pi)>5/2, since pi<16/5.

For n=1, the maximum of 2x exp(-x^2/2) is 2exp(-1/2)<5/4,
since exp(1)>64/25 by its first four Taylor terms. Finally

    [C_1 g(a)]^2=12/[pi^2(1-pi/12)]>196/121>25/16,

using 3<pi<22/7. Thus (T) holds also for n=1,2.
Combining (B) and (T) proves the entire literal conjecture.

## 7. Prior-art comparison and unresolved gates

The actual Foster--Krasikov (2000) primary PDF, Theorem 1, pp307--308, has
been read, including its odd-degree normalization. Its upper envelope at x=0
for n=3 has squared-bound/C^2 ratio about 1.001382658>1, and it blows up at
x^2=2n-3/2. Thus that displayed bound alone does not imply (B) over its full
range. This is not a proof that the proposed result is substantive: combinations
with small-x estimates, energy, or other classical bounds may still make the
source question an immediate known corollary. An independent review must test
that issue. Krasikov (2004), actual math/0401310 Theorems 1 and 2, has also been
read; its global maximum bounds are different. DLMF (6) resolves the tail only.

Initial targeted searches found the source statement and these classical bodies,
but this is NOT a completed novelty screen. The citing corpus, current versions,
public problem/proof registries, author followups, older Sonin/Szego bounds, and
any stronger odd-degree coefficient theorem still require assessment. No
independent review, literal Lean endpoint, manuscript, packet, or discovery credit
exists at this checkpoint.
