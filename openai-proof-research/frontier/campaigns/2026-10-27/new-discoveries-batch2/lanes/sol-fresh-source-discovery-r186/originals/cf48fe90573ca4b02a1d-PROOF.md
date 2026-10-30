# Proposed full ordinary proof of Conjecture 4.7

Status: complete proposed **computer-assisted exact ordinary proof**, awaiting independent review. The finite arithmetic certificate is part of the proof, not a numerical experiment. No Lean certificate or acceptance is claimed. Date: 2026-10-29 UTC.

## Statement and conventions

Let d=sqrt(17), alpha=(5+d)/2, beta=(5-d)/2. Thus alpha+beta=5, alpha-beta=d, alpha beta=2, and alpha,beta>0. For either (p,q)=(d,beta) or (-d,alpha), and every distinct a,b>0, define

M(a,b)=(b-a)/(sqrt(2) atan(log(b/a)/sqrt(2))),
B_r(a,b)=((a^r+b^r)/2)^(1/r).

We prove M(a,b)<B_p(M(a,B_q(a,b)),M(B_q(a,b),b)). M(a,a)=a by continuity. This is the literal nesting in arXiv:2405.13618v2, Definition 1.1, (1.5), Conjecture 4.7; the distinct-input convention follows the usual strict mean order. No assertion of strictness on the diagonal.

## 1. A classical exact comparison mean

Set

S(a,b)=[beta/alpha * (b^alpha-a^alpha)/(b^beta-a^beta)]^(1/d).

S is symmetric and homogeneous and has diagonal value a. Its stabilizability is classical (Raissouli 2011 preprint, Theorem 3.1); here is the required identity without reliance on that theorem.
For either branch set r=p+q, so {r,q}={alpha,beta}. Then

S(a,b)^p = q/r * (b^r-a^r)/(b^q-a^q).

If c=B_q(a,b) and a<b, then a<c<b and c^q-a^q=b^q-c^q=(b^q-a^q)/2. Adding the two corresponding identities gives

(S(a,c)^p+S(c,b)^p)/2=S(a,b)^p.

Positive real powers are injective also for negative p, so
B_p(S(a,c),S(c,b))=S(a,b) for BOTH branches.

Write the centered logarithms

g(t)=log M(e^-t,e^t)=log(sqrt(2)sinh(t)/atan(sqrt(2)t)),
f(t)=log S(e^-t,e^t)=1/d log[beta sinh(alpha t)/(alpha sinh(beta t))].

Both extend continuously with value zero at t=0. We shall prove k=f-g is strictly increasing on (0,infinity). This is the substantive comparison, not an inference from the mere order M<S.

## 2. Transfer of the increasing logarithmic ratio

Assume k is strictly increasing. Let t=log(b/a)/2, x=log(c/a)/2, y=log(b/c)/2. Then x,y>0 and x+y=t, hence k(x),k(y)<k(t). By homogeneity,

M(a,c)=S(a,c)e^-k(x)>S(a,c)e^-k(t),
M(c,b)>S(c,b)e^-k(t).

B_p is homogeneous and strictly increasing in each positive argument for every nonzero real p: its partial derivative is (1/2)u^(p-1)B_p(u,v)^(1-p)>0. Therefore

B_p(M(a,c),M(c,b))>e^-k(t)B_p(S(a,c),S(c,b))
=e^-k(t)S(a,b)=M(a,b).

Symmetry covers b<a. Thus only the global differential comparison remains.

## 3. Remove the inverse tangent by differential comparison

For t>0 set

A(t)=[cosh(4t)-cosh(t)cosh(dt)+(5/d)sinh(t)sinh(dt)]/2,
B(t)=sinh(t)[cosh(5t)-cosh(dt)]/2.

B>0 because 5>d. Direct hyperbolic addition formulas give

B=sinh(t)sinh(alpha t)sinh(beta t),
A/B=coth(t)-[alpha coth(alpha t)-beta coth(beta t)]/d.

Also A>0. Indeed, twice its derivative of order 2j at zero is

4^(2j)+(5/d-1)(d+1)^(2j)/2-(5/d+1)(d-1)^(2j)/2.

It vanishes at j=0. For j>=1 the first term already exceeds the absolute value of the last: 4<d<17/4 implies (5/d+1)/2<9/8 and d-1<13/4, while (16/13)^2>9/8. The middle term is positive because d<5. Its entire Taylor series therefore proves A(t)>0 for t>0. Expanding at zero gives A(t)=2t²+O(t⁴), B(t)=2t³+O(t⁵).

Define J(t)=sqrt(2)B(t)/[(1+2t²)A(t)]. Then J(t)->0 as t->0. Put

U=B'A-BA'-A², V=-4BA, E=(1+2t²)U+tV.

Differentiation, with every denominator positive, gives

J'(t)-sqrt(2)/(1+2t²)
= sqrt(2) E(t)/[(1+2t²)² A(t)²].

Section 4 proves E(t)>0 for every t>0. Integration from zero therefore gives J(t)>atan(sqrt(2)t). Consequently

k'(t)=f'(t)-g'(t)
=sqrt(2)/[(1+2t²)atan(sqrt(2)t)]-A(t)/B(t)>0.

This proves the hypothesis of Section 2 and finishes the full source statement.

## 4. Global positivity of the entire function E

The following is an exact finite-arithmetic plus analytic-tail proof. There is no finite-range sampling and no assertion that finitely many positive Taylor coefficients alone imply the result.

Write E(t)=sum e_n t^n/n!. All odd e_n vanish. We prove e_n=0 for even n<10 and e_n>0 for every even n>=10.

### 4a. Finite certificate, n<300

Here are explicit integer recurrences sufficient to verify every finite assertion. Set A_n=A^(n)(0), B_n=B^(n)(0). For even n,

2 A_n=4^n-sum_(even j=0..n) binom(n,j)17^(j/2)
                 +5 sum_(odd j=1..n) binom(n,j)17^((j-1)/2),
B_n=0.

For odd n, A_n=0 and

2 B_n=sum_(even j=0..n) binom(n,j)(5^j-17^(j/2)).

These follow by multiplying the entire sinh/cosh series. With negative subscripts interpreted as zero, set

U_n=sum_(j=0..n) binom(n,j)[B_(j+1)A_(n-j)-B_j A_(n-j+1)-A_j A_(n-j)],
V_n=-4 sum_(j=0..n) binom(n,j)B_j A_(n-j),
e_n=U_n+n V_(n-1)+2n(n-1)U_(n-2).

Exact integer evaluation gives e_0=e_2=e_4=e_6=e_8=0; all 145 values e_10,e_12,...,e_298 are strictly positive. The first four are 37847040, 19891322880, 5550283554816, 1162696473968640. The complete integer values, not decimal approximations, are in `integer-certificate.json`. `integercheck.py` is a self-contained standard-library reproduction of exactly the displayed recurrences, with assertions of every sign. No floating point is used. A separately implemented exponential expansion in Q(sqrt(17)), `expcheck.py`, agrees on EVERY finite value.

### 4b. Uniform tail, n>=300

Expand U=sum u_lambda exp(lambda t), V=sum v_lambda exp(lambda t), combining equal exponents. This is a finite exact expansion obtained from the displayed A,B. U is even, V is odd. Let L=7+d and R=41/4. The two largest absolute exponents are +/-L, and every remaining exponent has absolute value <R. Direct multiplication gives

u=u_L=(-85+21d)/544>1/1000,
v=v_L=(17-5d)/272>-1/50,
u_-L=u, v_-L=-v.

Moreover 11<L<12, sum |u_lambda|<10, sum |v_lambda|<10. These finite field identities and inequalities are also verified exactly in `expcheck.py`, by rational arithmetic and squared comparisons in Q(sqrt(17)). Its map operations literally implement addition, multiplication and differentiation of the A,B expressions; no fitted coefficients or unproved special-function facts enter.

For even n the contribution of +/-L to e_n is

2 L^(n-2)[u L²+n v L+2n(n-1)u].

For n>=300 its bracket exceeds

(2/1000)n(n-1)-(12/50)n
= (2/1000)n²-(242/1000)n >= (1/1000)n².

The absolute value of ALL remaining contributions is bounded by

R^(n-2)[10R²+10nR+20n(n-1)] <22 n² R^(n-2)

for n>=300 (use R<11 and divide by n²). Consequently

e_n > n²[(1/500)L^(n-2)-22 R^(n-2)] >0,

since L/R>44/41>1 and (44/41)^298>11000. The last inequality is a single exact integer inequality, checked in `expcheck.py` as well. This proves positivity uniformly for every even n>=300.

Together with 4a and entire convergence, E(t)=sum_(even n>=10) e_n t^n/n!>0 for EVERY t>0. The differential comparison and transfer are therefore global, including arbitrarily large input ratios.

## Scope, novelty limits and review objection

The stable Stolarsky identity, transfer idea, differentiation, and exact arithmetic methods are classical tools and receive no separate discovery credit. The proposed substantive output is only the full two-branch source inequality. No global priority claim follows from the bounded registry/path and web searches. The actual 2026 journal body remains unavailable under inherited access limits; the proven target is explicitly arXiv v2. No campaign acceptance or count change is made.

The strongest review objection is the exact computer-assisted finite certificate and the bookkeeping of its all-order tail: these require independent replay and mathematical audit before treating this as an established outcome. This is not yet a Lean proof. The proof has no identified unresolved analytic premise; the finite arithmetic is supplied openly as a proof dependency, not hidden behind numerical evidence.
