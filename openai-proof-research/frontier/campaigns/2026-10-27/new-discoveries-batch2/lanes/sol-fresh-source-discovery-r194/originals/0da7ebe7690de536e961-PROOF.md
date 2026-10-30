# Two arithmetic-function ratio inequalities

This joint proof covers Dimitrov's arXiv2606.12484v1 Conjectures3 and9, recorded separately as MathDB375256 and375257. Each package counts only its own source question. Both general arguments were posted earlier by Shivam Patel; this is formal verification, without a novelty or equality-classification claim. See the paper for the full printed right-hand sides.

Let x=φ(n)^k, y=ψ(n)^k, z=σ(n)^k, a=(n−1)^k, b=(n+1)^k, with n≥2 and k≥1. The functions are the actual Euler totient, Dedekind product ∏_{p|n}p^(e_p−1)(p+1), and sum of positive divisors. The formal proof additionally proves equivalence of the Dedekind product to n∏(1+1/p).

## Arithmetic bridge

The totient satisfies 0<φ(n)≤n−1. Each Dedekind factor equals p^e+p^(e−1)>p^e; there is at least one prime divisor, so ψ(n)>n and integrality gives ψ(n)≥n+1. The factorization of σ(n) is ∏_{p|n}(1+p+…+p^e). Its last two terms bound the Dedekind factor from below. Hence ψ(n)≤σ(n). Taking positive integer powers gives

0<x≤a<b≤y≤z.

Put r=x/y, q=a/b, t=z/y. Then 0<r≤q<1 and t≥1. Every denominator below is positive.

## Simple ratio

The source expression equals S(r,t)=r/(1+t)+1/(r+t)+t/(r+1). Setting v=t−1≥0, exact common-denominator identities give

\[
S(r,t)-S(r,1)=\frac{v[2v^2+(4+r-r^2)v+r(1-r)(r+3)]}{2(t+1)(r+t)(r+1)},
\]

\[
S(r,1)-S(q,1)=\frac{(q-r)[4-(1+r)(1+q)]}{2(1+r)(1+q)}.
\]

Both are nonnegative: 4+r−r²=4+r(1−r)≥0 and (1+r)(1+q)≤4. Thus S(r,t)≥S(q,1)=(a²+ab+4b²)/(2b(a+b)). Substituting ab=(n²−1)^k gives exactly the source right-hand side in Conjecture3.

## Mixed ratio

The second source expression, after dividing by y², is

G(r,t)=r(1+t)/(rt+r+2t)+(r+t)/(2rt+r+t)+t(r+1)/(rt+2r+t).

Define

P(r,v)=(2r⁴+4r³+7r²+8r+3)v²+(4r⁴−5r³+8r²+19r+6)v+(1−r)(3r+1)(5r+3).

Exact expansion gives

G(r,t)−G(r,1)=r(t−1)P(r,t−1)/D,

where D=(r+1)(3r+1)(rt+r+2t)(rt+2r+t)(2rt+r+t)>0. The only apparently negative coefficient is harmless because

4r⁴−5r³+8r²+19r+6=4r⁴+5r²(1−r)+3r²+19r+6≥0.

The horizontal identity is

G(r,1)−G(q,1)=(q−r)(3+r+q−5rq)/[(r+1)(q+1)(3r+1)(3q+1)].

Its remaining numerator is nonnegative since rq≤r and q≥r imply 3+r+q−5rq≥3−4r+q≥3−3r≥0. Thus G(r,t)≥G(q,1)=(5a²+5ab+2b²)/[(3a+b)(a+b)]. The same power substitution gives the exact Conjecture9 bound.

## Formal correspondence

The combined `ArithmeticRatios.lean` proves all arithmetic comparisons, both homogeneous rescalings, both real certificates, and the exact source right-hand-side rewrites. `mathdb_375256` and `mathdb_375257` have only natural parameters n,k and the source lower bounds n≥2,k≥1 as hypotheses. No totient, Dedekind, divisor-sum, or homogeneity bridge is assumed. A single combined namespace permits a self-contained fresh-source rebuild; the original two development modules are retained in the provenance checkout.
