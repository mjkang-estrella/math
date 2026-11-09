# W014 Card C review: preregistered fixed algebra certificate

Written 2026-10-08 before certificate.py was written or run. This is an exact
identity certificate on a FIXED predeclared case list, not a timing run, a
parameter/prime/degree sweep, or evidence of asymptotic cost. Every result,
pass or fail, is retained in certificate-output.json and the run manifest.
The script is run exactly once with `python3 -I certificate.py`; if it fails,
the failure is reported, not silently rerun with edits.

## Fixed semiprime cases (distinct odd primes)

(7,11), (13,17), (101,103), (997,1009), (10007,10009).

For each: d = smallest integer >= 2 with Jacobi(d,N) = -1. The inert prime is
named p ((d/p)=-1), the split prime q ((d/q)=+1); the script also records the
opposite labeling to confirm the sign rule.

## Assertions

A1 Jacobi(d,N)=-1 implies exactly one local Legendre symbol is -1.
A2 For every a in 0..min(N,2000)-1: gcd(a^2-d,N) is in {1,q}; never p or N.
A3 For each tested a with gcd 1: z=(a+t)/(a-t) has norm 1 mod N;
   z^(p+1)=1 mod p; z^(q-1)=1 mod q; z^p = conj(z) mod p.
A4 z^(N-1) = z^(p-q) mod N (p inert). With opposite labeling the exponent
   would be q-p; record whether z^(N-1)=z^(q-p) as well (expected only when
   z has order dividing 2|p-q| -- recorded, not asserted).
A5 u^(N+1) = u^(p+q) mod N for the fixed units u = 2,3,5 (when coprime).
A6 (C1): (u,z)^p * (u,z^-1)^q = (u^(N+1), z^(N-1)); S^2-D^2=4N.
A7 Cayley count at p (cases with p<=2000): a in F_p -> z mod p is injective
   and misses exactly z=1 in the norm-one group of order p+1.
A8 Block rewrite: for the true p, any block X<=p<X+H, integers b>=1,a,q0,
   T^b = g^(bX) hb^(bq0) (g^b hb^a)^h hb^e' with h=p-X, e'=bq-bq0-ah.
   Fixed choice: X=p-3, H=8, b=3, a=round(-3*q/p), q0=round(N/X).
A9 Inert-component exponent rule: for w in R^* (full unit group, fixed
   w=1+2t, 3+t), w^p = conj(w) mod p and w^(e0+e1*p) = w^e0 * conj(w)^e1
   mod p for e0,e1 in {-2..2}.
A10 Affine public-exponent classification, finite illustration: for
   a,b,alpha,beta in -2..2 (a,b not both 0), record which (a,b,alpha,beta)
   satisfy u^(ap+bq)=u^(alpha+beta*N) for u=2,3 AND z^(ap+bq)=z^(alpha+beta*N)
   on ALL five cases. Expected: G-channel survivors have a=b=alpha=beta;
   torus survivors have b=-a, alpha=-a, beta=a. This finite check only
   illustrates the general proof in the report.
A11 S-range per block: for the fixed blocks of A8, |S(X+H-1)-S(X)| <= H-1
   where S(x)=x+N/x as a rational, x >= sqrt(N) (larger factor parameterization).

## Non-semiprime scope controls (recorded, not asserted as theorems)

N=121 (prime square): count of d<N with Jacobi(d,N)=-1 (expected 0).
N=105=3*5*7: for u=2, record whether u^(N+1)=u^(a+b) for each split a*b=N
   with 1<a<b (expected: the identity fails, scope is semiprime-only).
