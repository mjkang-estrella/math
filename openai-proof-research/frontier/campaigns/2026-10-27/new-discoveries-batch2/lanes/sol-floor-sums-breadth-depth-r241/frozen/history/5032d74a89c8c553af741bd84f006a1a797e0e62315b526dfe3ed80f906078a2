# Richardson follow-up: exact kernel reduction, unresolved prime-power lift

No nomination, no count credit, no full PROOF. Root alone accepts/counts/stages. Administrative snapshot: 9 additional, 39 total, next 40. This is explicitly a follow-up to r214, not a NEW scout.

## Literal source and chronology

Richardson, *The Filbert Matrix*, arXiv:math/9905079v1, 12 May 1999, Definition 1.1 and Conjecture 5.1, printed preprint p5. Definition 1.1 indexes reciprocal Hankel entries by a_(i+j-1), with 1<=i,j<=n; b_k(r)=binom(k+r-1,r). Hence the requested matrix is literally R_ij=1/binom(i+j+r-2,r). For every positive integer n,r, the conjecture says its inverse is integral iff n is 0 or 1 modulo every prime power dividing r. Equivalently r divides n(n-1). Prime powers mean each maximal p^v_p(r) suffices; mixed CRT choices are allowed.

The actual journal body was obtained early, lawfully: https://www.fq.math.ca/Scanned/39-3/richardson.pdf . The issue page https://www.fq.math.ca/39-3.html identifies the article starting at268 and the next at276, i.e. Fibonacci Quarterly39(3)(2001),268–275. It retains Conjecture5.1 and Theorem5.2. It is not evidence that the conjecture remained open after2001. Actual citing body: Berg, https://arxiv.org/pdf/math/0609283 , v2 dated5 August2010, Theorem2.1 with its kernel proof and the introductory comparison with Richardson, plus Section4's shifted single-reciprocal Hilbert family. Its generic kernel theorem supplies the inversion bridge below; the specific Fibonacci and shifted-Hilbert integrality statements do not supply the reciprocal-binomial prime-power divisibility. The retrieved Berg PDF has an anomalous footer dated26 November2024 despite its arXiv v2 stamp; preserve that discrepancy, rather than silently equating footer and publication date. No newer journal version for Berg was authenticated.

The Richardson arXiv body, journal Conj5.1/Thm5.2, and Berg's actual kernel theorem/proof were read. Theorem5.2's inverse is credited, not rediscovered. Current arXiv searches for reciprocal Hankel, Richardson Filbert, and inverse binomial Hankel integrality are bounded keyword searches, not complete citation coverage. Inherited GitHub registry, ScienceDirect and Google challenge denials were not retried. No current complete proof-registry head/body is authenticated. No novelty or exclusion follows from elementary-looking formulas.

## Complete classical beta/Jacobi bridge

Use zero-based i,j=0,...,n-1 for the remainder. Define dmu=r(1-x)^(r-1)dx on[0,1]. The beta integral gives

    integral x^s dmu = r*s!*(r-1)!/(s+r)! = 1/binom(s+r,r).

Thus R is exactly its moment Gram matrix and is positive definite. Put

    Q_k(x) = sum_(i=0)^k c_(k,i) x^i,
    c_(k,i) = (-1)^i binom(k,i) binom(k+r+i-1,i).

These are shifted Jacobi polynomials P_k^(0,r-1)(1-2x), equivalently (-1)^k P_k^(r-1,0)(2x-1). The coefficient formula and Rodrigues formula below specify the normalization independently of convention. In particular Q_k(0)=1.

    Q_k(x) = [k! (1-x)^(r-1)]^(-1)
             d^k/dx^k [x^k(1-x)^(k+r-1)].

Leibniz expansion proves the displayed integer coefficients. Integration by parts k times, with all boundary terms zero because x^k(1-x)^(k+r-1) and its first k-1 derivatives vanish at both endpoints, proves orthogonality to every polynomial of degree<k. The leading coefficient is L_k=(-1)^k binom(2k+r-1,k). The same integrations with Q_k itself give

    integral Q_k^2 (1-x)^(r-1)dx
      = (-1)^k L_k Beta(k+1,k+r) = 1/(2k+r).

Consequently C R C^T = diag(r/(2k+r)), where C is the lower triangular coefficient matrix. Its nonzero diagonal makes it invertible. Inverting this identity gives the exact all-n,r factorization

    R^(-1) = (1/r) C^T diag(2k+r) C,
    (R^(-1))_ij = (1/r) sum_(k=max(i,j))^(n-1)
                              (2k+r)c_(k,i)c_(k,j).                 (K)

This is a full bridge to the general inverse, not merely a numerical fit. It also proves that every denominator divides r. For the first corner c_(k,0)=1, so

    (R^(-1))_00 = n(n+r-1)/r = n+n(n-1)/r.                         (C)

The last row has just one summand:

    (R^(-1))_(n-1,j) = (-1)^(n-1+j)(2n+r-2)/r
       *binom(2n+r-3,n-1)*binom(n-1,j)*binom(n+r+j-2,j).

Equation(C) proves the FULL necessary direction, uniformly. Since gcd(n,n-1)=1, r|n(n-1) iff every maximal prime power dividing r divides either n or n-1. No corner-only sufficiency is inferred.

## Uniform squarefree sufficiency (partial result, zero credit)

Here is a complete proof of the mod-p part of sufficiency, including arbitrarily large indices. Write r=pR, i=pI+b and k=pt+a with 0<=a,b<p. For a!=0, Lucas' theorem gives

    c_(pt+a,i) = (-1)^i H_i(t) f_b(a) mod p,
    H_i(t)=binom(t,I)binom(t+R+I,I),
    f_b(a)=binom(a,b)binom(a+b-1,b),

where the value is zero unless b<=a<=p-b when b>0. Indeed a<b kills the first binomial, and a+b-1>=p kills the low digit of the second; on the surviving range the upper high digit is t+R+I. When b=0 the same formula holds for every a!=0 with f_0(a)=1. This also covers i>k by the zero binomial convention. The a=0 terms can be discarded since their weight 2k+r is divisible by p.

For a=1,...,p-1, f_b(p-a)=f_b(a) mod p: replacing a by -a in each of the two binomials introduces two factors (-1)^b and interchanges their factors. The support interval is symmetric too. Hence the product c_(pt+a,i)c_(pt+a,j) is unchanged under a->p-a, while 2k+r changes sign. Every full block of p terms in(K)'s numerator therefore sums to zero mod p. For p=2 each weight is already zero. If n=0 mod p the sum consists of full blocks. If n=1 mod p there is one additional a=0 term, also zero. Thus p divides every numerator in(K) whenever p|r and n=0 or1 mod p.

If r is squarefree and r|n(n-1), applying this argument to each prime dividing r makes every numerator divisible by r. Combined with(C), this proves the complete iff for squarefree r. This partial parameter family is not nominated. The beta/kernel and Lucas tools are classical; no separate discovery credit is requested for any helper or case.

## Exact outstanding lift

For p^e|r, e>=2, a sufficient missing statement is

    sum_(k=t*p^e)^((t+1)*p^e-1) (2k+r)c_(k,i)c_(k,j) = 0 mod p^e

for all t,i,j>=0, interpreting c_(k,i)=0 when i>k. Full blocks and an extra k divisible by p^e would settle n=0 or1 mod p^e. This block lemma is consistent with the finite controls but NOT proved. It is stronger than the exact source endpoint because it also asks prime-power integrality of sizes independently of the other prime factors of r. Lucas modulo p cannot simply be reused modulo p^e; factorial denominators and carries change the high-digit factors.

For i,j<p there is an additional limited bridge: write c as products of (k-h)(k+r+h)/(i!)^2, with p-unit denominators. It is invariant under k->-k-r. Pairing the complete residue system modulo p^e by that involution cancels the weight2k+r (fixed points have weight0, including the even-prime case interpreted directly). Thus the block lemma holds for i,j<p, all e, with these p-unit denominators. It does not cover large row indices and is not a full proof. The decisive next step is a prime-power replacement for the Lucas factorization controlling the nonunit factorial denominators, or a legitimate citing theorem explicitly delivering this block congruence. No larger finite sweep substitutes for it.

## Controls and limits

checks.py verifies144 exact rational matrix products (r1..16,n1..9),4608 full denominator cases(r1..96,n1..48), and7614 block-entry controls. It checks the stronger observed denominator law lcm denominators=r/gcd(r,n(n-1)); that law is unproved here beyond the demonstrated cases. These controls validate transcription and algebra, not the uniform lift or literature status. Tyszka's arbitrary-subgroup fallback was not invested in: a rational Cramer solution alone still does not preserve subgroup denominators.
