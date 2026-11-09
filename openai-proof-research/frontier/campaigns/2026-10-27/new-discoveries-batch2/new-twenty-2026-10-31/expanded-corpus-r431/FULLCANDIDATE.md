# 326886: complete ordinary proof, NOT a qualified survivor
This document records a full ordinary derivation only. Novelty/significance is HOLD, not PASS. No formal execution, independent approval, or acceptance is claimed.

Literal: p is an odd prime, r=p-1, k is a positive integer, E=F_(p^(rk)), a nonzero in E, a^(p^k-1)=-1, d=(p^(rk)-1)/(p^k-1)+1. Then a^(-1) X^d is a complete permutation polynomial. Positive k and finite-field conventions are standing source conditions.

Primary read: sources/cpp.pdf, arXiv1312.4716v2, pages1–3 definitions and Lemmas4–5, section4 standing hypotheses, Conjecture2 and Remark5/Theorem5 on page13. These relevant statements and proof bodies were text-extracted and read. No diagram is needed. The manuscript reduces this conjecture to the base-field polynomial below and proves k=1; that instance is not a new outcome. Latest/final2015 manuscript was identified through search, not acquired. Its exact changes remain unpaid.

## A nonsquare lemma, proved here by ordinary algebra
Let K be any finite field of odd characteristic p, and let b in K be nonsquare (in particular b is nonzero). Set m=(p-1)/2 and H(t)=t(t^2-b)^m. Then H permutes K.

Every t^2-b is nonzero. Suppose H(x)=H(y). If either input is zero, both are zero. Otherwise put U=x^2-b, V=y^2-b and z=U/V, all nonzero. Squaring the equality gives x^2 z^(p-1)=y^2. Since x^2=z y^2+b(1-z), substitution gives
y^2(z^p-1)=b(z-1)z^(p-1).
In characteristic p, z^p-1=(z-1)^p. If z differs from1, division gives
b=y^2 ((z-1)/z)^(p-1)
 =[y ((z-1)/z)^m]^2,
contradicting nonsquareness. Thus z=1, U=V, and the original equality x U^m=y U^m implies x=y. Injectivity on finite K proves bijectivity. This proof uses no finite enumeration or experiment. The zero-input and division cases are explicitly separated.

## Full norm-fiber proof of the literal
Put q=p^k, Q=q^r and N=(Q-1)/(q-1). Let K=F_q inside E. From a^q=-a and odd characteristic, a is not in K and a^(q^2)=a. Hence b=a^2 lies in K and is nonsquare there: if b=c^2 with c in K, (a-c)(a+c)=0 in E forces a=+c or -c, a contradiction. Since r is even, this quadratic subfield is compatible with E.

The power map x -> x^(N+1) permutes E. Indeed gcd(N,N+1)=1. Any common divisor of N+1 and (q-1)N must divide q-1, while N+1 is congruent to r+1=p modulo q-1. Because p does not divide q-1, the gcd is1. The usual Bezout inverse exponent proves bijectivity of the nonzero power map; zero is its own unique preimage. Multiplication by a^(-1) also permutes E.

It remains to prove F(x)=x^d+ax=x(Norm_(E/K)(x)+a) permutes E. For t in K, the q-Frobenius conjugates of a alternate a,-a. The product over r=p-1 conjugates therefore gives
Norm_(E/K)(t+a)=(t^2-b)^m.
Consequently Norm(F(x))=H(Norm(x)). If F(x)=F(y), the nonsquare lemma yields Norm(x)=Norm(y)=t. Then (t+a)x=(t+a)y. Since a is not in K, t+a is nonzero, so x=y. Finite injectivity proves F bijective. Finally a^(-1)F(x)=a^(-1)x^d+x is bijective, so both required polynomials are permutations. This covers every admissible a, every odd p, and every positive k.

## Second route and failed shortcuts
The source Lemma5 gives the alternative reduction directly:
h_a(t)=t product_(i=0)^(r-1)(t+a^(q^i))=t(t^2-b)^m.
The nonsquare lemma and the same gcd argument close that route. The norm-fiber derivation above supplies the bridge independently rather than treating Lemma5 as an unchecked black box.

A tempting k=1 argument says (t^2-b)^m=+1 or -1. This works over F_p, but for k>1 the exponent is (p-1)/2, not (q-1)/2, and the sign assertion fails. The ratio argument repairs precisely that gap without changing the exponent. A character-sum approach would require cancellation for every nonzero additive character; no unproved such cancellation is used. Squaring outputs alone loses signs; the last cancellation with U^m restores them.

## Concrete contrary prior claim and significance gate
Native searches (full responses saved) identify Feng–Lin–Wang–Wang, Further results on complete permutation monomials over finite fields, arXiv1708.06955 / final DOI10.1016/j.ffa.2019.01.003. They report the exact characteristic-prime conjecture as already proved by Ma et al., Theorem3.2, and their own Theorem5 as an extension. This predates this lane. These excerpts are navigation, not authenticated proof bodies.

The selected DOI GET followed one redirect and delivered only 2684-byte Redirecting HTML. The article, including arXiv1708.06955 and alternate deliveries, is now unavailable under the lane's artifact-wide rule. No retry was made. Ma et al.'s actual Theorem3.2 proof has not been acquired or read; its bibliographic reference is not completely recovered. Thus this is a specific prior HOLD. Do not promote to a completed primary-body exclusion on excerpts alone.

Strongest case for significance: the displayed proof is a complete uniform all-parameter argument and fixes the k=1-to-general-k gap by an explicit collision obstruction. Shortness alone does not show a routine adaptation. Strongest contrary case: the target itself is explicitly reported resolved years earlier, including a theorem with the same scope; no new discovery credit is defensible without settling that specific comparison. Neither root-page nonmatches nor empty database solutions clear it.
