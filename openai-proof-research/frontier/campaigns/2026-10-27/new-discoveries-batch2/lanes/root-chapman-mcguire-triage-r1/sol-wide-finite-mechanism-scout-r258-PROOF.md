# Odd-characteristic full refutation; eligibility HOLD

This is a mathematical refutation of Chapman–McGuire, arXiv:2102.02081v1 (3 February 2021), Section 3 Conjectures 1 and 2, one family only. It is not a novelty clearance or an accepted outcome. Independent mathematical/source/substantive review is required. No Lean or manuscript was made.

## Literal source scope

The source introduces any prime power q, n>=4, and 1<d<n dividing n. For x in F_(q^n), alpha=x^(q^d-1), R_d(x)=x+x^q+...+x^(q^(d-2))+x^(q^(d-1)+q^d-1). Section 3 works with alpha not 0 or 1 and with the denominators in Eq(12) nonzero. Eq(12) is

 (1-alpha^(q+1))/(1-alpha^(q+1))^(q^d)
   = alpha^(1-q^(d-1)) (1-alpha)/(1-alpha)^(q^d).

Eq(13) is alpha^((q^n-1)/(q^d-1))=1. Conjecture 1 says that for d=2 Eq(12) implies alpha^(q+2)=1. Conjecture 2 adds Eq(13). The final remarks specify even n. We satisfy the stronger actual R_d(x) condition as well as both equations, with odd q and even n; no excluded characteristic or missing-source hypothesis is exploited.

## Route A: direct field certificate

All following polynomials have coefficients in F3. Put

 g(Z)=Z^7+Z^6-Z^4-Z^2-Z-1.

This polynomial is irreducible. Here is a short reproducible certificate, rather than a numerical irreducibility assertion. The successive residues of Z^(3^i) modulo g for i=1,...,7 are:

 Z^3;
 -Z^5-Z^4+Z^2+1;
 Z^6+Z^5+Z^4+Z^2+Z+1;
 Z^6+Z^5-Z^4+Z^2+Z+1;
 Z^6+Z^5-Z^4+1;
 Z^5-Z^4-Z^3+1;
 Z.

Each line is obtained by cubing the previous line and substituting Z^7=-Z^6+Z^4+Z^2+Z+1. Also g(0)=2,g(1)=1,g(2)=1. Since g divides Z^(3^7)-Z, each irreducible factor has degree dividing 7. Since 7 is prime and g has no linear factor, g is irreducible. This uses the standard finite-field factorization of X^(p^m)-X; it is not a bounded search for a conjecture witness.

Let K=F3[Z]/(g), and x be the class of Z. Then K is F_(3^7), embedded in F_(3^14) because 7 divides 14. Set q=3,n=14,d=2 and alpha=x^8. The identity

 Z^11+Z+1 = g(Z)(Z^4-Z^3+Z^2-1)

gives R_2(x)=x+x^11=-1 in F3. In particular, the original curve condition holds. The element x is nonzero, because g(0) is nonzero. Its minimal polynomial has degree 7. Therefore alpha is not 1 (otherwise x is a root of Z^8-1 and, more specifically, alpha's explicit degree-six residue below rules this out). Direct reduction gives

 alpha=-1+x^3-x^4+x^5+x^6,
 alpha^5=-x^6+x^5-x^4-x^3-x^2+x-1.

Both alpha-1 and alpha^5-1 are nonzero polynomials in x of degree below 7. Consequently alpha!=1 and alpha^(q+2)!=1. Further alpha^4!=1: otherwise alpha^5=alpha and the difference of these two displayed residues would vanish, which is a nonzero polynomial of degree below 7. Thus U=1-alpha^4 and V=1-alpha are nonzero, proving every denominator in Eq(12) is defined.

It remains to check the displayed equations, without relying on the source's converse in Theorem 3. Write R=x+alpha*x^3. Because R is in F3, R^3=R. Since x^9=alpha*x, this yields

 x(1-alpha^4)=x^3(1-alpha), hence U=x^2 V.

Raising to the ninth power gives U^9=x^18 V^9=alpha^2*x^2*V^9. Division is valid, and U/U^9=alpha^(-2)*V/V^9, exactly Eq(12) at q=3,d=2. Finally

 alpha^((3^14-1)/8)=x^(3^14-1)=1

because x is a nonzero element of F_(3^14). This is Eq(13). All source hypotheses hold, while the conclusions of BOTH conjectures fail. Two conjectures receive only one possible family credit. This does not classify all bonus points or all q,n,d.

## Route B: the alpha-polynomial mechanism

Starting from the source's Eq(6) at d=2, put T(A)=1+A+A^2+A^3. Requiring x^2=T(alpha) and alpha=x^8 reduces the compatibility obstruction to T(alpha)^4=alpha. In F3[A] there is an exact factorization

 T(A)^4-A=(A-1)(A^4+A^3+A^2+A+1)
             (A^7+A^6+A^5-A^4+A^3-A^2-1).

The first two factors are the expected fifth roots; the degree-seven factor is additional. It is irreducible by the prime-degree Rabin test, and coprime to A^5-1 and A^4-1 (checks.py records exact modular tests). A root alpha lies in F_(3^7), and a square root x of T(alpha) exists in F_(3^14). Then x^8=alpha. From x^2(1-alpha)=1-alpha^4 one obtains R^3=R directly, and the same division above gives Eq(12), with Eq(13) automatic. This independent parametrization explains why increasing n can expose components invisible in the source n=6 analysis.

Elimination gives the independent x-polynomial Z^14-Z^12-Z^10-Z^8-Z^2-1, whose degree-seven factors include g above. Route A verifies the chosen component without needing any assertion about the other component. SymPy elimination and an independent integer-tuple F3 quotient implementation agree on every literal equation; the proof is the displayed identities and field argument, not the checks alone.

## Nearest actual source proof and novelty objection

Theorem 3's derivation of Eqs(5)–(12), Section 3 pp4–5, was read. Theorem 4 handles d=n/2; Section 6's n=6 resultants and Lemmas 18–19 explicitly restrict to odd q and the final remarks describe Theorem 20 as the n=6 case. Our n=14 is outside both restrictions. The argument does not contradict those scoped results. The source's Fibonacci gcd remark is a different question, not a second discovery.

The strongest substantive objection is that adjoining a root of T(A)^(q+1)-A to a sufficiently large finite field is a short classical finite-field bridge from source Eq(6). This is not itself grounds to reject a full source resolution, but it must be adjudicated independently: the degree-seven extra component and its compatibility with an actual x, Eq(13), nonzero denominators, and odd characteristic are the concrete additional work. No theorem is claimed new to the literature. Current complete public registry heads and specialist citation bodies remain uncleared. HOLD.
