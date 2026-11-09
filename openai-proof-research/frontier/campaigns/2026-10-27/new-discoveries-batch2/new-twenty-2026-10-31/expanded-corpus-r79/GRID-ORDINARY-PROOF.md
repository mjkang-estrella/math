# 353680: ordinary proof route; no Lean endpoint and no novelty clearance

Source: Boyles, arXiv:2202.09878v3, Theorem 2.1, Conjecture 5.1 and Theorem 5.1. Here d_n is dim ker(I+A(P_n square P_n)) over F_2, not a coloring discrepancy. For every positive integer k, the following argument gives d_(2*3^k-1)=2, hence infinitely many nullity-two grids. The positive convention excludes k=0; no endpoint defect is claimed as a discovery.

## Algebraic calculation

In an algebraic closure of F_2 choose a primitive 3^j-th root z_j. Let P_j be the minimal polynomial of z_j+z_j^(-1), j>=1. The order of 2 modulo 3^j is 2*3^(j-1). One elementary proof uses v_3(2^(2*3^r)-1)=r+1: the base case is 4-1=3; cubing 1+3^s u increases that valuation exactly by one, since 1+y+y^2 has valuation one when y=1 mod3. The units modulo 3^j form a set of size 2*3^(j-1); the valuation identity rules out a smaller order. Moreover 2^(3^(j-1))=-1 modulo 3^j: the half-order power has order two, and the only roots of x^2=1 modulo the odd prime power 3^j are +/-1.

The Frobenius orbit of z_j+z_j^-1 therefore has length 3^(j-1). Indeed equality of two expressions z^a+z^-a implies z^a=z or z^-1, by the quadratic T^2+(z+z^-1)T+1. Thus its Frobenius period is the smallest h>0 with 2^h=+/-1 modulo 3^j, namely 3^(j-1). Consequently P_j is irreducible of that degree. In particular P_1=X+1.

For j>=2, its trace coefficient is zero. The trace is the sum z^a+z^-a over all exponents a in (Z/3^j Z)^* modulo sign, hence the sum of all primitive 3^j-th roots. Those roots form the roots of
Phi_(3^j)(T)=T^(2*3^(j-1))+T^(3^(j-1))+1,
whose next-to-leading coefficient is zero for j>=2. Therefore the coefficient of X^(deg P_j-1) in P_j is zero. Since deg P_j is odd, that coefficient in P_j(X+1) is one. Thus P_j(X+1) differs from P_j(X). Translation preserves irreducibility; distinct j have distinct degrees. No P_j, j>=2, shares a factor with any translated P_i. Also these irreducibles have degree>=3, so cannot share X or X+1.

Let f_0=0, f_1=1, f_(r+2)=X f_(r+1)+f_r over F_2[X]. For z !=0,1,
f_m(z+z^-1)=(z^m+z^-m)/(z+z^-1).
This follows by substitution and induction. For odd m, f_m is the square of a squarefree polynomial: it has only even powers by the recurrence, and the m-th roots of unity are distinct. Pairing z and z^-1 among the nonidentity m-th roots gives exactly (m-1)/2 distinct roots, all of multiplicity two (degrees agree). For m=3^k it follows that
f_(3^k)=product_(j=1..k) P_j^2.
The duplication identity f_(2m)=X f_m^2 follows from the same recurrence, or by substitution at the infinitely many z in the algebraic closure. Hence
f_(2*3^k)=X * product_(j=1..k) P_j^4.
The preceding irreducibility and coefficient calculation proves that the monic gcd of this polynomial and its translate by one is exactly X(X+1). Its degree is two.

## Nullity bridge (ordinary, not yet formalized)

Write a grid pattern in row vectors v_i, with v_0=v_(n+1)=0. The kernel equation for I+A is
v_(i+1)=(I+A(P_n))v_i+v_(i-1).
Thus v_i=f_i(I+A(P_n))v_1, giving an isomorphism from the grid kernel to ker f_(n+1)(I+A(P_n)). The endpoint vector e_1 is cyclic for A(P_n): the vectors e_1,Ae_1,...,A^(n-1)e_1 form a triangular basis with diagonal entries one. The characteristic polynomial of A(P_n) is f_(n+1), by the tridiagonal determinant recurrence. Consequently this path module is F_2[X]/(f_(n+1)). On this module the displayed endomorphism is multiplication by f_(n+1)(X+1). If f=dg and h=dq with d=gcd(f,h), then f divides hp iff g divides p, since gcd(g,q)=1. The kernel of multiplication by h on F_2[X]/(f) therefore has basis represented by g,Xg,...,X^(deg d-1)g and dimension deg d. Taking n=2*3^k-1 gives the result.

## Checks and unresolved qualification

The exact bit-polynomial search in scripts/finite.py covers k=1..9, through n=39365, and returns degree two each time. It is evidence only. The ordinary argument above requires independent scrutiny, particularly multiplicities and the Frobenius-orbit use. It does not prove any broader conjecture about odd bases other than 3.

Boyles v3 leaves this question open. The 2004 Hunziker--Machiavelo--Park paper and the 2010 Goshima--Yamagishi torus paper are material subsumption risks. Only abstract-level evidence for the former and a failed lawful 503 retrieval of a 2015 follow-up were obtained here. No claim of new-to-literature status is justified. A full Lean endpoint would need the actual grid linear map, the row-recurrence/cyclic-module/nullity bridges, the finite-field orbit and trace arguments, and the polynomial factorization/multiplicity argument. None has been certified in this lane. Zero credit.
