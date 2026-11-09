# Pre-execution symbolic audit — W006 cyclotomic validation

2026-10-08. Independent review recommendation: the stated sufficient all-unit
claim is valid. This is an elementary mathematical audit, not a Lean proof,
novelty finding, complexity improvement, or assertion of infinitely many pairs.
The fixed integers have not been tested when this document is written.

## 1. Exact central selector and its cost

Let p<q<2p be odd primes, N=pq and m=(N-1)/2. The digits below are written
most significant first. Since p+2<=q<=2p-1,

- N-1=(p-1)q+(q-1), m=((p-1)/2)q+(q-1)/2;
- N-1=p^2+(q-p-1)p+(p-1), m=((q-1)/2)p+(p-1)/2.

All displayed digits are in their required ranges; m<p^2. In base q each
lower digit is bounded by the corresponding upper digit. Lucas therefore
makes the central coefficient nonzero modulo q. In base p its missing high
digit is zero, while its middle digit exceeds the upper middle digit:

    (q-1)/2 - (q-p-1) = (2p-q+1)/2 > 0.

Consequently it is zero modulo p. More exactly, Legendre's factorial formula
has p-level contribution (q-1)-2((q-1)/2)=0, p^2-level contribution 1-0=1,
and no higher contribution: N-1<2p^2<=p^3 for p>=3. At q the first
contribution is (p-1)-2((p-1)/2)=0 and q^2>N-1, so v_q=0.
Thus gcd(binomial(N-1,m),N)=p and v_p=1. These are classical valuation/digit
consequences, not evidence for a cheap way to obtain this value from N alone.
The central coefficient has Theta(N) bits: it lies between 2^(N-1)/N and
2^(N-1), using the largest coefficient in a row of N coefficients.
No numerical central coefficient is needed in this review.

In Z/NZ[X]/(X^L-1), reduction sends X^i to X^(i mod L), so the folded
coefficient f_j equals the sum of all original coefficients with i=j mod L.
Schoolbook cyclic convolution and binary exponentiation give O(L^2 log N)
modular multiply-adds and O(L log N) working bits (excluding retained logs).
With classical integer multiplication/division this is a conservative
O(L^2 (log N)^3) bit upper bound when log L=O(log N), plus coefficient gcds.
The modular-ring event count is not a bit-time bound or benchmark comparison.

## 2. Roots, the p identity, and Fourier normalization

Take L=2^k>=2, prime p=1 mod L, prime q=2p-1 and N=pq. Necessarily p>=L+1,
so p>L-1 is in fact redundant but valid. Both p and q are odd, L divides
p-1 and q-1=2(p-1), and L is a unit in both fields. Their multiplicative
groups supply primitive L-th roots; X^L-1 has L distinct roots in each.
Evaluation therefore uniquely identifies a polynomial of degree <L.

The exact identity is

    N-1=2p^2-p-1=(p-1)(2p+1)>0.

At the root -1, (1+(-1))^(N-1)=0; this point must be excluded from Fermat's
identity. At every other root the base is nonzero, so its value is 1 over
F_p. The degree <L polynomial

    H(X)=1-L^(-1) sum_{j=0}^{L-1} (-1)^j X^j

has exactly these values. At -1 the sum is L. At another L-th root w,
the geometric sum of (-w)^j is zero, since (-w)^L=1 and -w!=1. Hence

    f_0=(L-1)/L,       f_j=(-1)^(j+1)/L (1<=j<L)    modulo p.

Their numerators are nonzero modulo p under p>L-1.

Fix a primitive L-th root omega in F_q. Since pq-1=p(q-1)+(p-1),
N-1 is congruent to (q-1)/2 modulo q-1. Euler's criterion gives

    F(omega^r)=epsilon_r in {1,-1}, r!=L/2;
    F(omega^(L/2))=0.

For any degree <L polynomial, orthogonality of the geometric sums gives

    L*f_j=sum_{r=0}^{L-1} F(omega^r)*omega^(-jr).

Indeed, substitute sum_i f_i omega^(ir); the inner sum is L for i=j,
zero otherwise. This checks the minus sign, the factor L, and every index.
No finite-field root or Legendre sign needs to be computed by the candidate.

## 3. The missing implication is supplied by the norm, not nonzeroness alone

Put d=phi(L)=L/2 (also d=1 at L=2), zeta a complex primitive L-th root,
and R=Z[zeta]. For powers of two, Phi_L(T)=T^d+1, so

    R/(1-zeta) = Z[T]/(T^d+1,T-1) = Z/2Z.

For any assignment of the actual signs, define

    C_j=sum_{0<=r<L,r!=L/2} epsilon_r*zeta^(-jr).

Negative powers are algebraic integers because zeta is a root of unity.
Each summand maps to 1 in the displayed quotient. There are L-1 odd many
summands, so C_j maps to 1 and C_j!=0 in characteristic zero. This includes
L=2, where zeta=-1 and (1-zeta)=(2). It does not generalize automatically
to odd L or arbitrary composite L. Signs and repetitions cause no problem.

Each of the d embeddings sends zeta to zeta^a for an odd residue a mod L.
Every conjugate of C_j is a sum of L-1 numbers of absolute value 1.
The triangle inequality and nonzeroness therefore give

    0 < |Norm_{Q(zeta)/Q}(C_j)| <= (L-1)^d.

The norm is a rational integer: multiplication by C_j on the integral
basis 1,zeta,...,zeta^(d-1) has an integer matrix with this determinant.
It is nonzero since multiplication by a nonzero field element is invertible.
Repeated summands or embeddings giving the same value do not change this.
The upper bound is non-strict; the lower bound is strict.

To make the prime-ideal step explicit, omega^d=-1 in F_q because omega
has even order L. Substitution defines a surjective ring homomorphism

    rho:R -> F_q,          zeta -> omega.

Its kernel P=(q,zeta-omega), with any integer lift of omega, is a maximal
ideal lying over q. It is also a prime of the full cyclotomic integer ring,
which here equals R; that equality is not required for the following argument.
The inverse Fourier formula says rho(C_j)=L*f_j. If f_j=0, C_j is in P.
Equivalently, reduce the integer multiplication matrix of C_j modulo q:
the nonzero row functional rho annihilates its image, so its determinant
is zero modulo q. Therefore q divides Norm(C_j). This is a direct proof
of the prime-ideal/norm implication without any unproved splitting claim.
One can also reduce the product over conjugates: its identity-embedding
factor is zero under rho, and its integer product reduces modulo q.

A nonzero integer divisible by q has absolute value at least q. The
strict condition q>(L-1)^d contradicts the norm upper bound. Thus every
f_j is nonzero modulo q and, together with the p calculation, every f_j
is a unit modulo N. Replacing > by >= is not justified by this argument.
The algebraic nonzero statement alone would not suffice; this is exactly
the unresolved objection, now resolved. No sign randomness is used.

## 4. Lower degrees, alias failure and quantified scope

For any odd N>1, the even and odd binomial sums both equal 2^(N-2),
so L=2 has only units modulo N. For L=4 in the conditional prime family
p=1 mod 4, q=2p-1, the p vector is (3,1,-1,1)/4. Modulo q let i have
order four. Since q=1 mod 8, chi(i)=chi(-1)=1. The relation
(1+i)^2=2i proves chi(2)=1 without a supplementary reciprocity formula.
Also 1-i=(-i)(1+i), so the signs at i and -i agree, say a=+/-1.
The values in root order (1,-1,i,-i) are (1,0,a,a), and the coefficient
vector is (1+2a,1,1-2a,1)/4. Its numerators belong to {3,1,-1}, nonzero
for p,q>3. This checks the original L=4 observation without repeating
A's tiny corpus. The general norm bound is sufficient, not necessary.

For the frozen proposed pair, if both primes certify, p=1 mod 16 and
q>(15)^8=2562890625 imply the bounds for all four fixed degrees, whose
norm bounds are respectively 1,9,2401,2562890625. Each inequality is
checked as an integer by the evaluator after both certificates succeed.

Exactly which information folding loses can be stated without the huge
coefficient. Since p,q=1 mod 2L in the frozen degree menu, m=(pq-1)/2
is 0 mod L. The target binomial is zero modulo p, but the total coefficient
f_0 is (L-1)/L!=0. Thus the sum of every other index congruent to 0 mod L
is (L-1)/L modulo p. Those aliases erase the zero. This proves their
aggregate contribution; it does not identify each large binomial term.

One finite menu and a conditional family theorem do not exclude every
polylogarithmic degree, adaptive menu, or compressed coefficient algorithm.
No infinitude of eligible prime pairs has been proved. Nor is the family
hard for factoring: 8N+1=(4p-1)^2, so knowledge of its promise yields
p=(1+sqrt(8N+1))/4 by an integer square root and verification. That promise
is evaluator knowledge and is not passed to the cyclic candidate.

## 5. Certificate logic, validated before target execution

Let t=3*2^e+1 with e>=1, (2^e)^2>t, gcd(a,t)=1 and

    a^((t-1)/2)=-1 mod t.

For any prime r dividing t, r is odd and the base is a unit modulo r.
Let h=ord_r(a). Squaring gives h | 3*2^e. But h does not divide
3*2^(e-1), because -1!=1 in F_r. Writing h=2^s*u with u odd, u|3,
forces s=e. Lagrange then gives 2^e | h | r-1, hence

    r >= 2^e+1 > sqrt(t).

Every composite integer has a prime divisor <=sqrt(t), including prime
powers, a contradiction. Therefore t is prime. The strict squared
inequality is evaluated exactly, without floating point. The congruence
itself implies the base is a unit, but its gcd is checked explicitly as
required. No converse or fixed-base completeness is assumed.

A residue other than t-1 is NOT, by itself, a composite certificate.
The frozen execution will only label a proper checked base gcd as a
factor/composite certificate; it will not add Fermat/Miller-Rabin tests or
residue-gcd searches. It records every prescribed failed base until the
first certificate, or NO_WITNESS after the finite menu. Both targets must
certify before the candidate vector cases are allowed to start.

## 6. Original reflection brief: symbolic checks only

This is ancillary context, not a numerical reflection screen or an audit of
later parent constructions. R_C(V)=V-2<V,C>C/c=-C*bar(V)*C/c. Composing
first C then D gives B1 and B2 exactly as in the original W006 brief:

    B2=B0+[-2*b*d*C+(4*b*h-2*c*e)*D]/(c*d).

Both reflections are rational orthogonal maps for c,d>0. Dotting with A,
using <A,B0>=0, gives -2(abd+cef-2bhf)/(cd); B2 is perpendicular exactly
when the displayed B2 equation vanishes. Integrality is coordinatewise
divisibility of the numerator by cd. One reflection is perpendicular
exactly when <A,C><B0,C>=0, giving the old fixing direction or no change.

If C is perpendicular to A, the quaternion identities in the brief give

    R_C(U*A)=A*(bar(C)*bar(U)*C/c),
    R_C(A*U)=(C*bar(U)*bar(C)/c)*A.

Starting with i*A, these alternate sides and preserve norm(U)=1. For a
finite word of direction norms coprime to N, all multiplier coordinates
are rational with denominators coprime to N. If the final B is integral,
the unique multiplier also equals B*bar(A)/N or bar(A)*B/N. Its reduced
denominator thus divides N as well. A divisor of N coprime to N is 1,
so this multiplier is an integer quaternion. Norm 1 makes it a signed
coordinate unit; orthogonality makes its real part zero, leaving the six
pure units on the appropriate side and at most twelve outputs altogether.
This denominator argument includes repeated prime powers and needs no
kernel classification (or even primitivity once A is supplied). In local
matrix language the invertible even left multiplier preserves the right
kernel and the odd right multiplier preserves the image at each prime
power. No claim about arbitrary two-sided rational rotations follows.

## 7. Bounded primary-source check; no novelty claim

- [Andrew Granville, Binomial coefficients modulo prime powers](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/granville.pdf),
  introduction (also read in the author-hosted HTML edition) and section 3,
  printed pages 1, 8–9: classical Lucas/Kummer facts and prime-power
  evaluation; the introduction also discusses sums over residue classes. This is
  background for the selector and fold; no claim that the exact W006
  balanced selector or obstruction is explicitly stated there. Published
  prime-power evaluation takes the prime as input, so it cannot be treated
  as factor-blind preprocessing. No general modular-binomial speed claim
  is imported here.
- [Tsz-Wo Sze, Deterministic Primality Proving on Proth Numbers](https://arxiv.org/pdf/0812.2596v5),
  definition (1.1), Theorem 1.1 and its immediately following cases,
  printed pages 1–2: the sufficient -1 congruence is Proth's test. Only
  this certificate statement is used; Sze's other algorithms, asymptotic
  bounds and witness-selection methods are not run or imported.
- [T. Y. Lam and K. H. Leung, On vanishing sums of roots of unity](https://arxiv.org/pdf/math/9511209v1),
  introduction and Main Theorem, printed pages 1–3: vanishing weights in
  characteristic zero are nonnegative combinations of the prime divisors
  of the root order. With order 2^k, signed summands are still roots of
  that order, so odd length cannot vanish. The quotient proof above proves
  the needed special case directly. No new root-sum phenomenon is claimed.
- [Lam and Leung, Vanishing sums of m-th roots of unity in finite fields](https://arxiv.org/pdf/math/9605216v1),
  introduction, Theorem 1.1, discussion (1.2), and Example 2.1, printed
  pages 1–4: finite-characteristic vanishing weights can differ from the
  characteristic-zero classification. This source is related prior art,
  not a proof that a nonzero complex sum stays nonzero modulo q. The norm
  bound above independently supplies that missing implication. No claim
  of locating the exact W006 all-unit theorem in this paper is made.

These bounded passages do not constitute an exhaustive novelty search. All
sources are primary research papers; PDFs are retained with pre-run hashes.
