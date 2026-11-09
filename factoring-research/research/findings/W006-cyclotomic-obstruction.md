# W006 — a cyclotomic norm obstruction to cyclic coefficient folding

Date: 2026-10-08. PROVISIONAL parent proof, not yet independently accepted.
No factoring speedup or infinite prime-pair assertion. This concerns exactly
the coefficient-gcd operation specified in W006 A.

Let L=2^k>=2, p and q=2p-1 be primes, p=1 mod L, N=pq. Let F_L be the
degree-below-L representative of (1+X)^(N-1) modulo (N,X^L-1).
The proposed sufficient condition for **all its coefficients to be units** is

    p>L-1,       q>(L-1)^phi(L).                          (C1)

Thus the cyclic coefficient-gcd candidate cannot split this N, although
the exact central binomial coefficient has gcd p by W006 A.

Over F_p, every L-th root zeta lies in the field. At zeta=-1 the value
is zero. Else (1+zeta)^(N-1)=1, because N-1=(p-1)(2p+1).
Consequently its degree-below-L representative is exactly

    1-(1/L)*sum_(j=0)^(L-1) (-1)^j X^j.

Every coefficient is nonzero when p>L-1.

Over F_q, N-1 is congruent to p-1=(q-1)/2 modulo q-1.
Evaluation at each L-th root except -1 therefore gives epsilon_r in {+1,-1};
at -1 it gives zero. Choose a complex primitive L-th root zeta. For each
coefficient index j form the algebraic integer

    C_j=sum_(0<=r<L, r!=L/2) epsilon_r*zeta^(-j*r).

Its reduction at the prime above q matching the chosen finite-field root is
L times that folded coefficient. The signs are simply the actual finite
evaluation signs; the argument below is valid for every assignment of them.

In Z[zeta], reducing modulo the ideal (1-zeta) sends zeta to 1 and the
integers to F_2 (for L a power of two). C_j has L-1 odd terms, each reducing
to 1, hence C_j is nonzero as an algebraic integer.
Every complex conjugate has absolute value at most L-1, so

    0<|Norm_(Q(zeta)/Q)(C_j)| <= (L-1)^phi(L).

If the folded coefficient vanished modulo q, the corresponding prime ideal
would divide C_j and q would divide this nonzero integer norm. Condition
(C1) rules this out. L is invertible modulo q. This proves the proposed
all-unit claim for every coefficient, without assuming any distribution of
the Legendre signs.

The theorem is conditional on a prime pair satisfying its explicit arithmetic
conditions; no infinitude of q=2p-1 is claimed. It is a representation
obstruction, not a hard factoring family: knowing that relation between the
factors makes N easy by a quadratic equation.

## One fixed certificate target, no search

Candidate p=3*2^29+1=1610612737,
q=3*2^30+1=3221225473, N=p*q.
These primality assertions are NOT yet verified. They are fixed targets
for the authorized certificate check, not trusted inputs.

If both primes verify, p=1 mod 16 and
q>15^8=2562890625, so (C1) excludes every degree L in {2,4,8,16}.
The parent is not treating an unverified recalled prime as evidence.
The checking task may prove either target composite; no replacement search
or expanded prime menu is authorized.

For t=3*2^e+1, with 2^e>sqrt(t), finding a with
a^((t-1)/2)=-1 mod t proves t prime: for every prime r|t the order of a
has full 2-adic part 2^e, hence r=1 mod 2^e and r>sqrt(t). Such a composite
t cannot have a prime divisor at most sqrt(t). Check every step, including
gcd(a,t), before accepting the certificate.

Use only fixed bases {2,3,5,7,11}, in that order, for each of the two targets.
Record all tested bases and first witness or NO_WITNESS. A failed witness
does not prove compositeness; only a proper gcd or verified compositeness
test does. No exact huge central binomial computation is needed or allowed.
