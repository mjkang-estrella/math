# W032: joint high digits through an explicit change of coordinates

Parent derivation, 2026-10-08. **Not independently accepted yet.** Imports
the scalar diagonal from the live W032 audit; does not broaden the live
single-top-digit audit's assigned scope. No numerical experiment. Verified
complete factoring improvement: **NONE**.

## 1. Normalize to an ordinary square with a known branch

Assume R>=1, 2R+1<leastprime(N), and a is a unit. Put L=2R-1 and

    W(a)=24*(V_R(a)-1)/N^2 mod N^L.

The division is exact on canonical V, since V=1 mod N^2. Multiplication
by 24 is a unit operation. The imported diagonal gives

    W(a)=a^2+sum_(k=2..R) 24*N^(2k-2)*G_k(a^2) mod N^L
        =a^2*(1+N^2*T(a^2)) mod N^L,                 (1)

where T is a polynomial with unit rational denominators. Every G_k(x)
is divisible by x, so this factorization uses no division by a variable.
In particular W(a)=a^2 mod N, and its formal derivative is 2a mod N.

There is a unique y=Phi(a) modulo N^L satisfying

    y^2=W(a) mod N^L,   y=a mod N.                   (2)

It can be computed without factoring N: start at y=a mod N and use
y <- (y+W(a)/y)/2 at doubled precision, with units checked. If y^2-W is
divisible by N^s, the new error is divisible by N^(2s), exactly as an
integer identity over the localization at the units. The derivative 2y
is a unit throughout. Uniqueness at each next base-N digit follows from
an invertible linear equation. This argument works for composite N and
prime powers; it is not field-only Hensel lifting.

Equation (2) computes the root in an ALREADY KNOWN branch a mod N. It
does not produce an independent CRT sign choice or a new square root of
an arbitrary input. Computing W by scalar powering and lifting its known
root fits soft O(R*poly(log N)) with doubled-precision fast arithmetic;
a conservative sequential implementation remains polynomial in R,log N.
All resident residue widths are O(R log N), with arithmetic workspace paid.

## 2. Exact digitwise bijection, not a mixing assumption

Fix a0 modulo N that is a unit. Let a range uniformly over all N^(L-1)
lifts of a0 modulo N^L. For s>=1 and any t modulo N, (1) gives

    W(a+N^s*t)-W(a)=2a*N^s*t mod N^(s+1).

Thus W maps the a0-fiber bijectively to all residues congruent to a0^2
modulo N. This follows by induction: at every next digit, multiplication
by 2a is invertible. The same calculation in (2), using y=a mod N,
shows Phi(a+N^s*t)-Phi(a)=N^s*t mod N^(s+1). Hence Phi is also a
bijection on the a0-fiber, congruent to the identity on successive digits.

Since 24 is a unit, Q(a)=(V_R(a)-1)/N^2 is consequently uniform over
all residues modulo N^L congruent to a0^2/24 modulo N. Every one of
its higher base-N digits is jointly independent and uniform. The leading
1 in V=1+N^2*Q introduces no carry, since 0<=Q<N^L and N^2>1.
Therefore the selected digits d_2,...,d_R are also jointly independent
uniform residues modulo N. d_1 is fixed and a unit. This is a finite
counting conclusion for the stated full-lift input distribution; it is
not a pseudorandomness claim about canonical inputs a<N.

For distinct primes N=pq, set s_N=(p+q-2)/(pq). The probability that at
least one of d_2,...,d_R gives a proper gcd is exactly

    1-(1-s_N)^(R-1) <= (R-1)*s_N.                   (3)

It is no better than choosing R-1 independent random gcd arguments
directly. Sampling all lifts uses (L-1) base-N random digits, charged as
O(R log N) random bits in expectation with rejection sampling. Sequential
or capped generation has its corresponding failure/work accounting.
This comparison concerns this random-lift algorithm only. It is not an
asymptotic lower bound for arbitrary adaptive computation or factoring.

## 3. Constructive significance and remaining scope

The proposed mechanism was to share one expensive scalar evaluation across
many high-digit tests, hoping correlated digits amplify separation. The
explicit coordinate change shows that FULL lift randomization removes
those correlations: it realizes exactly ordinary random residues. A
desired square target with the known residue branch can also be lifted
digit by digit, paying for scalar evaluations; forcing such a target does
not acquire a new root branch.

This rejects a precise randomization model, not W032 as a whole. Restricting
a to the canonical interval [0,N) selects one lift per residue and need
not map to uniform higher digits. The floor representation retains that
restriction. An improvement would require a proved useful law or selector
for those specific representatives, or another computation that avoids
the known-branch equivalence. No such success theorem is asserted here.
