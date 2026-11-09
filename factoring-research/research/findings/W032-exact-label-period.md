# W032: compute the true carry-label period before paying factorial width

Parent constructive proposal, 2026-10-08. **Algorithm and filter transfer accepted**
in [the independent review](W032-label-period-review.md). No numerical
experiment. Verified complete factoring improvement: **NONE**.

The accepted high-difference rejection used the sufficient period
D=4^R(2R+1)!. It did not prove D was necessary. This proposal replaces that
period by an exactly computed smaller period of the two actual labels.
It changes input acquisition, not the floor identity or its strict bound.

Assume R>=1 and leastprime(N)>2R+1. With the accepted integer polynomials
C_k(X)=D G_k(X), form modulo D the two polynomials in A

    E(A)=C_R(A^2),
    H(A)=sum_(k=0..R) N^(2k) C_k(A^2).

They have degree at most 2R. The labels are e=E(a) modD and
h=-H(a)*(N^(2R+1))^(-1) modD. Thus a common translation period of the
functions E,H from Z to Z/DZ preserves both labels. We need function
equality, not coefficient equality in (Z/DZ)[A]. The latter can be
strictly stronger because nonzero polynomials can vanish as functions.

## An actual exact period algorithm

Initialize S=D. Its factorization is known from 2 and the primes at most
2R+1 used to form the factorial. For each prime l dividing D, repeatedly
try t=S/l while it is integral. For P equal to E and H form

    T_P(A)=P(A+t)-P(A).

Its degree is at most 2R-1. Compute its values at 0,...,2R-1 modulo D and
their forward-difference table. Accept t exactly when every leading
difference Delta^j T_P(0), j=0,...,2R-1, is zero modulo D for BOTH P.
If accepted replace S by t and repeat; otherwise retain this prime's
exponent and move to the next prime. Do not enumerate D residue classes.

Why the test is exact: every integer polynomial T of degree at most d has
the identity T(A)=sum_(j=0..d) Delta^j T(0)*binom(A,j). Binomial polynomials
take integer values at all integer A, including negatives. Thus vanishing
of these coefficients modulo D implies all function values vanish. The
converse follows from the definition of finite differences. No modular
division by j!, or assumption that evaluation over a composite modulus
is injective, is used.

All integer periods of the pair of functions form an additive subgroup
of Z containing D Z, hence equal S_min Z with S_min dividing D. A trial
t is accepted exactly when S_min divides t. If S/l fails, the current
l-adic exponent is already the exponent of S_min; reducing other prime
exponents cannot change that. Therefore this greedy procedure returns
the smallest positive common function period S_min, independently of
the order of primes. This is for all integer inputs; restricting only
to unit inputs could in principle admit another notion of period, not
computed or claimed here.

## What computation is saved if the period is smaller

Use a_i=a0+i*S_min, i=0,...,2R+1, all canonical units. Fixed e,h give the
same decomposition d_R(a_i)=J(i)+floor Q(i) modN as before. J has degree
at most 2R and integer values on this class, Q degree at most 2R-2.
Therefore the SAME strict bound |Delta^(2R+1) floor Q|<4^R holds, now
with canonical width requirement (2R+1)*S_min<N instead of (2R+1)*D<N.
Every prime of S_min divides D, so S_min remains a unit modulo N.

If S_min were bounded by exp(O(R)) on a usable, N-only acquired input
family, depths R proportional to logN could become admissible. The
residual bound could then be a positive power of N, removing the specific
subpolynomial-residual rejection. This WOULD NOT prove a factor yield:
zero residuals, units, full gcds, prime-specific support and scalar costs
still require their own law. If S_min retains exp(Theta(R logR)) growth,
this changed acquisition has not removed the asymptotic width gate.

## Paid construction and decisive test

Generate C_k using the explicit products
prod_(i=1..j)((2i-1)^2-Y), j<=R, and the exactly divisible multipliers
D/[4^j(2j+1)!]. Their coefficients have polynomial bit length in R;
reduce modulo D as soon as each exact multiplier is available. This is
a polynomial-in-R coefficient computation, not a free scalar oracle.
Compute N modD and its even powers; no huge N^(2R) is materialized.
Each trial period uses O(R^2) modular operations for Horner values and
the difference tables of two polynomials. At most O(logD) successful
reductions plus O(R) failed prime trials occur. Operands have O(logD)
bits; reading/reducing N and acquiring the small prime table are paid.
Thus the exact-period algorithm costs polynomial in R and logN with
O(R logD) basic coefficient storage plus arithmetic scratch. This bound
does not assert a practical speedup over scalar powering.

A cheap *symbolic* falsifier is a lower bound on a prime-adic exponent
of S_min from one nonzero Newton coefficient of T_P. A diagnostic at a
few fixed R would only suggest growth, never prove it. No such diagnostic
is run here: first independently audit the period computation and inspect
whether the accepted coefficients force factorial-scale periods. Any
later experiment must freeze depths, public N inputs, counters, source
and budget before its single run. The next task is to resolve this exact
gate, not to assume a short period or a separating residual.

The completed audit proves the exact component
v_2(S_min)=v_2(D)-1-v_2(R), uniformly in permitted N, and the top-prime
divisibility when 2R+1 is prime. Full period growth remains unresolved.
The parent's subsequent [odd-prime-band bound](W032-label-period-lower-bound.md)
has its own pending audit; it was not part of this completed review.
