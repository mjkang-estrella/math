# W007 Fourier growth and actual work — parent disposition

2026-10-08. **Accepted within its explicit implementation and depth range.**
Verified new factoring complexity improvement: **NONE**.

The [independent review](W007-fourier-envelope-review.md) accepts the parent's
Fourier/Parseval recurrence and completes the actual-work proof with constants.
All 17 delivered file hashes match. Its 19 exact certificate checks accompany
the argument; they are not factoring experiments or a substitute for the proof.
The primary Weil theorem was checked in Kowalski, Theorem 3.2, printed p.31.

For the polynomial chain with independent uniform training, the unstopped
mean root count satisfies E[m_j]<=j^2+1 for every j<=k with 2^k<=sqrt(p).
This retains collision mass in the Fourier estimate and holds for every
realized polynomial before averaging. Repeated roots and zero parameters
require no genericity assumption.

For distinct odd primes p<q, fixed k>=2, t>=1, 2^k<=sqrt(p), and p>=1024,
the specified independently restarted triangular-acquisition / depth-k probe
implementation takes at least p/(40k) expected modular multiplications before
a proper factor. It stops early only on a proper factor; permitted gcds are
the stated chain values, factors, products and endpoints. It does not include
arbitrary coefficient-difference or discriminant tests. The proof bounds
executed work using the event of no earlier zero endpoint, and uses renewal
E[trial work]/Pr[trial success], without assuming cost-success independence.

The more general sufficient conditions are A<=1/4 and B<=1/8, where
eta=1/p+1/q,
A=eta*(k+k*(k-1)*(2k-1)/6), B=eta*(k^2+1).
The p>=1024 condition ensures them in the specified range. Full-tape coupling
accounts for early stopping without falsely conditioning independent CRT laws.

This implementation loses to the paid sqrt(p) times polylogarithmic control
in that range. The result is not a lower bound for adaptive depths, later
depths, arbitrary circuits or factoring. The component mean refinement is
recorded separately, with its own scope corrections. The constructive response
is to change the acquisition law or the scalar computation, as in W009 and
W008, rather than treat formal degree as acquired useful roots.
