# W006 coefficient and cyclotomic disposition

2026-10-08. The exact central selector and the conditional cyclotomic obstruction
are accepted at their mathematical scopes. The fixed degree menu is rejected as
an all-input factor finder. Verified new complete factoring improvement: **NONE**.

For distinct odd primes p<q<2p, N=pq, m=(N-1)/2, the reviewed Lucas/Legendre
argument proves gcd(binomial(N-1,m),N)=p, with valuations v_p=1 and v_q=0.
This does not supply a cheap modular evaluation algorithm. The exact integer
has Theta(N) bits; that fact is not a lower bound on modular evaluation.

The frozen 48-case coefficient screen completed once: 16 FACTOR, 32 NO_FACTOR,
zero UNKNOWN or errors. All factor witnesses and exact folded-vector controls
passed. The balanced-input coverage counts at L=2,4,8,16 were 0/8,4/8,7/8,5/8.
These are finite evidence, not asymptotic success rates. In particular N=2701
has only unit coefficients at all four degrees, although its central coefficient
has gcd 37. At L=16, 166 nonzero aliases outside the central zero block sum to
22 modulo 37 and erase its zero. The coarser vectors are determined by the
degree-16 vector, so the four views are not independent samples.
See [full coefficient review](W006-coefficient-validation.md), its frozen
protocol, outcomes, execution marker and saved-evidence validation.

The reviewed all-unit theorem assumes primes p,q=2p-1, L a power of two,
p=1 mod L, and q>(L-1)^phi(L). The folded coefficients modulo p are explicit
nonzero fractions. Modulo q their Fourier numerators are nonzero cyclotomic
integers by parity at (1-zeta); their nonzero integer norms have absolute value
at most (L-1)^phi(L)<q. Thus no coefficient vanishes modulo either prime.
This is a conditional obstruction for this particular coefficient-gcd operation.
It proves neither infinitude of eligible pairs nor failure of every adaptive
polylogarithmic menu. The factor relation itself permits easy promised factoring.

The fixed large certificate experiment remains **UNKNOWN**. In its one frozen
run, 1610612737 obtained no witness from bases 2,3,5,7,11; 3221225473 was
prime-certified at base 5. All four vector cases were correctly unstarted and
remain explicit UNKNOWN outcomes. Do not call the first integer prime, infer
vectors, replace targets, or conflate the conditional proof with this instance.
See [cyclotomic review](W006-cyclotomic-validation.md) and its pre-execution
[proof](W006-cyclotomic-validation-proof.md). The sufficient certificate argument
is accepted; its five-base menu is not a complete primality algorithm.

Both reports record successful project checks after their scratch code. Those
checks verify existing tests and Lean proofs, not the new mathematics. No shared
factorer or Lean source changed.

## Constructive consequence

The failed representation adds unrelated coefficients before testing divisibility.
An exact truncated polynomial keeps the selector but requires Theta(N) state;
its schoolbook reference costs O(N^2 log N) modular operations. Larger cyclic
degrees alone are not a justified repair. A replacement must compute a separating
linear functional or equivalent quantity while charging its dimension, precision,
and input acquisition. This branch is retained as a precise target, not the sole
research framing. Reflection and group-map branches remain independent.

