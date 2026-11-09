# W018 exact certificate preregistration

This freezes one proof-only exhaustive execution, before any execution of certificate.py.
The exact 21 cases are cases.json. For every case enumerate all a=1,...,N-1;
no RNG, adaptive selection, sweep, tuning or replacement run. Exhaustive counting
represents the exact uniform distribution in the theorem. The only variable
parameters are the fixed case records, not a searched parameter family.

Coverage: B=1; B just below, at, and above possible orders; square and nonsquare B;
duplicate babies; several matched positive annihilators and least-match selection;
matched annihilator outside B; B>N; M=1, nontrivial odd M, even M, M annihilating
all units, and the 65-bit integer 2^64+4 for N=15. N=45,63,75 have repeated prime
factors; N=105 has three components. N=9 and 25 are excluded prime-power controls:
check their individual outputs but do not apply the <=1/2 probability theorem.

Candidate boundary: trial(N,M,B,a) and bounded_order know no factors or orders.
The checker alone uses the explicitly supplied prime-power decomposition and
naive consecutive modular multiplication to tabulate true local and global
orders. Cached reference tables are proof fixtures only, never solver inputs.
The candidate uses repeated-squaring exponentiation and sorted baby lookups.

Required checks: exact beta, exact bounded-order result, every returned factor,
E annihilates a, every visited square-chain residue, extraction succeeds exactly
when local 2-valuations differ on the small-order branch, failure-set inclusion,
exact two-component equality probability, <=1/2 failed-unit fraction in theorem
domain. Record all unit and nonunit outcomes and all failed assertions. Also
exhaustively check the rejection sampler's accepted-bitstring bijection for
each modulus; this verifies its finite mapping, not physical random-bit quality.
Controls with M a multiple of their group exponent must have all units retry.

Execution limit: 60 wall seconds including fixture setup, 20,000 charged events
TOTAL, not per case. SIGALRM plus cooperative checks. On any exception or limit,
retain partial records and the error; unexecuted cases remain unexecuted. No rerun.
Significant charged operations: modular multiplication (each powering multiply
separately), gcd, integer remainder, v2 extraction, square root, ceil division,
annihilator/index arithmetic, exponent shift, sorted lookup, base visits and
sampler-bitstring visits, including reference work. Ordinary comparisons,
sorting comparisons, loop counters, input parsing, allocation, logging, fixture
small products, fractions and aggregation are not certified bit-machine events;
they are included in the wall budget. Event counts and elapsed time support only
budget compliance and must not be used for speed, bit-complexity or scaling claims.

Success criterion: complete run within both budgets with zero failed checks.
Any failed check rejects the corresponding implementation/proof assertion pending
explicit analysis; nothing is deleted. The theorem itself is decided by proof,
not by these finite fixtures. No polynomial batching, consumer, preprocessing
algorithm or huge-input asymptotic implementation is tested here.
