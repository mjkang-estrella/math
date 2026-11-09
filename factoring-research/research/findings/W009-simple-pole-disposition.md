# W009 reciprocal persistence — parent disposition

2026-10-08. **Equations (1)–(7) accepted within the frozen protocol.**
Verified new factoring complexity improvement: NONE.

The [independent audit](W009-simple-pole-review.md) validates the exact trace
law, the every-history character bound, the paid no-op process, recurrence
constants and all listed early-factor channels. All 21 delivery hashes match.
Ten exact symbolic checks support the derivation; no factoring experiment,
shared solver edit or Lean proof was performed.

For a fixed first legal reciprocal fold on uniform affine input, the next
locally legal update has residual collision mass 3/p+O(1/p^2), uniformly
in the first pair. Thus the initial near-doubling is not repeated even at
the second step. This expectation is not a pointwise or all-depth statement.

For k raw attempts with 2^k<=sqrt(p), the full-tape process satisfies

    E[v_j] <= 4*(j+1)/(p-1),
    E[m_j] <= 1/p+4*j*(j+1)/(p-1),   j<=k,

where m is combined root/pole mass. The accepted composite success bound
is equation (7) in the parent note, equivalently
O((k^3+t*k^2+k+t)*(1/p+1/q)), for k raw attempts and t fresh final probes
on distinct odd semiprimes in the stated depth range. It includes the
literal chart, intermediate root/pole gcds and anchor differences. It
does not include arbitrary additional coefficient or derivative tests.
The proof uses current-map CRT independence and coupling; it does not
assume survived histories remain independent.

This is a success envelope for a fixed budget, not an actual-work lower
bound or an expected restart theorem. The old polynomial tower's p/(40k)
work bound does not transfer. Greater depths, correlated anchors, powered
updates and other detectors remain outside the theorem.

The one-step powered-map contribution g*s^4/(p-1), g=gcd(e,p-1), is exact
but need not dominate the other characters. Exceptional coefficients equal
the residual mass s, not one. Binary powering preserves roots and poles,
so its possible gain is in subsequent nonzero collisions. The audit gives
explicit nonnegative remainder bounds and confirms that a simple pole is
lost after powering. Parent's new [four-fiber reset](W009-power-reset.md)
addresses later powered histories with a different geometric argument;
D is now accepted with scope repairs in W009-power-reset-disposition.md.
