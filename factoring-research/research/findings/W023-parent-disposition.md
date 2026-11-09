# W023 parent disposition

The decimation review was read in full. Its local checksum entries were
verified in W023-parent-intake-hashes.json; no external full-manifest terminal
anchor was supplied. No experiment or certificate ran. Verified complete
factoring improvement: **NONE**.

## Accepted representation result

For G_(a,c)(x)=sum_n binom(2(an+c),an+c)x^n with 0<=c<a, accept exact
algebraic degree 2^a over Q(x) and over F_p(x) WHEN p does not divide 2a.
The characteristic-zero result has no restriction beyond a>=1. The review
supplies the formal branch, multiquadratic signed-orbit proof, cyclic lift
and rational/prime-field descent. These are prose mathematics, not Lean
proofs. The field-degree argument is not a factoring lower bound.

For the binary schedule a=2^k, every odd prime is admissible. All digit paths
have degree 2^(2^k), not only the all-even path. Accept the extension to a
nonzero exact polynomial annihilator over an odd composite modulus: in a
prime-power component where it is nonzero, divide out the least coefficient
valuation and reduce modulo that prime to apply the field bound.

The terminal wording "every a over every odd p" is too broad if separated
from the theorem's condition. For example, when a=p, Lucas gives E_p=E_1
modulo p, of degree two. This is outside the binary case and does not
invalidate the accepted result. Keep p not dividing 2a explicit.

## Exact computational consequences and their limits

A dense equation needs a box of at least 2^a+1 coefficient positions.
A directly listed sparse equation still must encode an exponent of that
size and hence uses at least a+1 bits for one binary exponent. Degree alone
does not imply exponentially many nonzero coefficients.

There is also an elementary parent corollary for an EXACT annihilator
computed as a polynomial arithmetic circuit: with inputs Y and coefficients
in the base rational-function field, and ordinary binary +,-,* gates, s
multiplication gates give Y-degree at most 2^s. Any nonzero annihilator here
therefore requires s>=a. This is only a bound for constructing THAT polynomial
with THOSE gates. It says nothing about radical-expression states, truncated
relations, computing the one coefficient, or the short Newton circuit for an
approximate series. An exponentiation notation with a huge exponent must pay
for its encoding and evaluation rather than count as one of these gates.

The review's hypergeometric and explicit cyclotomic representations have
growing data size. Their stated operation envelopes are prices of those
representations, not optimality lower bounds for every recurrence or modular
extension. In particular an arbitrary ring containing a suitable root of
unity is not forced to have the rank of the full cyclotomic construction.
The denominator/height discussion is not needed for the accepted degree
claim; no height lower bound is adopted.

Do not turn the review's Lucas remark into O(log m) BIT work for a known
prime: its digit binomials also need computation or a paid precomputed table.
The important distinction is that known-prime Frobenius methods use an input
that our N-only splitter does not receive for free.

The final requirement that every useful state be subexponential in depth k
is unnecessarily strong for this research goal. Such size is necessary for
some target bounds, but a state costing 2^(gamma*k) with sufficiently small
gamma could still improve a matched complete exponent if the rest is paid.
Similarly, an attempted nonunit inversion that returns a proper factor is
a valid factoring branch; it cannot simply be forbidden when costing a new
complete algorithm. It cannot be silently assumed to succeed either.

## Constructive continuation

The parent developed a different, unit-safe computation while this review
ran: W023-single-residue-computation.md gives Newton iteration with only
division by 2, a short untruncated circuit, and an exact middle-coefficient
recurrence. The direct implementation pays for a long coefficient prefix;
the middle-product compression recovers the original hypergeometric target
and does not give it for free. This corrects a broad W022 acquisition claim
without establishing any speedup. The finite-field cubic diversion was
deduplicated against W011.

W023's other calculations retain parent-derivation status: direct quadratic
annihilators and small-gap folded support lose to simpler same-promise covers;
the first rational root chart pays for its denominator and loses compression;
higher Taylor degree changes costs but supplies no kernel. No additional
numerical run is justified by those arithmetic comparisons alone.

The new selected construction is W024's public prime-residue sign filter.
It removes zero exponents on whole ordinary chart boxes while preserving a
witness for at least one publicly scheduled prime. It is under independent
audit and does not erase the remaining product/carry cost. The parent stays
active on the computation; no result here is a new complete factoring bound.
