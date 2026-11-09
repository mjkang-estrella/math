# W015: remove interval fragmentation with a valuation representation

Parent constructive continuation, 2026-10-08. This changes the actual router's
representation and removes its linear record creation through the first binary
mixing scale. It does not improve complete factoring complexity. The algebra
below is a parent derivation, not yet independently reviewed or Lean-proved.
No additional experiment was run and no novelty is claimed for odd-part sieving.

## Exact survivor description

Use W015's odd N>=25, n=isqrt(N), H<=n/4 and s=ceil(log2 n).
Let v2(x) be the exponent of two in a positive x and odd(x)=x/2^v2(x).
The initial point x survives all prefix removals through round s exactly when

    odd(x)>H.                                                   (1)

If odd(x)<=H, its route reaches that value at depth v2(x)<=s and stops
no later. Conversely write x=2^j*u with u odd and u>H. For r<=j,
T^r(x)=2^(j-r)*u>H. For j<r<=s, its representative is

    (u+k*N)/2^(r-j), with k odd and 1<=k<2^(r-j).

This exceeds N/2^s>n/2>=H. It cannot have stopped. This also treats
prefix removal at depth zero.

Put m_j=floor(n/2^j) and

    c_j = # {odd u : H<u<=m_j}
        = ceil(m_j/2)-ceil(H/2), when m_j>H,
    U = sum_j c_j,              V = sum_j j*c_j.

Only j with m_j>H are included. These quantities and all endpoints take
O(log n) integer operations on O(log N)-bit integers, with an additional
logarithmic factor allowed for ordinary bit arithmetic. The inverse image of
the surviving set is the disjoint union

    {2^j*u : u odd, H<u<=m_j}.

Each component is one arithmetic progression. Thus O(log n) descriptors
replace the Omega(n) ordinary consecutive-interval records in the literal
router. This is an executable compact representation, not a cardinality claim.

Let O(H,m) denote the product of the odd integers in (H,m]. Their product
after s rounds is exactly

    A_s = 2^(V-s*U) * product_j O(H,m_j)             (mod N).     (2)

The negative exponent uses the publicly available inverse of 2 modulo odd N.
It is legitimate even when A_s is a nonunit. Equation (2) follows by multiplying
T^s(x)=2^(-s)*x mod N separately over the disjoint inverse images.

## Paid product computation, and why compression is not the missing gain

Each O(H,m_j) is a shifted factorial with step two, computable using monic
block product and multipoint operations in O~(1+sqrt(c_j)) operations modulo N.
Because c_j<=n/2^(j+1)+1, their sum of square-root costs is O~(sqrt(n)).
Alternatively the simultaneous interval evaluator can share equal-length blocks.
The representation construction is now cheap, but neither option makes the
largest odd interval product cheap enough to change the exponent.

For the factoring task one can go further: after checking H! for a factor,
suppose it is a unit. Then every prime factor p<=n of odd composite N is odd
and exceeds H. The single progression of all odd u in (H,n] contains p.
Thus gcd(O(H,n),N)>1. The j>0 progressions in (2) are unnecessary if only a
factor is wanted. A gcd equal to N is resolved by product bisection, whose
leaf integers lie in (0,N), so a nonunit leaf gives a proper factor.
This is the ordinary odd-candidate product method, at N^(1/4) scale up to
polynomial logarithms. The router has not created a new arithmetic identity
for that largest product.

## Consequence for the next search

The literal-router obstruction was caused by insisting on ordinary intervals
in the *image*. Valuation progressions in the *preimage* remove that assumption
and its record cost exactly. This is why the fragmentation proof cannot be a
lower bound on compressed algorithms.

The remaining decisive computation is a faster nonunit test or product for a
long arithmetic progression, with recovery charged. Writing its terms as a
compact modular progression, or renaming that product as an oracle, does not
supply such an operation. Beyond depth s, genuine modular wraps and the history
of prefix exclusions appear; (1) is not asserted there. Any later routing
proposal must give its new exclusion-product recurrence explicitly.

Keep the separate W014 branches alive at their actual scopes: a sparse retained
domain could avoid the full-grid rigidity and full-image bounds, and a changed
global collision computation is not ruled out by a classification of fixed
linear exponent identities. No pending audit blocks developing either route.
