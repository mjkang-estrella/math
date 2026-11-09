# W023: a unit-safe computation and the remaining coefficient cost

Parent construction, 2026-10-08 local. This is an explicit computation of the
W022 binomial target in a composite ring, not a fast factoring result. No
experiment ran. Verified complete improvement: **NONE**.

## Newton iteration removes the nonunit-division issue

Let R=Z/NZ with N odd, A(t)=1-4t, and m=(N-3)/4 for the W022 family.
Start G=1 modulo t. Given G correct modulo t^s, compute

    Gnew = G*(3-A*G^2)/2 modulo t^min(2s,m+1).

Only 2 is inverted. Polynomial additions, multiplications, truncations and
coefficient reductions modulo N are explicit ordinary operations. No factor,
prime characteristic, factorial inverse, or exact huge binomial is supplied.
If e=1-A*G^2, the exact identity is

    1-A*Gnew^2 = e^2*(3+e)/4.

Thus t^s | e implies t^(2s) divides the new error. The solution with constant
coefficient 1 is unique over any ring where 2 is a unit: in coefficient degree
j, the equation A*G^2=1 determines the new coefficient with coefficient 2.
The integral series sum binom(2j,j)t^j is that solution, so the last coefficient
after precision m+1 is exactly binom(2m,m) modulo N. This computes the residue
without encountering or needing to expose a factor first.

This is standard Newton inverse-square-root computation, not a novelty claim.
For a primary implementation reference, FLINT exposes
[nmod_poly_invsqrt_series](https://raw.githubusercontent.com/flintlib/flint/main/src/nmod_poly/invsqrt_series.c)
and dispatches to its generic reciprocal-square-root series implementation.
The fetched wrapper alone is not a proof of all generic ring preconditions;
the constant-term-1, odd-N proof needed here is given above. No package was
installed or used. The documentation URL returned HTTP 403; the raw official
source was retrieved and read. A bounded search found no usable exact prior-art
match for W023 B's decimation-degree claim; that audit remains separate.

With ordinary dense polynomial arithmetic this stores Theta(m) coefficients.
Using fast multiplication and doubling precision, the work is soft O(m)
coefficient operations, or soft O(m*(log N+log(m+1))) bit work via integer
packing and fast integer multiplication. All coefficient values have O(log N)
bits, but the NUMBER of coefficients is large. For m~N this is still roughly
linear in N and loses to known factor-search comparators. It is neither
polynomial in log N nor an improved complete factoring bound.

This corrects the broad wording in the W022 B review that every modular route
must use a nonunit division or expose a factor before reaching the coefficient.
The denominator problem applies to the factorial/ratio route, not to this
algebraic-series route. The latter's obstruction is its long coefficient
prefix. Even direct polynomial powering is another unit-free, large-degree
route, already present in that review's own table. No universal obstruction
to composite-ring coefficient extraction is accepted.

## A short circuit does exist; extracting a coefficient is the hard operation

One can OMIT all truncations and retain the straight-line circuit

    G0=1,  G_(k+1)=G_k*(3-(1-4t)*G_k^2)/2.

After k stages it agrees with the desired series through degree 2^k-1.
Its circuit has O(k) arithmetic gates and uses only the constant inverse of 2.
Its polynomial degree, however, is (3^k-1)/2 over characteristic zero:
the leading degree satisfies d_(k+1)=3d_k+1. Extracting a selected high
coefficient is not one of those circuit-evaluation gates.

The concrete attempted extraction is automatic differentiation / truncated
power-series evaluation of this circuit to order m. That gives the previous
dense Newton computation and still pays Theta(m) stored coefficients. A
root-of-unity trace does not cure this cost by itself: writing x=t^a, the
x^1 coefficient of E_a(x) is the t^a coefficient of E_a(t^a), so evaluating
that trace by ordinary t-adic truncation needs precision a+1, not precision 2.
The ramified substitution cannot be treated as a nonsingular first derivative.

This separates three facts: there is a small circuit describing the needed
prefix; the all-even section's minimal polynomial may have very large degree
(W023 B, under review); and neither supplies a cheap requested-coefficient
algorithm. No arithmetic-circuit lower bound is claimed.

## A concrete middle-coefficient compression attempt

There is more structure than an arbitrary circuit. Write B_j=binom(2j,j),
G_s=sum_(j=0..s-1) B_j t^j, and C_s=G_s^3. Direct coefficient comparison gives

    (1-4t)*G_s' - 2G_s = -2(2s-1)*B_(s-1)*t^(s-1).

Consequently, if c_j=[t^j]C_s, then

    (j+1)*c_(j+1) - (4j+6)*c_j
       = -6(2s-1)*B_(s-1)*4^(j-s+1)

for s-1<=j<=2s-2. Here the requested coefficient of G_s^2 has degree less
than s and is exactly the corresponding coefficient of (1-4t)^(-1), namely
4^(j-s+1). This replaces the dense cubic convolution over this middle range
by a constant-dimensional polynomial-coefficient recurrence with one known
boundary value. It is a specific attempted single-coefficient consumer.

Its exact solution over the integers is

    c_j = 3(2s-1)*B_(s-1)*4^(j-s+1) - 2(2j+1)*B_j,
          s-1 <= j <= 2s-1.

To verify this, 3(2s-1)*B_(s-1)*4^(j-s+1) is a particular solution;
(2j+1)*B_j is a homogeneous solution. At j=s-1, the full-series identity
F^3=(1-4t)^(-3/2) gives c_(s-1)=(2s-1)*B_(s-1), fixing the coefficient -2.
The equality is integral, so it also reduces modulo odd composite N without
requiring any j+1 inverse.

This is useful compression of the *description*, but its displayed solution
still contains the requested B_j. Iterating the recurrence by division again
requires possibly nonunit j+1; an accelerated recurrence algorithm must pay
for its hypotheses or a unit-safe replacement. Substituting these c_j into
the Newton coefficient -c_m/2+2c_(m-1) cancels the geometric particular terms
and returns B_m using its original binomial recurrence. It does not compute
B_m from the boundary B_(s-1) and a power of 4 alone.

The failed shortcut is therefore precise: the small Newton circuit has a
small differential description, but this proposed middle-product compression
has merely recovered the original difficult hypergeometric coefficient. This
does not rule out a different consumer of the circuit.

## Deduplication of a tempting dynamical diversion

In a formal extension with y=sqrt(A)*G, the Newton update becomes

    ynew=(3y-y^3)/2.

This is EXACTLY the critically fixed cubic already developed in W011 A.
It is not a new finite-field absorption mechanism. W011 explicitly separates
formal/real attraction from the size of rational basins and accounts for
the multiplicities at +/-1. The parent checked W011 A before duplicating
that work. The present series computation is useful for correcting the cost
model, but it does not reopen the old dynamical branch on the strength of a
new name.

## Next constructive computation

To improve this route, give an exact single-coefficient consumer for this
specific repeated cubic circuit, with sublinear paid data movement and no
hidden large truncation. A proposed reduction must state what coefficients
each multiplication requests and how the convolution is computed. The
existing dense prefix and full minimal-polynomial approaches are explicitly
priced and rejected. In parallel, the chart branch needs sharing across
charts; a fast kernel separately repeated for each chart is insufficient.
