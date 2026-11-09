# W003 Lens A — coordinator disposition

2026-10-08. **Accepted at the scopes below; this realization is closed as a
factoring speedup.** Verified new COMPLETE classical factoring improvement:
**NONE**. The research objective remains active.

The coordinator consumed all 667 lines of the
[independent review](W003-twisted-review.md), its source notes, and the
511-line [original submission](W003-twisted-submitted-draft.md). All 66 review
input snapshots and all 72 review delivery entries verify. The review SHA-256
is `f9d41aa781c405aff39c34ee44c18098fd88d0135762218f21c309c112944495`.
The original submission, intake, source records and manifests remain unchanged.
This disposition governs their historical UNACCEPTED labels. The separate
Lens B review was still live at this disposition and is not accepted here.

## Accepted construction and failure

The literal program selects u=R+2N, D_1=u^2+N, D_2=u^2+3N and
K_i=Q(alpha_i), alpha_i^2=D_i, then uses the ordered rows (j,1) for
1<=j<=n=bit_length(N). Paid elementary cases precede the raw-word outer
trial. Each continuing cofactor is odd and has at least two distinct prime
divisors; unequal repeated exponents are allowed.

The consecutive-square arguments prove irreducibility, distinct fields and
O(n)-bit heights without factoring a discriminant. Evaluation alpha_i -> R
has unit derivative 2R. The exact rational-coordinate root tests terminate
on squares and nonsquares with polynomial bit cost in their actual input
width. The trace argument in review section 4 independently proves
(2alpha_i)w in Z[alpha_i] for the integral roots encountered. Thus the
localized recovery formulas and their unit checks are valid.

At the negative real embedding, every nonzero rational-pair row
a^2-b^2 alpha_i is positive, while alpha_i times a nonzero square is
negative. Both mixed targets are impossible. This also covers any finite
enlargement, integer exponents, and common rational scalar multipliers as
specified in review section 5. It does not cover arbitrary field elements,
totally positive generators, complex fields or all factoring algorithms.

The field phase consequently contributes zero success probability. All
success comes from the stated earlier gcd or recognized-root branches.
The ordered CRT calculation, including stopping at a full gcd before later
rows, validates the exact success law

    sigma_N = (N-1-phi(N) + |U_N| + (2^r-2)|J_N|)/2^n.

Here U_N counts unit words whose scan first returns a proper gcd, while J_N
counts unit-square residues whose scan first returns a root. For distinct
N=pq with p,q>2n this becomes

    sigma_N = (2n+1)(p+q-2-2n)/2^n.

On balanced distinct semiprimes, sigma_N=Theta(n/sqrt(N)), and the probability
of reaching all 2^n subset masks is bounded below by a positive constant.
The literal program has expected split cost between Omega(N^(3/2)/n) and
N^(3/2)poly(n). These are bounds for that program only. The all-input
complete-factorization upper bound is N_0^(3/2)poly(log N_0), with polynomial
working space, paid preprocessing at every node and a polynomial-size factor
tree. The iid cold restart identity uses independence between trials, not
independence of cost and success within a trial.

Pruning the impossible field phase preserves every word's success/failure
outcome. It leaves polynomial trial work and complete expected cost at most
N_0^(1/2)poly(log N_0), still with Theta(sqrt(N)/n) trials on the balanced
family. Ordinary trial division already supplies the same conservative power
and space upper envelope deterministically. This pruning is not a new
factoring complexity result.

## Governing correction and qualifications

At original line 425, read **“a square root of unity”**, replacing “a root
of unity.” Only the kernel of squaring has the stated two elements modulo an
odd prime power. No quantitative formula needs alteration. The original
bytes remain preserved; this correction governs future use.

Use “typical” only with the explicit constant-probability search-reaching
branch, not a probability tending to one among all raw words. The k-trial
formula is a split law at fixed N, not completion of a whole factor tree.
Reapply primality/perfect-power handling after each split. Dixon/NFS time
comparisons do not assert a polynomial-space bound for those algorithms.
Unlimited restarts are an expected-time construction, not a bounded-error
polynomial-time theorem.

## Next action

No test, larger cap, implementation or Lean work is selected for this
selector. A changed generator must separately pay for field selection,
target attainment, useful probability and reconstruction. The parent is
checking a different, provisional norm-certified field law; this disposition
does not accept it or import any yield theorem into it. Resume the separate
Lens B review when its completion event arrives. Exact handles remain in
[tasks-W003.json](../tasks-W003.json).
