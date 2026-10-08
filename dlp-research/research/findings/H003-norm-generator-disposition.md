# H003 norm/coefficient generators: explicit scans, missing fast witnesses

Claude Opus developed three variants under the recorded task, no repository
edits or children. None supplies a credible improved complete solver. Root
checked the m2 algebra and optimized cost gate below. Raw report is not accepted
as a set of theorem-level exclusions or calibrated arithmetic costs.

## Concrete variants

For R=(r,y_R), a line y=lambda(x−r)+y_R has remaining intersection abscissas
x1,x2 with s=x1+x2, t=x1*x2. Comparing cubic coefficients gives
`lambda²=r+s` and `t=a+2r²+r*s−2*y_R*lambda`. This assumes y_R≠0 for the inverse
parameterization, automatic for nonidentity points of our odd prime-order group.
The line's three intersection points sum to O, with multiplicities handled.

G-A enumerates s<2X, takes both square roots of r+s, derives t and tests the
integer discriminant and root ranges. A successful witness is verified on the
curve. It costs O(X) square/character/root operations per target, not sublinear
generation; ordinary hash-based scans are required comparators. For X²>=p the
integer t lift may have multiple representatives and must be explicitly enumerated;
the pseudocode's one representative is only adequate in the small-box regime.
General coefficient-box enumeration leaves splitting/root extraction as the
missing primitive. Uniform-box losses are heuristics, not lower bounds.

G-B proposes fixed-parameter Coppersmith-style shifts of the summation polynomial,
LLL and integer resultants. A Howgrave-Graham norm condition makes a particular
short polynomial vanish at a small root; it does NOT guarantee enough algebraically
independent short polynomials, complete extraction, or a successful decomposition.
Constant dimension can give polylog work for that fixed basis, not a capacity
theorem. The raw `X<=p^(1/D_m)` capacity assertion is heuristic, not a proved
upper bound on every multivariate construction. No Newton-polytope or lattice
experiment is funded until an exact basis/extraction procedure with a meaningful
candidate cost is supplied.

G-C uses a multiplicative-coset x-base when K|p−1. Membership can be encoded by
`z^K−1` divisibility. For a monic quadratic z²−s'z+t', define U0=0,U1=1,
U_(j+1)=s'U_j−t'U_(j−1). Then z^K=U_K*z−t'*U_(K−1) in the quotient algebra;
gcd conditions can recover candidate line slopes. The explicit polynomial degrees
grow with K, and the proposed construction costs roughly a K-scale scan. A
constant number of polynomial operations is not constant work. Generic Bezout
degree estimates are not runtime lower bounds on all tower solvers.

## Corrected full-work gate

Under the stated uniform-sum heuristic, use B≈X representative x-classes (up to
constant factors), relation density about X^m/q, decomposition cost X^tau,
and sparse-algebra cost X². With explicit coverage/rank assumptions the rough
total is `q*X^(tau−m+1)+X²`, plus setup, witness checking and target recovery.
Both y signs in the literal affine factor base give about X points; X/2 refers
to one representative per admissible x, not both signs. Keep this convention fixed.

Set X=q^alpha, with alpha<=1/m in the rare-relation regime. An exponent below1/2
needs `alpha > 1/[2(m−1−tau)]` and `alpha<1/4`. Hence SOME feasible alpha exists
only if `tau < min(m−3,m/2−1)`, under these assumptions. Root independently
checked this optimization. At m4 and FIXED X=q^(1/5), however, tau must be<1/2,
not merely<1 as the report's concluding suggested parameterization implies.
The weaker tau<1 existential gate requires different alpha. No unconditional
relation density/rank/success theorem is established by this ledger.

Relations containing Q can absorb target recovery into the same linear system,
but a nonzero recovery denominator and adequate independent rank still need
probability/restart accounting. Generating targets along a walk is not a theorem
that the targets are independent uniform samples. Transferred large-prime
exponents are NOT adopted without complete applicable relation-graph hypotheses.
The report's negation-rho constants,6M+1S kernel price and negligible-memory
phrase are not calibrated complete-work baselines in this project.

## Scratch-check provenance and decision

The brief requested no execution of its proposed tests. The report says both
'no experiment' and that two scratch scripts checked degrees and200 random
identities each. No exact commands, source, seed, counters or output were supplied;
the '<1k field operations' statement is unverified. These are unrequested checks,
not accepted compliant evidence. No rerun is authorized merely to validate them.
The m2 line and quotient-polynomial identities above can be checked symbolically;
reported S4 degree12 and extrapolated S5 degree32 are not experimental findings
adopted here. Preserve the failure rather than hide it.

Decision: retain G-A/G-C as explicit unfavorable scans, G-B as an unspecified
capacity/extraction conjecture. No cheap relation generator or exponent improvement.
The proposed m2 lattice calibration does not justify escalating to m4/m5 without
a bridge; its event budget was an estimate, not an instrumented implementation.
Next qualifying submission must produce witnesses with the actual setup, coverage,
rank and arithmetic exponents passing the corrected gate. No generic Lean work.
