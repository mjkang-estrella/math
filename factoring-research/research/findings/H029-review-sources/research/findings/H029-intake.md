# H029 — Parent intake: capacity of same-base power differences

2026-10-08. **UNREVIEWED symbolic derivation.** No experiment or implementation.
Verified full factoring complexity improvement: **NONE**.

## Why revisit the cover branch

H004 accepted a costed prime-cover reduction, but its proposed progression
failed. The live lattice and number-field tasks do not address this deterministic
construction problem. Power differences have both cheap modular evaluation
and algebraic identities, making them a specific candidate for a new cover
with a recursive leaf routine. Neither property supplies coverage or factoring.

The coordinator rechecked the primary [Umans–Wang paper, sections 3, 5–7](https://arxiv.org/html/2511.10851v1).
Its conjectural structured covers require separate construction and prefactoring
obligations. The paper already considers prime coverage, a CRT characterization
of progression coverage, and short addition sequences. Its conditional 1/6
integer exponent is not an established uniform algorithm. These facts motivate
the interface, not a novelty claim. H004's accepted review additionally requires
interval products for all d<=N and strips multiplicities from the original N.

## A specific proposed obstruction

Let R>=2 and L>=log 2. Let B be a finite set of integer bases a>=2 with
log a<=L. Natural logarithms are used throughout. For each a put

    H_a=floor(L/log a).

Consider ANY set of nonzero leaves, each of the form a^x-a^y for one a in B
and distinct integers 0<=x,y<=H_a. Both terms therefore have logarithmic
height at most L. Exponent subsets, their number, and their generation can
be arbitrary; enlarging to all permitted pairs is safe for the following count.

Define the positive integer

    P_a=a * product_{h=1}^{H_a}(a^h-1).

For x>y, a^x-a^y=a^y(a^(x-y)-1). Every prime divisor of any allowed leaf
therefore divides P_a. Signs do not matter. This is a statement about prime
support; it does not claim that each leaf, with its multiplicities, divides P_a.
Including a in P_a is an upper-bound convenience even if all selected pairs
have y=0. The factor a^1-1 may equal one and causes no problem.

Consequently, if the union of these leaves covers EVERY prime at most R,
the squarefree primorial through R divides product_{a in B} P_a. Hence

    theta(R) <= sum_{a in B} log P_a
             <= sum_{a in B} (1+H_a(H_a+1)/2) log a
             <= |B| [L²/(2 log 2) + 3L/2].             (1)

The last step uses H_a<=L/log a, log a>=log 2, and log a<=L. No assumption
about prime factors of the bases, orders, or residue randomness enters (1).
The primorial need not be constructed: it is used only in the argument.

The already accepted H004 prime-capacity premise theta(R)=Omega(R) would give

    |B| L² = Omega(R).                               (2)

It can also be obtained directly from the primary prime-count inequalities
verified in H026: the primes in (sqrt(R),R] give, for sufficiently large R,

    theta(R) >= (log R)/2 * [pi(R)-pi(sqrt(R))]
              > R/2 - 1.25506 sqrt(R) = Omega(R).

Thus if L<=R^(alpha+o(1)) and |B|<=R^(kappa+o(1)), with fixed nonnegative
alpha,kappa and kappa+2alpha<1, this family cannot be a universal prime cover
for all sufficiently large R. In particular a subpolynomial number of bases
cannot realize logarithmic height R^(1/3+o(1)), even if every exponent pair is
available without cost. This strengthens a capacity screen for this particular
family by counting possible exponent gaps instead of all repeated leaves.

## Boundaries and constructive task

The argument covers only differences whose two terms have the SAME base.
It does not cover cross-base differences, signed bases, rational bases,
products of independently based powers, arbitrary short arithmetic circuits,
larger heights, or unrestricted growing menus. Equation (2) is a necessary
capacity condition, not a sufficient construction and not an algorithmic
runtime lower bound. No claim of novelty is made for this elementary count.

It requires coverage of all primes through R. An N-dependent construction
that only targets the actual divisors of N need not satisfy that requirement.
For example a=N+1 with exponents 1 and 0 gives a-1=N and covers all its prime
factors, yet leaves the entire factoring task at one leaf. This illustrates
the missing extraction obligation; it is not a counterexample to (1).

The new child should check this calculation, then attempt a concrete cross-base
or input-dependent construction with an actual paid leaf routine. Reusing a
known power-order method without changing its full cost is not an improvement.
No safe-prime infinitude, cheap order oracle, or factoring of cyclotomic values
is assumed. Any survivor needs independent review and a separately registered
experiment before code work. The H004 failed experiments remain unchanged.
