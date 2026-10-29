# Denominator log-concavity: a stronger block route, still unproved

**No full resolution, no nomination, no credit.** The root independently read
published Conjecture 4 and Proposition 3.8 of Ballantine–Beck–Feigon–Maurischat,
Reciprocals of subsum polynomials, Ramanujan J.70 (2026), article46,
https://doi.org/10.1007/s11139-026-01419-0. The intended coefficient inequality
is a_j^2 >= a_(j-1)a_(j+1) for den(n,x), all n>=1 except 3,5,6,7.
The prior completed Sol discrete r6 lane remains untouched.

## Published product and exact regrouping (uncredited)

Let P_m(x)=product_(i=1)^m(1+x^i), with P_0=1. Published Proposition3.8
states den(n,x)=product_(i=1)^n(1+x^i)^(1+floor(log_2(n/i))). Counting the
number of j>=0 with 2^j i<=n gives exactly

    D_n(x)=product_(j>=0) P_floor(n/2^j)(x).

This regrouping is elementary and not claimed as a new theorem. Independently,
the geometric recurrence from the previous lane agrees with it coefficient by
coefficient for n<=64 in root's exact implementation.

## A sufficient four-family statement

Define B_(t,m)(x)=product_(j=0)^(t-1) P_floor(m/2^j)(x).
Consider the following stronger, UNPROVED assertions:

    For each t in {4,5,6,7}, every integer m>=2^(t-1),
    all coefficients of B_(t,m) form a log-concave sequence.

These four assertions imply the entire source conjecture, not merely a fixed
parameter subset. Proof of implication: let L=1+floor(log_2 n). When L>=4,
write L=4q+r, 0<=r<=3. Split the L consecutive binary layers into q-1 groups
of four and one group of 4+r. A group starting at s with length t is precisely
B_(t,floor(n/2^s)); its last layer is nonzero, so its argument is >=2^(t-1).
The asserted blocks are log-concave with contiguous support. Their product is
log-concave by convolution closure. For L<4, direct exact calculation gives
precisely the exceptions n=3,5,6,7 and valid n=1,2,4.

For completeness the closure used here follows from TP2 Toeplitz matrices:
for a positive contiguous log-concave sequence its successive ratios decrease,
which makes every ordered 2x2 Toeplitz minor nonnegative (zeros outside support
preserve this). Matrix multiplication corresponds to convolution; the 2x2
Cauchy–Binet formula is a sum of products of such nonnegative minors. Finite
supports make the relevant sums finite. Thus no unexplained closure premise
is hiding in the conditional reduction.

This is only a sufficient reduction, NOT an equivalence: log-concavity of D_n
does not in general transfer to its block quotients. Proving the four all-order
block assertions is the remaining mathematical task, and may be harder than
proving D_n directly. No induction proving them has been found.

## Why fewer layers cannot give this route

For t factors P_(m_i) with every m_i>=3, the first coefficients are

    a_0=1, a_1=t, a_2=t(t+1)/2,
    a_3=t(t^2+3t+8)/6.

Indeed P_m=1+x+x^2+2x^3+O(x^4) for m>=3. Multiplication gives those formulas
by sorting the compositions of degrees 1,2,3. Consequently

    12(a_2^2-a_1 a_3)=t^2(t^2-13).

This is negative for t=1,2,3. In particular two consecutive dyadic layers fail
for m>=6 and three fail for m>=12. This exact obstruction rules out ordinary
convolution closure on blocks of at most three (irrespective of central
Gaussian heuristics). It is an auxiliary route obstruction, not a counterexample
to the source or a credit-bearing new result.

Nor can arbitrary four block lengths replace the dyadic hypothesis:
P_1^3 P_4 has coefficients (a_2,a_3,a_4)=(7,9,12), with 9^2-7*12=-3.
A general theorem that four P_m factors always suffice is false.

## Verification and limits

block_checks.py enforces a hard512MiB address-space cap. It checks all
coefficient determinants for B_(t,m) with t=4..7 and 2^(t-1)<=m<=160:
153+145+129+97=524 exact instances, zero failures. It independently compares
D_n products to the geometric recurrence through64, verifies the exceptional
set there, checks the symbolic low-degree formula at t=1..11, and checks the
integer grouping rule for4<=L<10000. The arguments above prove the latter
formulas for all parameters; these computations are diagnostics only.

Exploratory checks (not retained as a reproducible full run) also found that
P_1^a P_m can fail for a=1,2,3,4, and that four/five arbitrary P-lengths can
fail; the one exact retained four-factor witness suffices to reject that route.
No broad positive conclusion is based on exploratory samples.

The primary source itself already proves unimodality; it does not imply
log-concavity. Search results on distinct-part partition asymptotics, colored
unrestricted partitions, q-log-concavity in the number of parts, and generic
Bernoulli convolution do not supply a verified full block theorem. In particular,
a weighted Bernoulli summand supported at {0,b} is not a contiguous log-concave
sequence when b>1, so unweighted Bernoulli closure is inapplicable. No claim that
all these related bodies were exhaustively audited is made.

Current public-proof HEAD fetched successfully:67b4fae085cf19003a33f8027410c383b49e5046,
2026-10-29T04:37:11Z. The next tree request returnedHTTP429 and was not retried.
Thus this turn does NOT clear current registry bodies; the completed previous
lane's e1236ab0-era bounded screen remains historical. No acceptance-grade
novelty clearance, full proof, Lean endpoint, paper or proof packet is claimed.
