# BBK positive fractions: finite exact criterion, full conjecture unresolved

Research date: 2026-10-29 UTC. Credit 0; counts remain 3 additional / 33 total.
No complete ordinary conjecture proof, Lean, manuscript or acceptance claim.

## Literal target and source limitation

Banerjee–Bringmann–Keith, arXiv:2601.04014v1, Section 5, defines

G(k,n)=N/Q, N=product(i=0..n-1)(1-q^(2k-1+2i)),
Q=product(j=0..n)(1-q^(2j+1)), k>=1,n>=0.

Conjecture 5.4 asks for a sum z_j(q)/(1-q^(2j+1)) with nonnegative
coefficients in all z_j. The source omits the word polynomial in that
single statement; the motivating examples are polynomials and MathDB372434
explicitly makes them polynomials. This investigation adopts that polynomial
reading. No inference about unrestricted formal-series numerators is made.
The source suppresses dependence of z on n; we allow it, rather than attack
that notation. The related positivity and monotonicity questions are 5.1/5.2.

Actual source HTML was read, including Section 5 and its product definition;
the earlier cached PDF/HTML and corrected root-bbk-handoff-r4 and
sol-bbk-full-refinement-r4 notes were read. Fresh source open and targeted
searches on October 29 found no resolution; that is NOT a novelty clearance.
No new complete live registry audit, journal comparison or independent review
was performed. Current-registry screening is still required before any
candidate investment. Chern–Wang resolves the motivating summed question,
not the literal summands. Liu2605.28012's odd q-super-Catalan factorial ratios
and its Guo recurrences have no established all-parameter bridge to these
odd-Pochhammer quotients. No title-level similarity is used as subsumption.

## 1. A finite criterion (elementary, uncredited)

Set d_j=2j+1, M=n(2k+n-2)=deg N, and
D=M-(n+1)^2=2n(k-2)-1. Then a nonnegative-polynomial decomposition exists
if and only if there are nonnegative real numbers x_(j,a),
0<=a<=D+d_j, satisfying

  sum_(j,a) x_(j,a) q^a product_(l!=j)(1-q^d_l) = N.       (A)

An upper bound below zero means the corresponding numerator is zero.

Proof of necessity of the degree bound: for q tending to positive infinity,
G(q) is asymptotic to -q^D. Every nonzero term z_j(q)/(1-q^d_j) is asymptotic
to -c_j q^(deg z_j-d_j), with c_j>0. Terms with the largest exponent all
have negative leading coefficients, so they cannot cancel. That exponent
must equal D; hence every deg z_j<=D+d_j. Clearing Q now proves (A).
Conversely (A) gives the rational-function decomposition, with every
numerator nonnegative. Its series coefficients are therefore nonnegative
at every order, not merely to the cutoff used in solving the system.

For k>=2, (A) has M+1 coefficient equations and
(n+1)(2n(k-2)+n+1) unknowns, both polynomial in k,n. This avoids the
exponentially growing lcm-period expansion, but does NOT prove feasibility.
It is a rational linear system. A real nonnegative solution, if one exists,
has a rational nonnegative solution by rational-polyhedron theory; no
integrality statement is claimed or needed for nonnegative coefficients.

Let b_r=[q^r]G, 0<=r<=M. An equivalent 0–1 system is

  b_r = sum_(j,a: a<=r, r-a divisible by d_j) x_(j,a).     (B)

Indeed multiplying the truncated difference by Q shows the polynomial in
(A) has all coefficients through degree M zero; its degree is at most M,
so it vanishes identically. This proves the converse without trusting a
finite series cutoff as an infinite identity. A rational Farkas vector y
with all progression sums sum_(r>=a,r=a mod d_j) y_r>=0 and
sum_r b_r*y_r<0 would certify nonexistence. No such vector was found.

## 2. Optional symmetry reduction (elementary, uncredited)

The literal product satisfies G(q^-1)=-q^-D G(q). Thus a decomposition
can be replaced by the average of z_j(q) and
q^(D+d_j) z_j(q^-1). The degree bound ensures this is a polynomial.
It preserves nonnegativity, and gives reciprocal numerators about degree
D+d_j (zeros at either end allowed). Consequently one may impose
x_(j,a)=x_(j,D+d_j-a) without losing real/rational feasibility.
This reduction is proved here but not used by the saved solver.

## 3. Exact certificates obtained, all uncredited fixed instances

103 distinct (k,n) pairs have saved nonnegative rational polynomial witnesses:
2<=k<=12,0<=n<=8 (99 pairs), plus (1,0),(1,7),(11,9),(12,10).
Every complete cleared polynomial identity was verified independently by
verify_saved.py, which imports neither SciPy nor the discovery script and
uses sparse dictionaries and exact Fractions. It also cross-checks 251 series
coefficients per pair, 25,853 in total. There are 130 fractional nonzero
coefficients across the certificates; do NOT describe all numerators as
integer polynomials. No uniform construction has been extracted.

For example, the exact k=4,n=2 certificate is

G(4,2)=(1+q^3+q^5+q^8)/(1-q)+q^6/(1-q^5).

The solver uses floating point only to propose a witness. Rationalization
is followed by full exact identity verification; an unverified solver status
would not count as evidence of a theorem. The scripts retain exact dual
checking should an infeasibility proposal occur. No counterexample occurred.

## 4. Failures, limits and next useful step

The first capped HiGHS run aborted while trying to initialize its default
thread pool; explicitly setting threads=1 fixed it. The initial larger
polynomial matrix hit the 512 MiB address-space cap. A compact 0–1 matrix
removed that storage problem, but HiGHS itself still hit the cap at (15,13).
Both failures are saved. The larger cases (17,15),(19,17),(21,19) were never
reached and are NOT reported as checked. Selected (11,9),(12,10) then passed
within the same cap. No limit was raised. No process remains running.

The full missing step is feasibility for arbitrary k,n, e.g. a positive
recurrence on the z_j, a partition injection constructing them, or a
uniform inequality excluding all Farkas separators. Larger numerical grids
alone would not close it. Earlier divisibility matching, weighted-complete-
intersection, cleared-bivariate-numerator and naive termwise q-Chu–Vandermonde
routes have exact obstructions in predecessor lanes and must not be reused
without addressing those obstructions. All helper reductions and fixed
instances here remain credit zero.

Reproduce the independent verification with `python verify_saved.py` from
this directory. The discovery sweep is `python check_lp.py --max-n 8 --max-k 12`.
Both scripts enforce 512 MiB address-space and CPU limits; the solver also
enforces one thread and a 12-second limit per optimization call.
