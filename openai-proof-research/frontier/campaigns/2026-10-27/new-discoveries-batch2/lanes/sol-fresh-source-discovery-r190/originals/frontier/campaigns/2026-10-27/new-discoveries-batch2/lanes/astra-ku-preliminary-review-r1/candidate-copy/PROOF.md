# Provisional Ku torus result — credit 0

Source: Kuo-Han Ku, arXiv:2606.12880v1, printed pp.20–21,
Conjectures5.3 and5.4. Actual p21 rendered and read by root. No acceptance,
independent review, manuscript or novelty clearance yet.

## Exact witness inside the intended domain

On (Z/6Z)^2 take the fourteen points listed in verify_witness.py (k=6).
Every row, column, positive diagonal and negative diagonal contains at least
two. The direct integer checker verifies the four families and independently
all parametric lines p+t*v, t=0,...,5, v in {-1,0,1}^2 minus {0}.
The literal Lean module Counterexample.lean independently proves this using
kernel reduction, including cardinality14 and a closed negation of Conjecture5.4
even after restricting k>=6. This does not resolve Conjecture5.2 or the MathDB
record375265 (which concerns the separate hypercube Conjecture5.6).

The printed Conjecture5.4 also allows k=3, where all but one point is an
immediate counterexample. That wording defect is not a discovery. The preceding
paragraph explicitly discusses k in3N minus {3}; the k=6 witness meets that
intended scope. Whether the interior refutation is substantively countable
still requires independent judgment. All witnesses form ONE prospective family.

## General moment obstruction and proposed stronger lower bound

The no-size2n part below is now fully formalized in Moments.lean and
SourceUniform.lean. The closed endpoint source_conjecture53 proves the literal
four-direction torus Conjecture5.3 for every positive multiple of3. A fresh
temporary-copy replay passes25 declarations/3 modules under warnings-as-errors;
all actual type and axiom reports were read by root, and only the standard3
axioms occur. This is a root preliminary replay, not independent review.
Neither infinite-grid density definitions nor the source's equivalence theorem
have been formalized; do not advertise a literal Lean endpoint for the grid
MathDB claim. The extra exclusion of size2n+1 below remains mathematical only.

Let 3 divide n>0. If A meets every one of the four line families at least twice,
then |A|>=2n+2. Rows give |A|>=2n. Write S_j=sum(i^j,i=0,...,n-1).
For |A|=2n every line count is exactly2. Summing
(x+y)^2+(x-y)^2=2x^2+2y^2 modulo n gives 4S_2=8S_2 mod n,
and hence n divides4S_2.

For |A|=2n+1 each family has a unique excess line of count3, all others count2.
Let their labels be r,c,s,d for x,y,x+y,x-y. First moments and
2S_1=n(n-1) give s=r+c and d=r-c modulo n. The second-moment identity gives
4S_2+s^2+d^2=8S_2+2r^2+2c^2; substitution again yields n divides4S_2.

But 6S_2=n(n-1)(2n-1), so 3*(4S_2)=2n(n-1)(2n-1).
Writing 4S_2=nq and cancelling n gives3q=2(n-1)(2n-1), impossible
modulo3 when3 divides n. Both small sizes are excluded.

Thus the displayed witnesses at6,9,12,15 attain the proposed general lower
bound. The witness checks are exact; all-order attainment has NOT been proved.
The no-size2n part proves Conjecture5.3 and, by source Theorem3.8 mathematically,
Conjecture5.1. This may be a classical generalized Pólya obstruction; do not
claim novelty before actual primary-body screening and independent review.

## Excluded hypercube detour

The source's Conjecture5.6 is false already by the density Hales–Jewett theorem
(Polymath, arXiv0910.3926, Theorem1.4): a near-line-avoiding set is in particular
combinatorial-line-free. For fixed k>=3 its density therefore tends to zero
with dimension. A finite k=3,d=3 search gave maximum6/27, but this is not counted
as a fresh refutation of an already classical corollary.

## Closest prior investigation, bounded

Halleck, Magic square subclasses as linear Diophantine systems (UCSD thesis,
2000), actual pp.92–94: Proposition7.2.1 says that pandiagonal squares of
orders2 and3 are constant; Proposition7.2.2 gives reduction modulo a divisor;
Corollary7.2.3(2) says an integral pandiagonal square of order3q has index
divisible by3 when3 does not divide q. This DIRECTLY covers Conjecture5.3
for orders divisible by3 but not9, through the indicator matrix with index2.
That portion is known and cannot count. The root moment proof covers all
orders, but a general older divisibility theorem may subsume it. The shared
Pólya mechanism also makes substantive eligibility a real question. No
countable novelty decision has been made. Do not call this full-prior clearance.

Costalonga, Toroidal boards and code covering, AJC76(1)(2020)41–54:
the actual main theorem bodies and definitions retrieved in the public full
text describe semiqueen domination (covering cells by queen moves), not
two-fold intersection with every line. It does not directly supply this witness
or line-cover obstruction. This is only one checked neighboring source.
The author's2025 thesis was retrieved as a public multipart response with PDF
bytes extracted; it states strictness for k=6 but the relevant chapter does not
display the fourteen-point construction. Novelty remains unassessed.
