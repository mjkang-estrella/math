# Geometric q-Motzkin investigation: A.4 remains unresolved

2026-10-29 UTC / 2026-10-28 America/Los_Angeles. Credit **0**. No nomination,
acceptance authority, full proof, refutation, or Lean investment. Counts remain
3/30 additional, 33/60 total. The formulas and obstructions below are research
helpers, with no claim of novelty in the literature.

## Literal target and source checks

Oh–Scrimshaw, *Identities from representation theory*, arXiv:1805.00113v1,
Appendix A Conjecture A.4 / MathDB339078 asks, for every integer n,k >= 1,

    Delta_n^(2k) = det(M_(i+j+2k)(q))_(0<=i,j<n) in Z_nonnegative[q],
    M_0=1,
    M_(m+1)=M_m + sum_(a=0)^(m-1) q^(a+1) M_a M_(m-1-a).

The source HTML was freshly retrieved 2026-10-29T05:39:38.993233+00:00,
SHA256 ec9caeb98eab3d3c309a3c4f3f509dc827a1779b798426182135b73fb19e830a,
identical to root's cached source. The actual Appendix A and recurrence were
read from that cached source/excerpt. No reinterpretation or domain narrowing.
The journal body is not cleared. Root's ADOPTION corrects the old Pi material:
k=1 routine/uncredited; mixed Gram minor at k=3; old Lean fails. None of the
previously failed generic-weight, sign-gauge, Toda, or Smith-form routes was
rerun as a proposed proof, and no further target positivity grid was made.

Prior-proof screen before significant calculation: reused, as explicitly
permitted, the complete registry trees and head receipts obtained in
sol-fresh-analysis-discovery-r7 on October29 at 04:39–04:43 UTC. Heads:
trureturing 67b4fae085cf19003a33f8027410c383b49e5046;
count-ex-machina dbf673741a54c7dc9d88a6aec0e8148a538f4a3a;
openai/math 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a.
The complete Problems/D5/preprints path listings were screened for Motzkin,
Lommel and Scrimshaw. Actual sibling339076 body was read: it refutes only the
printed shift2 factorization, expressly excluding this positivity conjecture.
The preceding lane's actual Cigler boundary/column bodies and screen were
consulted; their constant-above-boundary parameters differ. Current public
searches returned the exact indexed MathDB339078 statement, but its label is
not prior-proof evidence. No new GitHub API requests (known rate limit), no
MathDB host request (preceding403), and no retries/bypass. These are dated,
bounded checks, not exhaustive current theorem-body or novelty clearance.

Closest primary bodies read: Barnabei–Bonetti–Castronuovo–Silimbani,
JIS21(2018)18.8.8, Sections2.2(f),2.3, and the determinant scope; the exact area
and Jacobi-fraction model is already present. Miller–Stanton, Section3,
Theorem1 and proof give unshifted Smith form, not this shifted positivity.
New closest body: Štampach–Šťovíček, arXiv:1407.0217, Sections2.1–2.2,
recurrence(3), Proposition1 and proof, Corollary2. Their q-Lommel generating
function already contains the formal q-difference mechanism derived below.
Therefore that mechanism is not advanced as a new theorem.

## Exact geometric orthogonal-polynomial bridge

Work over Q(q); all final polynomial identities descend to Z[q]. Set
B=KD on nonnegative heights, D_hh=q^h, K_ij=1_(|i-j|<=1), and
L(x^m)=M_m. To independently check the source bridge: weight a step by
q^(arrival height). For a closed Motzkin excursion, a first horizontal step
has weight1. An initial up step and its matching down step enclosing a
length-a excursion multiply that inner excursion's weight by q^(a+1),
where the extra a comes from raising its a arrivals by1, and the extra1
from the initial up step. The remaining excursion has unchanged weight.
Thus the excursion moments satisfy exactly the literal source recurrence;
L(x^m)=(B^m)_00.

Define monic p_-1=0,p_0=1 and, for h>=0,

    p_(h+1)(x) = (x-q^h)p_h(x) - q^(2h-1)p_(h-1)(x),

with the last term omitted at h=0. Direct induction gives

    p_h(B)e_0 = q^(h(h-1)/2)e_h.

Indeed B e_h=q^h(e_(h-1)+e_h+e_(h+1)), with e_-1=0;
the recurrence cancels the e_(h-1) term with exactly the same exponent.
Since DB=B^T D and D_00=1, polynomial self-adjointness implies

    L(p_i p_j) = (p_i(B)e_0)^T D (p_j(B)e_0)
               = delta_ij q^(i^2).

Consequently Delta_n^0=product_(i<n) q^(i^2)=q^beta_n, by the unit
triangular monic basis change. This also verifies the source's Jacobi
parameters without inferring truth from a catalogue label.

The classical confluent Christoffel identity here is

    Delta_n^r / Delta_n^0
      = (-1)^(nr) det( [x^i] p_(n+j)(x) )_(0<=i,j<r).       (1)

For completeness the algebraic bridge does not require a measure. Let
N=n+r, T_(i,m)=M_(i+m) (0<=i<n,0<=m<N), and let Q be the N by r coefficient
matrix of p_n,...,p_(N-1). Orthogonality gives TQ=0. Write T=[A C] with
A the invertible unshifted n by n moment block, and Q=[U;V] split after n
rows. Monicity makes V unit upper triangular, so U=-A^(-1)CV and det V=1.
The complementary-minor identity for the nullspace of [I A^(-1)C] yields

    det T_J / det A = sign(J,J^c) det Q_(J^c) / det V,

where sign(J,J^c) is the sign of the ordered concatenation J,J^c relative
to 0,...,N-1. This identity follows by expanding complementary wedges of
the row space and its annihilator; its normalization is fixed by J=0,...,n-1,
where both sides equal1. At J=r,...,N-1 this sign is (-1)^(nr), Q_(J^c)
is exactly the coefficient block in (1), and T_J is the shifted Hankel
matrix. This proves (1), including its sign. It works for every n,r>=1,
not just even shifts; it does not prove positivity.

## Geometric q-difference formula and exact signed coefficients

Put t=q^(-1), f_h(x)=q^(-h(h-1)/2)p_h(x). Then

    f_-1=0, f_0=1,
    f_(h+1)=(t^h x-1)f_h-f_(h-1).

In the formal power-series ring Q(t)[x][[z]], F(z,x)=sum_(h>=0)f_h(x)z^h
therefore satisfies

    (1+z+z^2)F(z,x)=1+xz F(tz,x).                         (2)

Iterating is legitimate coefficient by coefficient in z (each extra
iteration has an additional factor z). It gives the exact formula

    F(z,x)=sum_(j>=0) x^j z^j t^(j(j-1)/2)
                  product_(ell=0)^j (1-t^ell z)/(1-t^(3ell) z^3),

and hence

    C_(i,m)(t) := [x^i]f_m(x)
      = t^(i(i-1)/2) [z^(m-i)]
           product_(ell=0)^i (1-t^ell z)/(1-t^(3ell)z^3).  (3)

Set C=0 for m<i. Formula(3) is finite coefficient extraction, with no
analytic convergence assumption, irrational parameters, or denominators in
its resulting Z[t] polynomial. It makes the remaining all-shift task exact:

    Delta_n^(2k) = q^( beta_n + sum_(j=0)^(2k-1) binom(n+j,2) )
                       det C_(i,n+j)(q^(-1))_(0<=i,j<2k).  (4)

All positive monomial factors and inversion preserve coefficient signs.
Thus proving every determinant in (4) is coefficient-nonnegative in t is
EQUIVALENT to the full source conjecture, not a solution of it. Possible
negative powers disappear in (4) by identity(1).

## New-to-this-lane obstruction within the geometric coefficient route

The coefficient matrix in (3) is not coefficientwise nonnegative even up to
independent row/column signs or Laurent monomial rescaling. An exact entry is

    C_(3,6)(t) = t^12-t^8-t^7+t^3 = t^3(1-t^4)(1-t^5).

Multiplying this entry by any nonzero signed Laurent monomial cannot remove
both signs. In the original polynomials,

    [x^3]p_6(x) = q^3-q^7-q^8+q^12.

Even a smaller coefficient minor fails:

    det C_(rows 0,2; columns 3,4) = t^4-t,
    det ([x^i]p_j)_(rows 0,2; columns 3,4) = q^5-q^8.

To verify without a large computation: f_3 has coefficients C_03=1,
C_23=-(t+t^2+t^3), while f_4 has C_04=-1,
C_24=t^2+t^3+t^4, giving t^4-t immediately. Repeated use of the three-term
recurrence gives the displayed C_36, and (3) independently reproduces it.
Therefore a path-matrix representation with all coefficient-positive edge
weights for this whole coefficient array, or simple diagonal scalar signing
of that array into a coefficient-positive matrix, is impossible. This is a
strictly geometric obstruction, not a rerun of the independent-height failure.
It does NOT exclude a different network for the target determinants, nontrivial
basis changes, area-preserving cancellations, or determinant-specific identities.
The positive pointwise factorization of C_36 is insufficient for the requested
coefficientwise conclusion. No credit is claimed for this obstruction.

## Classical q-Lommel identification and its parameter obstruction

The actual primary recurrence(3) of Štampach–Šťovíček is

    F_(h+1)(a,Q;X)=(X-(1+a)Q^(-h))F_h-aQ^(-2h+1)F_(h-1).

Let a be either primitive cube root of1 and c=1+a. Then c^2=a, and direct
substitution proves

    p_h(x;q)=c^(-h) F_h(a,q^(-1);cx).                    (5)

The initial conditions and both recurrence coefficients match, proving this
identity for all h. This is an algebraic specialization of a classical family,
not new q-orthogonal polynomials. Their Proposition1 / equation(12) is the same
formal mechanism as (2) after this specialization and normalization.
The cited Proposition1 assumes a>0, and the surrounding analytic measure
results keep that assumption. Formal identities can be continued algebraically
or proved directly as above; positive-measure conclusions cannot simply be
imported through a complex parameter.

In fact no positive real a and real spectral scaling c can match the two
recurrence coefficients in this ansatz: one needs (1+a)/c=1 and a/c^2=1,
so a^2+a+1=0. Equivalently a/(1+a)^2<=1/4 for a>0, whereas the required ratio
is1. This exact mismatch identifies why this natural classical positive-real
specialization does not supply coefficient positivity. It is not a proof that
all q-Lommel literature or other transformations fail to subsume A.4.

## Validation, strongest objection and handback

`python check.py` is runnable from any directory and writes checks.json beside
it. Before importing algebra code it sets RLIMIT_AS=512MiB, CPU=60seconds,
BLAS/OMP/MKL threads1. It compares all91 coefficients through f_12 computed by
the recurrence against independent finite-product convolution, verifies (1)
on four selected shapes including odd shifts, and records exact mixed entries
and minors. These validate formulas and failure witnesses, not the all-n,k
positivity claim. No target positivity grid or numerical proof was used.
The source downloads are reproducible via fetch.py, subject to public access;
no retries occur. An attempted optional bs4 extraction failed with
ModuleNotFoundError and was replaced with stdlib HTMLParser; this failure is
preserved in progress.md. No mathematical diagnostic hit a resource limit.

Strongest objection: equations(1)–(5) are classical algebraic reformulations;
we have not controlled cancellation in the even coefficient-block determinants.
The mixed entries/minors disprove only stronger sufficient mechanisms, not
A.4. This is not an eligible discovery or a nomination. The precise remaining
gap is nonnegativity of det C_(i,n+j)(t) for every n,k>=1 and 0<=i,j<2k,
or an exact negative coefficient of one such determinant. No uniform
area-preserving involution, positive determinant evaluation, or refutation was
found. No PROOF.md or Lean work is justified by this incomplete outcome.
