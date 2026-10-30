# Weighted BW case (i): a precise obstruction to the proposed SOS route

Research date: 2026-10-29 UTC (local workspace date 2026-10-28).
Solo Sol delegate; only this assigned lane written. No target proof or refutation.
Discovery credit: **0**. No acceptance authority, no Lean verification claim.

## Source and exact target

Mayumi–Kimura–Ohno–Chruściński, arXiv:2403.04199v2,
https://arxiv.org/html/2403.04199v2, Conjecture 1, Eq. (14), asks for every
n>=2, every positive definite omega in M_n(C) with eigenvalues
0<lambda_1<=lambda_2<=...<=lambda_n, and every A,B in M_n(C),

    ||[A,B]||_omega^2 <= (1/lambda_1+1/lambda_2)||A||_omega^2||B||_omega^2,
    ||A||_omega^2=tr(A* A omega).

The body was refreshed, saved and read, including Conjecture 1 and the dimension-two
section. In an eigenbasis put W=omega^(-1/2), X=A sqrt(omega),
Y=B sqrt(omega). Then [A,B]sqrt(omega)=XWY-YWX and the weighted input
norms are the ordinary Frobenius norms of X,Y. This is exactly

    ||XWY-YWX||_F^2 <= c^2 ||X||_F^2 ||Y||_F^2,
    c^2=w_1^2+w_2^2, w_1>=...>=w_n>0.

The equivalent extension to nonnegative weights follows by W+epsilon I and
continuity; there is no inverse substitution at singular W. Dimension one,
if included with a padded w_2=0, is trivial and is not a discovery.
Orthogonalizing Y against X proves equivalence with

    D_W(X,Y) := c^2 (||X||^2||Y||^2-|<X,Y>|^2)-||XWY-YWX||^2 >= 0.

This equivalence of inequalities is NOT an SOS equivalence.

## Prior-lane corrections honored

Read pi-matrix-discovery-r3, pi-weighted-bw-case-i-r4 and, crucially,
root-weighted-bw-adoption-r4/ADOPTION.md before research. The prior all-pairs n=2
identity and displayed rank-one SOS are false and are not used. The full exterior
norm is sum(w_i^2), not (sum w_i)^2; cycle energies cannot be counted as disjoint.
The valid alternating/shear reduction is retained. Case (ii)/Eq. (15) is public,
Eq. (16) is a consequence in the same family, and rank-one/sparse/n=2 results earn
no credit.

## Main obstruction: the sharpened complex deficit is never quartic SOS if w_3>0

This is an elementary route obstruction, not the requested conjecture, and no
new-to-literature priority is asserted. It applies to arbitrary real polynomial
SOS in all real and imaginary entries, not merely a restricted ansatz.

### Lemma 1: Hermitian wedge forms have no kernel on complex decomposables

Let m>=2, z_ab=x_a y_b-x_b y_a for a<b, with arbitrary x,y in C^m. If a
Hermitian matrix H indexed by pairs satisfies z*H z=0 for all x,y, then H=0.

Proof. Substitute the minors and view the result as a polynomial in x,y and their
conjugates. These variables are algebraically independent for purposes of
polynomial identities on C^(2m): the invertible complex linear substitution
x=u+iv, xbar=u-iv (and likewise y) converts to independent real variables.
For a<b,c<d the coefficient of

    conjugate(x_a) conjugate(y_b) x_c y_d

is precisely H_(ab),(cd). No other minor pair contributes this monomial:
the factors x_a y_b uniquely specify the pair ab, with positive orientation.
Thus every entry of H is zero. This fails over real variables, where conjugate
and unconjugated factors coincide and Plucker relations can intervene. QED.

### Lemma 2: quadratic real polynomials vanishing on complex proportional pairs

Every real homogeneous quadratic q(x,y) vanishing whenever y=t x, for all
x in C^m and t in C, and also whenever x=0, is the real part of a complex
linear combination of the holomorphic minors z_ab.

Proof. The conditions at y=0 and x=0 remove the pure x and pure y terms.
Every remaining real bilinear form has the expression

    q(x,y)=Re(x^T A y + x* B y)

for complex matrices A,B. At y=t x, arbitrary t implies
x^T A x+x* B x=0. Replacing x by i x changes the first summand's sign
and leaves the second unchanged. Both summands vanish separately. Hence A is
skew-symmetric. The identity x* B x=0 for all complex x forces B=0:
use x=e_i, e_i+e_j and e_i+i e_j to obtain the diagonal and both off-diagonal
entries. Thus x^T A y=sum_(a<b) A_ab z_ab. QED.

### Lemma 3: SOS of a Hermitian wedge form forces positivity on the FULL wedge

For Hermitian H, suppose F(x,y)=(x wedge y)*H(x wedge y) is a real polynomial
sum of squares. Then H is positive semidefinite.

Proof. A sum of squares equal to a homogeneous quartic can be taken to consist
of homogeneous quadratics: the highest-degree square terms cannot cancel;
constants vanish at zero, and the coefficient of degree two then removes all
linear terms. Every individual quadratic vanishes on y=t x, since F vanishes
there and each square is nonnegative. It also vanishes at x=0. Lemma 2 gives
q_r=Re(l_r(z)) with complex linear forms l_r. Replacing x by exp(i theta)x
and averaging the identity over theta gives

    F(x,y) = (1/2) sum_r |l_r(x wedge y)|^2.

The right side has a PSD Hermitian wedge Gram matrix G. Lemma 1 applied to H-G
gives H=G, hence H>=0. Conversely H>=0 plainly supplies such a sum of squares.
This is an exact equivalence, with no numerical optimization. QED.

### Application to weighted BW

Identify M_n(C) with C^(n^2), use orthonormal matrix units, and define

    Lambda(x wedge y)_ij = sum_k w_k (x_ik y_kj-y_ik x_kj).

Then D_W(x,y)=(x wedge y)*H(x wedge y) for
H=c^2 I-Lambda*Lambda. Put S=sum_k w_k^2. Direct row products give

    Lambda Lambda* = S I - v v*,   v=diag(w) in M_n(C).

For completeness, each off-diagonal output row has squared norm S and supports
no common wedge coordinate with other rows. The i-th diagonal row has squared
norm S-w_i^2; its inner product with the j-th diagonal row is -w_i w_j,
from the shared coordinate E_ij wedge E_ji. Diagonal/off-diagonal rows have
disjoint supports. These statements prove the displayed identity, including
cycle multiplicities.

For n>=2 take eta=Lambda*E_12. Since E_12 is orthogonal to v,

    ||eta||^2=S, Lambda eta=S E_12,
    eta*H eta=(c^2-S)S.

If w_3>0 this is strictly negative. By Lemma 3, D_W is NOT a real polynomial
SOS, regardless of the chosen quadratic monomial basis, rational or irrational
Gram coefficients, or inclusion of conjugated mixed bilinears. This is not a
counterexample to the conjecture: eta is a nondecomposable wedge.

At w=(9,4,1), eta=9 E11 wedge E12+4 E12 wedge E22+E13 wedge E32,
||eta||^2=98 and eta*H eta=-98. In flattened indices (0,1,2,7), its Plucker
polynomial is 9. At w=(9,4,2,1), S=102,c^2=97, and eta*H eta=-510.
The exact checks also include w=(1,1,1), with negative value -3. Thus even the
known unweighted complex inequality illustrates the SOS obstruction: it says
nothing against validity of a nonnegative nonsos polynomial.

### Consequence for constant-degree Plucker Gram searches

A PSD real Gram in the real and imaginary wedge coordinates, adjusted by
quadratic Plucker relations and their real/imaginary parts, would pull back to
a quartic SOS identity for D_W(x,y). The relations vanish identically after
substituting x wedge y, contradicting the application. Hence that exact search
at n=3 or n=4 cannot succeed for three positive weights. In particular one
cannot replace a conjugated cross product z_ab conjugate(z_cd) by the ordinary
holomorphic Plucker identity z_ab z_cd-z_ac z_bd+z_ad z_bc=0. They have different
phase weights. This distinction invalidates that proposed absorption shortcut.

This result does NOT rule out SOS of the original unsharpened deficit
c^2||X||^2||Y||^2-||T||^2, SOS after an extra nonconstant multiplier, rational
certificates, real-only restricted problems, or analytic estimates. No large
SDP was run: the exact obstruction excludes the specified sharpened-degree-four
complex Gram route before numerical investment.

## Current public-source screen and chronology

Fresh retrievals started 2026-10-29T04:39:39Z; exact URL/time/hash receipts are
sources/receipts.json. openai/math HEAD was
7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a (2026-10-26T21:18:03Z).
trureturing HEAD was 67b4fae085cf19003a33f8027410c383b49e5046
(2026-10-29T04:37:11Z). These are current observed heads, not old pins.

The refreshed trureturing Blueprint WeightedBotcherWenzel body states the exact
all-complex case(ii)/Eq15 endpoint and explicitly separates cases(i),(iv).
Its Fang–Cheng library note explicitly says full-text hypotheses were not
independently verified. These actual bodies were read. The root recursive trees
are truncated: no complete current-registry clearance is claimed. The fresh
751-entry openai/math preprint directory listing has no title matching weighted
BW, but titles alone do not exclude a theorem inside another manuscript.

MathDB362175 refreshed unchanged (open, solutions empty); that label supplies no
novelty proof. The original arXiv v2 body gives the complete target above.
Pang, arXiv:2610.29240v1, posted October 21, 2026, was freshly body-read at
Introduction and main scope. It explicitly quotes Fang–Cheng Theorem2.4 for
both rank-one inputs, and solves a different rank-one UNWEIGHTED-output sharp
constant. It does not clear the full Fang–Cheng body. Zhu–Nie,
arXiv:2610.08980v1, posted October6, studies real Toeplitz BW SOS regimes,
a different object. Its scope/introduction was read, not an exhaustive audit.
General SOS literature (e.g. Laszlo arXiv:1207.6372) makes a novelty claim for
our elementary obstruction inappropriate without a much deeper comparison.

The fresh OpenAlex Fang–Cheng record has only a closed DOI location and no PDF.
An author-site search located the author's official publication listing; a
public fetch failed 503. No new direct ScienceDirect request was made after
reading the prior lane's 403. Fang–Cheng 2025 full-body access remains HOLD.

Operational failure: the supplemental directory traversal accidentally iterated
all 751 preprint subdirectories instead of a single complete subtree. Its
exception handler continued after 429s, recording 492 such failures before
completion/stop. This violated the requested stop-on-limit behavior. No bypass,
credential, alternate-IP request or browser was used. All failures are retained;
the script has been repaired to stop on 403/429, the broad loop removed, and
no further GitHub requests were made. Coverage is incomplete, and neither a
registry-clear nor a novelty-clear verdict is issued. Commit-history refresh
failed, so no precise settlement-publication date is inferred from HEAD date.

## Checks and strongest falsifier

Run scripts/exact_checks.py: 384 MiB address-space and 60-second CPU caps;
all BLAS thread environment variables one; pure integer arithmetic, n<=5.
verification/exact.json records exact Lambda Lambda* identities, explicit negative
full-wedge values and nonzero Plucker witnesses. Its finite checks do not prove
the universal lemmas, whose ordinary proofs are above. No numerical search,
formal stub, axiom endpoint or Lean artifact is represented as verified.

The strongest objection would be an error in Lemma2 or a Hermitian wedge-form
relation missed by Lemma1. Their explicit coefficient and phase proofs address
both. A purported degree-four SOS for the sharpened COMPLEX deficit at w=(1,1,1)
would directly falsify the obstruction and should be inspected coefficient by
coefficient. A real-only SOS or an unsharpened SOS would not falsify it.

The remaining target gap is unchanged: establish H>=0 only on decomposable
complex wedges in all dimensions, by a method beyond a quartic SOS of D_W, or
produce actual X,Y violating it. No such proof or X,Y were found. This helper
obstruction requests zero credit and no candidate promotion.
