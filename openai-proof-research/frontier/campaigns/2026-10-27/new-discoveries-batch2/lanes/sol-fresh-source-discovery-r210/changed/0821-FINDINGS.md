# Root special-function screen r6: no nominated discovery

Credit0. Actual MathDB snapshots and actual primary HTML bodies saved.

325585: MathDB references explicitly say the logarithmic-ratio CM conjecture
was confirmed. This is a deprioritization only; the actual cited resolution
body has not been read, so no independent proof or formal claim is made.

325521: root read actual Simon1305.1173 introductory strict-STP conjecture,
and1412.0132 Theorem1, Corollary1, proof2.2 and Remark2(b). The2014/2016
followup PROVES TP_n classification but explicitly leaves STRICT STP_n
open for alpha<1/n. Do not falsely mark strict conjecture solved from the
non-strict corollary. Source explains why fractional integration factors,
which have open zero regions, do not directly transfer strictness.

Potential route (UNVERIFIED in full): the followup gives an exact Gram
convolution of positive stable log-density translates. For any fixed distinct
x_i, the determinant in integration variables is analytic and not identically
zero if the translates are linearly independent. That independence follows
from their nonvanishing Mellin/Fourier transform. Under TP_n the determinant
is nonnegative, hence positive on an open dense subset of the ordered chamber.
The two such open dense sets for x_i and y_i intersect, making the integral
strictly positive. Source stable series should establish analyticity.
This may be a routine generic strict-composition theorem of Karlin and must
be screened before any credit or formal investment. All analytic and known
TP_n inputs would need a literal Lean bridge/reproof, not new axioms.

331384: root read actual Karp1509.05120 Section3 eq6 and Conjecture2. Both
signs for all positive shifts are asked: negative if0<b<1, positive ifb>1.
The normalized series coefficients are
 g_b(a+n)=Gamma(a+b+n)/(Gamma(a+n+1)*Gamma(b)).
Root observation: the0<b<1 half follows from the positive beta-integral
Laplace representation of g_b and the symmetrized double-integral kernel
 1/2 sum_(i+j=k) exp(-i*s-j*t)
   *(exp(-alpha*s)-exp(-alpha*t))*(exp(-beta*s)-exp(-beta*t)) >=0.
This gives the negative sign for the source Turan coefficient. It is a
generic CM-series consequence and is UNCOUNTED; the b>1 half is not proved.
No complete result or Lean for either target. Initial searches no exact
resolution of Karp full Conjecture2 located; that is not novelty clearance.
