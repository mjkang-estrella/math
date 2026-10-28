# Source screen: even-shift q-Motzkin Hankel positivity

28 October 2026; no discovery or credit claim. Root read actual arXiv
1805.00113v1 HTML, Appendix A Conjecture A.4 and surrounding discussion.
Actual abs history lists v1 only; journal reference Discrete Math.342(9)
(2019)2493–2541, doi10.1016/j.disc.2019.05.020. Published body not yet read.
Raw actual HTML and extracted text are retained locally; retrieval.json hashes
it. The web reader rejected the large HTML, so root used a lawful ordinary
HTTP download and stdlib HTML text extraction, with no challenge bypass.

The literal recurrence is M_0=1,
M_(n+1)=M_n+sum_(r=0)^(n-1) q^(r+1) M_r M_(n-r-1).
Conjecture A.4 / MathDB339078 asks every k,n>0:
det[M_(i+j+2k)]_(i,j=0)^(n-1) in Z_nonneg[q]. The surrounding primary
explicitly reports failure for higher odd shifts, and says its existing LGV
path model does not directly provide an edge weighting for this statistic.

Important prior-art scope distinction: the cached public trureturing problem
`oh-scrimshaw-2018-two-shifted-q-motzkin-hankel-refutation.md` resolves the
DIFFERENT explicit factored formula at shift2, MathDB339076. Its n=3 witness
is a missing constant term in the printed formula, with actual determinant
q^11(1+q^2+q^3). The record explicitly leaves the corrected formula, shift3
and positivity conjecture outside scope. Thus it does not refute A.4 and
must not be misrecorded as excluding MathDB339078. Fresh live registry and
published-source checks remain necessary before any nomination.

Possible UNPROVED route: formal generating recurrence suggests
F(z)=1/(1-z-q*z^2*F(q*z)), hence a Jacobi fraction with a_h=q^h and
b_h=q^(2h+1), satisfying a_h*a_(h+1)=b_h. A symmetric Jacobi matrix would
make even-shift Hankels Gram determinants, proving pointwise positivity,
but squares can have negative coefficients: that alone does not prove the
actual coefficientwise conjecture. A sign-controlled path/minor expansion
or a genuinely new counterexample would still be required. No completed
mathematical proof, Lean endpoint, novelty or eligibility claim is made.
