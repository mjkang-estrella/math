# Cauchy strictness: a classical weak-Chebyshev reduction

28 October 2026. Root adjudication: **routine-corollary exclusion recommended;
credit 0**. This is a new objection to the preliminary review's substantive PASS,
not a claim that an explicit earlier resolution of Simon's question was located.
The original six-file review freeze remains untouched. No full Lean endpoint exists.

## Primary theorem actually read

D. Zwick, *Degeneracy in WT-spaces*, Journal of Approximation Theory 41 (1984),
100–113, DOI 10.1016/0021-9045(84)90105-9. The author-uploaded full body is publicly
rendered at https://www.researchgate.net/publication/242815567_Degeneracy_in_WT-spaces .
The web reader exposed the actual article text, including printed pp. 103–104 and
113. The direct shell page returned 403; the initially exposed malformed PDF link
returned 404. The canonical author-profile PDF URL subsequently succeeded in
the web reader as an actual 14-page PDF; `sources/zwick-pdf-web-read.txt` preserves
its page-indexed text, including printed pp. 103–104. Shell access to that URL
returned 403, and the screenshot route did not yield an inspected page image.
These limits are retained: this is an actual PDF-body text reading, not a local
PDF download or a visual PDF audit. No access challenge was bypassed.

On pp. 103–104, Definition 2.2 calls a finite-dimensional function space
nondegenerate if none of its nonzero elements vanishes identically on a nontrivial
interval. Analytic function spaces are explicitly given as examples. The text
states the Stockenberg–Zalik characterization on an open interval: a WT-space is
a T-space exactly when it is nondegenerate and contains a positive function.
Theorem 2.2, attributed to Stockenberg, gives the separated-zero result proving
the needed implication. Corollary 3.2 gives a convenient compact formulation:
an n-dimensional nondegenerate WT-space on [a,b] containing a positive function
is a T-space on [a,b] for n even, and on (a,b) for n odd (also on the two half-open
intervals). We use only the interior conclusion, valid for either parity.

Proposition 1.1 identifies WT-spaces with spaces possessing a basis whose ordered
evaluation determinants are nonnegative; T-spaces have no nonzero element with
n distinct zeros. References [6] and [7] are respectively B. Stockenberg,
*On the number of zeros of functions in a weak Tchebycheff-space*, Math. Z. 156
(1977), 49–51; and R. A. Zalik, *A characterization of Tchebycheff systems*,
J. Approx. Theory 22 (1978), 356–359. Their original bodies were not separately
read. Zwick's body states the exact sufficient theorem used here.

## Shortest bridge: apply the theorem directly to the rational Cauchy kernel

The stable-factor route below is unnecessary for the exclusion. Simon's
1412.0132 Corollary 1 already proves the non-strict statement K_alpha in TP_n
for 0 < alpha < 1/n. Fix 1 <= m <= n and distinct positive t_1<...<t_m. Put

    q_i(x)=x^2+2*cos(pi*alpha)*t_i*x+t_i^2,
    r_i(x)=1/q_i(x),  x>0.

Each r_i is positive and real analytic on (0,infinity). The r_i are independent:
if sum b_i/q_i(x)=0 for every positive x, multiplication by product q_i shows
the polynomial sum_i b_i product_(j!=i) q_j is identically zero. Evaluate it at
rho_i=-t_i*exp(i*pi*alpha). Its modulus is t_i and it is a root of q_i. Each
root of q_j has modulus t_j, so q_j(rho_i) != 0 for j!=i. It follows that b_i=0.
The same argument applies if the relation holds only on any nontrivial interval,
since a polynomial vanishing there is identically zero.

For any compact [a,b] contained in (0,infinity), the m-dimensional span of these
functions is nondegenerate (alternatively, use their real analyticity), contains
the positive function r_1, and is a WT-space by the nonnegative evaluation
determinants in Simon's TP_n conclusion. Zwick Corollary 3.2 makes it a T-space
on (a,b). Given any positive x_1<...<x_m, choose 0<a<x_1<x_m<b (with the evident
choice if m=1). A zero determinant [r_i(x_j)] would produce a nonzero member of
this space with m distinct zeros in (a,b), contrary to the T-space conclusion.
Its determinant is therefore nonzero; the known non-strict TP_n inequality
makes it positive. This is the entire source STP_n conjecture.

Thus the full candidate is an immediate application of the actual classical
WT-to-T theorem to the source's own rational functions, using only the published
non-strict corollary and elementary independence. No stable-density series,
stable-factor strictness, Gram formula, or Andreief identity is needed for this
shortest reduction. The longer bridge below independently checks compatibility
with the proposed proof and preserves its repaired mathematics.

## Complete alternative bridge to the stable factors

Fix 0 < alpha < 1/n, 1 <= m <= n and x_1 < ... < x_m. Write

    a_i(u) = f_alpha(exp(x_i-u)),  U = span_R {a_1,...,a_m}.

We use Simon 1412.0132 Theorem 1 and the source's multiplicative-kernel reduction:
the ordered determinants det[a_i(u_j)] are nonnegative for every u_1<...<u_m.
We also use the classical strictly positive stable density and its convergent
series (the same dependencies as the proposed discovery):

    f_alpha(s) = s^(-1) G(s^(-alpha)),
    G(z) = sum_(k>=1) c_k z^k,
    c_k = (-1)^(k+1) Gamma(1+alpha*k) sin(pi*alpha*k)/(pi*k!).

Stirling gives limsup |c_k|^(1/k)=0, so G is entire. Thus every a_i is real
analytic on R. Moreover c_1,...,c_m are nonzero, since alpha*m < 1.

The a_i are linearly independent. Indeed, if sum_i b_i a_i(u)=0 on R, put
t=exp(alpha*u). After division by exp(u), the entire function

    sum_i b_i exp(-x_i) G(t exp(-alpha*x_i))

vanishes for t>0. Its first m Taylor coefficients give

    sum_i b_i exp(-x_i) exp(-alpha*k*x_i) = 0,  k=1,...,m.

This is an invertible Vandermonde system: the exp(-alpha*x_i) are distinct
positive numbers, and the extra row factors exp(-x_i) and first powers are
nonzero. Hence all b_i=0 and dim U=m.

For any compact [a,b], the restrictions remain independent by the real-analytic
identity theorem. Simon's nonnegative determinants and Proposition 1.1 make the
restricted space a WT-space. Analyticity makes it nondegenerate, and a_1 is
strictly positive. Corollary 3.2 therefore makes it a T-space on (a,b).

Given arbitrary u_1<...<u_m, choose a<u_1 and b>u_m. If the evaluation determinant
vanished, a nonzero element of U would have m distinct zeros inside (a,b), a
contradiction. Thus this determinant is nonzero, and Simon's TP inequality
fixes its sign as positive. This proves the stable factor is STP_n, using an
explicit classical theorem and its exact hypotheses; no Fourier nonvanishing
criterion is being invoked.

## Transfer to the Cauchy kernel

The Gram identity printed in the proof of Simon's Corollary 1 is

    K_alpha(exp(alpha*x),exp(alpha*y))
      = [pi/sin(pi*alpha)] exp((1-alpha)(x+y))
        integral_R a_x(u) a_y(u) exp(-2u) du.

All pairwise integrals are finite by this identity. Expanding the product of two
determinants gives a finite sum; the integral of each absolute summand over R^m
factorizes into a product of those finite pairwise integrals, by Tonelli. This
proves the absolute integrability needed for Andreief, without an extra stable
density tail estimate. Consequently

    det[K_alpha(exp(alpha*x_i),exp(alpha*y_j))]
      = [pi/sin(pi*alpha)]^m exp((1-alpha)(sum x_i+sum y_j))
        integral_(u_1<...<u_m) det[a_xi(u_j)] det[a_yi(u_j)]
                              exp(-2 sum u_j) du.

Both determinants are now strictly positive throughout the chamber. The chamber
is nonempty and open; continuity supplies a positive lower bound on a small
compact box inside it. Its integral is strictly positive. This is precisely the
strict Cauchy-kernel conclusion. The logarithmic coordinate map covers every
positive ordered source argument. No extra positivity assumption on x_i,y_j is
needed: these logarithms are arbitrary real numbers.

## Why this changes the eligibility assessment

The earlier review correctly ruled out the false claim that PF_n plus a nonzero
Fourier transform always implies strictness, using exp(-abs(x)). That example
is not analytic and does not meet the nondegeneracy hypothesis of the theorem
above: suitable linear combinations of its translates vanish on intervals.
It does not address this stronger, applicable classical theorem.

The conclusion now follows by checking analyticity, a short Vandermonde
independence calculation, and positivity before applying a published WT-to-T
theorem, followed by the source's existing Gram formula and strict composition.
Under the campaign's routine-corollary exclusion this should receive zero
discovery credit even if no earlier paper explicitly states the Simon endpoint.
An independent new review of this exact bridge is appropriate when a delegate
slot becomes free. It must test the mathematical transfer, not infer novelty
from the open MathDB label or the absence of a matching title.

## Repairs to the preserved original argument

1. The determinant prefactor is exp((1-alpha)(sum x_i+sum y_j)); there is no
   additional m in its exponent. For a full R^m integral there is additionally
   1/m!, absorbed above by restriction to the ordered chamber.
2. Put z_i=exp(-x_i), w_j=exp(v_j), t=exp(alpha*U). Then exactly

       D_x(U+v)=exp(m*U) prod_i z_i prod_j w_j
                 det[G(t*z_i^alpha*w_j^alpha)].

   The determinant on the right is entire in t. All Taylor coefficients below
   S=m(m+1)/2 vanish because a repeated chosen power yields proportional columns.
   Its degree-S coefficient is

       (prod_(k=1)^m c_k) det[z_i^(alpha*k)] det[w_j^(alpha*k)].

   It is nonzero. Factoring the two Vandermonde determinants yields the corrected
   factors prod_i z_i^(1+alpha) and prod_j w_j^(1+alpha) in the full leading
   coefficient. The remainder is O(t^(S+1)) by analyticity of a single entire
   function; no false uniform bound on exp(-alpha*k*x_i) is required.
3. Analyticity follows from the entire function G and analytic composition,
   not merely from locally uniform convergence of real-analytic functions.
4. Andreief integrability follows from the pairwise Gram integrals as above;
   neither of the original unproved tail rates is needed.

No complete formal certificate, new machinery, first-resolution, global priority,
or count is asserted. The repairs preserve a sound ordinary proof, but do not
overcome the newly identified classical reduction.
