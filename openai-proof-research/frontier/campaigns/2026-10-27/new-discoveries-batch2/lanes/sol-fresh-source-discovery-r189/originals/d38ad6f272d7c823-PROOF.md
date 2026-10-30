# Two-term failure of the Bessel–Fourier Fejér-kernel conjecture

Status: mathematical proof and exact rational certificate, not yet Lean or
independently reviewed. Credit 0; accepted tally remains 29/30. ONE proposed
source-conjecture refutation. No first-priority claim.

## Exact source and target

Acosta Babb, arXiv:2410.17681v1 (2024), Conjecture 1 p10; published as
*On the rate of growth of Bessel–Fourier coefficients for integrable functions*,
J. Math. Anal. Appl. 559 (2026), 130440, DOI10.1016/j.jmaa.2026.130440.
Root downloaded genuine publisher-version PDF from Warwick WRAP199656 and
visually read complete published pp7 and11: kernel definition and Conjecture1.
Section5 fixes nu=0; the displayed conjecture retains nu as a subscript, but
our nu=0 instance is in scope under either reading. The conjecture asserts
K(alpha,M,x)>=0 for 0<=alpha<=1/2, M>=1, 0<=x<=1, where

  K(alpha,M,x) = sum(m=1..M) (1-m/(M+1)) j_m^alpha J0(j_m*x),

and j_m is the mth positive zero of J0. No change of normalization or weights.
For M=2 this is (2/3) j1^alpha J0(j1*x)+(1/3) j2^alpha J0(j2*x).

We prove K(2/5,2,47/50)<-1/500. Both alpha and x are strictly inside their
source intervals. We also prove K(1/2,2,9/10)<-1/100. These are ONE outcome;
no helpers, endpoint case, plots, or numerical extensions earn extra credit.
We do NOT refute the source's separate slow-decay existence conjectures or
claim their conditional consequences false; this invalidates the proposed
positivity premise and its indicated route only.

## Defining series and rigorous uniform tails

Put q=x^2/4 and define

 J0(x) = sum(k>=0) (-1)^k q^k/(k!)^2,
 H(q) = sum(k>=0) (-1)^k q^k/(k!(k+1)!).

These are the ordinary Bessel J0 power series and its normalized derivative:
J0'(x)=-(x/2)H(x^2/4). They converge normally on compact sets by the ratio
test, which also justifies the derivative identity and continuity.
Let p and h be the respective sums over k=0..19. For 0<=q<=9, the absolute
ratio after index20 is at most 9/21^2<1/2. Consequently

 |J0(x)-p(x^2/4)| <= e = 2*9^20/(20!)^2,
 |H(q)-h(q)| <= eH = 2*9^20/(20!*21!).

This applies to every x used below (all are between0 and6). No floating-point
estimate is used for these bounds.

## Genuine first and second positive zeros

Set A=[2.4048,2.4049], B=[5.5200,5.5201], all terminating decimals exact.
The certificate evaluates p at the four rational endpoints and adds/subtracts
e. It verifies J0(A.left)>0, J0(A.right)<0, J0(B.left)<0, J0(B.right)>0.
It also verifies these whole-interval polynomial inequalities by Bernstein
coefficients (not a grid):

  h(q)>eH for q in[0,9/4];
  p(q)<-e for q in[9/4,5.5200^2/4];
  h(q)<-eH for q in[5.5200^2/4,5.5201^2/4].

The exact conversion for degree d on[a,b] is
 c_k=(b-a)^k sum(j=k..d) a_j binom(j,k) a^(j-k),
 beta_i=sum(k=0..i)c_k binom(i,k)/binom(d,k).
Then p(a+(b-a)t)=sum(i=0..d) beta_i binom(d,i)t^i(1-t)^(d-i).
The basis functions are nonnegative and sum to1 on[0,1], proving the claimed
bounds from min/max of the exact rational beta_i. The script checks every
coefficient and uses strict margins larger than the uniform tails.

Since J0(0)=1 and J0'<0 on(0,3], there is exactly one zero on(0,3], lying
strictly in A. J0<0 on[3,5.5200], so there are no further zeros there.
J0'>0 on B, and its endpoint signs give a unique zero strictly in B by IVT.
Thus these roots are precisely j1 and j2, not arbitrary approximate roots.
Only this initial zero segment is needed; no asymptotic zero theorem is used.

## Exact evaluation at interior parameters

The monotonicity of positive fifth powers and the exact checks

  1.4204^5 < 2.4048^2,  2.4049^2 < 1.4205^5,
  1.9805^5 < 5.5200^2,  5.5201^2 < 1.9806^5

imply j1^(2/5) in[1.4204,1.4205], j2^(2/5) in[1.9805,1.9806].
Here (j^(2/5))^5=j^2 for positive j, the usual real-power law.
Horner interval arithmetic evaluates p on the squared scaled intervals
q=(47*j/50)^2/4, adds[-e,e], and multiplies by the positive weight intervals.
Every operation is exact Fraction arithmetic; all four products are considered
for interval multiplication, including negative J0 values. The final rational
interval has decimal approximations

 [-0.00270118512545915, -0.002199884665157297],

and the script proves its upper endpoint strictly less than -1/500 by exact
integer comparison. Its full rational endpoints are in bessel-exact-certificate.json.
This proves the claimed strictly interior counterexample.

## Half-power check

Similarly, the exact square checks bound sqrt(j1) in[1.5507,1.5508] and
sqrt(j2) in[2.3494,2.3495]. The same interval method at x=9/10 gives

 [-0.012816668840794859, -0.012318919723609718] < -1/100.

This is a redundant witness, not a separate discovery.

## Scope, novelty and remaining gates

Live MathDB365454 has no solutions/replies/comments/attempts as fetched today;
this does not establish novelty. Actual arXiv and published statements match.
The 2024 thesis contains the same conjecture. Bounded initial web and local
registry screens found no matching refutation, but full citing-corpus and
classical Fourier–Bessel positivity/subsumption checks remain open. In
particular ordinary positive Fourier Fejér kernels have different frequencies
and coefficients, and their positivity does not transfer automatically.

No Lean PASS, independent review, manuscript, archive or acceptance is claimed.
The future formal proof must include convergence/termwise derivative, whole
interval Bernstein soundness, first-two-zero identification, literal rpow
weights and a closed source endpoint; rational evaluation alone is insufficient.
