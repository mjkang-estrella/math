# Fresh analytic screen — 2026-10-27 — no credit

All proposed new results below are UNFORMALIZED, UNREVIEWED, and have no discovery credit.
Actual source PDFs and complete live MathDB records are retained in sources/.

## Exclusions and open distinctions
- 353636: a full Shivam Patel posted solution, 20 August2026, id5d146176-e3a0-41e3-89d6-696d8f2761ce, already gives the exact dispersion identity and sharp constant. Full API solution read. No rediscovery credit.
- 372380 Henry: Liwen Gao, Axioms2026,15(8),577, DOI10.3390/axioms15080577, Corollary1 proves the conjecture. Actual primary full-text body was served through web search and read; publisher direct HTML/PDF/XML requests blocked. No PDF-read claim. Save an accessible complete body before using its other conjectures as a formal target.
- 347932: Segura successor2010.11118 Theorem5 is a likely exact prior resolution. The transformation between W_n and the original F_n still needs explicit verification before recording exclusion.
- 414106: newest source2610.33699 already refutes older integer-versus-real degree claims and determines integer parts. Its exact-real-degree question is still separate and unresolved here.
- 339000: symmetry forces odd derivatives at1/2 to vanish. This endpoint-only correction is uncountable. The substantive all-order interior claim is the prospective proof below.

## Prospective Ramanujan all-order proof (339000), not yet novelty-screened or Lean-proved
Actual source1804.07712v1 Theorem1.3(3), equation1.19, Conjecture5.3.
Let y=x(1-x), R=-2gamma-psi(x)-psi(1-x), B=pi/sin(pi*x), F=R-B/(1+y).
For n>=1 set N_n=n(n+1), epsilon_n=(-1)^n,
a_n=(2n+1)/(N_n-1), C=1-sum(epsilon_n*a_n).
The a_n decrease from3 through1 to0, so alternating-series bounds give3<C<4.
For n>=2 set w_n=(2n+1)*(1+epsilon_n/(N_n-1))>0; w_1=0.
With rho=F(1/2)=4log2-4pi/5>0, the proposed exact representation is

F(x)=rho+C*(1/(1+y)-4/5)
       +sum_{n>=2} w_n*(1/(N_n+y)-1/(N_n+1/4)).

Derivation uses the classical digamma/cosecant partial fractions
R=sum_{n>=0}(A_n-2/(n+1)), B=sum_{n>=0}epsilon_n*A_n,
A_n=(2n+1)/(N_n+y). The n=0 contribution after subtraction is1/(1+y).
For n>=1 the identity is
(1-epsilon_n/(1+y))*A_n = w_n/(N_n+y)-epsilon_n*a_n/(1+y).
Subtract the value at1/2 to remove convergent constants. The resulting difference sum converges absolutely and locally uniformly.

Let alpha=(1-sqrt5)/2 and beta=(1+sqrt5)/2. For k>=1,
(-1)^k F^(k)(x)/k! =
 C/sqrt5*((x-alpha)^(-k-1)+(-1)^k*(beta-x)^(-k-1))
 +sum_{n>=2}(1+epsilon_n/(N_n-1))*
       ((n+x)^(-k-1)+(-1)^k*(n+1-x)^(-k-1)).

Every summand is strictly positive for0<x<1/2: even k gives a sum; odd k gives the difference of inverse powers with first denominator smaller. At1/2 odd derivatives vanish, even derivatives remain positive. The k=0 representation gives F>=rho>0. Derivative series have uniformly summable absolute tails on compact subintervals (already k=1 suffices). This would settle the intended all-order complete monotonicity, rather than count an endpoint wording issue.

Outstanding: independently verify every infinite-series interchange; actual published target and citation/follow-up search; exact source interpretation and eligibility; literal digamma-series Lean bridge (Mathlib digamma exists but the needed partial-fraction theorem is not yet identified); independent adversarial review; paper/packet.
A2022 paper New properties for the Ramanujan R-function DOI10.1515/math-2022-0045 has a different f3=(2-y)R-1/y. Its entire body and potential implications still need comparison; do not infer novelty from different notation.

## Other prospective routes — no proofs accepted
Gao's2026 Conjecture2 extends F_q(s)=zeta(s,q)-psi(1-s) to allq>0 and claims convexity. Numerical q=4 midpoint gap at1/4,1/2,3/4 is0.006336654386601086>0 and F_4second(1/2)=-0.216124261301. This concerns the main convexity assertion; a mere constant-normalization failure is not creditable. For integerN, F_N=F_1-sum_{k=1}^{N-1} k^(-s). Each removed term contributes midpoint gap (k^(1/4)-1)^2/(2k^(3/4))>0. Coarse known zeta integral bounds would allow a rational proof atN256, but have not been formalized. Mathlib periodic UnitAddCircle Hurwitz zeta cannot silently represent q4. Eligibility may fail as an immediate standard-asymptotic consequence; assess before heavy work.

Schmidlin2601.21906 Conjecture37 Burnside refinement: set z=x+1,a=alpha-1/2. The log error is StirlingErrorGamma(z)+a-(z+a)log(1+a/z); RHS denominator12(z+a)-12(exp(1/48)-1). Entropy bound a^2/(2(z+a)) plus refined Stirling error is a possible route for1<=z<=2. No proof, numeric certificate or Lean here.
