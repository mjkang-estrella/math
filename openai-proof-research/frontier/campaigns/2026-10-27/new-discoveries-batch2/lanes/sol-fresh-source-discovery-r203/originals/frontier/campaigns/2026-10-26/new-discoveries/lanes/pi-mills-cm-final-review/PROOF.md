# A fortieth-derivative obstruction to the Mills-ratio conjecture

Status: **prospective counterexample; credit 0**. Two independent computations agree and an exact rational Bernstein certificate has been generated. Literal Gaussian-tail Lean bridge implemented; full derivative/sign/positive-input endpoint and independent review remain pending. No novelty or acceptance claim yet.

## Exact source

R. A. C. Ferreira and T. Simon, *Convolution of beta prime distribution*, arXiv:2108.09244v2 (19 May 2022), Conjecture 3, p.31; published Trans. Amer. Math. Soc. 376 (2023), 855–890, DOI10.1090/tran/8748. MathDB351688 is open, all solution/progress/attempt/comment fields empty in the full live record. The published PDF/DOI endpoint was inaccessible (403/tool fetch failure); this source-version comparison remains a limit. The latest arXiv is v2. The conjecture includes n=0: Proposition10 explicitly singles out n=0,1 for its stronger known square-root-input statement.

Let

`r(x)=exp(x^2/2) * integral_{x}^{infinity} exp(-t^2/2) dt`.

Conjecture3 asserts that `-r^(n)(x)^2/r^(2n+1)(x)` is completely monotone on `(0,infinity)` for every integer n. We examine the actual n=0 function

`F(x)=-r(x)^2/r'(x)=r(x)^2/(1-x*r(x))`.

This does **not** contradict the paper's Proposition10, whose input is `sqrt(x)`. No separate outcome is sought for higher n or Taylor helpers.

## Derivative computation

The literal Gaussian tail gives `r'(x)=x*r(x)-1` and `r(0)^2=pi/2`. It is smooth on the whole real line. The denominator of F is 1 at zero, so F and every derivative are continuous on an open neighborhood of zero.

Write `c=r(0)`, `R_k=r^(k)(0)`, `D_k=F^(k)(0)`. Differentiating the ODE and the identity `F-x*r*F=r^2` gives the finite, exact recurrences

* `R_0=c`, `R_1=-1`, `R_(k+2)=(k+1)*R_k`;
* `D_0=c^2`;
* `D_(n+1)=sum_(k=0)^(n+1) binomial(n+1,k) R_k R_(n+1-k) + (n+1)*sum_(k=0)^n binomial(n,k) R_k D_(n-k)`.

Thus D40 is an even integer polynomial in c, hence an integer polynomial `P(c^2)` of degree21. Its complete ascending coefficient list is retained in `derivative40-polynomial.json`. At `c^2=pi/2` it has approximate value

`F^(40)(0) = -24628065653022778370272.2022227366... < 0`.

The decimal is not the sign proof. For an independent computational cross-check, direct 200-digit power-series division of r^2 by 1-x*r, performed before deriving this integer recurrence, gives the same value after multiplication by40!. Its coefficient40 is approximately `-3.0184586756343535e-26`.

## Exact rational sign certificate

Set `a=392699/250000=1.570796` and `b=3141593/2000000=1.5707965`. Standard proved six-decimal bounds on pi give `a<pi/2<b`.

The exact rational certificate in `bernstein-certificate.json` lists22 numbers `B_k`, each strictly negative, such that the polynomial identity

`P(a+(b-a)u) = sum_(k=0)^21 B_k * binomial(21,k) * u^k * (1-u)^(21-k)`

holds identically. The file also gives the already binomial-scaled coefficients, so there is no normalization ambiguity. Every term is strictly negative for `0<u<1`. Taking `u=(pi/2-a)/(b-a)` proves `P(pi/2)<0` by exact arithmetic.

The coarser four-decimal interval did not have all-negative Bernstein coefficients; it was rejected, not used. The retained six-decimal certificate has every coefficient negative. No high-precision pi assumption is needed for the proposed Lean sign proof.

## A violation on positive inputs

Continuity of `F^(40)` at zero and its strictly negative value imply that some `delta>0` satisfies `F^(40)(x)<0` for every `0<x<delta`. Since40 is even, this violates the defining inequality `(-1)^40 F^(40)(x)>=0` at genuinely positive inputs. This is not a boundary-only objection.

## Current formal scope

`formal/Mills.lean` defines the literal Gaussian tail, proves its finite-integral identity, its initial value/square, the ODE and all finite smoothness orders. It defines the actual source quotient through the genuine derivative. `DerivativeRecurrence.lean` is under development for the finite Leibniz recurrences. No completed source refutation endpoint is claimed until the finite polynomial identity, sign certificate, derivative continuity, and positive-input contradiction are all proved in Lean.

## Bounded novelty screen so far

Full live MathDB351688 was read: all posting/attempt/progress fields empty. The latest arXiv v2 retains Conjecture3, but an empty record is not novelty evidence by itself. OpenAlex identifies three citing papers; copies are retained in `sources/`: the 2026 modified-Bessel-distributions paper, the 2025 unimodality-preservation paper, and the 2026 positive-Fox-H-functions paper. Their citation contexts and relevant sections do not supply this refutation; their full bodies still require systematic comparison. S2 returned429, recorded without repeated polling. Yang2507.10954's Mills-ratio section concerns a different square-root/weighted ratio comparison; the 2026 Xu–Yang higher-order-monotonicity paper concerns a different polynomial expression `Y_(a,a-2)`, and does not cite Ferreira–Simon in its searchable body. Targeted searches did not locate a fortieth-derivative obstruction. Author follow-ups, full published source and serious independent prior-art review remain to be completed. No MathSciNet/zbMATH or absolute-priority claim.
