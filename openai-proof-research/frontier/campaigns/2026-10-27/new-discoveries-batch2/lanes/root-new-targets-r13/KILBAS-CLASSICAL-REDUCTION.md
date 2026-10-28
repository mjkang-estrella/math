# Full sandwich via a classical exponential-functional factorization

28 October 2026. Ordinary argument only; no Lean endpoint and no discovery
credit. This is an explicit candidate **routine-corollary exclusion**, not an
acceptance or a worldwide novelty assertion.

The target is Boudabsa–Simon, arXiv:2012.05666v1, Conjecture 4.5, and the
published *Mathematics* 9 (2021), 217, Conjecture 4 (MathDB 348998).
Assume 0<alpha<=1, m>0, l>m-1/alpha. Put

    a = 1+alpha(l-m)>0, b=alpha m>0,
    phi(s) = Gamma(a+bs+alpha)/Gamma(a+bs), s>=0.

## 1. Explicit killed-subordinator exponent

For 0<alpha<1 the difference of the beta-integral representations gives

    phi(s) = phi(0) + alpha/Gamma(1-alpha)
      * integral_0^infinity
          exp(-(a+alpha)t) (1-exp(-bs t))
          / (1-exp(-t))^(1+alpha) dt.

For a direct proof without subtracting divergent integrals, set h=bs and
u=exp(-t). Integrate the convergent integral
(u^a-u^(a+h)) u^(alpha-1)/(1-u)^(1+alpha) by parts using
d[(u/(1-u))^alpha]/du=alpha*u^(alpha-1)/(1-u)^(1+alpha).
Both boundary terms vanish. The remaining two convergent beta integrals give
Gamma(1-alpha)/alpha times the claimed Gamma-ratio difference.
The displayed positive Levy density behaves like
t^(-1-alpha) near zero and decays exponentially at infinity; hence its
integral against min(1,t) is finite. After the change of variable t -> t/b
this is exactly a Bernstein/Laplace exponent, with killing rate
kappa=phi(0)>0. At alpha=1, phi(s)=a+bs, a killed deterministic drift.

Let xi^0 be the corresponding unkilled subordinator, zeta an independent
exponential time of rate kappa, and

    I = integral_0^zeta exp(-xi^0_t) dt.

The classical exponential-functional moment formula gives

    E[I^n] = n! / product_(k=1)^n phi(k).

Since a+bk=1+alpha((k-1)m+l), its reciprocal product is **exactly** the
coefficient c_n of z^n in the literal Kilbas–Saigo series. Thus

    E[exp(-x I)] = E_(alpha,m,l)(-x), x>=0.

Identification is justified by positive-series monotone convergence for
E[exp(rI)], r>=0: the resulting sum is the entire source series. The
negative-argument exponential series is then dominated by exp(xI).

## 2. Lower bound: killing-time domination

Since xi^0_t>=0, I<=zeta pathwise. Consequently

    E[exp(-xI)] >= E[exp(-x zeta)] = 1/(1+x/phi(0)).

Here

    1/phi(0)=Gamma(1+alpha(l-m))/Gamma(1+alpha(l-m+1)),

exactly the conjectured lower constant.

## 3. Upper bound: classical independent remainder

Bertoin–Yor's exponential-factorization theorem, including killing, supplies
an independent positive R with

    I R =_d Exp(1), E R=phi(1).

See Patie, *A refined factorization of the exponential law*, introduction
equations (1.2)–(1.3), which states both the moment formula and the
factorization for possibly killed subordinators; it points to Bertoin–Yor's
2005 survey Theorem 2 for the killed case. Applying conditional Jensen to
the convex function r -> exp(-x I r/phi(1)) gives

    E[exp(-x I)]
      <= E[exp(-x I R/phi(1))]
       = 1/(1+x/phi(1)).

Finally

    1/phi(1)=Gamma(1+alpha l)/Gamma(1+alpha(l+1)),

the exact upper constant. At x=0 both equalities hold. This proves the full
stated ordinary sandwich if the quoted classical dependencies are used.

## Status and strongest objection

The new-to-this-lane work is the explicit phi substitution and identification
of the source coefficient product. The remaining steps are the published
general moment/factorization theorem, a pathwise integral bound, and
conditional Jensen. Under this campaign's exclusion of routine classical
corollaries, this is **not nominated for discovery credit**. No assertion
that nobody has made the same observation is needed for that disposition.
The primary MDPI search-rendered HTML displays the published Conjecture 4
in full, and that display was read; a direct full-page open returned 429,
the direct MDPI PDF returned 403, and the EPFL deposit returned 429.
No actual published PDF or complete HTML-body read is claimed.
The actual downloaded Patie body (equations 1.2–1.3) and Bertoin–Yor
survey Theorem 2, including the independent exponential time and its proof,
were read. Numerical checks alone cannot establish any of these statements.
No formal, manuscript, independent
review or acceptance gate is claimed.

Sources:
- https://doi.org/10.3390/math9030217
- https://people.orie.cornell.edu/pp396/patie_aff.pdf
- https://arxiv.org/abs/math/0511265
- https://doi.org/10.1214/ECP.v6-1039
