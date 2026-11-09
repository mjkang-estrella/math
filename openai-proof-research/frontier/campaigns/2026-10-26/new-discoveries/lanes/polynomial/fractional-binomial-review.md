# Independent mathematical/source/novelty review — MathDB 352508

Date: 2026-10-26. Reviewer: polynomial lane. No candidate files, shared indexes, git state, or discovery tallies were changed. This is a mathematical and source review, **not a Lean audit**.

**Verdict: mathematical PASS; exact-source PASS; novelty HOLD with a substantial classical-consequence qualification.** The candidate proves the full printed Gerhold–Simon Conjecture 3.2, provided the standard trigamma integral representation used in its analytic proof is supplied or cited. No missing mathematical bridge was found. The exact sharp lower bound has not been located in the retrieved prior primary literature. However, the exact single-term function is already covered by Alzer's 2018 complete-monotonicity theorem, so neither that convexity fact nor the elementary finite-sum closure can be presented as new mathematics. The proposed contribution is the application of convexity to the two integer anchors, resolving the stated lower-bound conjecture. This review does not certify absolute novelty or authorize counting.

## Reviewed bytes

Candidate `lanes/matrix/fractional-binomial/PROOF-CANDIDATE.md` SHA256:

`b0d267d4c655654345dff391336b84da0545472835b407b0be09c3f5fada3e1e`.

The review concerns that full written proof, not a hypothetical future Lean theorem or later manuscript.

## Exact statement and normalization

Primary: Stefan Gerhold and Thomas Simon, *A converse to the neo-classical inequality with an application to the Mittag-Leffler function*, Monatshefte für Mathematik 200 (2023), 627–645, DOI [10.1007/s00605-022-01817-8](https://link.springer.com/article/10.1007/s00605-022-01817-8). The published Conjecture 3.2 is at printed p.634; the author's 26 November 2021 manuscript also labels it Conjecture 3.2, on manuscript p.8. Both ask, for positive integer k, real α>2, and x,y≥0,

    2^(α−1) Σ_{j=0}^k binom(αk,αj) x^(αj)y^(α(k−j)) ≥ (x+y)^(αk).

Here the binomial coefficient is the gamma quotient Γ(αk+1)/(Γ(αj+1)Γ(α(k−j)+1)). All gamma arguments in this sum are at least 1. There are no signs, negative gamma arguments, infinite series, or omitted tail terms in the conjectured finite sum.

For x+y>0, putting p=x/(x+y), q=y/(x+y) gives p+q=1 and extracts the same homogeneous factor (x+y)^(αk) from every summand. Thus the candidate's normalized F(α) is exactly the required sum divided by that factor. In Hino–Namba notation it is **Z_(α,p)^(k)/α**, not Z itself. The resulting new bound for their Z would be α·2^(1−α).

## Independent verification of the analytic argument

For j,l>0 and k=j+l, differentiate the logarithm of the gamma quotient twice with respect to a. The result is

    k² ψ₁(ak+1) − j² ψ₁(aj+1) − l² ψ₁(al+1).

The candidate's signs are correct: the numerator contributes positively and each denominator negatively. Define g(t)=tψ₁(t+1). The standard positive-argument trigamma integral gives

    ψ₁(t+1) = ∫₀∞ [u/(e^u−1)] e^(−tu) du,
    g(t) = ∫₀∞ e^(−v) [(v/t)/(e^(v/t)−1)] dv.

The substitution v=tu includes the correct Jacobian. Both integrals converge for every t>0. The function h(z)=z/(e^z−1) decreases on z>0: its derivative numerator is e^z(1−z)−1, which is negative because the derivative of e^z(1−z) is −ze^z<0 and its value at zero is 1. As t increases, v/t decreases, hence the second integrand increases pointwise. Therefore g increases.

The displayed second derivative equals

    [k g(ak) − j g(aj) − l g(al)]/a.

Since ak≥aj,al, its numerator is at least (k−j−l)g(ak)=0. This is the decisive curvature inequality; there is no reversal caused by rescaling a. For j=0 or l=0 the quotient is identically 1, so those terms need no limiting trigamma argument. The powers p^(aj)q^(al) contribute an affine logarithm. With p,q>0 each complete summand is positive and log-convex on a>0.

For 0<t<1, finite Hölder gives

    Σ f_j((1−t)a+tb)
      ≤ Σ f_j(a)^(1−t) f_j(b)^t
      ≤ (Σ f_j(a))^(1−t)(Σ f_j(b))^t.

The t=0,1 cases are equality. Consequently F is positive and log-convex. This step applies to the actual finite sum, with no infinite-sum interchange or convergence assumption.

The anchors are exact:

    F(1)=(p+q)^k=1,
    2F(2)=(p+q)^(2k)+(q−p)^(2k)=1+(q−p)^(2k)≥1.

The second equality is the ordinary even-index binomial filter; the exponent 2k is an even integer, so the last term is nonnegative even when q−p<0.

For a>2 set t=1/(a−1), so 0<t<1 and 2=(1−t)·1+t·a. Convexity gives

    log F(2) ≤ t log F(a),
    log F(a) ≥ (a−1)log F(2) ≥ (1−a)log 2.

Thus F(a)≥F(2)^(a−1)≥2^(1−a). This is convex **extrapolation**, and the lower-bound direction is correct even though log F(2) is nonpositive. The a=2 extension follows directly from the second anchor.

The sharpened bound using [1+(q−p)^(2k)]/2 follows by retaining F(2), so it is valid as part of the same result, not a separate discovery.

## Boundary cases and sharpness

For p=0 or q=0, exactly one endpoint summand is 1 and every other summand vanishes, under the ordinary 0^0=1 convention. Hence F(a)=1 and the required lower bound holds. If x+y=0, nonnegativity forces x=y=0; for k>0 each summand and the right-hand side is zero. No logarithm at zero is taken. If one extends the statement to k=0, its separate elementary inequality is also true, but the printed conjecture only requires positive k.

For k=1 and p=q=1/2, F(a)=2^(1−a), so the coefficient is sharp for every fixed a>2. This exact equality and the optimal coefficient were already anticipated in the original conjecture and must receive source credit.

## Prior-art assessment

The exact single-term function is **known**, not merely analogous to a known function. Horst Alzer, *Complete monotonicity of a function related to the binomial probability*, J. Math. Anal. Appl. 459(1) (2018), 10–15, DOI [10.1016/j.jmaa.2017.10.077](https://www.sciencedirect.com/science/article/pii/S0022247X17309903), proves complete monotonicity of the normalized gamma-binomial probability function. The accessible primary paper by Feng Qi and Bai-Ni Guo, *From inequalities involving exponential functions and sums to logarithmically complete monotonicity of ratios of gamma functions*, J. Math. Anal. Appl. 493(1), 124478 (published online 2020; issue 2021), explicitly records Alzer's theorem in §5.2, equation (5.1), for every p∈(0,1) and integers 0≤j≤k. It also identifies the stronger logarithmic complete monotonicity of this exact term. See [primary full text](https://pmc.ncbi.nlm.nih.gov/articles/PMC7416756/).

Finite sums of completely monotone positive functions remain completely monotone and are log-convex. Thus the candidate's needed sum log-convexity is already an elementary consequence of Alzer's published exact result. The candidate supplies a correct self-contained second-derivative proof of the weaker convexity fact, but rediscovering that fact itself earns no novelty credit.

I independently checked the newer Hino–Namba primary source. The latest arXiv version is **2408.12011v3, revised 25 February 2026**, beyond the v2 named in the assignment. Its Theorem 2.9 still states, for α≥2, only

    α^(1−α²) ≤ Z_(α,x)^(n) ≤ α.

The published article is Masanori Hino and Ryuya Namba, *Fractional binomial distributions induced by the generalized binomial theorem and their applications*, Math. Annalen 395, article 9 (2026), DOI [10.1007/s00208-026-03424-6](https://link.springer.com/article/10.1007/s00208-026-03424-6). The v3 theorem is available in the [primary arXiv text](https://arxiv.org/html/2408.12011v3). Its lower bound is strictly weaker than α·2^(1−α) for α≥2, including 1/8 versus 1 at α=2. It does not subsume this candidate's bound.

Gerhold's author-maintained addenda/corrigenda, dated 22 September 2025, mention Hino–Namba's application of inequality (1.7) but contain no resolution or correction of Conjecture 3.2. The current author publication list and searches for the exact conjecture, title, fractional-binomial convexity, complete monotonicity, and converse neo-classical inequalities revealed no primary publication already stating the sharp full lower bound. This is bounded negative evidence, not a proof of absence.

**Classification limit:** The exact endpoint appears to be a valid resolution of a genuinely printed open conjecture, rather than a typo or a formalization of the source's own theorem. Nevertheless, the proof after Alzer's theorem is short and uses only finite-sum closure, two elementary binomial anchors, and convex extrapolation. If the campaign's strict novelty policy excludes new connections that are immediate classical consequences, as applied to the Vandermonde candidate, that risk must also be considered here. The mathematics review alone cannot turn this distinction into a certified novelty verdict. Do not describe the gamma convexity or finite-sum log-convexity as new, do not count subsidiary corollaries separately, and do not infer novelty solely from the absence of search hits.

## Reproducibility and review limits

No Lean declaration was available in the reviewed packet, and no formal PASS is implied. A later audit must establish the gamma/trigamma bridge or another complete proof of actual summand log-convexity, finite-sum closure, both anchors, homogeneity for nonnegative real powers, and all zero cases. A theorem merely assuming F log-convexity would not finish the source result.

Source SHA256 inventory:

- Published Gerhold–Simon HTML `fc06057a1685d488c1e2e9669efadd0b077bbec43687d8f1fb2091e56ea87c21`.
- Author Gerhold–Simon PDF `5ec90f8bd4fbbb8799e7c034d332ee0ded765c6f8b9e374fdb381175ac2437e7`.
- Hino–Namba v2 HTML `60b39eafd0fd6873b84ccf9c7903cc1d95515dda503f5b994bcd9dc648b082ab`.
- Independently fetched Hino–Namba v3 HTML `6bdf4ee177447e71d1d34e394f44ccd3c4c018f0519b7a324ece894ff2302caa`.
- Qi–Guo primary full HTML `bc91c7f4d86860951a23602d1165246af052ebe327e1b872d151d7cf73b1b09c`.
- Independently fetched Gerhold addenda PDF `ae219b85a915b496874b45bed40c195ea20283f1b6a4e04e799eb89b3c4440ff`.

Independent fetches and text extractions are in `polynomial/review-fractional-binomial/sources/`. This review makes no external publication, priority claim, or tally change.
