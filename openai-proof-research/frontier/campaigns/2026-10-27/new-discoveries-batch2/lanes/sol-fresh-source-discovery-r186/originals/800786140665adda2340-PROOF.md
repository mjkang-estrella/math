# Ordinary analytic refutation of Frank ordinal attenuation

Status: complete ordinary argument offered for independent mathematical and substantive-eligibility review. No acceptance, Lean or manuscript clearance claimed. Finite diagnostics are not used in the argument.

## Literal source target

Barbiero, *The Frank copula as a latent model for ordinal variables: dependence structure, correlation attenuation, and statistical inference*, version of record 26 September 2026, DOI 10.1007/s11634-026-00709-1, Sections 2.1–2.2 (paragraph immediately before Theorem 2), and Section 3.3. The conjecture compares Pearson correlation of discretizations with Pearson correlation of the uniform latent variables (their Spearman correlation). Category scores are the consecutive integers, with arbitrary strictly increasing interior thresholds. This is not a statement about normal latent margins, equal-probability bins, or arbitrary scores.

We prove existence of a finite number m and strictly positive identical m-category margins for which the conjectured upper bound fails, already for theta=8. No claim of minimal m, optimal thresholds or exact maximal correlation is needed.

## Conditional mean is not affine

Put q=exp(-8), d=1-q. Let (U,V) have the source Frank copula C at theta=8. Its density is positive and smooth on the closed square, its margins are uniform, and it is exchangeable. Write m(u)=E[V|U=u], with the continuous version obtained from its density. The conditional distribution function is

    H_u(v)=a b/(d-b+a b),  a=exp(-8u), b=1-exp(-8v).

Consequently m(u)=integral_0^1 (1-H_u(v))dv. The denominator stays strictly positive on the compact square, so all differentiations below are justified by uniform boundedness of the differentiated integrands. Direct differentiation and integration give

    m(0)=1/8-q/d,
    m'(0)=8/d^2 integral_0^1 (1-exp(-8v))(exp(-8v)-q)dv
         =(1+q)/(2d)-8q/d^2.

Radial symmetry of C, or a direct change of variables in its density, gives m(1-u)=1-m(u). Thus m(1)-m(0)=3/4+2q/d>3/4. On the other hand q<1/1000: the Taylor lower sum sum_{j=0}^7 8^j/j! exceeds 1000. Therefore

    m'(0)<(1+q)/(2(1-q))<1001/1998<3/4.

An affine m would have derivative m(1)-m(0), contradicting these inequalities. Thus m is not affine.

## A strictly increasing perturbation raises correlation

Work in real L2[0,1] with Lebesgue measure. Put l(u)=u-1/2 and s=<l,l>=1/12. Let T be the conditional expectation operator (Tf)(u)=E[f(V)|U=u]. Exchangeability makes T self-adjoint. Uniform margins make it a contraction and preserve integrals. Put r=Corr(U,V)=<l,Tl>/s and

    h=Tl-r l=m-1/2-r l.

Then integral h=0, <h,l>=0 and h is a nonzero smooth real function, by non-affineness of m. For f_e=l+e h, its variance is s+e^2||h||^2 and its covariance across the copula is <f_e,Tf_e>. Define R(e)=Corr(f_e(U),f_e(V)). Differentiating the quotient at zero yields

    R'(0)=2<h,Tl>/s=2||h||^2/s>0.

Hence for every sufficiently small positive e, R(e)>r. Since h' is bounded on [0,1], choose such an e also satisfying e||h'||_infinity<1. Then F(u)=u+e h(u) has strictly positive derivative everywhere. The affine rescaling

    g(u)=(F(u)-F(0))/(F(1)-F(0))

is a continuous strictly increasing bijection of [0,1], with positive derivative, and Corr(g(U),g(V))=R(e)>r. The latent r is strictly positive by the source's positive-quadrant-dependence property (or Hoeffding's covariance integral), so this also violates an absolute-value upper bound.

## Consecutive-integer ordinal coding

For each integer n>=2 define X_n(u)=1+floor(n g(u)) for u<1, and set X_n(1)=n. It has exactly the source scores 1,...,n, with thresholds t_i=g^{-1}(i/n), 1<=i<n. Each bin has positive Lebesgue measure, so the margins are nondegenerate and every category has strictly positive probability. Both margins use the same thresholds.

For every u, |X_n(u)/n-g(u)|<=1/n. Uniform convergence implies convergence of all first and second moments and mixed moments under the copula. The limiting marginal variance is positive because g is strictly increasing. Therefore

    Corr(X_n(U),X_n(V)) -> Corr(g(U),g(V)) > r.

There exists a finite n for which the source upper bound fails. This closes the entire negation of the universal conjecture within its stated consecutive-score domain. It does not rely on any numerically selected parameter, finite census, rounding issue or modified score convention.

## Independent-review objections

The essential possible disqualifier is substantive novelty: this uses the classical Rayleigh-quotient/conditional-expectation perturbation and elementary monotone quantization. A general old theorem about monotone maximal correlation for smooth exchangeable laws may already subsume the construction, even if no one wrote this Frank counterexample. The source-specific non-affineness and positive equal-score finite-margin bridge are established above, but they do not themselves prove novelty. Root should independently adjudicate this before any formal or manuscript work. Also recheck the literal source comparison against uniform latent Pearson correlation; comparing instead with a transformed latent maximum would evade this refutation but is not the stated source conjecture.
