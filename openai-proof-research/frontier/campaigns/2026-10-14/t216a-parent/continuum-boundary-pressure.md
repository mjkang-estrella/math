# Continuum boundary-pressure comparison for the T216A author proof

Myeongjin Kang. No affiliation. Original exposition CC BY 4.0.

This is parent author research, not an independent review or a proof of the lattice amplitude theorem. The analytic agent proposed the harmonic small-ball/Hölder comparison and the lattice pressure sandwich. Parent and agent independently obtained the collar exponents; the parent supplies an explicit small-ball proof using Šidák's inequality and the assembly below. The whole-plane moment/tail asymptotic and sharp local chaos moments remain credited primary inputs.

## Statement and normalization

Let D=(-1,1)^2. Let Γ_D have zero Dirichlet boundary conditions and covariance with logarithmic singularity log(1/|x-y|). Fix β=1/2 and use the ultraviolet normalization

    μ_D = lim_(ε→0) ε^(-β²/2) exp(iβ Γ_(D,ε)).

This is not full-variance Wick ordering. Write μ_* for the correspondingly normalized whole-plane chaos with an independent uniform global phase. The whole-plane field itself is taken modulo constants. Set

    F_D,E(t)=log E exp(t Re μ_D(E)),
    F_*,E(t)=log E exp(t Re μ_*(E)),    p=16/15.

Assume the standard spatial Markov decomposition of the whole-plane field into an independent Dirichlet field and a harmonic field modulo constants. The primary whole-plane tail theorem implies that

    A=lim_(t→∞) F_*,D(t)/t^p

exists and lies in (0,∞). Then

    lim_(t→∞) F_D,D(t)/t^p = A.

Thus division by |D|=4 gives the same pressure coefficient for these two continuum ensembles. No lattice-limit interchange is included in this statement.

## Actual primary inputs

1. Aru–Baverez–Jego–Junnila, [arXiv:2401.14942](https://arxiv.org/abs/2401.14942), equations (1.1), (2.1)–(2.2), Lemma 2.5, and Theorem 1.6 with Appendix B. Lemma 2.5 gives sharp absolute moments on compactly contained rectangles in the ultraviolet normalization. Theorem 1.6 and Appendix B give the corrected whole-plane absolute-tail exponent 4/β², here 16. The exponent and lower-tail inference in the older appendix should not be substituted for this corrected result.
2. Junnila–Saksman–Webb, [arXiv:1806.02118](https://arxiv.org/abs/1806.02118), Theorem 1.3, supplies the underlying sharp moment growth. On a fixed reference square compactly inside a larger square it gives ||μ(f)||_q ≤ C ||f||_∞ q^(1/16), q≥2, after the bounded conversion between full-variance and ultraviolet normalization. Bounded measurable weights follow from the moment integral/dominated approximation, also recorded in ABJJ Lemma 2.1 and (2.7).
3. Šidák, [Rectangular Confidence Regions for the Means of Multivariate Normal Distributions](https://www.math.utoronto.ca/mccann/assignments/477/Sidak67.pdf), 1967, Theorem 1 and Corollary 1: the probability of simultaneous centered Gaussian interval events is at least the product of their marginal probabilities. Independence of the coordinates is unnecessary, and singular covariance matrices are allowed by approximation.

The first input's sharp absolute tail implies the stated A by the elementary Laplace principle. An independent uniform phase does not change the leading Laplace coefficient: its upper bound is exp(t|μ_*|); restricting the phase to a fixed interval where cos θ≥1−η gives a positive constant times exp((1−η)t|μ_*|). Let η decrease to zero after taking the large-t limit. Whole-plane scaling also gives

    A_(aD)=a² A,   0<a≤1,

because μ_*(aD) has absolute law a^(15/8)|μ_*(D)| and (15/8)p=2. This argument only needs the existence and positivity of A, not an explicit evaluation of it.

## 1. Conditional phase comparison and collar moments

For a fixed bounded weight f, a neutral even moment of μ_D(f) is an integral of a positive Gaussian charge kernel times ∏f(x_j)overline(f(y_j)). Consequently replacing f by |f| can only increase the absolute value of that integral. In particular, for deterministic phases ψ and nonnegative w,

    E|μ_D(w exp(iψ))|^(2N) ≤ E|μ_D(w)|^(2N).

The statement extends to an independent random harmonic phase by conditioning. This is a moment comparison, not stochastic domination.

Let B be a Whitney square of side s in D, and let its concentric enlargement Q have side comparable to s, remain in D, and contain B in a fixed compact interior proportion. Spatial Markov gives

    μ_D|B = exp(iβ h) μ_Q|B,

with h independent of Γ_Q. There is no extra diagonal-variance factor in this ultraviolet identity. Conditional phase comparison, exact dilation of the ultraviolet chaos and the primary sharp moment bound imply, uniformly over all such B,

    ||μ_D(B)||_q ≤ C q^(1/16) s^(15/8),    q≥2.                 (1)

For real q, interpolate between the next larger even moments. Write E_δ=(1−δ)D and C_δ=D\E_δ. A dyadic Whitney decomposition of the collar has O(1/s) squares at every scale s≤Cδ; squares intersecting the inner edge of the collar are handled by indicator weights in their enlarged parent squares, with the same O(1/s) count. Minkowski's inequality and (1) yield

    ||μ_D(C_δ)||_q ≤ C q^(1/16) δ^(7/8).                       (2)

The sum is geometric because 15/8−1=7/8>0. Infinite Whitney sums converge in L^q, so this also supplies the boundary-cutoff definition and approximation of the total integral. No independence among Whitney squares is used.

If a nonnegative random variable satisfies ||Y||_q≤K q^a for all q≥2 and 0<a<1, optimizing Markov's inequality gives a tail bounded by C exp(−c(u/K)^(1/a)). Integrating that bound against t exp(tu), or maximizing tu−c(u/K)^(1/a), gives

    log E exp(tY) ≤ C+C(tK)^(1/(1−a)).

Applying this with a=1/16 to (2) proves

    log E exp(t|μ_D(C_δ)|) ≤ C+C t^p δ^(14/15).                (3)

Here constants are independent of δ and t. The same argument for a fixed interior core and ||f||_∞≤ε gives log E exp(t|μ_D(f)|)≤C_E+C_E(tε)^p.

## 2. Explicit small-ball bound for the harmonic part

For a fixed compact E⊂D and a centered Gaussian harmonic function h on D, with covariance bounded on compact subsets, there is C_E such that

    P(sup_E |h|≤ε) ≥ exp(−C_E[log(e/ε)]²),    0<ε<ε_E.       (4)

To prove this, conformally map D to the unit disk. The image of E lies in {|z|≤ρ}, and choose ρ<ρ_1<1. The harmonic expansion is

    h(re^(iθ))=A_0+Σ_(k≥1)r^k(A_k cos(kθ)+B_k sin(kθ)).

All coefficients are jointly centered Gaussian. Their Fourier integral formulas on the circle of radius ρ_1 and the bounded second moment on that circle give standard deviations at most Cρ_1^(-k); the constant coefficient has bounded variance. Degenerate coefficients cause no difficulty.

Require |A_0|≤ε/4 and, for each k≥1, require

    ρ^k|A_k|, ρ^k|B_k| ≤ c ε/(k+1)²,

where c makes the sum at most ε. These events imply the required supremum bound. Put q=ρ/ρ_1<1. Each standardized threshold is at least c'ε q^(-k)/(k+1)². Choose K=C_0 log(e/ε) with a sufficiently large fixed C_0. For k≤K, the product of the marginal interval probabilities is at least exp(−C log²(e/ε)), using the lower bound c min(1,u) for a standard Gaussian interval of radius u. For k>K, the thresholds are at least a fixed exponential in k after increasing C_0 and decreasing ε_E. The Gaussian tail deficits are summable, and their product has a positive lower bound independent of ε. Apply Šidák to each finite prefix and pass to the decreasing intersection to obtain (4).

For a harmonic field modulo constants, choose its value at one interior point to be zero; the remaining harmonic field is centered Gaussian. The independent uniform global phase U supplies the omitted constant. The event that U is within ε/2 of zero and sup_E|βh|≤ε/2 has probability at least

    exp(−C_E[log(e/ε)]²).                                    (5)

The extra uniform-phase factor is proportional to ε and is absorbed in this bound. This does not require a small-ball estimate on the boundary of D.

## 3. Comparison on a fixed interior core

Couple μ_*|E=exp(i(U+βh))μ_D|E. Let Z_ψ(t)=E_D exp(t Re μ_D(1_E exp(iψ))) for a deterministic phase ψ on E. For 0<η<1, Hölder applied to

    (1−η)t Re μ_D(E)
      =(1−η)t Re μ_D(1_E exp(iψ))
        +(1−η)t Re μ_D(1_E(1−exp(iψ)))

gives

    F_D,E((1−η)t)
       ≤(1−η)log Z_ψ(t)
          +η log E_D exp(((1−η)t/η)Re μ_D(1_E(1−exp(iψ)))).

If sup_E|ψ|≤ε, the last term is at most C_Eη+C_Eη((1−η)tε/η)^p by the weighted moment bound. Set ε=t^(-2) and keep η fixed. Average Z_ψ over the event (5). Its probability has logarithmic cost O_E(log²t)=o(t^p), and the error term above is o(t^p). It follows that

    limsup_(s→∞) F_D,E(s)/s^p
       ≤(1−η)^(1−p) A_E.

For a square core E=aD, the known whole-plane coefficient is A_E=a²A. Taking η↓0 gives the upper bound A_E.

The reverse comparison is termwise in the exponential series. The uniform phase deletes every nonneutral charge term of the whole-plane series. For each remaining neutral term, averaging the independent harmonic field multiplies the Dirichlet Gaussian charge kernel by exp(−Var(βΣq_jh(x_j))/2)≤1. Every Dirichlet charge kernel, neutral or not, is nonnegative. Thus Z_*,E(t)≤Z_D,E(t) for t≥0. Absolute exponential integrability justifies the expansion. This proves

    lim_(t→∞) F_D,E(t)/t^p=a²A.                              (6)

## 4. Restore the boundary collar

Decompose μ_D(D)=μ_D(E_δ)+μ_D(C_δ). Hölder and (3), followed by (6), give

    limsup F_D,D(t)/t^p
       ≤(1−η)^(1−p)(1−δ)²A+Cη^(1−p)δ^(14/15).

First let δ↓0 with η fixed, then η↓0. The upper bound is A. The neutral-term comparison applies on D as well, by first using cutoffs and the collar integrability, and gives the lower bound A. This proves the stated continuum coefficient equality.

## Remaining boundaries of this work

This is a new author-side assembly of credited moment, Gaussian comparison and tail inputs. It supplies no independent contribution judgment. The full T216A proof still needs its lattice whole-plane spin-field limit, exact normalization, exponential-integrability passages, pressure sandwich, and conversion from pressure to magnetization. In particular ABJJ Lemma 2.8 alone would not prove the fixed-domain large-tilt comparison: its additive error at a fixed outer radius dominates sufficiently small tail probabilities. The argument above uses (5) instead.
