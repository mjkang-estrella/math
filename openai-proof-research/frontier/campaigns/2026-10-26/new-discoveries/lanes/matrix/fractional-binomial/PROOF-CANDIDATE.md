# Full candidate proof of Gerhold–Simon Conjecture3.2 / MathDB352508

Status: complete mathematical proof and a frozen, warning-free Lean4.34.1 certificate of the full source inequality. Fresh all-declaration audit and independent final review are being run. No tally/novelty acceptance is asserted here. This addresses all real α>2, every positive integer k, and x,y≥0. The classical integer case is a tool, not counted separately.

Normalize x+y=1 and write p=x/(x+y),q=1−p. Cases x+y=0, p=0, or q=0 are immediate under the source's0^0=1 convention. Assume p,q>0. Set

    F(a)=Σ_{j=0}^k Γ(ak+1)/(Γ(aj+1)Γ(a(k−j)+1)) p^(aj)q^(a(k−j)),  a>0.

The key is that F is log-convex in a. Indeed, let ψ₁ denote trigamma and define

    g(t)=t ψ₁(t+1),  t>0.

Its standard integral representation and substitution v=tu give

    g(t)=∫₀∞ e^(−v) [(v/t)/(exp(v/t)−1)] dv.

The function z↦z/(e^z−1) is decreasing for z>0: its derivative has numerator e^z(1−z)−1<0, because e^z(1−z) starts at1 and has derivative −z e^z<0. Therefore g is increasing.

For j,l>0 and k=j+l,

    d²/da² log[Γ(ak+1)/(Γ(aj+1)Γ(al+1))]
      =k²ψ₁(ak+1)−j²ψ₁(aj+1)−l²ψ₁(al+1)
      =(1/a)[k g(ak)−j g(aj)−l g(al)] ≥0.

If j=0 or l=0, the gamma quotient is identically1, so its log is affine(constant). The remaining logarithmic term aj logp+al logq is affine. Thus each summand of F is positive and log-convex; Hölder's inequality makes their finite sum log-convex as well.

The exact anchors are

    F(1)=(p+q)^k=1,
    F(2)=((p+q)^(2k)+(q−p)^(2k))/2 ≥1/2.

For a≥2, the point2=(1−t)·1+t·a with t=1/(a−1)∈(0,1]. Log-convexity gives

    logF(2)≤(1−t)logF(1)+t logF(a)=t logF(a),

hence

    F(a) ≥ F(2)^(a−1) ≥ 2^(1−a).

Rescaling gives exactly

    2^(α−1) Σ binom(αk,αj)x^(αj)y^(α(k−j)) ≥(x+y)^(αk).

For k=1,x=y>0, equality holds, so the source coefficient is sharp. This equality is already identified by the source and carries no separate novelty claim.

The argument actually yields the stronger explicit bound

    F(a) ≥ [ (1+(q−p)^(2k))/2 ]^(a−1), a≥2.

Its role is a corollary of the same proof, not another discovery count. The source conjecture remains the single proposed outcome.

## Classical ingredients and proposed contribution

The scaled gamma-ratio convexity used above is classical. In particular, Qi–Guo, J.Math.Anal.Appl.493(1)(2021),124478, published online2020, §5.2, Eq.(5.1), records Alzer's2018 complete monotonicity theorem for the exact normalized single binomial summand. The2017 MathOverflow discussion280075 gives logarithmic convexity of the underlying binomial gamma quotient using Karp–Prilepkina's2015/2016 gamma-ratio criterion. These ingredients must receive prior credit. No claim is made that gamma-ratio log-convexity, log-convexity closure under finite sums, or the integer even-binomial filter is new.

The proposed resolution is their combination: log-convexity of the entire finite sum in the parameter, followed by extrapolation from its exact anchors1 and2, proves the unrestricted real-parameter conjecture. The full bound is not stated in the prior bodies inspected; independent novelty review is a separate gate.

## Kernel certificate without an unproved analytic ingredient

The formal proof does not assume Alzer's theorem or introduce a trigamma axiom. `GammaRatio.lean` constructs Euler approximants for logΓ(d·a+1), with cutoffNd and a finite sum of log(a+i+r/d). Existing Mathlib `Real.BohrMollerup.tendsto_log_gamma` gives the exact pointwise limit. The second derivative of the log-ratio approximant is a sum, overi, of

    Σ_{r=1}^{j+l}1/(a+i+r/(j+l))²
      −Σ_{r=1}^j1/(a+i+r/j)²−Σ_{r=1}^l1/(a+i+r/l)².

The copied, independently audited finite-grid theorem `GridMajorization.antitone_grid_sum` proves this nonnegative. Thus every approximant is convex, and the pointwise limit is convex. The zeroj/l cases are treated directly. `ConvexExtrapolation.lean` proves finite-sum logarithmic convexity by normalized convexity of the exponential and proves the one/two anchor extrapolation. `BinomialAnchors.lean` proves the classical even-filter identity. `BinomialConverse.lean` bridges the exact gamma coefficients, handles all indices, establishes both anchors, rescales positive inputs, and treats each zero input using a nonnegative endpoint summand.

The main declaration `FractionalBinomial.source_conjecture_352508` has no `GridMajorizes`, log-convexity, integrability, differentiability, or positivity-of-input assumption left. Its only mathematical hypotheses areα≥2,x≥0,y≥0, andk:ℕ. This includes every source instance (α>2,k≥1) and benign boundary extensions. The current six-module certificate does not expose the biased refinement or sharpness as separate endpoints; the parent is adding those in a seventh module for paper-scope alignment.
