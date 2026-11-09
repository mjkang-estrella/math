# Sustained investigation of Q2; unresolved

Primary: https://arxiv.org/pdf/2609.39008v1, Aktaş–Baricz, submitted 2026-09-30, Q2 p28. Full definitions and Theorem3.2 proof pp8–11 were read, as was the neighboring J-order proof pp4–7. Fix phase α∈(0,π), order μ>0, and positive-zero index n≥1. Write Cμ(x)=cos(α)Jμ(x)−sin(α)Yμ(x), c=cμ,n, and a the unique minimum of Φ(x)=1−Cμ−1(x)Cμ+1(x)/Cμ(x)^2 on (cμ,n,cμ,n+1). Write b=Φ(a), y=xC′/C and σ=y(a). The source proves 0<σ<μ, b=1/(1+σ), a²=(1+σ)(μ²−σ²)/σ, and b′(μ)<0 when c>μ. Q2 asks whether order monotonicity persists when c<μ; the question also explicitly allows a negative answer for some phase. These are not arbitrary independently chosen solutions: α is fixed while differentiating order.

## Route 1: parameter variation and an exact missing inequality

Let D=μ²−σ²>0, A=Cμ(a)^2, B=Cμ′(c)^2 and

E=∫[c,a] t(Cμ′(t)−σ Cμ(t)/t)^2 dt > 0.

Differentiating the Bessel equation in μ and integrating its Wronskian from c gives A ∂μy(a)=cBc′+2μ I1, with I1=∫C²/t. Integration by parts and the Lommel identity give E=I2−D I1 and I2=a²bA/2−c²B/2. Consequently, with no inequality discarded,

σ∂μy(a)−μ = σ/(D A) [c B(Dc′−μc)−2μE].

The envelope identity is b′=2(σ∂μy(a)−μ)/a². Thus a precise sufficient-and-necessary missing lemma for strict monotonicity is

**For every fixed α∈(0,π), μ>0 and nodal index n with cμ,n<μ, c B(Dc′−μc)<2μE.**

This retains the energy discarded in the published c>μ proof. It is not proved here. A lower bound on E uniform in the singular phase/order corner, or a direct sign computation for this entire expression, would be decisive. Pointwise positive E alone gives no quantitative domination.

## Route 2: why the obvious classical extension fails

The source's Lemma3.1 uses the classical zero-motion integral c′/c=2∫₀∞K₀(2c sinh t)e^(−2μt)dt and bounds it by c′/c<1/μ when c>μ. Extending that bound to c<μ is false. Take μ=1/2 and α=π−e^(−20). The half-order formula makes C proportional to sin(x+α)/√x, so its first positive zero is exactly c=e^(−20).

Use K₀(z)=∫₀∞exp(−z cosh s)ds and restrict the positive double integral to 0<t<1, 0<s<20. There 2c sinh t cosh s<(1+e^(−40))sinh1<2. Hence

c′/c > 40 e^(−2)(1−e^(−1)) > 40/18 > 2 = 1/μ.

The elementary bounds 2<e<3 and (1+2^(−40))·3/2<2 justify both strict estimates. check_exact.py verifies these rational comparisons, including a factorial-series enclosure for e. This is an ordinary exact obstruction to the method; it neither computes b′ nor refutes Q2. The zero-motion integral is used with precisely the fixed-phase convention of the source. Its classical origin is expressly acknowledged, not credited as a new formula.

## Route 3: singular phase asymptotics

For fixed nonintegral μ>0 and ε=π−α→0+, the two Frobenius terms give C≈−aμ x^μ+ε dμ x^(−μ), aμ,dμ>0. Thus c^(2μ)≈ε dμ/aμ and ∂μ log c contains −log ε/(2μ²). The preceding exact obstruction confirms that the singular boundary motion cannot be bounded by 1/μ uniformly. At the minimum the regular x² correction competes with ε x^(−2μ), suggesting a of scale ε^(1/(2μ+2)) and b→1/(1+μ). These are only fixed-order asymptotic heuristics here, without differentiated uniform remainder. They cannot prove the global order sign or exchange ε→0 with μ differentiation. A uniform remainder bound in both parameters is missing. This route does not repair the energy estimate.

## Route 4: bounded numerical diagnostics

work.py diagnostic brackets candidate first two zeros on a fixed logarithmic/linear mesh, minimizes Φ between them, and takes central order differences at 40 (μ,α) pairs. μ∈{.1,.3,.5,1,2,5,10,20}; α/π∈{.84,.9,.99,.9999,.99999999}. It found no positive derivative; 34 reported first zeros were below μ. These are floating diagnostics, with neither certified root completeness nor interval errors. An overflow warning in the sign-product test is preserved in FAILURES.md. They certify no universal sign and no counterexample. No resource cap was approached or raised.

## Strongest classical-adaptation objection

The Wronskian/envelope/Lommel/completing-square chain above is already the source's Theorem3.2 mechanism. The displayed exact energy identity merely retains its discarded positive term and is not a substantive new result. If the missing lemma follows from a complete applicable classical Sturm comparison or zero-motion inequality, that entire bridge must be supplied and compared before claiming novelty. Conversely, the use of classical tools alone does not settle whether a future full resolution is routine. Presently there is no complete applicable bridge, no full proof/refutation, and no acceptance recommendation.
