# Ordinary counterexample; EXCLUDED ROUTINE, HOLD for review

Target: Pierre Bosch, *HCM Property and the Half-Cauchy Distribution*, arXiv:1402.1059v1, Remark 1(a), PDF p5. The conjecture asserts that for **every s,t>0**, the square root of the product of independent unit-scale Gamma(s) and Gamma(t) variables has a hyperbolically completely monotone (HCM) density. The displayed density on that page is 4 x^(s+t−1) K_(t−s)(2x)/(Γ(t)Γ(s)). Square-root placement in the extracted text is garbled; the density and surrounding unit-exponential example fix the meaning. This is not the separate conjecture about stable powers or GGC closure.

Take s=1/2,t=2. Its density is f(x)=(1+2x)e^(−2x), x>0. Here is an independent density derivation, including the classical bridge. If A~Gamma(2), B~Gamma(1/2) are independent and Z=√(AB), change variables in the joint density to obtain

    f_Z(z)=2/√π ∫_0^∞ x^(1/2) exp(−x−z²/x) dx.

For a,z>0 let J(a,z)=∫_0^∞ x^(−1/2)exp(−ax−z²/x) dx. Substitution x=z²/(a y) gives ∫x^(−3/2)exp(−ax−z²/x)dx=√a J(a,z)/z. Differentiation under the integral therefore gives ∂_z J=−2√a J. Dominated convergence at z↓0 and the Gaussian integral give J(a,0)=√π/√a. Hence J(a,z)=√π a^(−1/2)e^(−2z√a). Differentiating in a at a=1 yields ∫x^(1/2)exp(−x−z²/x)dx=√π(z+1/2)e^(−2z), proving the density formula. Every differentiation for positive a,z is justified by exponential decay at both endpoints, locally uniformly in these parameters.

By definition HCM requires, for each fixed u>0, that f(uv)f(u/v), expressed as a function of w=v+1/v>2, be completely monotone. In this case that function is

    G_u(w)=e^(−2uw)(1+4u²+2uw).
    G_u''(w)=4u²e^(−2uw)(4u²+2uw−1).

At u=1/10 and w=3 (realized by v=(3+√5)/2),

    G_(1/10)''(3)=−(9/625)e^(−3/5)<0.

This violates the necessary second-derivative condition for complete monotonicity at an interior point. Thus the universal Gamma-product HCM assertion is false. The witness satisfies every substantive s,t,independence,scale and positive-domain hypothesis. It does not refute GGC or infinite divisibility of this product, nor any stable-power question.

Strongest classical/substantive objection: the source already supplies the exact K-density; the classical half-integer K_(3/2) evaluation gives the same elementary density immediately. Differentiating its hyperbolic product twice exhausts the counterexample. The derivation above makes that full bridge explicit rather than merely calling it short. **No discovery credit requested.** No novelty or worldwide-priority claim; current HCM/Gamma citing coverage is incomplete. HOLD for source/math review if root wishes to use this as an exclusion record. No Lean/manuscript work authorized or performed.
