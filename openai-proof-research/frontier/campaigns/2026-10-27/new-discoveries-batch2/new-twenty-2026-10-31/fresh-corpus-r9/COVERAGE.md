# 329608: ordinary asymptotic proof for the literal approximation; scope HOLD

Source: Sadr–Adve arXiv1501.01668, actual Theorem4 proof Eq28–29 and Conjecture1, retained PDF/text and HTTP hashes. Corollary2's proof explicitly uses displacement much smaller than connection distance. The following analysis treats the resulting formula as a mathematical function at arbitrary displacement. It is not asserted to refute a physically restricted small-displacement model. No Lean endpoint, strict replay, novelty clearance or discovery credit is claimed.

Take two identical tiers, λ=1, β=1, α=4, and let A1=A, A2=1−A. The Eq28 integral for one tier, after t=πr², is

F(v,A,ρ) = (1/π) ∫_0^π ∫_0^∞ exp(−(1/A+ρ)t −v a(θ)√(t/π) −v²(π−θ)) dt dθ,
a(θ)=2cosθ(π−θ)+sinθ.

The full objective is F(v,A,ρ)+F(v,1−A,ρ). This uses the integral in the proof body and does not replace the Gaussian Q term by an unjustified approximation. At α=4 the source interference function is ρ(τ,4)=√τ arctan√τ. It is continuous, increasing from zero to infinity; hence ρ=1/v² can be realized by a positive threshold for each v>0.

## Asymptotic lemma and proof

For each fixed 0<A≤3/4, set ρ=1/v². Then

lim_(v→∞) v³ [F(v,A,1/v²)−A/(πv²)] = A^(3/2)/(2π).

Set s=v²(π−θ), t=Au, ε=s/v². Then

F = A/(πv²) ∫_(0≤s≤πv²) ∫_(u≥0) e^(−s−u) exp(w_v−Au/v²) du ds,
w_v=−v[sinε−2εcosε]√(Au/π).

For fixed s,u, sinε−2εcosε=−ε+O(ε³), so v w_v→s√(Au/π) and v Au/v²→0. To justify passage of the first-order limit through the integral, use |sinε−2εcosε|≤3ε on [0,π]. If w_v>0 then ε<π/2, since the bracket is nonnegative for ε≥π/2. Also the bracket is ≥−2ε; therefore

w_v ≤ 2(s/v)√(Au/π) ≤ √(2A s u) ≤ c(s+u), c=√(2A)/2<1.

The elementary bound |e^z−1|≤|z|e^(max(z,0)), with z=w_v−Au/v², gives for v≥1 an integrable dominating function

[3s√(Au/π)+Au] exp(−(1−c)(s+u)).

The missing s-tail of the subtracted constant contributes v e^(−πv²)→0. Dominated convergence thus gives

lim v³(F−A/(πv²))
= A/π ∫∫ e^(−s−u) s√(Au/π) du ds
= A^(3/2)/π^(3/2) · Γ(2)Γ(3/2)
= A^(3/2)/(2π).

Every integral in this argument is absolutely convergent, as follows from the same bound. No numerical quadrature is used in the proof.

## Consequence and scope limit

The linear A/(πv²) terms cancel in the midpoint comparison. Consequently

lim v³ [2F(v,1/2,1/v²)−F(v,1/4,1/v²)−F(v,3/4,1/v²)]
= [2(1/2)^(3/2)−(1/4)^(3/2)−(3/4)^(3/2)]/(2π)<0,

by strict convexity of x^(3/2). Thus the literal approximation is nonconcave for sufficiently large v at some positive thresholds. The numerical script independently probes this sign, but does not certify a witness.

The strongest objection is source scope: this mechanism operates at displacement large relative to mean connection distance, whereas the derivation expressly invokes a small-displacement approximation. It may therefore be only a model-domain correction, which the campaign excludes. The paper's unrestricted wording of Theorem4 does not by itself settle the intended eligibility. A second route toward a genuine proof within small displacement would seek a signed angular-integral bound for the A-second derivative; termwise concavity is unavailable because a(θ) becomes negative near θ=π. No such bound was proved. Do not invest in a large Lean development of the high-v route before resolving the domain and significance objection.
