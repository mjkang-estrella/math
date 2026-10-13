# I298 — independent contribution review of S295

2026-10-13. **TECHNICAL under the existing substantial-finding standard, for the complete S295 package including the required unaccepted I128/I131/I290 ingredients.** Full all-rectangle S128 remains **UNRESOLVED**. This review changes no count or acceptance. An independent full-proof gate remains separate.

The [detailed reduction](../experiments/i298_gaussian_stability_contribution/analysis.md) evaluates the internal ingredients rather than assuming that they are upstream theorems or already accepted substantial findings. [Reading/failure records](../experiments/i298_gaussian_stability_contribution/reading-and-failures.md), [input authentication](../experiments/i298_gaussian_stability_contribution/input-authentication.json), and [primary-source comparison](../sources/i298_gaussian_stability_contribution/literature.md) bind the evidence. The frozen target/report/I290 hashes match the brief.

## Exact scope

For X uniform on {-1,1}^n, arbitrary u:X→[-1,1], and

    ψ(t)=((1+t)log(1+t)+(1−t)log(1−t))/2,
    I(u)=Eψ(u)−ψ(Eu), I(u)=ψ(a),

fix 0<a₀≤a₁<1, 0<ρ₀≤ρ₁<1, with **ρ₁a₁<1/√2**. The classified result is

    min_(i,ε=±1) E|u−εaX_i|²
        ≤C[ψ(ρa)−I(T_ρu)]

for every n≥1, a∈[a₀,a₁], ρ∈[ρ₀,ρ₁], with C depending only on the four endpoints. Bias, spikes, endpoint values, and unlimited complexity are included. No monotonicity, balance, initial proximity, or singleton premise is added. No effective C or optimal parameter threshold is claimed.

## Constructive reason for the technical verdict

The theorem is not obtained directly from the published Boolean stability theorem. Its Boolean endpoint entropy and distance identities fail for arbitrary soft kernels. The concrete reduction instead retains the stronger operations of the stipulated family119 proof and the actual soft adaptations:

1. **Q131b:** use the existing sorting/convexity/spectral-gap calculation with Ed²≤Eu² in place of the Boolean derivative identity. It preserves the full input law and yields d_a(u)≤C_comp[d_a(g)+L_gain], with Δ(u)=Δ(g)+L_gain.
2. **L131:** the constrained entropy Hessian is uniformly coercive on the compact parameter rectangle. Split an L2 perturbation into a small-amplitude part and a small-support tail. Real-function hypercontractivity makes the noisy tail and output remainder negligible relative to the input quadratic energy. This pays spikes and endpoint values and supplies a uniform local linear bound.
3. **J290/M290/P290:** retain the strictly positive derivative margins already displayed in the pinned reserve/thinning proof. Common-corner mass loses strictly; a deterministic biased core loses strictly; optimizer uniqueness makes equality the actual reflected pair law. Compactness of laws on a fixed square gives a uniform modulus at a specified nonzero singleton, with arbitrary remaining face dimension.
4. **B290:** integrate production surplus on a middle noise-time interval, retain the marked singleton, and use that modulus to enter a smoothed coordinate neighborhood. Original-budget strong convexity pays the backward step. L131 then gives the linear bound at the original kernel; d_a≤4 handles larger deficits.
5. **Diffuse sector:** Borell and layer cake give law-preserving scalar Gaussian rearrangement. Ordinary scalar EPI applied to each biased posterior, followed by Jensen, gives the classical bottleneck curve. The elementary curvature/chord estimate gives a uniform gap below the cube curve when the Gaussian amplitude is below 1/√2. A fixed unequal split ρ₁<λ<min(1,1/(√2a₁)), standard fixed-degree invariance, clipping, and entropy/mean continuity exclude a diffuse near-extremizing sequence. Combining the two sectors and Q131b gives the exact displayed linear theorem.

The analysis writes out the formulas and constants needed by every step. In particular, it does not discard B290/L131/Q131b as earlier work or label their conclusions standard without giving the reduction. The marked bridge is useful, but its structural optimizer and strict margins are already supplied by the stipulated proof; the modulus and entrance are standard compactness and perturbative operations. Borell/EPI/invariance provide the remaining restricted sector. Under the project's requirement of an additional substantive mechanism beyond source operations and standard transfers, the whole package is technical.

## Comparison and limits

The actual current Ky–Tran stability/companion, Chen v2, and Yu v5 operative passages were inspected and version drift checked. Their scopes do not warrant an exact-duplicate claim for S295. The pinned Hellinger companion is Boolean and has a different profile. The verdict concerns reducibility under the stipulated source operations; it does not establish worldwide priority or rule out publication value. The Gaussian route and conservative curvature lead were parent-supplied, which also limits attribution to I295 alone.

Scalar monotone Gaussian compactness is a technical optimizer reduction. It does not prove pointwise strictness below the cube curve at all amplitudes. Strict EPI cannot pay that extension wherever its curve exceeds the cube curve. Ordinary LSI strictness leaves the nonlinear reserve unpaid. Guo–Wu–Shamai–Verdú Proposition 8 requires complex nonvanishing/tail-ratio conditions not verified for these posteriors. Full S128 is therefore unresolved in this package.

No blocking internal gap was found in the operative deductions needed for the contribution reduction. This statement is not a separate full-proof certification. Thirteen accepted findings toward twenty remain user-supplied metadata; no count, target, shared index, staging, commit, or publication was changed. Detached hashes of the five authored outputs are returned outside the artifacts.
