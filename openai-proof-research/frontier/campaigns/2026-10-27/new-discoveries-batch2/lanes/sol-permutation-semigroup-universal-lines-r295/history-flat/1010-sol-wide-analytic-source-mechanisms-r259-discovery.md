# Sustained full-scope work: planar Fourier-zero maximum

Target is exactly Open Problem1.6 of arXiv2609.10517v1, not the already refuted 2009 ball conjecture and not the already proved regular-polygon comparison. For every bounded convex centrally symmetric planar K of area π, prove κ(K)≤κ(P12), or exhibit one K violating it. No qualified survivor: the following are incomplete research mechanisms, with routine obstructions proved explicitly.

## Mechanism I: global anisotropy, exact failure of the obvious source transfer

The source proves unboundedness in dimensions d≥3 using Ω_{α,d}={|x|+α|y|<1}. Its proof needs positivity without zeros along the long axis. In d2 this is a diamond D_α, a linear image of the square. Write x=u(1/2,1/(2α))+v(1/2,−1/(2α)), |u|,|v|<1. Its Fourier transform is a positive constant times sinc(ξ·c1)sinc(ξ·c2). Its zero set is the union of lines ξ·c_j=kπ, k nonzero integer. Distance to their union is therefore π/max|c_j|=2π/√(1+α^−2). Since area(D_α)=2/α, the area-π rescaling has

    κ² = 8πα/(1+α²) ≤ 4π,

because (α−1)²≥0 for every α>0. This whole anisotropic family is bounded by the square, already strictly worse than P12 by source Thm1.5. This is an exact full-parameter obstruction, not a finite search. Higher-dimensional zero-free-axis reasoning cannot be transplanted to the plane: the triangular planar section profile has real Fourier zeros. No new ordinary source resolution or credit is inferred from this elementary identity.

## Mechanism II: local boundary variation, including an exact affine obstruction

First, any det1 affine path exp(tS), tr S=0, sends the zero set to exp(−tS^T) times the original zero set. If e_j are the twelve side-midpoint minimizing directions from source Thm1.7, the candidate zero κ exp(−tS^T)e_j has radial derivative −κ e_j^T S e_j. The symmetric part suffices, and Σ e_j e_j^T=6I. Thus the derivatives sum to zero and their minimum is ≤0. Since the true nearest zero is no farther than any such tracked zero, the upper right directional derivative of κ along this path is ≤0. **No positive first-order affine improvement is possible.** A pure rotation gives zero; second-order or nonaffine behavior is not settled by this argument.

For genuinely nonaffine changes use the apothem-one dodecagon: a=tan(π/12)=2−√3, A=12a, normals n_j=(cos θ_j,sin θ_j), θ_j=jπ/6. Side points are n_j+s τ_j, −a≤s≤a. Divergence gives the entire profile along e_0:

    F(r)=Σ_j 2a cosθ_j sin(r cosθ_j) sinc(ra sinθ_j)/r.

For an admissible smooth symmetric boundary perturbation with normal velocity v_j(s), the first variations are δA=Σ∫v_j(s)ds and δF=Σ∫v_j(s)cos(r(cosθ_j−s sinθ_j))ds. At a simple tracked root r the implicit-function derivative is −δF/F′(r). Restoring area A by homothety gives

    δr_normalized = −δF/F′(r) + r δA/(2A).

These identities follow by differentiating domain integrals and the scalar implicit equation; they require an actual convex family and a simple root, not arbitrary signed boundary velocities. The bounded calculations use v_j=a^{2k}−s^{2k}, k1..4, whose concavity on a side suggests outward bulges, but a full closed convex-family construction and angular minimum theorem for the perturbed domains were not supplied. They must not be silently assumed.

There is an exact consistency check independent of quadrature: because x·n=1 on every side, divergence of x exp(iξ·x) gives B(r)=2F(r)+rF′(r), where B is the unweighted boundary cosine integral. At a root B=rF′. Uniform side offsets have δA=24a=2A; hence their area-normalized derivative is exactly −r+r=0. This velocity is just polygonal homothety, so no improvement should appear.

boundedchecks.json reports 45-digit mpmath quadrature diagnostics only: tracked root r≈3.78748545616 at apothem1; parabolic-bulge normalized derivative ≈−4.12410835e−5, and the three higher-power bulges are also numerically negative. These are not interval-certified signs, and r is not the source's area-π normalized root. No numerical result establishes full-scope failure or local maximality. The analytic global anisotropy and affine obstructions above go beyond these bounded tests.

The next decisive calculation is a rigorous, convexity-compatible shape-cone sign certificate for the boundary kernel at the root, including control of the minimum over every Fourier direction. A positive tracked direction alone does not suffice. If all feasible first variations are nonpositive, one still needs second-order analysis or a separate global inequality. The source's regular-polygon theorem supplies neither missing bridge. No further solving is justified by merely repeating regular-polygon scans.

## Closest-body and chronology limits

Primary §2 anisotropic proof, §3.3 Jacobi–Anger proof and §4.4 comparison proof were read before the sustained calculations. Source v1 is 9September2026. All exact fetched latest-version histories are in chronology.json; the PDF identifies v1. Bounded current arXiv title/object searches did not provide a full resolution of Open1.6. This does not certify openness or priority. Original BLP2009 full body, a full citing-corpus audit, subscription databases and current public proof-registry heads remain unavailable/unread. No novelty PASS and no PROOF.md.
