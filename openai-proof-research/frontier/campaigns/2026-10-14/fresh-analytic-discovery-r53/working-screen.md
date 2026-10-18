# Nonsymmetric polar-product embedding screen

Author: Myeongjin Kang; no affiliation. Original prose CC BY 4.0.
Status: pre-freeze feasibility screen, no theorem nomination. The tentative question is whether every n-dimensional convex body K with 0 in its interior has c_G(int K × int K°) ≥ 2+2/n. This is not a frozen campaign target: no credible full construction has yet been obtained. No symmetry, centering beyond 0∈int K, smoothness, or dimensional restriction is inserted to rescue the question.

## Actual comparisons and chronology

I70's source-W contract and polar-product screen concern symmetric width4 and packing up to volume, with the selected unresolved target being relative ball packing. They do not prove or select the present nonsymmetric embedding problem. The whole I70 read attempt was output-truncated; relevant source contract and polar screen were intact. I74 and the wider Mahler algebra/stability chains are developed and are not reopened here. Search silence is not freshness proof.

ABKS, arXiv1401.0442, actual Section4/Theorem4.1 proves the sharp bound 2+2/n for ξ_(K°)(K), the shortest asymmetric Minkowski billiard length. Their introduction identifies this with Hofer–Zehnder capacity. Since c_G≤c_HZ, that lower bound does not give a ball embedding. Their proof reduces a non-coverable polygon to a simplex, with length 1/M for M=∑_(i<j)m_i m_j≤n/[2(n+1)]. It is a finite trajectory argument, not a symplectic realization. We do not transfer sharpness automatically to c_G.

Vicente2505.07572v2, Theorems1.3,1.5 and actual Section2 constructions, use coordinatewise area-preserving maps and a separable sum of Young functions. Absolute values in the defining Luxemburg norm impose unconditional symmetry. This does not supply nonsymmetric bodies or arbitrary facet systems. The relation between functional dual and polar dual costs a factor2 through Young's inequality; it is not an arbitrary-body embedding theorem.

The pinned width source's full realization.tex has the exact unpaid step: h_K(±b_j)≤1 converts its signed J_k coefficients into h_K(p)≤C_K+(πk/4)τ+o(k). Its planar map has imaginary range (−1,1) and common zero0. The general Mahler companion's introduction describes a cone/Gaussian-projection entropy proof, not a ball realization. The symmetric companion's introduction expressly retains symmetry and identifies its analytic construction with this same lens. No volume-to-width inference is valid.

## Why the immediate modifications do not close the question

1. Keeping the source lens and replacing a one-sided polytope K={b_j·x≤1} by the same strip conditions produces K∩(−K), not K. Also K°=conv{b_j} need not contain −b_j. These are separate position and momentum losses.

2. Arbitrary facet weights in τ do not preserve the compact-sublevel hypothesis. Suppose Ω has a boundary point z* at which |g_j(ℓ_j(z*))|=1 for exactly one index j, all other moduli<1, and z* is approachable from Ω. If 0<a_j<1, then for fixed positive weights a_i and sufficiently large k,

  lim_(z→z*) τ_k(z)=a_j+∑_(i≠j)a_i|g_i(ℓ_i(z*))|^(2k)<1,
  τ_k=∑a_i|g_i(ℓ_i)|^(2k).

Choose s strictly between that limit and1. A sequence approaching z* belongs eventually to {τ_k≤s}; that set is not compact in Ω. Thus normalizing facet weights to sum1 cannot simply reduce a sum of one-sided primitive costs while retaining the source ball theorem. This is a route-specific lemma; it does not prohibit different exhaustions or a different ball theorem.

3. A momentum translation p↦p+∇S(q) is symplectic, so one may shift each J_j(v,t) by a function C_j(t): take S(q)=∑∫_0^(b_j·q)C_j(r)dr. This correctly allows one-sided primitives. But each shift introduces a full slice integral, not a term bounded by |g_j(ℓ_j)|^(2k). The source budget is τ<1, a sum of local powers. No uniform support-function estimate for the aggregate offset has been proved. Balancing normals with weighted coefficients does not remove the compactness issue in item2.

4. A soft maximum or other nonlinear aggregation can preserve plurisubharmonicity and compact sublevels, but it generally destroys the source's fiberwise phase-space realization with q=x. The source form is a sum of rank-one terms d(b_j·u)∧d(b_j·x), so every fiber x=constant is Lagrangian. For a general aggregate φ(u,x), dd^cφ can have nonzero du_i∧du_j terms. Any map (u,x)↦(x,p(u,x)) pulls back ∑dq_i∧dp_i to a form vanishing on each x-fiber. Thus a new fiberwise Lagrangian foliation or a different realization is required; positivity of dd^cφ alone does not suffice.

The remaining obligation is an actual one-sided holomorphic exhaustion plus a symplectic realization with the sharp polar support budget, or a different full-body ball construction. No such construction is currently proved. None of these failures refutes the tentative width bound.

## Explicit tests of the two analytic interfaces

For item2, no asymptotic example is necessary. Use the source lens D, Ω=D^n, ℓ_j(z)=z_j, and τ=∑a_j|g(z_j)|^(2k), with any a_1<1. Along z=(F(r),0,…,0), r↑1, τ=a_1 r^(2k)→a_1. For s∈(a_1,1), this sequence lies in {τ≤s} but exits every compact subset of Ω. This holds for every k. It does not contradict the source theorem, whose compactness hypothesis is absent here.

For item4, take n=2 and the standard smooth maximum

  φ(z)=log(exp(|z_1|²)+exp(|z_2|²)), z_j=u_j+i x_j.

It is smooth and plurisubharmonic. At u=(1,0), x=(0,1), the coefficient of du_1∧du_2 in dd^cφ is 1/4 under the source convention d^c=−(1/4)d∘i. Indeed, for h_j=|z_j|², Γ_12=−1/4 at h_1=h_2=1; dh_1=2du_1 and d^ch_2=−du_2/2. The remaining terms contribute no du_1∧du_2 there. Adding |z|² does not change that coefficient. Therefore this positive Kähler form cannot be realized by any map with q=x. A different map or foliation is not excluded.

An asymmetric-width proof could conceivably replace both interfaces at once, but no source theorem presently supplies such a replacement. A smaller embedding constant, a symmetric subclass, or a conditional comparison would not answer the tentative full question and is not proposed as a nominee.
