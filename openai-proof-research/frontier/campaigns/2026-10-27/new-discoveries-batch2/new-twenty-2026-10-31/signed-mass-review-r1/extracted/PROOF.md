# MathDB 368007 — three nonzero signed masses have a local minimum

Candidate for independent fidelity, novelty and significance review; ZERO accepted credit.

The primary source is Alvis Zahl, arXiv:2504.09840v2, Section 10, equation (10.12), position variations (10.13), Conjecture 10.14 and the off-diagonal force sums (10.17). The versioned HTML is retained with a dated receipt. The versioned and unversioned HTML bytes agree. The primary toy statement allows points in R^n and d >= 2, normalizes the squared masses to 1, and considers variations x+tv with fixed masses. No n >= 2 restriction was found in the inspected introduction or toy section. This is a statement about the toy energy, not the fractional-Laplacian eigenvalue minimization problem.

Use n=1, s=1/2, d=3; let r=sqrt(129), masses (8/r,-1/r,8/r), and positions (-1,0,1). All masses are nonzero, the three positions are distinct, and the mass squares sum to (64+1+64)/129=1. This does not exploit a zero-mass particle or a collision.

On the OPEN chamber x0<x1<x2 put u=x1-x0>0 and v=x2-x1>0. The ordered-pair interaction energy, omitting self interaction, is exactly

E = (32/129)[1/u^2+1/v^2-8/(u+v)^2]
  = (32/129)(u-v)^2(u^2+4uv+v^2)/(u^2 v^2 (u+v)^2) >= 0.

The witness has u=v=1 and E=0. Thus it is a global minimum on that open chamber, and a local minimum in the entire Euclidean configuration space of three points in R^1. Both translation and dilation give flat directions; strict local minimality was not conjectured. This also explains the failed scaling shortcut: homogeneity forces zero energy at stationary configurations, but zero energy need not imply instability. The factorization gives a whole open-chamber proof, not a bounded directional Hessian diagnostic.

The source writes the double sum including i=j, which is undefined classically without a self-interaction convention. Equation (10.17) explicitly uses j != i. Our model uses the intended off-diagonal interaction throughout; the counterexample does not depend on the diagonal defect. If masses were permitted to vary too, our theorem would not establish a minimum in that larger space. Equation (10.13) varies only positions, and fixed masses are the interpretation submitted for review.

## Literal formal endpoint

`MathDB368007.energyN n d s m x` is the finite ordered off-diagonal sum of -2 m_i m_j / norm(x_i-x_j)^(n+2s), on actual `EuclideanSpace ℝ (Fin n)` positions. `NoLocalMinimumConjecture` quantifies over all positive dimensions, all d>=2, all s in (0,1), all normalized mass functions and injective configurations; `source_refutation` proves its negation. It is not a surrogate matrix, fixed-grid test or restricted variation predicate.

`normalized`, `mass_nonzero`, `witness_injective`, `energy_formula`, `gap_nonneg`, `local_minimum`, `norm_one`, `bridge`, and `euclidean_local_minimum` supply the semantic bridges. The scalar one-coordinate calculation is transferred by a continuous coordinate map to the actual Euclidean-space norm and full product topology. No derivative theorem is necessary to refute a no-local-minimum statement.

The fresh sanitized archive extraction rebuilds with Lean 4.34.1, -j1 and warningAsError. `leanchecker SignedMass` passes. All 45 module-local declarations, including generated proof and simp declarations, are enumerated and transitively audited using Lean.collectAxioms; only propext, Classical.choice and Quot.sound occur. Public endpoints also have literal #print axioms commands. Upstream cached oleans are trusted; no full upstream rebuild is claimed.

## Qualification risks requiring root review

1. This is genuinely one-dimensional. Transverse motion in higher dimensions invalidates this particular stability mechanism. An independently established n>=2 restriction anywhere in the governing source would invalidate the proposed source refutation. There is no claim of a higher-dimensional result.
2. The root must decide whether this is a substantive refutation of the exact universal toy conjecture or an excluded dimension/domain correction or routine convexity consequence. Simplicity alone is not novelty or significance evidence; no self-acceptance is made.
3. Bounded primary-source and registry searches found no inspected prior proof of this exact toy statement. They do not certify global novelty. No general Earnshaw/Riesz-equilibrium literature body was exhaustively read. Ordinary collinear equilibrium with three charges is familiar; our claim requires this specific reversed-sign interaction, normalization, exponent and local minimum in the full one-dimensional position space.
4. The formal theorem concerns the fixed-mass interpretation supported by (10.13), not jointly variable positions and masses. Independent fidelity adjudication is mandatory.
