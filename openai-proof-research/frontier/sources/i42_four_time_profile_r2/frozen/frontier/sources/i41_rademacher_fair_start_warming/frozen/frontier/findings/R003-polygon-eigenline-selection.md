# R003 — Polygonal Neumann eigenline selection

Status: project-level mathematical finding, checked by two independent agents and parent review. **Not a demonstrated literature-first result or a significant new MathDB advance.** The [novelty review](../reviews/hotspots-polygon-novelty-r3.md) identifies the classical smooth mechanism and assesses the remaining corner extension as modest. This record groups the corner lemma and its eigenline consequence as one finding.

## Exact statements

Let P be a bounded connected polygonal Lipschitz domain in the plane. Real eigenfunctions and weak Neumann boundary conditions are understood throughout. Slits, self-touching boundaries and zero-width necks are excluded; remove redundant straight-angle vertices.

1. If h and k are nonzero eigenfunctions at the same positive eigenvalue λ, they cannot satisfy hτ kτ = λhk on every open side of P. Holes and higher eigenvalues are allowed in this statement.
2. At a positive eigenvalue of multiplicity exactly two, smooth ambient deformations supported away from the vertices produce every traceless symmetric first-variation form on its eigenspace. Deformations may curve the sides.
3. If P is simply connected, every first-positive eigenfunction u is a local smooth limit of first-positive eigenfunctions on bounded smooth simply connected domains with simple first-positive eigenvalues. Each compact subset of P is eventually contained in those domains. They need not be nested or contained in P.

These three assertions do not use the OpenAI hot-spots theorem. Accepting **family 369, Theorem `thm:main`**, at pinned revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, they give the conditional consequence

\[
\min_{\partial P}u < u(x) < \max_{\partial P}u \qquad (x\in P)
\]

for every nonzero first-positive eigenfunction. This does not assert a nonvanishing gradient or resolve eigenline selection on all Lipschitz domains.

## Proof and source dependencies

The [complete derivation](../reviews/hotspots-multiplicity-r2.md), with the [independent analytic clarifications](../reviews/hotspots-polygon-proof-r3.md), is the proof record. Its main steps are:

- At a convex corner, the two tangential derivatives tend to zero, forcing hk = 0 at the vertex. At a reentrant corner put ν = π/β ∈ (1/2,1). The sector expansion on the two rays is h± = A ± arν + br²ν + O(r³ν + r²), and likewise for k. Finite-energy Bessel expansions give the corresponding differentiated remainder O(r³ν−1 + r). Boundedness of λhk first forces the leading derivative-product coefficient ac to vanish. Adding the two edge identities cancels odd angular parity. All remaining derivative products tend to zero because 4ν−2 > 0. Hence AB = 0. The proof review §3.1 supplies uniform infinite-tail estimates, not merely formal series manipulation.
- On each side the product hk has zero endpoints. A nonzero stationary value would give h′/h + k′/k = 0 and (h′/h)(k′/k) = λ > 0, an impossibility over the reals. Thus hk vanishes along the side. Analytic reflection and boundary Cauchy uniqueness contradict two nonzero eigenfunctions. This proves assertion 1.
- The shape form is the integral of V·n times (vτ zτ − λvz). No corner term occurs because V vanishes near the vertices. A nonzero annihilator of its traceless image diagonalizes to diag(ρ,−ρ). Polarizing with h = f+g and k = f−g contradicts assertion 1, proving assertion 2.
- The first-positive eigenspace of a simply connected polygon has dimension at most two (Judge–Mondal, Corollary 5.4; independently justified in the proof review §2). At multiplicity two choose a shape form with the desired line as its strictly lower eigenline. The variational expansion, including mean correction, gives a positive first-order spectral gap for t > 0 and convergence to that line. The simple-eigenvalue case needs no splitting. For each fixed perturbed domain, Ball–Zarnescu's topology-preserving smooth approximation has uniformly bi-Lipschitz maps that are identity off a shrinking boundary collar. Compactness and a diagonal choice prove assertion 3.
- Family 369 excludes strict local extrema of the limit. The classical Bérard–Helffer shifted-nodal-component lemma makes the complement of a global maximum set connected. Planar analyticity makes a nonisolated maximum component a proper embedded curve, which separates a simply connected domain. This contradiction gives the strict boundary inequalities.

The smooth cross-stress argument and polarization occur in Marrocos–Pereira, [Lemma 2 and Theorem 9, case ii](https://arxiv.org/pdf/1310.5178), with attribution there to Uhlenbeck. Traceless transversality and subsequent first-order branch selection are standard mechanisms. The potential additional content is the short polygon-corner extension; a bounded search did not establish priority.

## Validation and limits

The parent reproduced both [exact-check outputs](../experiments/hotspots_polygon_proof_r3/results.json): 144 original parity checks, 7,830 surviving derivative-product checks and 2,840 rectangle stress tests. All nine successful source downloads in the review manifest were hash-verified. Finite checks validate algebra only; the PDE, spectral and topological arguments are supplied in the proof review. This is agent review, not formal verification or external peer review.

The angle restriction is essential to the local corner lemma: on a slit of angle 2π, h = k = exp(√λ x) cos(√(2λ)y) satisfies the local equation and cross-stress identity on both slit faces while hk = 1 at the tip. This is not a counterexample to the stated polygon theorem.
