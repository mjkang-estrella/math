# I214 analytic attempts and failure checks

## Status

PROVED NOMINATION written to `../../iterations/i214-neumann-eigenmap-discovery.md`. Conditional on family 369 at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. This file records the development and checks, not a second nomination. Both parent acceptance gates remain open. No numerical experiments, research programs, tests, or scans were performed.

An early partial version of this file was written before completing source reading. At that checkpoint the origin argument and boundary finite-order issue were explicitly unresolved. They are resolved in the proofs below and the nomination.

## Route A: nodal foliation to global univalence

1. Every evaluation w→∇w(x) on the two-dimensional V is injective, hence invertible. det DF never vanishes.
2. The zero set of any nonzero first mode is a regular closed one-manifold. A circle component forces an interior extremum. A line component is properly embedded, since components of this locally connected closed level set are closed in Ω. A proper line separates the topological plane Ω. The two connected sign sets must occupy its opposite sides. A second zero component would place both signs on one side. Thus exactly one line remains.
3. For w=a·F and z=b·F with independent a,b, orient the zero line by T=J₀∇w/|∇w|. The derivative dz(T)=det(∇w,∇z)/|∇w| has constant nonzero sign. This makes z strictly monotone on the entire line. Two equal F-values therefore coincide.
4. Consequently U∩L is an interval for every line through 0. If 0 is missing, radial projection of U is a connected open arc without antipodal pairs. Its length is at most π. The midpoint direction has positive scalar product with every F(x), contradicting mean zero. This proves 0∈U and star-shapedness.

### Incorrect shortcuts rejected

- A local inverse does not prove a global inverse. The nodal-line monotonicity supplies global injectivity.
- “Zero is in the convex hull” alone does not put zero in an arbitrary open image. The radial interval property and connected angular projection supply the missing separation proof.
- Connected positive and negative sets do not by themselves furnish finite boundary nodal endpoints. Initially the proof uses proper lines in the open topological plane and allows boundary accumulation.
- Ordinary ordered-index Courant reasoning can be confusing in a multiple eigenspace. The direct Rayleigh restriction argument applies to every first-positive eigenfunction.

## Route B: boundary nodal topology and degree

1. A conformal half-disk chart produces ΔW+qW=0, W_y=0 on its real diameter, with q smooth on the half-disk. Even reflection yields a C² solution with bounded reflected potential.
2. The Fourier Carleman inequality in the nomination proves finite boundary vanishing order without assuming an analytic boundary. The bound follows from the explicit multiplier (τ+iξ)²−n² at half-integer τ, whose modulus is at least τ/2.
3. The first nonzero Taylor term is A Re(z^k), and there are exactly k nodal branches at the boundary zero. Their angular roots are simple, so a C¹ angular expansion excludes hidden branches. The trace zero is isolated. Compactness gives finitely many such zeros.
4. The single interior zero line has two ends. Thus k≤2. If k=2, both ends terminate at one point, yielding a Jordan loop based at that boundary point and an interior extremum. Thus k=1 and there are exactly two distinct boundary zeros.
5. F has no boundary zero: a combination perpendicular to F_τ would otherwise have both value and derivative zero. The combination perpendicular to F(p) now proves det(F,F_τ)≠0. The boundary angle is a smooth circle covering. Exactly two zeros of every a·F force absolute degree one.
6. The resulting boundary curve is a smooth positive radial graph. Since every interior preimage has one Jacobian sign, degree equals that sign times the finite preimage count. Winding number ±1 inside and 0 outside proves one preimage inside and none outside. Local openness excludes mapping an interior point onto the boundary curve. This proves the same global result without route A's origin lemma or its global monotonicity argument.

## Smoothness/limit checks

- Even reflection is asserted C², not C∞. For W_y=0 along the diameter, W_xy also vanishes there, which is enough. The reflected potential is bounded; no higher smoothness is needed for the Fourier estimate.
- If the upper-side jet were identically zero, smooth Taylor estimates make W and its first derivatives decay to arbitrary orders after reflection. This justifies the inner-cutoff removal in the Carleman proof at each fixed τ.
- The outer-cutoff error is supported in R/2≤r≤R; comparison with r<R/4 gives the factor 2^(−τ). The bounded potential term is absorbed for large τ. There is no illicit simultaneous τ/ε limit.
- Interior analyticity continues a vanishing local solution after the boundary argument; it is not used to assert analytic continuation across a nonanalytic boundary.
- Each end eventually occupies one boundary-zero neighborhood: transitions between the finitely many disjoint neighborhoods would revisit a compact interior set, violating properness.
- A loop meeting ∂Ω only at one point still encloses a disk in Ω because the exterior of Ω is connected and unbounded.
- The global inverse on Ω is analytic by patching analytic local inverses. The boundary inverse is a separate one-dimensional assertion.
- Neumann normal flattening is unavoidable. Along p−tν, F changes by O(t²); hence no Lipschitz inverse on the closure. The disk exhibits the same effect.

## Scope and value

One proposed bridge: global coordinates by a double lowest Neumann eigenspace, a smooth star-shaped target, and its common nodal center. This is not a new multiplicity estimate. The deduction uses familiar planar and PDE tools; its claimed content is the global spectral-map conclusion, not novelty of the tools. No claim is made about convex target, quantitative distortion, rough domains, higher modes, or unequal lowest eigenvalues.
