# Further geometric and analytic screens

These are preselection records. The calculations below are not frozen candidates or independent correctness/contribution decisions.

## 366: crack-tip superlevels

The pinned `completion.tex` proves `cor:classification`, completes `thm:main`, and observes that endpoints/triple junctions are relatively closed and discrete, hence finite on compact subsets. Its `cor:weak-l4` uses the full local-model equivalence of De Lellis–Focardi, not merely an unspecified integrability theorem. `reductions.tex` supplies the exact SBV/reduced-minimizer interface for the bounded fidelity problem.

The stronger primary input is De Lellis–Focardi [2308.14660v2](https://arxiv.org/pdf/2308.14660v2), Proposition2.5.6 and its first-variation proof: the half-line profile is b sqrt(r) sin(theta/2), up to rotations, signs and additive constants, with b^2=2/pi. Thus |grad U|^2=1/(2pi r). Theorem6.1.6's proof gives |grad u(x)|<=C dist(x,{tips})^(-1/2) near the finitely many tips and bounded gradient away from them, including triple-junction neighborhoods. Theorem2.2.3 and its setup provide local convergence off the limiting crack; AppendixD Step3 explains the ordinary elliptic convergence there. Only the beginning of AppendixD was read, not its complete compactness proof.

The feasibility calculation uses this stronger interface. Fix a tip p and scale r=t^(-2). On fixed rescaled balls, t^(-1) grad u(p+t^(-2)y) converges, along every convergent blow-up subsequence, off the limiting half-line to grad U. The limiting half-line and the level circle |grad U|=1 both have planar measure zero. The pointwise estimate confines the original t-superlevel set to a ball of radius C^2 t^(-2) around p. Dominated convergence of indicator functions on this fixed rescaled ball gives

    t^4 area({|grad u|>t} near p) -> pi(1/(2pi))^2 = 1/(4pi).

No common limiting orientation is necessary: all possible rotations/signs have the same radial gradient magnitude. The subsequence criterion therefore gives the unrestricted t limit. Continuous compactly supported tests localize to finitely many tips, so the compatible measure calculation is

    t^4 1_{|grad u|>t} dx  ->  (1/(4pi)) sum_(interior tips p) delta_p

vaguely in the interior. A slightly larger compact neighborhood handles tips near the support boundary. A test vanishing at a boundary tip contributes zero by continuity. The corresponding log-truncated fourth moment has coefficient 1/pi per tip by layer cake, with the truncation convention fixed before using that observation. It is not a uniform estimate over minimizers.

This calculation preceded any selection and no target was frozen. It is the classical distribution-function transfer from the source's finite-tip regularity and the primary normalized asymptotic. It leaves no identified new compatibility operation. The old I122 quantitative tip-count question remains a different question: finiteness depending on a minimizer gives no polynomial or uniform bound in the data. Nothing here changes that question, creates a uniform rate, or handles variable coefficients.

## 341: actual compatible families versus the endpoint choices

The October7 `05-families.tex`, `lem:compatible-family`, already constructs smooth closed lifts by the elliptic inverse G_v=(L_v+H_v)^(-1)(I-H_v), the correction D_v=dd*G_v+H_v, and a convex partition of unity in the external parameter. This pays a genuine parameter-dependent exactness operation. Simply asking for a smooth family of compatible forms would repackage that construction.

The complete `11-endpoint.tex` uses a primitive null class F, rotates the cohomological basis, prepares a fibration and auxiliary data, chooses one sufficiently small epsilon, solves the appropriate Kähler/Yau steps, and joins compatible tamers along the path. The source introduction also already obtains individual Kähler forms in the relevant positive classes and the smooth K3/T4 classification. The earlier I80 geometric-flows report discusses the genuine family/equivariant issue. A free finite group action descends to the quotient within the relevant hypotheses; a general nonfree action or arbitrary compact parameter family requires compatible geometric preparation throughout. The local elliptic lemma does not select that preparation. This round constructed no such global family mechanism. The September main file was only an input map, not a fresh reading of every earlier proof section. No parametric theorem is asserted or frozen.

## 083: the actual old maximal question

The pinned introduction puts sup_epsilon OUTSIDE the L2 norm. It includes deterministic packet subcollections and Hilbert-valued bin estimates, not arbitrary output-dependent selectors. Actual r65 `flow-route.md` and r67 `selected-diagonal-status.md` were read. The old straight-segment maximal question has an unresolved diagonal-selected short-scale piece; it is not a fresh target for r120.

Lacey–Li [0704.0808v1](https://arxiv.org/pdf/0704.0808v1), Theorem1.18 statement and the proof of Lemma4.25, was checked. The fixed-kernel/packet estimates and its footnote concerning the missing suitable maximal function do not license an unnoticed supremum interchange. The flow route has a classical one-dimensional maximal transform after straightening a flow with controlled Jacobian, but comparing actual straight segments with flow curves costs O(t^2) displacement and can be order one at high transverse frequency. That method obstruction does not refute the original maximal question. No restart of its frozen target occurred; acquired reduction/assembly bodies not semantically needed were removed.

## 090: a stationary variance calculation, with explicit limits

The full Gaussian-transfer section supplies `prop:density-lp` and `lem:gaussian-duality`: a common radial Schwartz minorant f, Fourier positivity, and triangular direct/dual contact. The atomic companion's `prop:global-signs` has a strictly positive deleted-jet margin on the first left half-cell (greater than .032 before the positive normalization). With s=(sqrt(3)/2)|x|^2, this is the actual source operation behind I134/I137's first-shell quadratic gap q=G-f>=c_alpha(1-s)^2 for s<1. It is stronger than knowing only the optimum energy. I137's original-cell deficit and finite-window signed-measure-square arguments were read, including their square-density/subsequence limitations. Its old stationary/Palm warning is not adopted as a theorem of impossibility.

Here is the compatible probabilistic calculation tested. For a stationary simple intensity-one point process N with finite Gaussian pair energy per unit area, E N(Q)^2 is finite for a fixed unit square Q because G is bounded below on Q-Q. Translation invariance and Cauchy–Schwarz then bound mixed second moments of any two unit cells uniformly. Hence every Schwartz kernel is absolutely integrable against the expected pair measure, by summing cell displacements.

For a large square D, the signed finite measure (N-dx)|D has nonnegative f-energy by Fourier positivity. Taking expectations, dividing by |D|, and passing to the limit using the preceding cell bounds yields

    E sum_(x in N intersect Q) sum_(y in N,y!=x) f(x-y)
       >= fhat(0)-f(0),                 |Q|=1.

The cross/background terms converge to their integrals by stationarity; the pair boundary weights tend to one and are dominated by the summable Schwartz envelope. If the expected Gaussian pair energy equals the triangular value fhat(0)-f(0), subtraction and q>=0 show that the expected q-pair sum is zero. Countable windows therefore give no pair at distance below a=(sqrt(3)/2)^(-1/2), almost surely, using the strict first-shell gap. This calculation handles the expectation interface at this explicitly finite-energy Gaussian contract. It is not an unscreened Riesz/Coulomb equality theorem.

The remaining passage from stationary maximal-density hard-core packing to an almost sure single triangular lattice has the familiar saturation/Voronoi equality route: stationary saturation must preserve the relevant intensity comparison, mean side count is controlled by planar boundary errors, and equality in the polygon area bound forces hexagons. This round did not complete a fresh, fully specified stochastic saturation/mass-transport proof or read the closest primary for that entire passage. It therefore does not assert a new stationary crystallization theorem. The source's stationary minimizing-field construction and long-range screening appendix were not freshly read. They must be checked before any later claim involving renormalized energy. A mere stationarity restriction of an old rigidity question would not establish contribution.

The circle-packing companion main was inspected only for its actual input map and periodic-equality abstract; its proof sections were not acquired. That abstract is navigation, not a cleared comparison or a proof premise. No lattice candidate was frozen, no finite test was treated as proof, and no claim of exhaustion follows from this screen.

Late historical strengthening for341/342: the actual r23 `342-parametric-screen.md` was read before sealing. It replaces a varying harmonic kernel projection by the fixed-cohomology finite-rank augmentation R_b dd_b* plus sum (R_b h_i) tensor (R_b h_i). Poincare duality kills its kernel; its smooth inverse supplies closed lifts across jumping cokernel dimensions, and convex cutoffs supply the relative parameter extension with varying cohomology. This already covers a broader compatible-form family question than constant-rank patching. It still does not choose the hypersymplectic endpoint's geometric preparation in a prescribed family. No independent approval of that older full proof or its author rating is issued here.
