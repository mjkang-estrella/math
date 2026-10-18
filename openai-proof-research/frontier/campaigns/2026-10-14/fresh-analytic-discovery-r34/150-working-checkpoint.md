# Family150: collision-clock spectral rigidity

Myeongjin Kang, no affiliation. Original prose CC BY 4.0. Exploratory checkpoint, not a nomination, independent review, or count increase.

The initial family150/triangular-billiard queries found no hit; a later expanded irrational-billiard/collision-map query found I52 section2B, which was then read completely. It screens strong mixing for one explicit fully irrational triangle and selects a different standard-map target. No prior collision-map target was found. This corrects the initial zero-history description. This is bounded search evidence, not a worldwide priority claim. All five mathematical sections of the pinned weak-mixing companion have now been read completely. The earlier ergodicity companion has subsequently been read completely, including its already-paid collision ergodicity and spectral corollary. Primary proof comparison is recorded separately in reading-and-limits.md.

## Natural target under investigation

For every nondegenerate Euclidean triangle Q with at least one angle irrational relative to pi, let T be its unit-speed billiard collision map on open-side points with inward unit direction, after removing the null singular trajectories. Let s be boundary arclength, phi the angle from the inward normal, and dnu=cos(phi) ds dphi/(2 perimeter(Q)). The full target is weak mixing of T on this entire finite collision phase space. No genericity, Diophantine, angle, symmetry, acute-triangle, smooth-eigenfunction or frequency restriction is introduced. This is a post-exploration scope, not a claim of a pre-exploration freeze. It remains unproved and unrefuted.

The source proves weak mixing for the physical-time flow, not its collision map. Ergodicity of T follows from source flow ergodicity by suspension. Weak mixing does not transfer by that argument: a T-eigenfunction h with h(Tz)=omega h(z) suspends to a field constant during flights and jumping by omega at collisions. A genuine flow eigenfunction would instead have h(Tz)=exp(i lambda tau(z)) h(z), with the nonconstant flight roof tau.

## Exact unpaid seam interface

On the oriented double, a lift constant along flights has phase omega across a seam in one crossing direction and omega^{-1} in the reverse direction. This is required by reversibility of a geometric gluing, and differs from the scalar constant transitions of the source coefficient bundles. After choosing a normal and writing omega=exp(i alpha), its angular transmission is

J_alpha(theta)=exp(i alpha sign(cos theta))=cos(alpha)+i sin(alpha) sign(cos theta).

The sign convention may be reversed; that only conjugates J. Its Fourier coefficients are j_0=cos(alpha), j_m=(2i sin(alpha)/pi) sin(m pi/2)/m for m nonzero. Unless sin(alpha)=0, one angular mode generates infinitely many modes across the seam. The source tail equation AU=B with exactly two boundary modes therefore does not transfer verbatim.

A quantitative control: let P_+ project to modes >=0. The finite block from inputs -N,...,-1 to outputs 0,...,N of [P_+,J_alpha] has squared Hilbert--Schmidt norm

(4 sin(alpha)^2/pi^2) sum_{m=1}^{2N} c_N(m) sin(m pi/2)^2/m^2,

where c_N(m)=m for 1<=m<=N, and c_N(m)=2N+1-m for N<m<=2N. Hence it is (2 sin(alpha)^2/pi^2) log N+O_alpha(1). The operator norm remains bounded, at most 2; the logarithm is a failure of finite-mode/Hilbert--Schmidt summability, not an operator-norm obstruction or a counterexample to the target.

The source's corner cutoffs use a bad set of area O(eps^2), derivatives O(eps^{-1}), and T eps=s in the long-average argument. Cutting out whole seams instead gives area O(eps) and the crude product ||Aw||_2 ||1_E grad w||_2 of order eps^{-1}; it cannot supply the source's uniform individual-mode bound. Cutting only the phase discontinuity near grazing has phase-space codimension two, but angular projection spreads its support and the transmission mixes coefficients; this observation does not restore the source's coefficient integration-by-parts identity.

## A technical parity control

The special eigenvalue omega=-1 has constant seam phase. If h(Tz)=-h(z), lift to the oriented double by multiplying the last-collision value by the sheet sign. A forward collision flips both signs, so the lift is invariant under geodesic flow. The source transverse-rigidity proposition applies at lambda=0 on the double and makes this lift horizontally constant. Holonomy around an irrational vertex rotates directions by an irrational multiple of 2pi, so its measurable angular amplitude is constant. Connected chart propagation makes the whole lift constant. The deck involution negates it; hence it vanishes. This rules out the eigenvalue -1. Together with ergodicity it proves ergodicity of T^2, but this is a short technical consequence and is not substituted for the full weak-mixing target.

The argument requires the intrinsic double and its deck involution: simply pretending that h itself is a global invariant function would drop the phase and be wrong. For other roots of unity, a naive collision-count cover is not automatically a flat surface cover: edge gluing must be an involution, while a forward collision increments the count in either traversal direction. The direction-dependent seam phase above is exactly the remaining issue.

## Other routes screened

The source energy and long-average operations use compactness, finitely many Euclidean cone points, unitary angular coefficient transitions and cone area O(eps^2), not the number three itself. Extending the physical-time proof to arbitrary finite polygonal doubles is therefore likely a technical operation; no such extension is nominated. Strong mixing or absolutely continuous spectrum would require correlation/spectral-measure estimates not supplied by the exact-eigenfunction endpoint identity. No broad strong-mixing theorem is frozen merely because it is stronger.
