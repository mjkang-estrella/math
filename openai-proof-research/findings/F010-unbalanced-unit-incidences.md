# F010 — Power-saving incidences for unequal unit-circle and point sets

Status: **proved downstream corollary; accepted in two independent review rounds**. Upstream results
are accepted as true. Literature priority is not established.

## Source and hypothesis

The accepted [family 167 unit-distance theorem, `thm:main`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-power-saving-for-planar-unit-distances-September-23-2026/build/sections/00-introduction.tex)
gives absolute C₀>0 and 1≤β₀<4/3 such that u(N)≤C₀N^β₀ for every
positive integer N, where u(N) is the maximum number of unordered unit
distances among N planar points. Choose once and for all
β=(β₀+4/3)/2, so **1<β<4/3**, and put δ=4/3−β∈(0,1/3).
Then u(N)≤C₀N^β as well. All constants below may depend on this fixed
choice; no effective numerical exponent is supplied.

The standard partition input is [Guth–Katz, Theorem 4.1](https://arxiv.org/pdf/1011.4105),
also [Sharir–Sheffer–Zahl, Theorems 2.1–2.2](https://arxiv.org/pdf/1208.0053):
a degree-at-most-D polynomial partitions the plane into O(D²) connected
cells each containing O(m/D²) of a supplied m-point set. The constants
are absolute; points on its zero set are accounted for separately.

## Theorem

For finite P,Q⊂R², let I(P,Q) count ordered pairs (p,q) at distance 1.
The sets may overlap. If m=|P|≥n=|Q|≥1, then

    I(P,Q) ≤ K [m^(2−β) n^(2β−2) + m]
           = K [(mn)^(2/3) (m/n²)^δ + m].

Here K is an absolute constant for the fixed upstream input. If m<n,
interchange the two sizes. Thus for fixed 0<ε≤1 and
n≤m≤n^(2−ε), the bound saves at least a factor n^(εδ), up to
constants, relative to the classical (mn)^(2/3) scale.
For m≥n² the correct order is Θ(m).

## Complete proof

**Step 0 (crude unbalanced bound).** Let m′ ≥ n′ ≥ 1. Split P′ into at most ⌈m′/n′⌉ ≤ 2m′/n′ groups G, each of size at most n′.

The map (p,q) ↦ {p,q} sends incidences between G and Q′ to unit-distance pairs in G ∪ Q′. Each pair has at most 2 preimages. Also |G ∪ Q′| ≤ 2n′ and u is nondecreasing. So I(G,Q′) ≤ 2u(2n′) ≤ 2^{1+β} C₀ n′^β. Summing over the groups gives:

  I(P′,Q′) ≤ A (m′ n′^{β−1} + n′ m′^{β−1}),  A = 2^{2+β} C₀,   (∗)

for all m′, n′ ≥ 1. The second term covers the case m′ < n′, by symmetry.

**Step 1 (range m ≥ n²).** The incidence graph has no K_{2,3} with the 2 on the circle side, because two distinct unit circles meet in at most 2 points. Kővári–Sós–Turán then gives I ≤ C(n m^{1/2} + m) ≤ 2Cm.

**Step 2 (range n ≤ m ≤ n²; polynomial partitioning).** Put D = ⌊m/n⌋. Then 1 ≤ D, m/(2n) ≤ D ≤ m/n, and D² ≤ m. The Guth–Katz partitioning theorem gives a nonzero f with deg f ≤ D. The complement ℝ² \ Z(f) has L ≤ C₂D² connected cells, and each cell contains at most C₁m/D² points of P.

- *Circles contained in Z(f).* Such a circle's polynomial (x−a)²+(y−b)²−1 is irreducible over ℂ. Since f vanishes on infinitely many of its points, Bézout shows it divides f. Distinct centres give non-associate factors, so at most D/2 circles lie in Z(f).
  - Let Γ₀ be these circles. Each point has degree d_p ≤ 1 + C(d_p, 2) in the incidence graph. Two circles share at most 2 points. Hence I(P, Γ₀) ≤ m + 2C(|Γ₀|, 2) ≤ m + D²/4 ≤ 2m.
- *Other circles, points on Z(f).* A circle not contained in Z(f) meets it in at most 2D points (Bézout). This contributes at most 2Dn ≤ 2m incidences.
- *Other circles, points inside cells.* Such a circle minus its at most 2D points of Z(f) has at most max(1, 2D) arcs. Each arc lies in one cell, so the circle meets at most 3D cells.
  - Let cell i contain m_i ≤ C₁m/D² points and meet n_i circles. Then Σn_i ≤ 3Dn.
  - Apply (∗) in each cell and use Σ_{i≤L} x_i^θ ≤ L^{1−θ}(Σx_i)^θ with θ = β−1 ∈ (0,1/3), omitting empty cells:
  - Σ m_i n_i^{β−1} ≤ (C₁m/D²)(C₂D²)^{2−β}(3Dn)^{β−1} ≲ m n^{β−1} D^{1−β} ≤ 2^{β−1} m^{2−β} n^{2β−2}. This uses 1−β < 0 and D ≥ m/2n.
  - Σ n_i m_i^{β−1} ≤ (C₁m/D²)^{β−1} · 3Dn ≲ n m^{β−1} D^{3−2β} ≤ m^{2−β} n^{2β−2}. This uses 3−2β > 0 and D ≤ m/n.

Adding the four contributions gives I ≤ K(m^{2−β}n^{2β−2} + m). Finally, m^{2−β}n^{2β−2} = (mn)^{2/3}(m/n²)^δ with β = 4/3 − δ. ∎


## Degeneracy checks and comparison

A circle polynomial is irreducible over C: a translated complex linear
change makes it uv−1, whose quotient is the domain C[u,u^−1]. Thus the
Bézout argument also applies over C; factoring only its homogeneous part
would be incorrect. Repeated polynomial factors, tangencies and points
on intersections do not invalidate the separate zero-set counts.

The partition theorem's degree-O(√r) form gives the stated degree cap by
choosing r as a sufficiently small fixed multiple of D²; bounded D is
covered by increasing absolute constants. Empty cell incidences are zero.

In n≤m≤n² the nonlinear term divided by m is
(n²/m)^(β−1)≥1, so the additive m term does not spoil the claimed
power saving. If m≥n² the nonlinear term is at most m, and the lower
example consists of m points on the unit circle around one member of Q,
with n−1 additional distinct centers. This gives I≥m. There is no
matching nonlinear lower bound asserted for n≤m<n².

## Novelty and rejected extensions

This is a standard polynomial-partitioning transfer of a balanced
unit-distance estimate to unequal sets. The statement was not found in
the checked upstream sources or references; that does not establish
priority. The actual same-family companion is [The weak pinned planar
distance theorem](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-weak-pinned-planar-distance-theorem-September-23-2026/build/sections/introduction.tex),
which concerns distance-fiber decay and almost-every-pin distinct
distances. It is not the unbalanced theorem.

The initial scout's optional claims are excluded from this finding:

- Its rich-point formula has one r-decay exponent above 3 and one below 3;
  the statement that both exceed 3 was false.
- Its claimed universal comparator O(k^(2/3)n^(4/3)) for arbitrary k
  prescribed distances is false. A square grid realizes all its Θ(n²)
  pairs using O(n/√log n) distances, contradicting that comparator.
- Substituting a variable exponent 1+o(1) into a theorem with constants
  depending on a fixed β is unjustified. The source also reports a
  superlinear fixed-power lower bound, so the historical near-linear
  target is not asserted here.

None of these excluded statements is used in the main proof.

## Validation

[First independent review](../reviews/unbalanced_incidence-r1.md) checked
every cell exponent, KST orientation, contained-circle count, source
statement and degenerate case, accepting the main theorem with the
corrections now incorporated. The parent independently re-derived the
balance at D≈m/n and removed the unsupported optional claims. The
scout's finite lattice-copy experiment is not evidence for this theorem;
its validation is analytic. No proof-assistant verification is claimed.

[Second independent review](../reviews/unbalanced_incidence-r2.md) accepted
the corrected proof, rechecked every exponent and degenerate case, and
confirmed that no rejected optional claim survives. Its cosmetic edits are
incorporated.
