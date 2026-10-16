# R018 — Sharp logarithmic ball–slab nesting cost

**Accepted as the twelfth substantial finding.** The unchanged [I275 full proof](../iterations/i275-logarithmic-contact-full-proof.md) passed [I277 independent proof review](../reviews/i277-logarithmic-contact-proof.md), and [I278 independent contribution review](../reviews/i278-logarithmic-contact-contribution.md) judged the full theorem SUBSTANTIAL. The parent read the reviews and complete reconstructions and checked their recorded local hashes. This is written mathematical validation, not a formal proof certificate, external peer review, or a worldwide-priority claim.

## Exact theorem

Let T^3=R^3/Z^3 have its unit cubic flat metric, and let P denote De Giorgi perimeter. Fix

    1/(2pi) < R < 1/3.

For sufficiently small epsilon>0 define

    L_R(epsilon) = inf { P(E)+P(F)-4pi R^2-2 :
                        E subset F a.e.,
                        |E|=4pi R^3/3,
                        |F|=2(R-epsilon) },

where the infimum runs over all finite-perimeter pairs in T^3. Then

    lim_(epsilon down to 0) |log epsilon| L_R(epsilon)/epsilon^2 = 2pi.

Thus every admissible sequence has normalized liminf at least 2pi, and smooth nested pairs attain the coefficient asymptotically. Both interfaces are free. No symmetry, connectedness, fixed topology or regularity is imposed on the original competitors. R is fixed; constants and convergence may depend on R.

## Dependencies, attribution and contribution

The [pinned cubic-torus theorem](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026), actual Theorem `intro:main`, supplies the scalar profile and equality classes and is stipulated true. The inner volume lies strictly on the ball branch. The limiting outer volume 2R lies in (1/pi,1-1/pi), strictly on the slab branch, including by complementation above half volume. Consequently the separate scalar deficits are nonnegative. At epsilon=0 the limiting ball touches the slab at two poles; positive epsilon forces deformation.

The paired BV reduction, common volume correction, scalar quasiminimality, reference centering and energy expansions build on [R017](R017-ball-tube-contact-asymptotic.md). The external improved-convergence input is Acerbi–Fusco–Morini, [Minimality via second variation for a nonlocal isoperimetric problem](https://cvgmt.sns.it/media/doc/paper/540/Acerbi-Fusco-Morini.FINAL.pdf), Definition 2.5 and Theorem 4.2. Their hypotheses and conclusion were checked; the classical regularity theorem is not reproved or claimed as new.

Logarithmic contact response is classical, including [Lacasse–Grest–Levine](https://arxiv.org/abs/mtrl-th/9603005), [Lv](https://arxiv.org/abs/1704.05830), and moving-contact calculations in [Ginot et al.](https://arxiv.org/abs/1910.10029). Equal displacement sharing and annular capacity are also classical. Neither these facts nor the numerical constant are separate discoveries here.

The incremental contribution is the sharp lower passage for the unrestricted nonlinear minimum at two shrinking contacts. R017 uses a fixed-circle trace; a point on a two-dimensional interface has zero H1 capacity. Here normalized graph heights converge to zero globally in H1 while an order-epsilon displacement is still forced locally. Exact nonlinear charts, removal of fixed low modes, sharp high-mode localization and shrinking-circle averages recover the missing logarithmic energy without a contact-shape assumption. This is one theorem, including its matching recovery, not several findings.

## Proof

**Upper bound.** Set ell=|log epsilon| and a=sqrt(epsilon) ell. In each polar chart use a cutoff chi equal to one near radius a, zero beyond fixed small delta, and logarithmic in between. Rounded corners give Dirichlet energy (2pi+o(1))/log(delta/a), squared-L2 mass O_delta(ell^-2)+O(a^2), and integral O_delta(ell^-1)+O(a^2). Move the sphere inward by t chi at both poles and each slab face outward by t chi, where t=(1+eta)epsilon/2. Fixed free patches permit exact independent volume corrections of size O_delta(epsilon/ell), costing o(epsilon^2/ell). In the cores the relative gain is (1+eta+o(1))epsilon. Outside the cores the original quadratic separation is at least c_R a^2, much larger than epsilon. Elsewhere the original separation is positive. These facts put the whole inner boundary between the faces. Taking extrema of each nonempty compact vertical slice proves containment of the region, without assuming connected slices. Area expansion of the four patches gives limsup ell L_R/epsilon^2 <=2pi(1+eta)^2(1+O_R(delta^2)). Take epsilon to zero first, then delta and eta to zero.

**Exact minimizing replacement and global graphs.** BV compactness gives exact minimizing pairs. The upper bound and nonnegative scalar deficits force every limiting pair to be a radius-R ball inside a width-2R coordinate slab. Inclusion centers the ball normally between the faces. Common translations and signed coordinate permutations normalize the pair. Choose a sphere patch strictly inside the slab and a face patch outside the ball projection. Two ambient vector fields there have an invertible diagonal derivative for the two volumes. Integrating smooth flow Jacobians over nearby measurable pairs preserves uniform invertibility. A common flow corrects total volume error q with parameter and perimeter cost O(q), preserving inclusion.

For an arbitrary scalar competitor H for E use (H intersection F,H union F); for a competitor for F use (E intersection H,E union H). Perimeter submodularity and the exact symmetric-difference identity, followed by common volume correction, yield uniform scalar quasiminimality. Larger-perimeter competitors and larger balls satisfy the bound trivially. AFM gives global C1-small graphs over the sphere and both disconnected slab faces; L1 convergence selects the occupied side. Choose the sphere reference center to remove its three degree-one moments. Choose the slab reference center so its two outward heights V^+,V^- have zero means: their sum is zero by exact volume, and reference translation changes their means oppositely. Retain relative axial displacement h. These are representations of unchanged sets. The sphere spectral gap and face Poincare inequalities give

    ||psi||_H1 + ||V^+||_H1 + ||V^-||_H1 = O(epsilon/sqrt(ell)),
    P(E)-4piR^2 = Q_B(psi)/2 + o(epsilon^2/ell),
    Q_B(psi)=integral_(S_R)(|grad psi|^2-2psi^2/R^2).

Each face has its Dirichlet area expansion with the same controlled remainder. The sphere mean is O(epsilon^2/ell).

**Exact charts and spectral localization.** In horizontal polar coordinates let W^+,W^- be the actual outward vertical sphere heights. Inclusion gives exactly

    V^pm(x)-W^pm(x) >= epsilon +/- h - [R-sqrt(R^2-|x|^2)].

The radial-to-vertical change is W=A psi composed with F, with F the inverse actual horizontal parametrization and, writing p=psi(F(x)),

    A(x)=(2R+p)/(sqrt((R+p)^2-|x|^2)+sqrt(R^2-|x|^2)).

On fixed small charts the metric distortion is 1+O_R(delta^2)+o(1), A has the same bound, and |grad A|<=C_R delta+o(1). No arbitrary C1 error is asserted to be o(epsilon). Decompose psi into its constant, degrees 2 through N, and high part k. For fixed N the low part is uniformly o(epsilon). Define W_high=A k composed with F, keeping the actual A and F. The high-mode bound integral k^2 <=R^2/[(N+1)(N+2)] integral |grad k|^2 absorbs the curvature potential and chart losses. Choosing delta small, an auxiliary gradient parameter small, and N large, all before epsilon tends to zero, gives for any zeta>0, with Z^pm=V^pm-W_high^pm,

    L_R(epsilon) >= (1-zeta)/4
                     sum_pm integral_(|x|<2delta)|grad Z^pm|^2
                     +o(epsilon^2/ell).

The local H1 norms of Z^pm are O(epsilon/sqrt(ell)). The exact parameter-order and change-of-variable estimates are proved in [I275 Sections 4–5](../iterations/i275-logarithmic-contact-full-proof.md) and checked in the [independent reconstruction](../experiments/i277_logarithmic_contact_proof/analysis.md).

**Shrinking annuli and center drift.** If m(rho) is the circle average of Z, Jensen and weighted Cauchy–Schwarz give

    integral_(a<|x|<b)|grad Z|^2
      >= 2pi [m(a)-m(b)]^2/log(b/a).

The L2 bound supplies an outer radius b in [delta,2delta] with m(b)=o(epsilon), separately for each sign. At a=c sqrt(epsilon), exact inclusion and the low-mode bound give m^pm(a)>=[1-c^2/(2R)+o(1)]epsilon +/-h. Use positive parts for negative lower bounds. Since log(b/a)=ell/2+O(1), the two annular energies and

    (s+h)_+^2+(s-h)_+^2 >= 2s^2  for every s>=0 and real h

yield liminf ell L_R/epsilon^2 >=2pi(1-zeta)(1-c^2/(2R))^2. No bound on h/epsilon is assumed. Let c and zeta decrease to zero. The upper bound matches. Every original pair has energy at least the exact minimum, proving the full statement.

## Validation and limits

- **Proof:** I277 PASS without necessary repairs on I275 SHA256 `ab1a54ce81fc0047d05edc343ab6c65ac00e2a62fcc4515725df748c7aaf693f`. The reconstruction checks upper containment, both volume corrections, disconnected graphs, exact charts, negative Jacobi terms, limit order and drift.
- **Contribution:** I278 SUBSTANTIAL for the singular nonlinear all-BV lower passage, crediting R017 and classical droplet calculations. The [parent disposition](../iterations/i278-logarithmic-contact-contribution-parent-disposition.md) records the nomination boundary.
- **Read limits:** full original Morse–Witten and Höhler–Weaire calculations were inaccessible. General contact-capacity and shape-sensitivity literature beyond the bounded screen was not exhaustively read. Worldwide priority is unverified. The [I278 source record](../sources/i278_logarithmic_contact_contribution/literature.md) preserves exact comparisons and limits, including ABLW Theorem 4.5.
- **Scope:** no endpoint-uniform limit, general unequal-tension result, functional Gamma-limit, contact-set classification, arbitrary near-minimizer graph theorem or dynamics is asserted.
- **Provenance:** I277 manifest `3db98a91c446596597d1c93bb8424b3f14a676dd5c681cf8c058c100316d9382`, with 32 local records checked; I278 manifest `b0e4ef18b95479569610997b56c0c575f7144122f639c81f8974d62d22ac788d`, with 26 checked. Hash authentication does not expand stated reading extents.

**Twelve accepted substantial findings; eight remain toward twenty.** Original ten decisions are preserved. This acceptance receives its own commit and verified project-only publication.
