# R24: an obstruction to regular multiscale Heilbronn realizations

Status: pre-freeze mathematical screen, no substantial nominee. Family191. No campaign count increment, independent PASS or worldwide priority is claimed. The two complete deductions below reject specific transfer mechanisms; they do not refute the stipulated finite source theorem or a general nonregular construction.

## Exact stipulated source and proposed interface

At revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, *A power improvement in the Heilbronn triangle lower bound*, Theorem `intro:main`, gives absolute η,c₁>0 and n₀ such that for every integer n≥n₀ there is an n-point P⊂[0,1]² with every distinct triangle of area at least c₁ n^(-2+η). The actual source has 0<η<2. Its eleven mathematical TeX/Bib files, including all nine sections, were read and authenticated against the complete preprint tree. Source truth is stipulated, not audited.

The source's complete mechanism is finite-scale: alternating finite-field norm data is encoded in a selected determinant digit; distinct labels rule out small determinant residues. A shared special-linear transformation supplies an orbit law; a separate cap and restricted shift exclude short zero-determinant relations. Uniform conditional digit moments cover repeated labels. Chinese-remainder lifting, weighted lattice counts and deletion retain enough points. The final prime-interval interpolation gives every large n, but it is by taking subsets of separate finite configurations, not by extending a fixed nested configuration.

The screened interface was to retain the power gain in one compact object whose small-scale packing configurations inherit a quantitative all-triple area bound. Qualitative avoidance alone is not new: a circle has no three collinear points, and stronger dimension-one avoidance results already exist. The exact regular model below is impossible. No broader research target was frozen before or after this obstruction.

## Complete obstruction 1: stationary homothetic repetition

Let S₁,…,S_N be contracting homotheties of R², S_i(x)=r_i x+t_i with 0<r_i<1, and let K be their nonempty compact invariant set. If two maps have distinct fixed points a and b, then K contains three distinct collinear points.

Indeed invariance puts S_i^k(x) in K for any x∈K, and closedness puts each fixed point in K. If a is fixed by S_i, then

S_i(b)=(1-r_i)a+r_i b∈K.

Because 0<r_i<1 and a≠b, this is a third point on the open segment from a to b. Thus simply using a finite Heilbronn configuration as the digit set of a stationary homothetic system destroys even qualitative noncollinearity. This argument does not cover rotating similarities, varying constructions, or nonstationary maps with no common fixed-point structure.

## Complete obstruction 2: no Ahlfors-regular power-gain realization

For a nonempty compact K⊂R² and r>0, let

P_K(r)=max{|F|: F⊂K and |x-y|≥r for distinct x,y∈F},

and, whenever such triples exist, let

Φ_K(r)=min{Area(xyz): x,y,z∈K and min(|x-y|,|y-z|,|z-x|)≥r}.

Compactness makes both extrema well defined. Call K Ahlfors s-regular, with s>0, if there are a finite nonzero Borel measure μ supported on K, constants 0<a≤b<∞ and R>0 such that

a r^s≤μ(B(x,r))≤b r^s for every x∈K and 0<r≤R.

Closed or open balls give the same notion after adjusting constants. Fix closed balls below.

**Assertion.** There do not exist an Ahlfors s-regular compact K⊂R² with s>0, an exponent 0<α<2, and constants c,r₀>0 such that

Φ_K(r)≥c P_K(r)^(-α)                                                   (1)

for every 0<r≤r₀ for which the triple set is nonempty.

This explicitly rules out α=2−η from the source in this compact regular model. It does not assert a bound on arbitrary finite configurations.

### Step 1: (1) forbids collinearity and forces s≤1

A fixed distinct collinear triple has positive minimum pair distance. Taking r below that distance and r₀ makes Φ_K(r)=0, contradicting (1). Thus every line meets K in at most two points.

Ahlfors regularity implies 0<H^s(K)<∞ and dim_H K=s. For completeness, the upper mass bound gives a positive lower bound for H^s by the mass distribution argument. Maximal r-separated sets and the lower mass bound give O(r^-s) covering balls, hence finite H^s. These conclusions also ensure s≤2.

If s>1, the classical plane-section theorem gives a line whose intersection with K has Hausdorff dimension s−1>0, contradicting the preceding two-point bound. The precise primary interface used is Mattila, *Hausdorff dimension of plane sections and general intersections*, arXiv:2310.07538v1, Theorem1.2, specialized to all orthogonal line projections, p=2, n=2 and m=1. Its hypotheses in this classical specialization can be checked directly: for a measure ν in the unit ball satisfying ν(B(x,t))≤t^s,

I₁(ν)=∬|x-y|^-1 dν(x)dν(y)≤C_s ν(R²),

by layer-cake integration, since s>1. Polar coordinates and the Fourier energy identity give

∫||P_θ#ν||²_{L²(R)} dθ=C I₁(ν).

In particular these projections have L² densities for almost every θ, and the displayed estimate is the theorem's condition(1.4). The theorem supplies positively many fibers of dimension s−1. This is a credited classical slicing operation, not new work. Therefore s≤1. [Primary preprint](https://arxiv.org/abs/2310.07538v1).

### Step 2: comparable triples exist at every small scale

Choose κ∈(0,1/4) so that 2bκ^s<a. Fix x∈K and 0<r≤R. The ball B(x,r) has μ-mass at least ar^s. Its intersection with B(x,κr) has mass at most bκ^s r^s, so choose y∈K∩B(x,r) outside B(x,κr). The union B(x,κr)∪B(y,κr) has mass at most 2bκ^s r^s<ar^s. Choose z∈K∩B(x,r) outside that union. Thus x,y,z have all pair distances greater than κr and diameter at most 2r. Their area is at most 2r², so

Φ_K(κr)≤2r².                                                        (2)

### Step 3: packing cardinality contradicts the proposed exponent

For any (κr)-separated set F⊂K, the balls B(y,κr/3), y∈F, are disjoint. The lower mass bound gives

|F| a(κr/3)^s≤μ(K),

so P_K(κr)≤C r^-s, where C=μ(K)3^s/(aκ^s). Applying (1) and (2) for sufficiently small r yields

2r²≥c P_K(κr)^(-α)≥c C^(-α) r^(sα).

But s≤1 and α<2 give sα<2. Division by r^(sα) and r→0 is a contradiction. This proves the complete assertion.

Equivalently, if one assumes a positive all-triple lower bound Area(xyz)≥c·minpair(x,y,z)^β on an Ahlfors s-regular compact set, the same local triples force β≥2, while slicing forces s≤1. Its effective packing exponent β/s is therefore at least two. This is the same obstruction, not a second proposed result.

## Closest operations and remaining scope

Máthé's *Sets of large dimension not containing polynomial configurations*, arXiv:1201.0548v1, Lemma2.1 shifts one role's rational grid by a derivative-controlled amount so a polynomial value stays away from its discrete lattice. Proposition2.2 schedules countably many local exclusions at rapidly decreasing scales; Theorem2.3 uses derivatives to remove the nonsingularity restriction. Theorem4.1 already gives a compact dimension-one planar set with no collinear triple and with each direction realized at most once. The dimension lemma allows strongly separated successive scales and does not assert (1). Thus qualitative avoidance or introducing a Cantor schedule would not be a substantial new operation. [Primary preprint](https://arxiv.org/abs/1201.0548v1).

Fraser–Pramanik's *Large Sets Avoiding Patterns*, arXiv:1609.03105v1, Proposition3.4 and Lemmas3.5–3.6 explicitly select role-dependent small cubes by successive projections of boxes meeting the zero set. Coarea bounds the number of bad boxes; averaging selects low-incidence slices and the final role discards the remaining projected boxes. The resulting scale is tied to the number of variables and codimension, with constants depending on the coarse scale and derivative bounds. These are already paid multiscale avoidance operations. The global rank hypothesis of Theorem1.2 is not silently applied to the determinant at the full diagonal, where its derivative vanishes. [Primary preprint](https://arxiv.org/abs/1609.03105v1).

The source's separate finite configurations are compatible with these obstructions. No regular compact limit with (1) is supplied or needed by the source. A nonregular, rotating or nonstationary scheme would still have to control triangles with two points in one small cell and the third outside it, while retaining an appropriate quantitative cardinality law. Separate childwise copies give no common determinant congruence for such triples. The source's conditional estimates retain a shared global residue/orbit law; arbitrary prescribed cells or older fixed points are not part of that statement. No relative extension or global label compatibility mechanism was paid here.

The two obstruction proofs use standard homothety, regularity and slicing operations. They are useful exclusions, not a substantial campaign nomination. No general impossibility for nonregular sets, infinite sequences or other constructions is asserted. No narrower positive substitute, manuscript or formalization is offered.
