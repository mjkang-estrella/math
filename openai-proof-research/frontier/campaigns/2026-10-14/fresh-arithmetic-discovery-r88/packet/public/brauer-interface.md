# Brauer twisting: an exact uncancelled evaluation interface

No target was frozen. The exploratory full question was whether source055's exact ordinary large-volume charge and standard double-tilt heart extend to every Brauer twist on every smooth projective complex threefold with trivial canonical bundle, on an open real B,H sector with one threshold for all t beyond it and support on the full twisted numerical group. Choices of gerbe/twisted Chern character would have to be fixed in an actual freeze. None was selected, and no étale-split, abelian, rational-parameter, weak-support or asymptotic-only substitute is nominated.

## Strongest compatible existing reductions tried

[Hotchkiss–Perry,2405.03315v2](https://arxiv.org/pdf/2405.03315v2), §10, defines the rational Chern character for a μ_n-gerbe; Remark10.3 distinguishes it from the Chern character normalized with a chosen twisted generating bundle. This distinction prevents silently transferring an exact ordinary charge through tensoring by a generator.

The actual Lemma12.4 treats finite smooth surjections. It preserves the first tilt heart, and semistability descends. The converse semistability assertion used in its proof requires an étale map and rational twisting divisor: an HN filtration is uniquely invariant on the Galois closure and descends. Theorem12.6 uses multiplication on an abelian threefold, which is étale and annihilates the Brauer class. Its proof therefore already supplies that abelian case. Theorem12.8 transfers its twisted BMT inequality to stability on the ch_H lattice. It is not by itself full numerical support. Neither result supplies an arbitrary étale splitter for every Brauer class on every threefold.

Using a ramified finite splitter would need a compatible upward tilt-semistability statement, or another replacement, through precisely that map. No such proof was constructed. Tensoring an α-twisted object by W^∨ produces an ordinary complex, but does not preserve the relevant exact Chern character or tilt semistability. Applying the ordinary theorem to that complex is therefore not an established reduction.

## Analytic calculation and the actual cancellation

The source's strong inequality has a rank-sensitive analytic core. `03-analysis.tex` obtains a negative-slope surface cohomology estimate controlled by rξ, with no additive bare-rank term; ξ is the projected discriminant defect. In a prospective twisted version, one might use a Hermite–Einstein connection on G and pass to the honest bundle W^∨⊗G. Fixed curvature from W can in principle be dominated by a sufficiently negative central slope, while the trace-free G-curvature retains a discriminant energy bound. This is a feasibility observation only: a full twisted analytic estimate with the source's uniformity was not proved.

[Perego,1910.01867v1](https://arxiv.org/pdf/1910.01867v1), Theorem1.1, supplies twisted Hermite–Einstein correspondences with a fixed B-field. Its actual setup and curvature/gluing description were read; the long existence proof was not completely read. Its assertion is for twisted holomorphic vector bundles, not an automatic proof of every reflexive-sheaf, restriction, discriminant and finite-characteristic interface in the source. No new estimate is claimed from its abstract.

The decisive arithmetic of the attempted replacement appears in `04-apex.tex`, `lem:restriction-image`. Let e=d_B(E)−A|r(E)| for the original ν=0 semistable E. The source residual P is tested by an ARBITRARY finite-dimensional space U⊂Hom(O_X(−tH),P), of dimension N. N is not initially bounded by e. At a fixed side tilt point, take the image I and kernel K′ of O_X(−tH)^N→P. The source proves rank(I), c_1(I), projected ch_2(I)=O(e), independently of N, using the side-tilt comparison and support. After twisting, K′(t) has rank N+O(e), slopes in a bounded nonpositive interval, and

    Σ_i r_i μ_i² + Σ_i r_i δ_i^0 = O(e).

Surface Riemann–Roch then gives almost all the N h^0(O_S(m)) source sections inside the kernel. Negative-cohomology errors and the subsequent curve restriction cost only O(e). Subtracting these sections proves that the restriction image of U has dimension O(e), independently of N. The argument uses derived restriction; no exactness of tilt-image formation under restriction is presumed.

Replacing the source line by a fixed twisted bundle W gives instead the K-theory relation

    [K′(t)]=N[W]−[I(t)].

Even if one could reproduce the side-tilt image bounds, c_1(K′(t)) and ch_2(K′(t)) now contain N c_1(W) and N ch_2(W). Normalizing the first slope does not generally remove the discriminant of W. The displayed source moment bound becomes at best a bound with a fixed multiple of N added; it is no longer O(e). Such a term defeats the exact cancellation of the unrestricted evaluation dimension. The fact that rank(I)=O(e) does NOT bound N: the source expressly permits redundant sections and proves the N-independent bound by its kernel argument.

A completed replacement would need a relative-to-W surface/curve cohomology cancellation removing the full N[W] contribution while retaining all side-tilt estimates and the original charge, or a genuinely different global mechanism. No such cancellation was established. Nor was it shown impossible: the failure concerns this literal proof substitution, not all twisted stability conditions. Assuming W projectively flat would change the full question and is not an allowed repair.

This round did not complete a twisted Frobenius/presentation argument either. A prime progression preserving the period does not itself supply the source's global evaluation and exact normalization. The generic full-numerical mass–Hom operation in `quotient-support.md` would help only after a compatible stability construction and mass bound exist; it does not construct the twisted heart or the required charge.

The full exploratory direction remains unproved here. The missing operation has been stated precisely, without an assertion that it is new in the literature, a target refutation, or a conditional nominee.
