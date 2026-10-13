# I211 source statement checks

2026-10-12. Existing retained sources were read in place. No external retrieval or new source copy was necessary. This is a proof review, not a worldwide-priority, contribution, or count review. Source bytes and precise reading limits are recorded in [input-authentication.json](../../experiments/i211_tetrahedron_lower_bound_proof/input-authentication.json).

## Primary comparison actually checked

K. Bezdek and A. E. Litvak, *Covering convex bodies by cylinders and lattice points by flats*, [arXiv:0903.4842v1](https://arxiv.org/abs/0903.4842v1), existing file `frontier/sources/i201_elliptic_covering/bezdek-litvak-2009v1.pdf`. Read PDF pages 1–7 through text extraction, not pages 8–14.

Theorem 3.1 on pages 5–6 states that every finite cylinder cover of a d-dimensional convex body has sum of directionwise cross-sectional volume ratios at least 1/d, and at least 1 for an ellipsoid. Its cylinder definition permits measurable bases. The proof on pages 6–7 uses a nonnegative density for ellipsoids and volume/section bounds for general bodies. Thus the mass divided by a uniform line-integral bound principle predates I209. Its 1/3 directionwise bound implies the absolute lower bound A_min/3 in dimension three because every projection denominator is at least A_min. The introduction discusses the regular tetrahedron's two-cylinder half-area example. No claim is made here to have read Bang's original paper or the later lattice applications.

## Pinned companion statements actually checked

Pin: `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` in `https://github.com/openai/math`. All of their results are stipulated true. Each following introduction was read fully in the existing I198 source tree, without reading the whole manuscript:

* `Finite-cylinder-approximation-of-ruled-sets-September-27-2026/build/sections/introduction.tex`: cylinder/base conventions; b:projection, the physical perpendicular-area formula; b:approximation, the finite approximation theorem with trace zero and -L^-2<det DV<=0. None is a needed lemma for the lower proof.
* `Finite-angular-cylinder-covers-below-the-half-area-bound-September-27-2026/build/sections/introduction.tex`: thm:counterexample and cor:normalized-covering. The first is an absolute-area upper construction for regular tetrahedra; the second is an affine directionwise statement. Their distinct normalizations agree with the scope restriction in I209.
* `Slope-field-perturbations-of-the-two-cylinder-covering-September-27-2026/build/sections/introduction.tex`: c:main and c:affine-tetrahedra, plus the explicit distinction between absolute and directionwise costs.
* `Finite-triangular-approximation-of-radial-sweeps-September-27-2026/build/introduction.tex`: thm:radial and cor:tetrahedron, giving finite radial-sweep realization and a tetrahedral upper cover, not the quadratic lower certificate.

Three further existing retained sections were fully read:

* `frontier/sources/i209_elliptic_tetrahedron/slope-projection.tex`, corresponding to the pinned slope manuscript's `build/sections/projection.tex`: c:normal-frame states A_min(K_2)=sqrt(2); c:nil-projection states A(u)=3 volume(T)/L_u. It contains the normal-frame and overlap-volume explanations.
* `frontier/sources/i209_elliptic_tetrahedron/radial-projections.tex`, corresponding to the pinned radial manuscript's `build/projections.tex`: prop:simplex states A(u)L(u)=dV and min A=dV/diameter; eq:regular-normalization gives A_min=e^2/(2sqrt(2)). The entering-face formula also appears explicitly. These confirm the normalization independently reproduced in the review.
* `frontier/sources/i201_elliptic_covering/angular-cubic-buffer.tex`, corresponding to the pinned angular manuscript's `build/sections/cubic-buffer.tex`: prop:angular-cubic states the finite compact triangular cover and normalized expansion 1/2-tau^2/240+(25/2)tau^3 with error at most 2tau^4 for 0<tau<=1/50, and strict saving for 0<tau<=1/4000. This is context only.

No quadratic weighted-chord optimum is stated in these sections. That is a statement about these reads, not an exhaustive prior-art result. This review performed no web search and adopts no worldwide novelty conclusion from I209's literature search. The relevant source normalization and old density method are verified; the new lower estimate and nonsymmetric quadratic reduction were checked directly in written mathematics.

## Exclusions

The initial broad catalogue display was truncated; only lines 2435–2490 of `sources/CONTENTS.md` were subsequently read completely and used as the Result 100 locator. Neither source tree catalogue was read. No other active review was read. The I203 nonlinear theorem, the square lemma, and the complete finite-cover details of the failed upper route are outside this proof gate; no dependency on them enters the lower theorem.
