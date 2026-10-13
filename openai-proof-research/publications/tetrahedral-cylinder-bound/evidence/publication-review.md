# Publication check

The publication assistant checked this manuscript against R015 and the full I209 lower-bound proof, I211 proof review, and I212 contribution review at public research revision `013c239d257cb6f9956d3d5724fd7a726770c43b`. These are AI research records, not human peer review.

The manuscript proves the result from elementary tetrahedral geometry and Tonelli's theorem. It does not depend on the pinned OpenAI corpus for a mathematical theorem. The proof includes the minimum projection area, barycentric second moment, midpoint constraint for every chord, the opposite-edge equality family, both breakpoints in the line maximum, arbitrary measurable bases, and symmetrization of every admissible quadratic polynomial. Scaling gives the stated bound for every positive edge length.

Primary comparison: Bezdek–Litvak 2009, Section 3, Theorem 3.1 and its density proof were read from the arXiv PDF. Their ellipsoid theorem gives the inscribed-ball consequence pi/(6 sqrt(2)), which is explicitly acknowledged. The 2016 paper's Theorem 3.1 treats multiple covers. No worldwide priority or best-known-bound claim is made. The generic density method and averaging are not presented as new principles. The asserted optimality is only among nonnegative polynomial densities of degree at most two with one common maximum-line-integral denominator. No covering sharpness, arbitrary-density optimality, directionwise-normalized improvement, or arbitrary affine-image extension is claimed.

Validation: `validate.py` checks 7,056 rational barycentric chord pairs, 31 opposite-edge pairs, and the exact squared constants. Those finite checks supplement the analytic argument; they are not its proof. The standalone ZIP rebuilds without LaTeX warnings and has text identical to the inspected PDF. All four pages were visually inspected at 105 dpi. The prose was edited under the requested unslop skill and the established AMS-style format. The acknowledgment preserves the disclosure wording used in the earlier papers.

Disposition: suitable for release as an author preprint within this stated scope. No independent human or formal verification is claimed.
