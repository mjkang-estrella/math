# T096N126 contribution review r1: TECHNICAL (conditional on correctness)

I reviewed the full integrated theorem: one absolute positive correlation threshold at which the three-sector propeller uniquely maximizes centered Gaussian noise stability, for every finite d ≥ 2 and k ≥ 3, with arbitrary masses and empty cells. I recommend **TECHNICAL**. No count, acceptance, gate or worldwide-priority claim is made. The separate proof review was not inspected.

The strongest compatible reduction is an integrated route, not a list of components. It has three parts. First, an exact quadratic expansion of S_ρ around a fixed planar reference propeller. Second, accepted R012/I38's weighted calibration J_t ≤ C₀Δ, whose contract I checked at (6.10), (7.1) and (7.2): it holds for every maximizing frame, on every full partition, and uniformly in d, k and masses. It supplies the leading-order coercivity and all of the label-count uniformity. Third, the tails use the exact bounded smoothed score. This design already appears in the primary literature through Eldan's T_β 1_H weight and Heilman 2108.04950v1's bounded-Φ penalty, which is explained there by the failure of linear centroid penalties.

The remaining compatibility steps are classical, and none needs a new uniform estimate:

* Higher-chaos energy is controlled by Hermite tensorization in fixed planar coordinates, the Mehler diagonal bound, and I38's slab-margin principle applied to a tilted Gaussian. This is uniform in d.
* The tail first-chaos coefficient vanishes by Gaussian integrability.
* The frame change after truncation is paid by Lipschitz stability of the polar factor.
* The proof chooses R before ρ.

Heilman's SSC Theorem 7.1 (unrestricted three-label derivative objective), together with Heilman–Tarter Theorem 1.9 (dimension reduction), essentially already gives the k = 3 case with an absolute threshold; this is my own sketch. SSC Section 8 attributes the open k ≥ 4 case to a missing order-zero stability estimate, which R012 has since supplied and which has been counted. It attributes the dimension dependence to an optimizer bootstrap that the contender expansion does not need. No primary source examined proves the full theorem, or the theorem for any fixed k ≥ 4, so REDISCOVERED is not supported within this bounded reading.

Read `packet/public/review.md` for the mathematics and `packet/public/reading-limits.md` for exact reading extents, provenance and rights. Private search notes keep their original third-party rights.

Detached FINAL (SHA256 of exact `packet/MANIFEST.json`):

    b69e072445b6923c4b541049293183d7bf5917ef4ffdf7de442e81eec70de3d5

This report's SHA256 is in `REPORT.sha256` and in the handoff. Run `python -B packet/public/verify.py --expected-final <FINAL> --expected-report <REPORT>`; it is read-only. `packet/public/controls.py` mutates only disposable copies under a scratch directory that it removes afterwards, and its result is in `controls-result.json`. Integrity checks are never mathematical gates.
