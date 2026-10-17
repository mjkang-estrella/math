# R023 — Uniform interior gradient estimates for all finite p >= 3

**Accepted as the first substantial result of the 2026-10-14 ten-additional
campaign.** This is an internal research acceptance, relative to the user's
stipulated pinned OpenAI theorems and the credited classical inputs. It is
not external peer review, a worldwide-priority certificate, or a public
submission. It is additional to the sixteen previously accepted results.

The repaired full proof passed independent Opus review; its contribution
passed a separate Grok review as SUBSTANTIAL; and the complete standalone
manuscript passed a fresh independent Codex mathematical/presentation gate
with no required repair. Parent integration and package verification are
committed at `c5728459`. The parent read the complete reviews and their
limits, checked the exact reviewed bytes, and reran the final verification.

## Exact theorem

For each integer n>=2 there exist alpha_n in (0,1/3] and C_n<infinity
such that, for **every finite p>=3** and **every bounded weak solution**
u in W^(1,p)_loc(B_1 subset R^n) of

    integral |Du|^(p-2) Du . Dphi = 0     (phi in C_c^infinity(B_1)),

the continuous representative belongs to C^(1,alpha_n)(B_(1/2)) and

    ||Du||_(L^infinity(B_(1/2))) + [Du]_(C^(0,alpha_n)(B_(1/2)))
        <= C_n osc_(B_1) u.

Neither constant depends on p or u. There is no assumption about the
original critical set, sign, level-set geometry or boundary data. The
exponent is nonexplicit. The statement does not include 2<p<3, an endpoint
sharp exponent, or the full inhomogeneous p-Laplace conjecture.

## Full proof and the new contribution

The complete proof is the [21-page manuscript](../campaigns/2026-10-14/p-gradient-manuscript/output/pdf/main.pdf),
PDF SHA256 `bc66e9d14e6d83e8e0a9c579e4856c0a302958af952a1506a5849f5b46875155`.
Its source/build receipt has SHA256
`d689320069f165faeb21cb2f8be63cbf5a70f269b6bf328963dea47b103649a6`.
Historical candidate/pending banners are preserved to keep reviewed bytes
unchanged; this finding and the [parent disposition](../campaigns/2026-10-14/p-gradient-parent/manuscript-gate-disposition.md)
record the later acceptance. A publication version with author metadata
will require a separately bound build.

The proof first obtains common Lipschitz control and qualitative flatness.
An explicit compact-p Uhlenbeck audit handles bounded p intervals, leaving
p tending to infinity at selected bad scales. The affine lift U(y,b)=u(y)+b
satisfies a different constrained degenerate elliptic equation; the paper
proves the viscosity identity even where Du=0, without asserting that U
is p-harmonic. Its rescaled equations have an effective viscosity.

For finite effective viscosity, an exact transport projection puts every
limit in a fitted isotropic equation, preserving the same fit constant.
Zero viscosity uses the pinned Liouville theorem. Positive viscosity uses
the complete appendix: cone infima, exponential flux, viscosity-to-weak
passage, contact propagation, and fitted-class rigidity. Limit closure
includes both the PDE and every center/radius fit.

For unbounded effective viscosity, the paper constructs one family with
common ellipticity and C2 jet bounds, including degenerate parameter
endpoints. Savin's theorem then gives a proportional Hessian estimate
on an anisotropic coarse cylinder. A quadratic comparison between unequal
fitting parameters retains the coarse slope's size; this is stronger than
the available vector-angle estimate and is needed before invoking that
cylinder estimate. Both branches contradict the selected bad scale.
The pinned geometric derivative extraction yields the common positive
Holder exponent and the stated oscillation bound.

These constrained PDE identifications, projected fit preservation,
uniform rescaled family and unequal-parameter comparison constitute one
substantial bridge. The source infinity theorem, fixed-p regularity,
positive-viscosity technical precursor, Savin theorem and geometric
extraction are credited antecedents, not separate new findings.

## Dependencies and independent gates

- Pinned input: [OpenAI infinity-harmonic manuscript](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026),
  interior regularity, linear lift, zero-viscosity fitted Liouville theorem,
  and equation-free fit/envelope geometry. Its truth is stipulated.
- Classical inputs include Kotschwar–Ni, Uhlenbeck, Julin–Juutinen, Savin,
  linear Harnack, and standard compactness/weak-solution facts. The
  [final source map](../campaigns/2026-10-14/p-gradient-manuscript-review-r1/source-map.md)
  states actual primary interfaces and reading boundaries; not every
  classical proof has been independently re-proved.
- [Opus round 2](../campaigns/2026-10-14/p-gradient-proof-r2/review.md):
  PASS for the full repaired four-text proof, resolving R1–R7.
- [Independent contribution review](../campaigns/2026-10-14/p-gradient-contribution-r1/review.md):
  SUBSTANTIAL after comparison with actual primary statements. Its search
  is bounded; worldwide priority is not certified.
- [Independent standalone-manuscript review](../campaigns/2026-10-14/p-gradient-manuscript-review-r1/review.md):
  PASS for the entire frozen manuscript and P1/P3–P8. Parent independently
  verified the P2 archival commit. Review output manifest SHA256:
  `886eb20219722239b7810f20904219ab14bb940fc6117321afe684a1fea596e6`.

## Supporting artifacts and submission limits

The [Lean project](../campaigns/2026-10-14/formal/README.md), pinned to Lean
4.34.1 and mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, certifies
three scalar and seven vector ellipticity lemmas. The vector theorem
proves both bounds for the actual zero-jet form with sqrt(e), in any real
inner product space under its explicit unit/parameter constraints.
All ten proofs compile from source with only propext, Classical.choice
and Quot.sound. **The PDE, compactness, jet-neighborhood, Savin and full
analytic theorem are not formalized.** The ten lemmas are not ten results.

The [release workflow](../campaigns/2026-10-14/p-gradient-release/README.md)
provides PDF/TeX, reviews, source pins, Lean sources and reproducibility
instructions. A clean extraction passed hash verification and both finite
algebra checkers; a deliberately changed manuscript was rejected. These
checks supplement the written proof, not replace it.

Value-to-gradient convergence and the large-p sharp inhomogeneous transfer
are corollaries of this theorem, with the latter restricted to fixed
p>max(3,1+1/alpha_n) and p-dependent constants. Neither counts separately.
The full [MathDB 405360 problem](https://mathdb.com/p/405360/the-c-p-regularity-conjecture)
is not solved by this finding. No exact matching homogeneous record was
identified in the bounded search. The publication copy lists Myeongjin Kang with no affiliation, CC BY 4.0
for the paper/original prose and MIT for original code/Lean. Third-party
notices are preserved. Final destination/account details remain outstanding. Nothing has
been submitted to Zenodo or MathDB.

## Public publication

Published 2026-10-17 UTC: [Zenodo manuscript and supporting package](https://zenodo.org/records/23429943), DOI `10.5281/zenodo.23429943`; [MathDB paper](https://mathdb.com/abs/2610.00023). Files and metadata were verified; see the [submission receipt](../campaigns/2026-10-14/submissions/README.md). Earlier pending-submission statements above record the acceptance-time state. Publication does not imply external peer review.
