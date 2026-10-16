# R025 — Functional hard-sphere fluctuations on a regular Boltzmann lifespan

**Accepted as the third substantial result of the 2026-10-14 ten-additional
campaign.** This is internal research acceptance relative to the stipulated
pinned source interfaces, not external peer review or a worldwide-priority
certificate. The shrinking-window estimate and path-space conclusion count
as one result.

## Exact theorem and dependencies

Consider deterministic elastic hard spheres of diameter epsilon in
three-dimensional whole space, with activity mu = epsilon^(-2). The initial
grand-canonical law is proportional to

    mu^N/N! 1_{|x_i-x_j|>epsilon} product_i f_0(x_i,v_i) dZ_N,
    N = 0,1,2,... .

Let f_0 be a smooth probability density. For some beta>0 assume that both
f_0 and its spatial gradient have finite norm

    ||g||_{Bol,2beta} = sum_{a in Z^3} sup_{|x-a|<=1,v} exp(2beta|v|^2)|g(x,v)|.

Assume a nonnegative classical Boltzmann solution on the entire prescribed
finite interval [0,T], T>0, with a uniform exp(2beta|v|^2) bound. Relative
to the finite-history interfaces of the pinned source, for every finite
list of real compactly supported smooth tests on R^6, the vector of fields

    X_t^epsilon(phi) = mu^(-1/2)(sum_i phi(z_i(t)) - E sum_i phi(z_i(t)))

converges in D([0,T],R^d), with the Skorokhod J1 topology, to the continuous
Gaussian field of the credited finite-dimensional theorem. The sequence
is C-tight. The covariance, backward propagator, weak linearized drift and
collision-noise form are specified in equations (1.6)–(1.8) of the paper;
the initial covariance is integral f_0 phi psi, without a fixed-number
subtraction.

The result concerns the actual unsmoothed gas with exact microscopic
centering throughout the supplied interval. It adds no equilibrium,
periodicity, smallness, resampling, shortened-lifespan or global-existence
assumption. It does not assert weak convergence in the uniform-topology
Borel space on all of D. The operational source assumptions are stated in
Section 2; their truth is stipulated at
`openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

## Proof and contribution

The complete [19-page manuscript](../campaigns/2026-10-14/kinetic-manuscript-consolidation/output/pdf/main.pdf)
has PDF SHA256 `08a092590559fa81c1d2c759e06efb9a03b1e7b6ede1d708ace731cc0f2028dc`
and TeX SHA256 `f2548882cf47aa4259c68b43ea38d755c395b47008300783856788ab5ef6fd38`.

One collective time translation of a connected history supplies a
shrinking-window factor at the sharp factorial-cumulant scale, including
redundant contacts whose times are determined rather than independent
coordinates. The repaired construction retains a prefix-measurable global
chronology indicator through the translation and flux-tree bound. Initial
links retain their connected activity scale. A fixed Gaussian reserve
keeps summability independent of later moment order. A decorated final-slab
kernel controls the number of jumping particles. Together with credited
moment, continuity, chaining and centering arguments, these estimates give
the full unsmoothed path-space conclusion.

Short-time nonequilibrium and long-time equilibrium process theorems of
Bodineau–Gallagher–Saint-Raymond–Simonella, the regular-lifespan framework
of Deng–Hani–Ma, the pinned finite-dimensional theorem, and the earlier
project's continuity and centering arguments are antecedents. They are
identified in the paper and source map. The separate contribution review
judges the new bridge SUBSTANTIAL within its recorded literature search;
this is not an exhaustive priority determination.

## Independent gates and validation

- [Proof round 2](../campaigns/2026-10-14/kinetic-proof-r2/review.md): PASS
  after the extended-history chronology repair; full original scope.
- [Contribution review](../campaigns/2026-10-14/kinetic-contribution-r1/review.md):
  SUBSTANTIAL for the new path-space bridge, conditional on proof validity.
- [Original manuscript review](../campaigns/2026-10-14/kinetic-manuscript-review-r1/review.md):
  PASS with seven nonblocking corrections, all addressed in the consolidated edition.
- [Final manuscript review](../campaigns/2026-10-14/kinetic-manuscript-review-r2/review.md):
  PASS for that edition, SHA256
  `feddd8af34f64fc0f856f3b2ca97a1f5a0ed9c3cdf55c36cffd737a539cbb396`.
  Six remaining editorial clarifications are retained in the included parent
  companion without altering reviewed manuscript bytes.

The parent authenticated the corrected paper's 107 input and 57 output
records, checked the exact editorial diff, reproduced its 213 structural
checks and inspected all 19 rendered pages. Final review authenticated
71 inputs and two outputs. The final archive passed clean-extraction
verification: all 208 project files, exact membership, hashes and gate
bindings, plus byte-identical receipts from five finite-check programs.
These checks support the analytic proof; they do not replace it.

## Publication materials and formal coverage

Author: **Myeongjin Kang**, no affiliation. Original paper/prose: CC BY 4.0;
original code/Lean: MIT. Third-party rights remain intact. The local archive
includes the reviewed paper, provenance, reviews, reproducible supporting
checks, scoped Lean material, and the two credited unpublished project
antecedent notes. Third-party reading copies and dependency binaries are
excluded.

**The full analytic theorem is not formalized in Lean.** Nine supporting
declarations cover collision energy, affine shifts and exponent arithmetic.
The independent semantic audit checks their actual types, compiles fresh
sources and fourteen audit declarations, and rejects four mutations. The
pinned environment is Lean 4.34.1 with mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`; only standard Lean axioms occur.
History existence, chronology, Jacobians, analytic estimates and tightness
remain prose proofs.

The [release machinery](../campaigns/2026-10-14/kinetic-release-v2/README.md)
and [final verification receipt](../campaigns/2026-10-14/kinetic-parent/final-package-verification.json)
identify `output/release/r025-functional-hard-sphere-fluctuations-v1.zip`
(4,944,245 bytes), SHA256
`7ea2d13611222315032221fbf2ddf5462953a86d83d1ce4898643ffb893679c3`.
Its bundle manifest SHA256 is
`1c87ef4c0f4b411eb83effc2c988269ee47377b3c76515fbd57151763191b34e`.
Preparation-time pending/count text in frozen files is historical; this
acceptance record supersedes that status without changing reviewed bytes.
Nothing has been publicly uploaded or submitted to Zenodo or MathDB.
