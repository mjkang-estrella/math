# Original scope (frozen before sustained proof work)

Author: Myeongjin Kang (no affiliation). Prose licence: CC BY 4.0.
Campaign: fresh analytic discovery r11, 2026-10-14 lane.
Pinned upstream: openai/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.

## Source family

Catalogue family 153, "Arithmetic classification and non-Pisot singularity for
Bernoulli convolutions" (OpenAI, October 3 2026), path
`preprints/Arithmetic-classification-and-non-Pisot-singularity-for-Bernoulli-convolutions-October-3-2026/`.
No earlier iteration or campaign of this project used this family.

Pinned results accepted as true (AGENTS.md): `sal:main` (singularity of
nu_{1/beta} for every quartic Salem beta in (1,2)), `sal:construction`,
`sal:loss`, `cls:classification`, `np:main`.

## Frozen target T

Let beta_6 = 1.4012683679... be the real root greater than one of

    P6(x) = x^6 - x^4 - x^3 - x^2 + 1.

beta_6 is a Salem number of degree six (two unit-circle conjugate pairs).

**Target T.** Prove that the unbiased Bernoulli convolution nu_{1/beta_6}
(law of sum_{n>=0} eps_n beta_6^{-n}, independent fair signs) is singular with
respect to Lebesgue measure; or disprove it by proving absolute continuity.

Optional extension (not required for success, not to be claimed unless proved):
the same conclusion for every Salem number of degree six in (1,2).

## Why T is not paid

* `sal:main` covers degree four only; its multiplier construction uses
  one-dimensional Dirichlet approximation for a single unit-circle angle.
* Cheng-Fang-Ma-Zhang, arXiv:2610.12072v2 (dimension drop) and
  arXiv:2610.09902v1 (correlation-dimension drop) treat quartic Salem numbers
  only.
* Literature screen to date found no singularity, dimension-drop, or
  absolute-continuity result for any Salem number of degree at least six.
  (The 2017 claim arXiv:1708.05544 was withdrawn by its authors.)

## Unpaid nonroutine operation

Simultaneous suppression of two unit-circle conjugate pairs in algebraic
multipliers while keeping the accumulated Fourier "action" (cosine losses)
below the logarithmic smallness of the circle conjugates. In degree four the
growth exponent 3 of the smallness beats the doubling 2 of the action; in
degree six the corresponding exponents tie or lose, so the pinned argument does
not transfer.

## Allowed outcomes

* PROOF: complete self-contained proof of T, using only pinned theorems and
  explicitly labelled, independently reproved primary-literature lemmas.
* DISPROOF: proof that nu_{1/beta_6} is absolutely continuous.
* UNRESOLVED: neither; report the exact obstacle, every proved partial
  statement with its hypotheses, and numerical evidence labelled as evidence.

Numerical evidence is never a proof. No counting, no self-awarded PASS.
