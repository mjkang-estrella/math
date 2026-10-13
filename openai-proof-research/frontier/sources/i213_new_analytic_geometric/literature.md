# I213 — primary literature and source-dependence ledger

The exact paths, SHA-256 hashes, pinned raw URLs and line-level scopes are recorded in `../../experiments/i213_new_analytic_geometric/input-authentication.json`. No external paper is promoted to a stipulated source. The only new source files here are a primary PDF and its fully read text extraction.

## Main primary comparison, read in full

T. Iwaniec, L. V. Kovalev, J. Onninen, *Diffeomorphic approximation of Sobolev homeomorphisms*, [arXiv:1009.0286v1](https://arxiv.org/abs/1009.0286v1), September 1, 2010; published in Archive for Rational Mechanics and Analysis 201 (2011), 1047–1067, [DOI](https://doi.org/10.1007/s00205-011-0404-4).

- Retrieval: `https://arxiv.org/pdf/1009.0286v1`.
- Local: `frontier/sources/i213_new_analytic_geometric/iko-1009.0286v1.pdf` and `.txt`.
- Reading: complete extracted text, lines 1–1044, including all five proof stages. Theorem 1.1(i) has zero-trace error, and (v) has compactly supported changes for a smooth-outside-compact input. The conclusion concerns planar domains. Proposition 2.6 supplies energy-decreasing p-harmonic replacements; Theorem 2.5 supplies their planar injectivity. These are the substantive ingredients that cannot simply be inferred in three dimensions.
- Novelty limit: the concept of an exact relative/boundary approximation theorem is established prior art. I213 does not claim that its elementary compression or cutoff warning is new to the literature.

## Problem-context source, existing copy read in place

S. Hencl, *Ball–Evans approximation problem: recent progress and open problems*, [arXiv:2502.01336v1](https://arxiv.org/abs/2502.01336v1).

- Versioned full text: `https://arxiv.org/html/2502.01336v1`.
- Existing local text: `frontier/sources/i07_analysis/literature/hencl2025.txt`; source HTML and original retrieval manifest are in the same existing directory.
- Reading: full extracted text with center reread after output truncation. Theorem 2.1 recalls planar trace preservation; Open problems 1, 4, 5 distinguish ordinary approximation, energy control and incompressibility. No priority or current open-status inference is made from the survey alone. Its browser-rendered date differs from the submission date; the version identifier is the provenance anchor.

## Bounded current bibliographic check, not an imported proof

D. Campbell, L. D'Onofrio, T. Vítek, *Diffeomorphic approximation of piecewise affine homeomorphisms*, [arXiv:2507.02854v2](https://arxiv.org/abs/2507.02854v2); [publisher article](https://doi.org/10.1007/s12220-026-02398-w), published March 31, 2026. The current arXiv page lists v2 dated October 7, 2025. Abstract/introduction metadata identifies a piecewise-affine input and forward/inverse Sobolev smoothing in dimensions three and four. That does not supply the missing approximation of a rough input with prescribed collar. No local copy or full-proof reading is claimed; the operative smoothing theorem here is the pinned source's own `sm:smoothing`.

Online discovery also located the different planar paper [Approximation up to the boundary of homeomorphisms of finite Dirichlet energy](https://arxiv.org/abs/1108.0199). It was not imported as a theorem or copied; the original IKO paper above suffices for the primary relative comparison. Search-result misses establish no worldwide novelty.

## Pinned interfaces, read in existing corpus

All below are under `frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/` and are authenticated against the complete pinned tree. Raw URLs use `https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/` followed by the displayed manuscript path.

- `Strong-diffeomorphic-approximation-in-three-dimensions-for-1-le-p-le-2-September-24-2026/`: introduction `main:theorem`; smoothing `sm:smoothing`, `sm:relative-pl`.
- `Strong-diffeomorphic-approximation-in-three-dimensions-for-p-gt-2-September-24-2026/`: introduction `main:theorem` / `ha:approximation`; smoothing relative PL, local extension, proper-degree interfaces; preparation `hp:opening`, `hp:carrier`; final main-theorem assembly. Lower relative statements have their stated input classes and output controls; no unstated collar-density theorem is assumed.
- `The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/`: `paper.tex`, `intro:main`; `preliminaries.tex`, `pre:standard`, `pre:supports`, `pre:reduction`; `elementary-estimates.tex` fully read. No rectangular anisotropic endpoint theorem is supplied by these readings.
- `Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/`: full introduction, `thm:main`, `cor:interior-c1`, proof outline and limitations. No explicit exponent, endpoint estimate, boundary derivative theorem, or actual p-harmonic approximation bound is inferred.

## Final assessment

The source dependence is explicit: ordinary ambient approximation and fine smoothing are stipulated; the new relative derivative estimate is not. Technical A1/A2/B1 use elementary Sobolev dilation, smooth collar geometry, and an explicit triangular map. B2 is a direct source consequence. They neither resolve B_p nor warrant a substantial nomination. The next unpaid estimate is `C_p` or sufficient `(CS_p)` in the analytic note.
