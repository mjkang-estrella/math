# I209 literature and novelty boundary

2026-10-12. Corpus pin: `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Individual source hashes, reading scopes and provenance are recorded in [input-authentication.json](../../experiments/i209_elliptic_tetrahedron/input-authentication.json). Existing sources were read in place; four newly fetched pinned source sections are retained here and were read in full. This is not a snapshot or historical replay.

## Primary external comparison

**Károly Bezdek and Alexander E. Litvak, Covering convex bodies by cylinders and lattice points by flats**, J. Geom. Anal. 19 (2009), 233–243. [arXiv:0903.4842v1](https://arxiv.org/abs/0903.4842v1); [published DOI](https://doi.org/10.1007/s12220-008-9063-6). The complete 14-page v1 was read through the existing I201 PDF; no duplicate source copy was made. The mathematical use is Theorem 3.1 and its proof in §3. It gives the general directionwise lower bound 1/3 in three dimensions, which also implies the absolute minimum-shadow bound. Its ellipsoid proof uses a nonnegative density and Fubini along cylinder lines. Thus a mass divided by maximal line integral is an old method. I209 nominates a new explicit tetrahedral line estimate and optimized quadratic density, not the method.

The introduction identifies Bang's regular tetrahedron as the equality example motivating the half-area question. This supplies primary-literature importance evidence for tightening this body's extremal interval. The paper's general 1/3 bound does not assert that 1/3 is attained for the tetrahedron. Nor does its general theorem preclude a stronger tetrahedron-specific lower bound.

The full paper, including its later lattice-point applications, was read to avoid claiming an unread-source comparison. Those later sections are not used in I209. A direct request for Bang's 1951 AMS PDF returned HTTP 403; no copy was retained and no claim to have read Bang's original paper is made. Historical attribution here is to Bezdek–Litvak's explicit primary discussion.

## All four accepted companions

1. **Finite cylinder approximation of ruled sets.** Existing I198 `introduction.tex`, `linear-coverings.tex`, `finite-approximation.tex`, `comparison.tex` and `references.bib` were read in full. Relevant labels are `b:projection`, `b:approximation`, `b:lattice`, `b:affine-cover`, and `b:finite-retention`. The projection formula, compact-label retention argument and deformed-square lemma are paid. The actual square lemma only requires 0<=alpha beta<1; it does not bound individual shear coefficients. These facts justify the scoped check of I203's displayed identity, without treating its entire nomination as accepted.
2. **Finite angular cylinder covers below the half-area bound.** Existing I198 introduction and I201 `angular-cubic-buffer.tex` were read in full. `prop:angular-cubic` gives normalized cost 1/2-tau^2/240+(25/2)tau^3 with absolute error <=2tau^4, for an actual finite triangular cover. The strict half-bound, its finite count and affine directionwise transfer are paid. This is the upper endpoint used for comparison, not a new result.
3. **Slope-field perturbations of the two-cylinder covering.** Existing I198 introduction was read in full. Newly retained [slope-rational.tex](slope-rational.tex), [slope-singular.tex](slope-singular.tex), and [slope-projection.tex](slope-projection.tex) were fetched from the pinned raw repository and read in full. Relevant labels include `c:rat-rational-proposition`, `c:sing-theorem`, `c:sing-cutoff-flexibility`, `c:normal-frame`, and `c:nil-projection`. They already supply rational wall fields, the hyperbolic power range p>1, nilpotent endpoint p=1, cap-overlap squares, tip accounting and simplex chord/projection normalization. I209's p=1/2 mixed field continues that geometry into an unpaid elliptic regime, but fails its cost test and is not nominated. The source's ordinary unweighted longest-chord identity is different from I209's quadratic weighted chord optimization.
4. **Finite triangular approximation of radial sweeps.** Existing I198 introduction and newly retained [radial-projections.tex](radial-projections.tex) were read in full. `thm:radial` already gives prescribed-tag, one-triangle-per-interval finite covers including the apex. `prop:simplex` and `eq:regular-normalization` fix projection areas and ordinary longest chords. These are not new I209 content. No arbitrary affine-image conclusion is inferred for I209's absolute-area lower bound.

Original locations of the four retained copies are the same named files under the following pinned paths:

* `preprints/Slope-field-perturbations-of-the-two-cylinder-covering-September-27-2026/build/sections/{rational,singular,projection}.tex`;
* `preprints/Finite-triangular-approximation-of-radial-sweeps-September-27-2026/build/projections.tex`.

All were fetched under `https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/`.

## What the search does and does not support

Early queries covered regular tetrahedron cylinder covers, actual primary lower bounds, the Bang equality example and Bezdek–Litvak's results. Follow-up queries tested tetrahedron cylinder covering with quadratic densities, exact constants and lower-bound terminology. Results repeatedly led to the same primary general theorem and to the four corpus companions. Searches also returned unrelated circular enclosing-cylinder, sphere packing, lattice-covering-density and shadow-containment problems; none establishes the all-cylinder inequality considered here. Corpus mirrors were not treated as independent sources.

No searched primary source was found stating the new lower constant sqrt(15)/9 or the sharp quadratic-certificate optimization. That is a limited search outcome, not a proof of worldwide novelty or a comprehensive current best-bound survey. The supportable claim is a proved new-to-project geometric deduction with a primary-source comparison. The independent contribution gate must decide whether this suffices as a substantial new finding.

The new estimate is absolute and regular-tetrahedral. Bezdek–Litvak's affine-invariant directionwise functional is distinct. The quadratic certificate, the resulting lower bound, and any interval description combining it with a paid upper bound are parts of one contribution and must not be counted separately.
