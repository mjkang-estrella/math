# Stipulated source interfaces and exact normalization

All source paths below are relative to `preprints/` at immutable OpenAI math commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The 35 selected non-PDF blobs are authenticated against the complete canonical preprints tree in source-receipts.json. Acquisition is not a claim of reading every acquired file or every family companion. No upstream theorem is audited here.

Use the following folder abbreviations:

- S: `The-Critical-Spin-Field-of-the-Planar-XY-Model-October-5-2026/`.
- L: `The-critical-logarithmic-correction-for-the-planar-XY-model-October-5-2026/`.
- C: `Critical-Center-Magnetization-in-the-Planar-XY-Model-October-5-2026/`.

| Interface | Exact source locator | Use in the author proof |
|---|---|---|
| Critical model and normalized pinned field | S `build/sections/01-introduction.tex`, `eq:free-spin-law`, `eq:critical-parameter`, `eq:pinned-spin-law`, `eq:center-magnetization`, `eq:spin-field`, `eq:target-field`, `thm:main` | Specifies b_c, a_n, K*=2/pi and the compact-interior field law. |
| Positive finite center amplitude | C `build/sections/introduction.tex`, `thm:main`, `eq:main` | a_n~A_XY n^(-1/8)(log n)^(1/16), with A_XY>0. |
| Free correlation threshold and geometric comparison | L `build/sections/introduction.tex`, `eq:critical-definition`, `thm:main`; `geometry.tex`, `geo:comparison` | Same critical point and normalization; the existing two-point comparison is an antecedent, not the new theorem. |
| Finite affine/matching comparisons | L `build/sections/heights.tex`, `lem:duality`, `prop:comparisons` | Releasing matching constraints and adding compatible pins/observations order ratios; each exterior ratio is at most one. |
| Fixed mixed height limit and pin localization | L `heights.tex`, `prop:height-inputs`; S `02-heights.tex`, `heights:mixed-input`, `heights:pin-input`; S `03-sectors.tex`, `sectors:localization` | Single-lift confined Gaussian energy, then vanishing centered pin interaction in fixed positive-separation geometry. |
| Pinned-rim slit restoration | L `geometry.tex`, `geo:pinned-sector`, lines418–675, especially `geo:confinement-below-bare`, `geo:cell-pin-localization`, `geo:global-data-comparison`, `geo:conditional-pin-identity` | Repeated finitely for disjoint pairing arcs. Retain all other strips, use only the exterior ratio≤1 and the same pre-pin cell localization. No estimate uniform in the number of insertions is asserted. |
| Thermodynamic spin/height bracket | L `geometry.tex`, `geo:thermodynamic-bracket` | Applied to a fixed finite neutral current, whose connection vanishes near the outer rim. Outer thermodynamic limit is taken first. |
| Identical k-nest attachment | S `06-correlations.tex`, `correlations:exterior-lattice`, `correlations:attachment`, proof of `correlations:separated`; L `geometry.tex`, `geo:attachment-factorization` | The already available product density bound2^k and joining identity cancel the same microscopic factor against a_n^k. Constants may depend on fixed k and configuration. |
| Exterior energy and Green normalization | S `06-correlations.tex`, `correlations:exterior-energy`, `correlations:green-diagonal`, `correlations:normalized`; L `geometry.tex`, `geo:single-energy` and subsequent energy formulas | Neutrality cancels the outer log radius. The surviving center regular part gives kappa^k. |
| Integrable collision bound | S `06-correlations.tex`, `correlations:nest-bounds`, `correlations:diagonal` | Uniform O((distance+1/n)^(-1)) bound on fixed interior compacts, including repetitions. |
| Moment/UI and collision removal | S `07-fields.tex`, `fields:lee-yang`, `fields:circle-chaos`, `fields:moment-bounds`, `fields:moments`, `fields:law` | Nonnegative signed moments and sqrt(q) absolute moments give fixed-tilt Laplace convergence. The collar argument is supplied explicitly in the lattice note. |

There are two normal-ordering conventions. The source full-variance field is `exp(R_D(z,z)/(2K)) mu_D(z)`, where mu_D uses only epsilon^(-1/8) before exp(i Gamma/2). Removing the source lattice Green correction contributes `exp(-(R_D(z,z)-R_D(0,0))/(2K))`, leaving the spatial constant kappa. The continuum parent lemma is entirely in this ultraviolet-only convention. It does not invoke a full-variance covariance comparison after silently changing conventions.

The new lattice extension fixes the charge number, all arcs/holes/patches/guards/rim and every positive clearance before the mesh limit, and sends cell scale to zero after that limit. The annular parameters can then be chosen for arbitrarily small error at that fixed charge configuration. Source fixed-geometry theorems are never claimed uniform under a shrinking physical radius or growing number of charges.
