# Source contracts and endpoint use

All source files are pinned to openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Exact original paths, Git blob identities, local paths, raw URLs and SHA256 are in source337-receipts.json and smooth337-receipts.json. Their identities are checked against the copied complete canonical preprints-tree.json, not the truncated root-tree cache. Identity checking is not auditing the stipulated source truths.

The operative source prefix is `preprints/Sharp-integral-fillings-in-CAT(0)-spaces-September-23-2026/`, local `private/source337/`.

* 01-introduction: `thm:main`, sharp filling bound for compact integral cycles, arbitrary multiplicities/proper CAT(0).
* 02-currents: `thm:current-background`, compact minimizer; `eq:extremizer` and `eq:normalization`; `prop:chart-mass`, exact signed chart mass; `lem:euclidean-density`, lower density; `eq:gradient-lipschitz`, scalar gradients. In the new proof (1) derives the same variational inequality from sharp equality, so the source's construction of a positive maximizer is not imported at its forbidden endpoint.
* 03-radial: `prop:radial` and full proof use only that inequality and normalization. `eq:base-cutoff-estimate` supplies the endpoint completed square when m=4π; no λ>0 or smooth limit is assumed.
* 04-sobolev: `prop:small-set`, `prop:almost-sobolev`. Their proofs use the variational inequality, positive finite mass and lower-dimensional sharp filling. Strict m<s_n is not needed.
* 05-minimizer: `prop:sobolev-space`, `prop:compact-embedding`, `prop:minimizer`, `lem:powers`, `lem:composites`. Strict m<s_n is used to get Λ<S_* from the constant test. The new proof instead assumes Λ<S_* for contradiction, uses the same compactness/concentration proof, then concludes Λ=S_* with constant1 an attained minimizer. No compactness at the critical threshold is asserted.
* 06-chords: `prop:chord-transform`, `lem:chord-density`, `eq:chord-upper`. The probability measure is ν=v^p μ/W, not v^p μ. The transform comparison and tangent-density estimate also hold at W=s_n for constant1; only the final strict inequality uses W<s_n. Source `rem:chord-sphere` explicitly describes W=s_n saturation. The output is I(y)/m≤2 when v=1.
* 07-conclusion: full `lem:opposite-average`, classical barycentric variance; the probability normalization is retained. At v=1 this supplies the required integrated lower bound. The final sharp theorem is stipulated.
* 08-classical: top-dimensional constancy and Euclidean sharpness, not a classification of equality currents in singular CAT(0) spaces.

Smooth companion prefix `preprints/Generalized-Cartan-Hadamard-isoperimetry-and-Euclidean-equality-rigidity-September-23-2026/`, local `private/smooth337/`: 01-introduction `thm:equality` is bounded positive-volume codimension-one smooth equality; 08-rigidity `eq:offset-sphere` uses the signed outward normal and `eq:phase-recovery` uses the ambient exponential diffeomorphism. These paid operations are close comparators. They are not silently promoted to arbitrary singular currents.
