# SOUP recovery round 2: unresolved full target

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

**UNRESOLVED_FULL_SOUP; counted=false.** This is a research checkpoint, not a candidate complete proof, independent PASS, novelty verdict, or new accepted result. The frozen full target in original-scope.md is unchanged.

The requested conclusion is full-sequence convergence in C(R) for every fixed beta>1 of the centered SK free energy on amplitude n^(-1/6) and OU clock n^(-2/3), with the stipulated marginal law and a temporally nonconstant limit. Both full-sequence uniqueness and nonconstancy remain unpaid.

## Work recovered independently

1. `checkpoint-tightness.md` proves uniform increment tails using reversible forward/backward martingales. Tightness and the stationary/reversible, correctly normalized marginal of every subsequential limit follow. The parent independently found a simpler Gaussian rotation proof. Neither argument identifies a unique limit.
2. `checkpoint-cross-root.md` derives the finite multiroot covariance derivative. Its two-root specialization agrees with the parent's `soup-parent/two-root-identity.md`, which was read and checked: the coefficient is -beta² qr rho/2 and the correction is -1/n. A covariance defect O(n^(-2/3)) produces an order-one scaled transform derivative, so discarding it as a small perturbation is unjustified.
3. The same note proves an n=2 obstruction to copying the single-pin gauge argument: pinning a tuple of terminal spins at correlated roots changes the joint free-energy law. A common gauge preserves relative spins. This is a failure of a proposed proof step, not a counterexample to SOUP or to all possible joint augmentation arguments.
4. `checkpoint-spectral.md` derives the exact four-replica expression for the second chaos moment. Available deterministic bounds permit that moment to grow like n^(1/3). A putative O(n^(-1/3)) four-replica bracket bound would suffice for this route but is neither proved nor assumed; it may be too strong in the low-temperature regime. Other possible routes would need fractional higher-moment uniform integrability or a direct positive lower bound on an integrated critical-window overlap. Neither has been obtained.

## What a full proof still needs

The scalar size increment theorem compares one positive transform and preserves independent roots. A joint transform under nearly identical correlated disorder has additional cross-overlap insertions. To use the source finite pressure expansion, one must construct a valid coupled positive law, identify its deterministic cross-overlap centers, retain normalized future marginals when integrating a moving fork, and obtain summable finite-size errors uniformly as the root covariance has eigenvalues tending to zero. The actual scalar interfaces do not assert this extension. Marginal Holder estimates control densities but do not replace this calibration.

Even convergence of the covariance would not identify all finite-dimensional distributions. Conversely, tightness and all scalar moments do not exclude a random constant path. The current spectral bounds allow all limiting spectral mass at zero. No argument forcing positive mass away from zero was found.

The older I17 two-temperature same-disorder screen was undeveloped, rather than an accepted/developed result being renamed. Nevertheless it already identified a coupled-transform calibration gap. SOUP has one temperature and vanishing covariance defects, a different precise target, but shares that missing operation. This recovery does not claim a new independent mechanism merely from that difference. P3R family262 remains excluded and is not revived.

## Limits and disposition

Source truth at the pinned revision is stipulated. Reading extents and byte identities are in source-reading.json; the main and exponent companion theorem statements, full main companion interface and chaos consequence, and selected actual comparison/expansion bodies were read. No complete audit of upstream proofs, worldwide literature novelty finding, or full-source read is claimed. The finite identities and tightness deduction above are proved independently.

The appropriate disposition is to retain the complete original SOUP target as unresolved after this recovery attempt. Do not count these standard supporting facts, start manuscript/formalization acceptance gates for them, or reclassify the target as solved by a conditional or subsequential substitute.
