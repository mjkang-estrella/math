# MathDB333569 — literal endpoint candidate

MathDB ID 333569, UUID 7bcf4f81-fad1-4654-9523-9d461c47a301. The exact question is Petersen arXiv:1607.02425, Conjecture 4.6.8 (source text lines 2802–2803), and Petersen–Wilson arXiv:1512.01143v6, Conjecture 6.3. Both assert existence of a fully supported local intricacy maximum among all stationary one-step Markov measures on the full two-shift. No global, unique, all-invariant or higher-order conclusion is claimed.

## Source semantics

`ShiftSpace` is the actual two-sided product `ℤ → Fin 2`. `OneStepMarkovLaw` is exactly the cylinder-law presentation in source Section 6, equation (6.1): an arbitrary row-stochastic binary transition matrix, a nonnegative normalized stationary initial vector, and every translated block cylinder equal to the initial mass times the transition product. The transition matrix is parametrized by its two diagonal entries in the CLOSED unit square. Initial masses may vanish; matrices may be degenerate; no irreducibility or ergodicity hypothesis is imposed. These boundary/nonergodic laws belong to the relative comparison class.

`actualIntricacy μ` is `limUnder atTop` of `rankZeroFiniteIntricacy μ 0`. This is the literal uniform-subset rank-zero join entropy expression: twice the uniformly averaged selected entropy minus full block entropy, divided by block size. Logarithms are natural. The final theorem explicitly supplies convergence at its witness AND throughout a weak neighborhood within the full comparison class. `rankZeroFiniteIntricacy_tendsto_series` and `sourceIntricacy_eq_series` establish convergence and series identification for every interior chart parameter, hence a full parameter neighborhood of the chosen symmetric witness. The local inverse-chart proof is `source_parameter_claim`.

The topology on `ProbabilityMeasure ShiftSpace` is mathlib's weak topology (convergence in distribution), not an imposed parameter topology. `lawMass_continuous` proves continuity of cylinder masses by the clopen portmanteau theorem. `recoveredTransitions_continuousAt` proves continuity of conditional cylinder ratios. `markovLaw_eq_bundled` proves coverage of every comparison law with positive state masses and an interior recovered matrix. These conditions form a weak open neighborhood of the witness. Thus boundaries are excluded locally by proved open conditions, not removed from the comparison class by definition.

## New proof bridge index

- Selected333569: `twoSidedLaw_past_next`, `twoSidedLaw_past_gap`, `twoSidedLaw_selected` contract every unselected symbol using `kernel_comp`, giving the exact arbitrary increasing integer-time product.
- SelectedEntropy333569: positive inhomogeneous chain rule, stationary endpoint expectations, `observedEntropy_selected`, `sampleEntropy_selected`, and empty observations. The source finite marginal sum is eliminated.
- FairSelections333569: exact free-selection equivalence/cardinality, consecutive-pair count, sorted adjacency bijection, `sampleEntropy_pairs`, and exact entropy sum in endpoint-pair form.
- FairEntropy333569: group endpoint pairs by their gap; `fairEntropy_gap_sum` is exact at every finite size.
- EntropyLimit333569: `fairEntropy_average` is precisely the requested finite fair-subset formula with N=n+1; `triangularEntropy_tendsto` proves its dominated limit; `finiteIntricacy_series_boundary` tracks the vanishing boundary; `rankZeroFiniteIntricacy_tendsto_series` identifies the actual law's limit.
- TransverseEntropy333569: actual first/second transverse derivatives; `conditionalEntropy_second_derivative_zero` identifies twice the inherited explicit coefficient; joint continuity of the elementary derivatives; uniform derivative bounds on compact rectangles including gap limit r=0.
- SeriesDerivatives333569: two successive termwise differentiations with proved geometric bounds; joint continuity of the second-derivative series; `entropySeries_second_derivative_zero_neg` connects the actual derivative to inherited strict coefficient-series negativity.
- ParameterMaximum333569: concavity in the transverse interval plus label symmetry, and inherited compact diagonal maximization give `entropySeries_has_local_max` in two dimensions.
- SourceParameter333569: local inverse chart transfers the actual series maximum to the inherited SourceClaim; SourceClaim alone is NOT the final result.
- WeakMarkov333569: all-law weak-topology recovery and final `fullySupported_stationary_oneStep_localMaximum`.

The eleven inherited local mathematical modules are byte-preserved copies. All predecessor frozen bytes remain unchanged. The source statements, Proposition 5.10/proof (5.28)–(5.31), finite definitions, Section 6/(6.1), and inherited ordinary/source review were read. Source text copies and normalized record are included in inputs; hashes/pins are recorded.

## Review and access limits

This is a full formal endpoint CANDIDATE, not independent formal/source-fidelity review or root acceptance. The qualified ordinary/significance PASS is inherited. Publisher full-body, dissertation, earlier-version, predecessor/citing-body and registry limits remain exactly those in inputs/REVIEW.md. No blocked fetch was retried, no new registry/full-literature clearance was obtained, and no novelty or worldwide-priority claim follows from formalization. No acceptance or campaign count changed.

Lean 4.34.1; mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. Fresh local sources are compiled with warningAsError; every named local declaration is transitively audited. The external pinned prebuilt dependency cache is explicitly TRUSTED and is not rebuilt.
