# Literal mixing assembly: all-N limit closed; weighted bridge residual

Solo implementation, 2026-10-30. No novelty, acceptance or full SourceClaim assertion. Counts remain 9 additional / 39 total / next 40; root alone accepts. No children, manuscript, shared, git commands, public, browser, external retrieval or MathDB changes.

All 18 inherited r11 mathematical modules are byte-identical. Five new mathematical modules: Observables, FiniteProbability, Measurability, Median, AllN.

## Exact compiled interfaces (namespace LiteralGame)

- `X w i`: one-based split indicator, zero at index zero and after termination. `X_eq_one`, `X_padded` and `sum_X` identify its literal meaning and cumulative sum.
- `prefix_observable`: for every `w ∈ completeDomain N` and every natural m, `w.length < m ↔ N-Z N < m-(∑ j ∈ Finset.range m, X w (j+1))`. Both T=m and m>T are covered.
- `duration N`: maximum of actual complete-word lengths. `length_le_duration` and `suffix_observable_finite` use this actual finite maximal-duration cutoff, rather than 3N as the row length.
- `Outcome N`: subtype of completeDomain. `eventProb` sums its actual rational P_N masses, cast to reals. Nonnegativity, normalization, monotonicity, complement and intersection-complement identities are proved.
- `coordinateSigma N I = ⨆ i ∈ I, MeasurableSpace.comap (fun w => X w i) ⊤`. Prefix indices are 0..m and suffix indices m+k..duration. These are full generated sigma-algebras, not restricted cylinders or a surrogate saturated class.
- `termination_measurable`, `lastSplit_measurable`: proved directly in these sigma-algebras, using the observable identities.
- `literalAlpha N k`: supremum of absolute covariance over full prefix/suffix sigma-algebras and cuts 0≤m≤duration. `literalAlpha_bounds` proves `0≤literalAlpha N k ∧ literalAlpha N k≤1/4` for every N,k, using actual finite probabilities.
- `median_lower`, `median_previous`, `median_upper`, `late_lower`: the least median has CDF at least 1/2, preceding CDF below 1/2, CDF at most `1/2+intervalError n`; uniformly for k≤n^6, late probability at least `1/2-2*intervalError n-suffixError n`. Window and suffix probabilities are proved equal to the r11 sum formulas. The disjoint events are never assumed independent.
- `eventual_median_bounds`: eventually in n, for EVERY N in its Fibonacci interval and EVERY 1≤k≤n^6, the median cut is admissible and `1/4-intervalError n-suffixError n/2 ≤ literalAlpha N k`. The proof first establishes positive late probability; a cut beyond the actual duration would make this event empty.
- `fibIndex_pos`, `fibIndex_lower`, `fibIndex_upper`, `fibIndex_unique`, `fibIndex_tendsto`: for N≥1 this is the unique n≥1 with F n≤N<F(n+1), and n(N) tends to infinity.
- `all_N_alpha_limit : Tendsto (fun N => literalAlpha N ((fibIndex N)^6)) atTop (𝓝 (1/4:ℝ))`.
- `all_N_uniform_alpha_ninth : ∀ᶠ N in atTop, ∀ k, 1≤k → k≤(fibIndex N)^6 → (1:ℝ)/9≤literalAlpha N k`.

## Exact residuals

The all-N limit is closed for the published 2025 absolute-covariance Eq.(7), including its full sigma-algebras. There is NO compiled weighted Question 3 refutation, tsum/divergence endpoint, or exact existential-delta SourceClaim negation. The remaining bridge must define the literal weighted sum with exponent δ/(4+δ), fix arbitrary δ>0, use the uniform ninth bound on 1..n(N)^6, and prove divergence for every such δ. The earlier v1 Eq.(7) prints signed covariance; equality of that coefficient to the published absolute coefficient by complementation is mathematically standard but NOT a compiled interface here. No assertion about the restricted realization-only Question 4 or Gaussianity is made.

Audit, source-only archive, fresh extracted replay and separate final verification are recorded in audit.json, source-only.zip, replay-receipt.json and verification-receipt.json. The full history of local compiler failures remains in attempt files; these are evidence, not mathematical inputs.
