# Weighted literal source endpoint

Solo implementation, 2026-10-30. Formal endpoint CLOSED, subject to the recorded audit/replay receipts. Root alone accepts. Counts remain 9 additional / 39 total / next 40. No novelty or acceptance decision, manuscript, shared, git, browser, public, external retrieval or MathDB changes.

All 23 inherited r12 mathematical modules are preserved byte-identically. Endpoint.lean adds the following unconditional interfaces in namespace LiteralGame:

- `signedAlpha_eq N k`: signed covariance supremum equals the existing absolute `literalAlpha`, for every N,k. The proof complements the prefix event in its full sigma-algebra, preserves the cut and suffix event, and uses `eventProb_compl` and `eventProb_inter_compl`.
- `paddedSuffix_eq`, `prefix_without_zero`, `source_value_set_eq`: all infinitely padded suffix coordinates generate the finite suffix sigma-algebra; omitting constant coordinate zero preserves the prefix; allowing every natural cut adds only the already present zero covariance. `sourceAlpha_published` and `sourceAlpha_v1` identify both literal source Eq.(7) conventions with `literalAlpha`. No equivalence is postulated.
- `literalAlpha_zero N k`: alpha is zero whenever duration N < k. Its proof makes the generated suffix sigma-algebra bottom and proves the measurable event is empty or universal.
- `sourceExponent_pos`, `weightedTerm_nonneg`, `weightedTerm_zero`, `weighted_summable`: for every delta>0, the actual weighted real terms are nonnegative and supported in 0..duration N. Summability is proved before the first real-tsum lower bound. Thus divergent-real-tsum's default zero has no role.
- `weightedSeries_diverges {δ} (hδ : 0<δ)`: `Tendsto (weightedSeries δ) atTop atTop`. This is along ALL natural N. It uses one term k=(fibIndex N)^6, the actual `all_N_uniform_alpha_ninth`, and `fibIndex_tendsto`. With c=(1/9)^(δ/(4+δ))>0, the term is at least c*(k+1)^2. No unproved ordinary-proof premise or cubic summation identity is used.
- `SourceClaim` is exactly existence of real delta>0 and real C>0 such that the weighted series is strictly <C for EVERY natural N. `publishedQuestion3_false : ¬ SourceClaim` and `v1Question65_false : ¬ V1SourceClaim` are unconditional.
- `DisplayedSourceClaim absolute` writes the same quantifiers directly with the unrestricted-cut, infinitely padded `sourceAlpha`. `displayedSourceClaim_iff` proves correspondence and `displayed_source_false absolute` refutes both published (true) and v1 (false) conventions.

See PROOF-SOURCES.md for the exact probability law, full sigmas, indexing, weights, exponent and source correspondence. PROOF.md explains the short final bridge. RUN.md documents fixed limits, replay and final verification. Compiler attempts, including failures, remain in attempt files.

Residuals: final independent source/formal review, root replay, substantive novelty/prior-art adjudication, manuscript and acceptance remain separate. The inherited prior-review HOLD and routine-adaptation objection remain attached. No claim about Gaussianity, published restricted realization Question 4 or v1 Question 6.6 is made. Formalization and standard helpers receive no separate discovery credit.
