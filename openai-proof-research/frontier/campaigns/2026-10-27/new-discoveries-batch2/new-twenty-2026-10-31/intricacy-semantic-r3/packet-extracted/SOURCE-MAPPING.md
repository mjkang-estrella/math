# Lean and ordinary-source mapping

Exact source: Petersen arXiv:1607.02425 Conjecture 4.6.8; Petersen–Wilson arXiv:1512.01143v6 Conjecture 6.3. Existence of a fully supported stationary one-step Markov law locally maximizing rank-zero-partition uniform-subset intricacy, relative to all stationary one-step Markov laws on the two-sided full two-shift. No uniqueness, global, all-invariant, or higher-order assertion.

Read actual source Definition 5.1 and (5.1)–(5.5), Proposition 5.10 and proof (5.28)–(5.31), Section 6 cylinder formula (6.1), and both conjectures. Frozen full ordinary proof and qualified independent review are copied under inputs. No flaw in the ordinary argument was found on rereading; in particular the compact entropy-argument interval is uniform in all positive gaps and only transverse derivatives are required. This is not a new independent review.

Inherited eight Lean files are byte copies of r2. Their 56 component theorems remain partial, with their exact mapping in inputs/intricacy-formal-r2/SOURCE-MAPPING.md. Target333569 retains its finite definitions and unproved SourceClaim; it is not silently promoted to the literal source measure theorem.

New Consistency333569:
- wordProb_cons and wordProb_left_consistent give left extension for (6.1), supplementing r2 right extension.
- marginal_restrict proves arbitrary nested restrictions inside a fixed finite block, without needing positivity assumptions. It does not by itself provide consistency across all integer intervals.

New TwoSided333569:
- rowPMF/historyKernel convert the actual source transition rows to normalized probability kernels.
- halfLaw and halfLaw_probability use mathlib Ionescu–Tulcea to give actual infinite forward laws conditional on a symbol. halfLaw_prefix, halfLaw_zero, halfLaw_one give finite projections.
- halfLaw_prefix_next proves finite past/next factorization; halfLaw_word proves the full explicit forward transition product.
- detailed_balance proves binary stationary reversibility, for use in the negative branch.
- conditionalTwoSided is the map of two conditionally independent infinite chains under the positive/negative index gluing map. twoSidedLaw mixes these actual measures with source stationary weights. Probability instances prove total mass one; no external consistency hypothesis is assumed.
- twoSidedLaw_finite_cylinder evaluates any finite collection of integer coordinates by finite iterated kernels; this is a concrete finite computation formula on the actual two-sided measure. twoSidedLaw_zero_cylinder identifies the one-coordinate law at zero. twoSidedLaw_neighbors and twoSidedLaw_gap_two identify the actual {-1,1} marginal with pi(c) P²(c,b).
- twoSidedLaw_cylinder_pos and twoSidedLaw_fullSupport prove positivity of every finite cylinder and every nonempty open set in the actual two-sided product topology. This is full topological support, not just positive finite data.

Still missing: general translated wordProb evaluation, stationarity, two-sided Markov characterization, selected-gap entropy chain rule and source limit, uniform differentiation/local promotion, and weak-law topology chart. See RESIDUALS.md. The cylinder formulas through finite kernels do not replace those obligations.

## Trust, source and novelty limits

Pinned Lean 4.34.1, mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 and inherited transitive Lake pins. The external dependency cache is trusted and read only by convention; there is no full upstream rebuild or transitive source-truth audit. Every local module is freshly extracted and rebuilt with warningAsError; theorem/definition/instance transitive axiom audits admit only propext, Classical.choice, Quot.sound.

The inherited ordinary/significance review remains qualified PASS only. Publisher full bodies, dissertation, predecessor/citing proof bodies and version comparisons retain every limitation in inputs/intricacy-source-review-r1/REVIEW.md. Registry receipt is head-only, not full clearance. No new novelty or priority claim arises from formalization. No new external searches/fetches, registry retries, Palomar/MathDB403 retries, browser tabs, external messages, publication, child agents, git operations, shared edits or count changes occurred in this lane.
