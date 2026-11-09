# MathDB 342364 — round 3 partial handback

PARTIAL, not accepted. Root decides. Exactly zero of the six residual Props closed. EvenFormula, OddOneBound, OddThreeBound, OddOneEquality, OddThreeEquality and FifteenBound all remain open. The unconditional ¬ Conj61 and Conj61Some are not proved.

New mathematical work in UlasWeight.lean:

- Explicit integral binomial reduced operator on integer polynomials.
- Nat.size subadditivity and halving estimates, including zero edge cases.
- Divisibility weight predicate Weighted and per-monomial gains.
- Lemma W's one-step and iterated weight gains for that explicit operator.
- Stronger two-unit gain for the tail after removing the leading exceptional terms, with an exact finite-sum main/tail decomposition.
- Exact constant coefficient formula [y^0] reduced m R = 2(m+1)R_0+R_1.

UlasFinal3.lean retains explicit conditional endpoints and additionally derives the per-k refutation from FifteenBound alone. It does not supply that premise.

The central unresolved step is Lemma R's identification of the explicit polynomial operator with the actual series even-section transfer. The even initialization/invariant, odd-case initialization and low coefficients, valuation readout and general nonzero differences are also absent. Nothing in the weight proof is presented as a substitute for that bridge. See REMAINING.md and NEXT-ROUND.md.

All nine frozen round-2 sources, including audit instrumentation and the four round-1 modules, remain byte-identical to the SHA-bound archive. frozen-before.json and frozen-after.json agree, including original, local and fresh-extracted copies.

No child agents, git operations, shared ledger edits, network access, uploads, external messages or browser tabs were used. All writes and temporary/build/cache paths stayed in this lane. No acceptance or credit is claimed.

Fresh extracted strict serial rebuild and leanchecker passed for all 12 modules. Three exact Python regressions passed, including 130 new reduced-operator monomial comparisons with 32 series coefficients. Both new negative controls were rejected with the expected type mismatch.

Endpoint closure audit: 3,653 modules and 349,626 declarations; the audited set equals the entire import closure. LOCAL: 285 declarations, all forbidden metadata counts zero, all transitive axiom sets within propext, Classical.choice and Quot.sound. Upstream metadata is reported separately in results.json and fresh-replay/logs/audit-summary.json. Compiler IR extra names are separate from kernel declarations. No background process remains.
