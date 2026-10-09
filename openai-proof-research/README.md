# OpenAI mathematics research

[Public repository and commit mapping](PUBLICATION.md). Only this research directory is published; historical local commit identifiers map to filtered public commits.

**Research resumed on 2026-10-09 toward [10 substantial findings](frontier/TEN-FINDINGS.md): 4 accepted, 6 remaining.** The fourth, [R010 — factor-count residues and PD independence](frontier/findings/R010-complex-modes-PD-independence.md), has passed independent proof and significance reviews plus parent verification. The spectral-width extension remains proof-verified but is technical only after final significance review. The ternary topology and six-point spherical Ramsey theorems retain their proof PASS verdicts but are technical only after final significance reviews. Elementary unimodality, kinetic fluctuations and combinatorial discovery continue; signed Saxl remains unresolved after a focused follow-up; joint prime-neighbor research remains outside the count. Candidates do not enter the count before all acceptance gates pass.

**[R009 — variable-channel reconstruction capacity](frontier/findings/R009-variable-channel-capacity.md).** A weighted nonlinear capacity characterizes four-state reconstruction on locally finite trees with arbitrary known edge channels, including perfect transmission. Independent proof and prior-art reviews pass; the parent reproduced their checks. The degree-free extension belongs to the same finding. Worldwide priority remains unverified.

**Second substantial deduction accepted:** the user's request for another result after R006 is met, on the stated accepted-corpus and bounded novelty basis, by R008. [Iteration 05](frontier/iterations/README.md#iteration-05--second-substantial-result-accepted) records the search, failed routes and final acceptance decision.

**[R008 — parity and factor-size independence](frontier/findings/R008-parity-PD-independence.md).** Assuming the pinned corpus, the number of prime factors of p−1, counted with multiplicity, is asymptotically even or odd equally often in every fixed reduced progression, independently of its PD(1) factor-size law and squarefreeness. Independent proof and final significance reviews support acceptance; parent checks reproduce. It also implies the precise Moree–Hommersom parity conjecture with finitely prescribed valuations. Worldwide priority remains unverified.

**Research result: [R006 — positive-proportion primitive roots](frontier/findings/R006-progression-PD-primitive-root-density.md).** Continued discovery reached a substantial, nonroutine deduction under the user's accepted-corpus premise. Independent proof and final significance reviews support acceptance; worldwide priority remains unverified. The [iteration record](frontier/iterations/README.md) preserves the failed approaches and decisions. The [first-pass outcome](frontier/OUTCOME.md) and ten deductions below are historical; routine corollaries alone did not meet the user's refined objective.

Assuming the pinned corpus, every integer base `|a|≥2` that is not a positive square is a primitive root for a positive proportion of primes in every sufficiently large dyadic interval. A fixed-progression Poisson–Dirichlet argument yields the improvement from `x/log²x` to `x/log x`. [Independent proof review](frontier/reviews/i03-arithmetic-progressions-r4.md) passes; the [final novelty review](frontier/reviews/i03-arithmetic-novelty-r5.md) found no established duplicate under the available premises and supports the nonroutine-improvement judgment. This does not prove existence of natural density or the exact Artin density formula.

## First-pass consequences

**Ten deductions have complete proofs and independent T3-agent reviews. Each finding has its own commit.** They use the OpenAI theorems as true premises, exactly as requested. No claim of first discovery in the mathematical literature is established, and no proof-assistant verification was run.

The most useful starting points are the promised-class undecidability theorem (F003), the prime-predecessor divisor law (F009), the unequal-size incidence bound (F010), and the block-spin tail bound (F007). F008 is a particularly short combination of two different upstream families.

## Accepted findings

| ID | Result | New upstream input | Finding commit |
|---|---|---|---|
| [F001](findings/F001-pi-orbit-quadrature.md) | Sampling x+j/π has uniform O(1/N) integration error on periodic H^s exactly when s>1, within the point-evaluation range s>1/2. | 017: μ(π)=2 and its series corollary | `7105fc6` |
| [F002](findings/F002-clique-free-edge-genus.md) | A k-chromatic K_r-free graph, fixed r≥4, needs Ω_r(k^((2r−3)/(r−2)) log²k) edges and Euler genus. | 184: improved degree coloring | `3da4ec0` |
| [F003](findings/F003-rational-singularities-undecidable.md) | Rational singular-point existence is undecidable even for normal, geometrically integral, rational affine quartics with a supplied smooth rational chart and point. | 004: H10(Q) | `4251b99` |
| [F004](findings/F004-cyclic-affine-actions.md) | Every cyclic group of order m≥2 has the constructed nonlinearizable action on A⁵_C, with quotient A⁵, exotic fixed/branch divisor, and linearization after one trivial stabilization. | 047: affine cancellation counterexample | `b9496da` |
| [F005](findings/F005-quartic-sum-convergence.md) | Reciprocal-sum convergence over all natural zero tuples in one fixed degree≤4 family is Σ₂⁰-complete, despite unique fibers and infinitely many zeros on every input. | 242: single-fold representation | `e718a3b` |
| [F006](findings/F006-quartic-transcendental-sum.md) | A fixed nonnegative degree≤4 polynomial has a finite reciprocal zero-set sum that is transcendental and of Turing degree 0′. | 242: single-fold representation | `113feef` |
| [F007](findings/F007-haldane-block-tails.md) | Block magnetization in the specified spin-one ground states has tail ≤2e² exp(−0.0519799…r), uniformly in block and ring size in the stated range. | 268: periodic Haldane gap | `c93435f` |
| [F008](findings/F008-powerfree-liouville-signs.md) | Fixed admissible polynomial power-free constraints preserve ordinary binary Elliott cancellation; quartic squarefree conditions give each Liouville sign pair density c/4. | 007 + 020 | `c0d489d` |
| [F009](findings/F009-prime-predecessor-divisors.md) | Two uniform divisors of random p−1 have a Dirichlet(¼,¼,¼,¼) gcd/exclusive-part/remainder law; conditional divisor distributions do not concentrate at a deterministic arcsine law. | 011: prime-predecessor PD law | `399fe2b` |
| [F010](findings/F010-unbalanced-unit-incidences.md) | For m≥n, unit-circle incidences are O(m^(2−β)n^(2β−2)+m) for some fixed 1<β<4/3, with a power saving throughout n≤m≤n^(2−ε). | 167: balanced unit-distance saving | `0a6318f` |

Every linked file contains exact hypotheses, the proof, immutable source links, novelty limits and validation. Constants, fields, sampling conventions and quantifier restrictions in those files are part of the statements.

## What “new” and “validated” mean here

The release makes formerly conditional applications available under the accepted premises. The methods mostly belong to existing mathematics: Fourier analysis, degree decomposition, algebraic suspension, cancellation, computability encodings, spectral-gap inequalities, periodic sieves, PD marking and polynomial partitioning. F002 removes an iterated-logarithm loss; it does not establish a new polynomial exponent. F004–F006 are especially direct normal-form or example-building corollaries.

“Validated” means a complete written deduction was checked against actual source statements, reviewed by another T3 agent, checked by the parent, and corrected where necessary. These are AI research reviews, not external human peer review or Lean certificates. Numerical and exact-arithmetic experiments only test finite algebra and diagnostics. The assumed upstream proofs were not re-proved or audited.

“Previously impossible” is interpreted as previously blocked by an unavailable theorem, not logical impossibility. The bounded literature checks found important predecessors; they cannot certify publication priority. The related Sobolev inverse result was demoted to a [supporting reformulation](notes/rotation-sobolev.md), rather than counted as an eleventh finding.

## Research record and reproduction

- [Screening decisions](SCREENING.md): proof hypotheses, duplicates, rejected upgrades and open directions.
- [Validation record](VALIDATION.md): review outcomes, corrections and actual experiment results.
- [Source guide](SOURCE_GUIDE.md): revision, source hashes and retrieval.
- [T3 task ledger](T3_TASKS.json): 8 scout and 11 review delegations, including failures and interrupted exploratory runs. Seven scout reports were recovered; the analysis/geometry lane ended without a completed report. No accepted finding depends on that unfinished lane.
- `proposals/` contains archived working drafts; some initial claims there are false or superseded. `findings/` is authoritative.

All six accepted-result experiment scripts use only Python's standard library. Run them individually as listed in the validation record. The archived combinatorics diagnostics additionally use `networkx==3.7`; the unfinished analysis experiment is parked and excluded.

```bash
python openai-proof-research/sources/fetch_used_sources.py
python openai-proof-research/sources/fetch_used_sources.py --verify-only
```

The research began on 2026-10-08. Upstream is [openai/math at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb). Its pinned README describes 719 manuscripts in 372 families. Copied upstream catalogue materials retain their [Apache-2.0 license](sources/LICENSE). Existing sibling research projects were not included in these commits.
