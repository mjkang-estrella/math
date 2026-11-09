# MathDB 347913 — partial formalization, zero credit

**The full literal conjecture is NOT proved.** `PolynomialConvexity.SourceConjecture` is only a definition of the exact requested proposition. There is no theorem inhabiting it. No acceptance/count changes: campaign remains 2/20 beyond 39.

## Source and definitions

Read the author r40 attempt, raw/347913.jsonl, the primary arXiv text (Eq. (2), Section 3 Conjecture 1), published SIAM text (Eq. (1.1), Section 4 Conjecture 1, DOI 10.1137/20M1369592), and Polak's parameter-limited Theorem 1.1/proof setup. Sources remain at their frozen original paths; no recursive evidence copies. The existing independently reviewed ordinary proof is the intended route, not a new bibliographic clearance.

`Edge n L` is the subtype of ALL finsets of `Fin n` of cardinality L. Zero-based vertex labels correspond to [n] by i ↦ i+1. An ordered tuple is a function `Fin d → Edge n L`, with no injectivity condition. `prefixUnion e j` includes j; `mem_prefixUnion` proves its exact membership semantics. `sourcePolynomial_eq_quotients` equates the definition to the displayed product of quotients. The polynomial is not defined using an expectation. The simplex has nonnegative coordinates and sum exactly one. The source proposition quantifies over all n,L,d≥2, with no L≤n restriction. Empty E when L>n is explicitly proved, as is its empty-simplex convexity. This does not prove the nonempty case. The related final-union-only p_d is not used.

## Kernel-checked partial content

- Source.lean: literal definitions, product-of-quotients bridge, prefix semantics, denominator positivity, empty-family boundary, constant repeated-edge coefficient L^(-d).
- Reindex.lean: tuple permutation is a genuine equivalence, preserves weight products, and summing the permutation-symmetrized coefficient gives exactly d! times the literal polynomial. No stabilizer division occurs for repeated edges. `symCoefficient` is a finite combinatorial sum, NOT asserted equal to a mixed moment.
- Convexity.lean: ordered-tuple expansion of the dth power; pointwise convexity of a nonnegative linear form to any natural power; a generic integral convexity helper with explicitly stated integrability. That assumption is not discharged for the clock model and is not disguised as an endpoint.
- Model.lean: concrete finite product of rate-one exponential measures, probability instance, independent coordinate clocks, nonempty-edge minimum, measurability/clock bound/nonnegativity on nonnegative clocks, exact threshold semantics, finite vertex maximum threshold, joint event as a rectangle intersected with nonnegative clock support, and its product-measure formula.

## Exact remaining obligations

1. Evaluate expMeasure 1 (Ici t) at nonnegative t, establish a.e. nonnegative clock support, and remove the support intersection in `joint_event_probability`. Deduce joint survival exp(-sum vertex thresholds).
2. Prove the nonnegative mixed product layer-cake formula for the concrete lifetimes using Tonelli, including finite-dimensional product volume and the strict/weak threshold boundary convention.
3. Prove null coordinate ties and zeros and the disjoint union of all d! labelled coordinate chambers. Repeated edge values do not identify integration coordinates.
4. Construct the descending-coordinate gap substitution and inverse; prove the unit determinant/Jacobian, domain transport and exponent identity sum_v max thresholds = sum_j card(prefixUnion) u_j. No such change-of-variables or prefix-exponent theorem is in this packet.
5. Factor each chamber integral, evaluate its positive-rate exponential factors, and identify the concrete mixed moments with `symCoefficient`.
6. Prove integrability of every power of the finite clock sum and each mixed product, then the weighted linear-form powers for all nonnegative vectors. The clock moment d!, the finite-sum power bound, and domination are still obligations.
7. Commute the finite expansion with integration, combine obligations 5–6 with the proved symmetrized_sum to obtain E[(sum x_e Z_e)^d] = d! f_d(x), including the all-same-edge moment control d!/L^d.
8. Apply the generic convexity helper, divide by positive d!, restrict to the simplex, and prove `SourceConjecture` for every n,L,d≥2.

These are substantial mathematical formalization gaps, not merely missing import wiring. The partial code has no added axioms, placeholders, unsafe declarations, native_decide or ofReduceBool proofs. Generic helper assumptions remain visible in the full declaration audit.

## Validation and trust limits

The source-only ZIP has pinned toolchain metadata, manifest, bounded build driver and replay.py. Replay requires a fresh output directory, validates entry paths/file hashes, extracts only there, and compiles strictly with -DwarningAsError=true and -j1. Its sanitized LEAN_PATH includes only its fresh build output plus pinned dependency package caches. It does not use upstream project build outputs. Each module's stdout/stderr and every checker invocation are retained. All local-origin declarations, including generated helpers and instances, are audited by module origin, with full types and transitive axioms, rejecting partial/unsafe/axiom declarations and dependencies outside propext, Classical.choice, Quot.sound. Leanchecker replays local modules from their imports; this is the same kernel and is not an independent verifier. The entire upstream dependency library is not reattested. See fresh replay result and build.json for exact outcomes and caps. The root-level leanchecker --help probe failed because lean was absent from that probe's PATH; the actual replay uses a sanitized PATH containing the pinned binary directory.

## Novelty qualification

Retain the independent review's ordinary-proof/source PASS and conditional Lean-investment recommendation. The common-shock representation is classical Marshall–Olkin; the full 1967 mgf body and the 2025 quantum-channel citing body remain unread. This phase found no new subsumer and did not repeat the bibliographic investigation. No worldwide priority claim, complete later-literature clearance, or significance acceptance is made. No work on held 348760 was performed.

All 192 frozen input bindings are checked before/after in integrity receipts. Reservation and historical inputs remain unchanged. No git, external messages, tabs, publication, uploads, shared edits, or child agents. No background job remains at handback.
