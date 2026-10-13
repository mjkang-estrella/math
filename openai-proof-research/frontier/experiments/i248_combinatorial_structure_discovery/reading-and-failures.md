# I248 reading and failures

Date: 2026-10-12. No tests, research code, numerical experiments/scans, agents, snapshots, staging, commits, or publication. Python was used only for retrieval, text extraction, provenance hashing, and writing the assigned authentication file.

## Read boundaries

Read AGENTS.md and sources/upstream.json. Selected only 169, 174, 175 initially. Read bounded corresponding CONTENTS entries and the accepted table. An initial `rg --files` listing was much broader than useful and was truncated; no files listed in snapshot subdirectories were opened. The first TEN-FINDINGS range exposed historical status paragraphs before the accepted table was located; only its accepted table was used for the count. A historical filename glob was broader than ideal, but no I247/I249 content was returned, inspected, or used. Subsequent substantive historical reads were restricted to old opening dispositions and R011/R014 statements.

The source ledger and read extents are in `frontier/sources/i248_combinatorial_structure_discovery/literature.md`. In particular, a combined tool display truncated the middle of EP `06-witness.tex`; it was not retained and is not a proof input. All retained excerpts were fully read. The original AH full proof and withdrawn Yang preprint were not accessed; their limits are explicit.

## Rejected routes

1. **169 positivity to palindrome or insertion-digit concentration.** Those conclusions are supplied directly by the source or are elementary consequences of the source's insertion product. Not substantial.
2. **169 positivity to unimodality by abstract Lefschetz/permutation modules.** The source disclaims the required cup-product compatibility, and I24 already records the missing shape-preserving positive structure. Not a new gap or theorem here.
3. **174 cut thinness to spectral thinness.** Invalid in general and previously rejected. No retry.
4. **174 simultaneous cost/cut control.** Explicitly contained in `cor:ta-fractional-rounding`, including binary-rational data and a zero-cost case. Rejected as duplicate.
5. **175 two unions at constant density loss.** Explicitly in both companions. Rejected as duplicate.
6. **175 deleting a small common set of target images.** The slack in the source Hall proof gives this routinely. For example, with its notation, small-x tests give supply at least 6xm and demand at most 4xm; large-x tests leave linear slack. An O(nr^s) common deletion budget is consequently a technical corollary. Not nominated.
7. **175 arbitrary common embedding for all edge pieces.** Unsupported and false without restrictions: agreement plus disjointness of nonshared images would embed the whole target, and spanning matching/isolation obstructions already prevent a universal constant-factor threshold conclusion. Source embeddings deliberately need not agree.

## New attempt and adversarial checks

The completed attempt replaces scalar Hall supply by a maximum-packing rank for rooted blocks. Its full analytic proof is in `analytic-attempt.md`.

- Verified direction of max/conditional-expectation inequality explicitly; it is max E≤E max.
- Vertex-block exposure changes only hyperedges containing that nonroot vertex, even when one block owns many underlying graph edges. A matching uses at most one such hyperedge. This pays the Lipschitz constant 1.
- Added slot symmetrization before claiming the compatibility hypergraph is exchangeable.
- Added random tie-breaking among all maximum packings and conditioned only on their cardinalities, not on a fixed host. This pays the uniform-matching step.
- Used global independent graph layers, so their union has exactly density 1−(1−r)^(128d). Monotonicity is why induced patterns are excluded.
- Handled floor errors through a fixed large N_d and μ_Q≥c_d n^.99. No finite numerical checks were used.
- Made the cap explicit: a full matching cannot be multiplied by 2d.
- Required no root-root edges in the extension corollary, or that they were already embedded in a separate host. A new random host cannot be assumed to reproduce fixed root-root edges.
- Separated the self-contained rank theorem from the optional AH-based embedding corollary and from all global graph-decomposition claims.

## Disposition

One nomination only: the uniform rooted-pattern packing-rank comparison (T), with bounded-component rooted extension as an application in the same package. Author verdict: candidate worthy of independent proof and contribution gates, subject to a particularly serious contribution check against standard block-embedding transfer arguments. The rank theorem is completely proved at author level; no external numerical validation, independent proof PASS, contribution PASS, or acceptance is claimed.
