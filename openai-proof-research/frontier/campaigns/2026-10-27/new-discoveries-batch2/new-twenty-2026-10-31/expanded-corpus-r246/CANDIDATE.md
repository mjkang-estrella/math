# MathDB 339235 — certified refutation, acceptance on hold

**Zero accepted credit.** The mathematical witness passes Lean, but novelty, significance, and the campaign's source-correction/small-modification exclusions require root adjudication. No independent review or manuscript is claimed.

## Exact target and source

Lau, Shiu and Ng, *On local antimagic chromatic number of cycle-related join graphs*, [arXiv:1805.04888v1](https://arxiv.org/abs/1805.04888v1), Conjecture 3.2: for every even n >= 4, chi_la(M_(2n)) = 4. The source has one arXiv version. Its preceding Theorem 3.11 proves the odd n case has value 3; this packet does not extend that formula or use it as a proof ingredient. The reserved raw line, literal statement and provenance hashes are in raw/339235.jsonl and extracted.json.

## Ordinary exact proof

Take n = 6 and vertices 0,...,11. The first twelve edges are (i,i+1 mod 12), in order i = 0,...,11. The remaining six edges are (i,i+6), in order i = 0,...,5. Give these eighteen edges the respective labels

    17 13 7 8 3 15 6 18 4 5 12 2 | 10 1 9 16 14 11.

They are a permutation of 1,...,18. The sums incident with vertices 0,...,11 are

    29 31 29 31 25 29 31 25 31 25 31 25.

Consecutive sums differ, including the last and first. The antipodal pairs have sums (29,31), (31,25), (29,31), (31,25), (25,31), (29,25), respectively. Thus this is a local antimagic labeling with exactly three distinct vertex sums. Its existence contradicts minimum value four and refutes the conjecture at even n = 6 >= 4. No lower-bound proof is needed for this negation. We do not claim that the Lean theorem proves chi_la(M12) = 3, although ordinary chromatic considerations can supply a lower bound.

## Literal Lean endpoint

`Mobius.conjecture_false` in lean/Mobius.lean negates the entire universal statement. `LocalAntimagicChromaticNumberEq n k` uses the attained-minimum definition: some local antimagic labeling has k colors, and every such labeling has at least k colors. Its local-labeling definition requires List.Perm with 1,...,3n and distinct incident sums on every edge. Color count is the number of distinct vertex sums, not a surrogate optimization score.

The canonical edge enumeration has no duplicate undirected edges and no loops. `adjacency_literal` certifies all 144 ordered pairs on the literal 12-vertex cycle-plus-antipodes graph. The permutation condition ensures all indices used to access labels are in range. The graph encoding and all mathematical definitions are in the packet, with no external semantic assumption.

The full ZIP was extracted into a fresh allowlisted directory, compiled with Lean 4.34.1, `-j2 -M3500 -DwarningAsError=true`, and checked by `leanchecker`. Audit enumerates every Mobius-prefixed declaration including generated declarations: 19 passed. Only propext, Classical.choice and Quot.sound occur transitively. Only Init is imported; mathlib is unnecessary. Full outputs: logs/full-build.log, logs/full-checker.log, logs/full-audit.log; result: replay/full-result.json. Packet hashes: packet-manifest.json. Prebuilt core dependencies and the installed checker are trusted; no full upstream rebuild is claimed.

## Discovery and source comparison

A source-first literature search and current proof-registry tree scan preceded the labeling search. Simulated annealing over proper vertex-color partitions found M8 and then M12 witnesses. Both logs and the deterministic C scripts remain in the lane. The search score is the within-color sum variance; the final certificate uses only exact arithmetic and is separately kernel checked.

A material follow-up is Lau and Shiu, [arXiv:2203.06594v1](https://arxiv.org/abs/2203.06594v1), Section 2.1. Theorem 2.4 claims all cubic graphs of order eight have local antimagic chromatic number four, including M8. Its proof prints 2x + 3y + 3z = 132, although twice the sum of 1,...,12 equals 156. The independently found M8 witness has class sizes 2,3,3 and sums 15,22,20, giving 156. **This arithmetic issue is not proposed as a separate discovery.** The primary packet uses M12, outside that theorem's order-at-most-eight scope, to avoid relying solely on its first-parameter correction.

The original source has figures for wheel deletions, odd-order Mobius ladders, generalized Petersen graphs, and book labelings. The follow-up prints the cubic order-eight graphs and four-color labelings. The text-derived example/figure/conjecture index is source-example-index.json. No printed counterexample gadget was used. Nevertheless, the referee must decide whether this remains a small modification/near-folklore failure under the user's unusually strict credit standard. Do not infer significance merely from the age of the conjecture.

## Bounded novelty investigation and unresolved gates

88 immutable HTTP receipts cover primary PDFs, abs pages, version requests and public-registry requests. sources/web1.json through web16.json retain the live literature/GitHub-index queries, including exact titles, acyclicity, Mobius local antimagic, M8, M12 and Lean variants. The current complete Lean Pool tree contains no relevant path-name match. OpenAI and Omega recursive trees are truncated; current OpenAI CONTENTS was fetched separately. This is not a complete code-content search. No prior positive 3-color labeling of an even-n Mobius ladder was located in this bounded pass, but no worldwide novelty claim is made.

Important remaining gates:

- The publicly indexed 2020 workshop slides on Scribd and publisher-only/citation-neighborhood bodies have not all been read. They may contain the decisive value. The 2022 source was read directly, not merely its abstract.
- The 2022 theorem's arithmetic failure makes source-correction significance a serious objection; the M12 witness broadens the failure beyond its finite theorem but does not settle the objection automatically.
- A relabeling/subdivision/construction-comparison review of the exact witness is required under the campaign's exclusions.
- Independent literal-fidelity and adversarial proof review, a paper, and root acceptance remain outstanding.

Do not self-accept or increment any ledger. If root judges this a small source-arithmetic correction, discard the candidate despite its valid certificate.

## Final registry audit and sequencing caveat

The raw Lean Pool candidates/ index files at the recorded HEAD were fetched and scanned for all reserved IDs, source arXiv IDs, authors and distinctive keywords. projects.yml returned 404 and is absent from the complete tree; its receipt is retained, with no retry. Four spaced unauthenticated GitHub repository queries (source ID, local antimagic, Lau/Shiu, Mobius ladder, each with lean) returned no repositories. Full queries, heads, receipts and hits are in outputs/registry-screen.json.

**Procedural failure disclosed:** the live tree/path and web screens preceded numerical work, but the mandatory raw candidate-index scan and GitHub repository API search were completed only during final audit, after the witness and Lean certificate. This does not satisfy the required sequencing. No pre-investment novelty-clearance claim is made; the candidate remains on hold.
