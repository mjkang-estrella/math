# Expanded corpus r58 — research handoff

**One formal refutation candidate: MathDB 364095. Zero self-accepted credit. Campaign count remains 4/20 beyond the historical 39.**

The candidate proves that no four-color edge coloring of K5 gives all ten triangles different color **sets**, refuting the exact universal equality in Pilśniak–Woźniak Conjecture 5 at n = 5. The paper's displayed examples are orders 4 and 6; this is an interior counterexample order, not a change of domain or palette convention. Significance and novelty are not self-adjudicated. The multiset conjecture remains separate. See PROOF.md for the ordinary argument and full semantic bridge.

## Formal handoff

- Endpoint: `Palette.source_refutation : ¬ Palette.SourceClaim`.
- `Edge n` is the actual complete graph's undirected edge set, encoded by increasing pairs. `Triangle n` is encoded by increasing triples. Palettes are actual Finsets of the three edge colors. `SourceClaim` uses `IsLeast` to state the literal universal minimum, not a surrogate checker predicate.
- Kernel `decide` proves a finite Boolean checker result. A proved soundness bridge reaches the literal graph-coloring endpoint. No solver result, external numeric script, new axiom, unsafe declaration, `native_decide`, or `ofReduceBool` is a trusted premise.
- `364095-proof-packet.zip` and `proof-packet-manifest.json` bind the sanitized sources and receipts. `replay.py` rebuilds all four mathematical modules plus Audit with strict warningAsError. `packet-replay/` is a separate extraction of that ZIP, with a further clean strict rebuild.
- Audit covers all **66 local mathematical-module declarations**, including generated declarations, with actual module origins. All are safe; no added axioms. All transitive `#print axioms` results lie within `propext`, `Classical.choice`, `Quot.sound`. See audit-summary.json and full fresh-Audit.log. The audit command module is outside the mathematical inventory.
- Lean 4.34.1 and mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612 are recorded with actual binary and manifest hashes in environment.json. External prebuilt upstream oleans are trusted. There is no full upstream rebuild or source-to-olean correspondence claim.

The direct quantified Finset attempt and a staged proposition attempt hit the sampled 6 GiB RSS cap and were killed. A fixed-prefix case passed but is only a probe. The final Boolean checker passed using about 3.85 GiB sampled peak RSS. All these attempts have retained full logs and guard receipts. An initial unrestricted-thread Lean invocation failed to create a thread; subsequent Lean commands explicitly use -j1. A C++ diagnostic compile failed because g++ was absent; a bounded Python replacement completed. These failures do not belong to the accepted proof chain. Unused generated Case files are experiments, not the packet endpoint.

## Review scope and other sustained routes

Exactly 40 reserved IDs have ID-keyed entries in results.json. All 40 literal statements were read. **Four received selected primary-definition review; three received primary proof-body passages; only the five-page palette source was read in full.** The remaining 36 are statement-only dispositions, including explicit source or prior-resolution leads. They are not claimed technically excluded or primary-reviewed.

ATTEMPTS.md records the new primary review depth and sustained mechanisms:

1. 364095: two independent exact diagnostics, ordinary finite exhaustion, unsuccessful direct formalizations, then a complete sound-checker Lean endpoint.
2. 363759: recovered the real even/odd bivariate source scope; derived a partition-histogram formula and the odd vertex-deletion bridge. An 800-graph seeded order-9 diagnostic found only isomorphic collisions. Switching does not answer the actual source conjecture. No general reconstruction theorem or nonisomorphic full-polynomial collision was obtained.
3. 364118: read the published Section 8 proofs; attempted binomial inversion and insertion-coefficient recovery of the alphabet maximum. The source's refined-count theorem does not recover refined counts from their unrestricted sum. Finite length-3/4 checks are only diagnostics. Uniform maximum recovery remains open here.
4. 364087: read the primary and 2026 published definitions and exact conjecture. Binomial lifting does not preserve a dual-feasible basis or its spread. A spread-preserving optimal-support transfer remains unproved. No isolated-feasibility LP surrogate is offered.

No old held/protected candidate was taken over. Historical ID/title screens found administrative reservation occurrences, unrelated numbers, and one old source-title abstract catalogue occurrence; no inherited target exclusion for these 40 was identified in the checked notes. This is a bounded search, not proof of global nonreview. A broader JSON read-and-hash attempt hit its CPU cap and did not complete. The replacement focused disposition/review/rejection/Markdown search completed; its line and per-file limits are recorded in history-focused-command.json. The campaign ledger was mutable and differed from its reservation-time hash; it was treated as administrative context and never edited.

## Corpus, prior art, and limits

The full inventory has 95,675 historical distinct IDs: 87,990 retrieved records and 7,685 stubs. The old 10,000 routing queue is not that inventory. All 20 normalized corpus chunks were byte-verified against their manifest. The exact reserved raw lines, including newlines, are in raw/. provenance.json records one-based lines, chunk hashes, raw-line hashes and literal-statement hashes. Metadata and assignment-index disjointness establish neither global novelty nor complete review.

Live registry requests at approximately 15:17 UTC on 2026-11-01 used `/commits/HEAD`:

- OpenAI/math: 4eaee87548250b2682affda7d05d947c05554bae, unchanged; reused the byte-hashed complete preprints tree 3f56f68a176b4494c346091ea0a319651bc217ec.
- Omega: fff5d21d2972d3b0c0d2468818163f1f385ca1f0. Fetched its actual complete root tree. D5 da7b727392fb95300b19e1759d1f2bcde0b70baf and Problems 0b45ced5e033ab15556c8f7a9177458bc5ad1de6 match the complete r56 caches, whose bytes were hashed before reuse.

registry-screen.json records exact scopes and all path hits. This is a path/title screen, not a read of all registry proof bodies or deleted history. The bounded web queries and source-author publication list did not identify an earlier palette resolution. No worldwide priority clearance, full citing-literature review, journal/erratum clearance, or live MathDB/Palomar clearance is asserted. Source receipts contain dated actual URL/status/byte hashes. No denied route was retried or bypassed, and no authors were contacted.

Every expensive process used at most two allowed CPUs, CPU 120 seconds, wall 140 seconds, 12 GiB address space and a sampled 6 GiB process-group RSS ceiling. Successful final replay peaks stayed below the cap. Sampling at 100 ms is not a cgroup/transient-peak guarantee. Independent reviews, manuscript preparation, and root acceptance follow separately. No publication, upload, browser tab, external message, git operation, shared edit, count change, or child agent was used.
