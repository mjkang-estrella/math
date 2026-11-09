# Expanded corpus r91

One full literal Lean candidate is ready for independent root review: **372630**, a refutation of the uniqueness classification in Lindzey's Conjecture 16. An eight-element even-cycle-intersecting family of S5 contains the identity but is not a subgroup and hence cannot be a Sylow double-translate. The endpoint negates the universal source classification. It does **not** refute the weaker maximum-cardinality conjecture.

- Ordinary proof and source-scope discussion: `PROOF-372630.md`.
- Source-only packet: `372630-lean-packet.zip`.
- Lean endpoint: `Eventown372630.literal_source_refutation` in `formal/Eventown.lean`.
- Fresh extracted strict rebuild, all 57 local declarations including generated declarations audited, and `leanchecker`: **PASS**. Only `propext`, `Classical.choice`, `Quot.sound` occur transitively. See `validation.json` and `logs/packet-*.{log,receipt.json}`.
- All 20 reserved IDs appear exactly once in `results.json`; exact newline-preserving raw records, source chunk/line bindings and statement hashes verified.
- Accepted credit: **0**. Root acceptance, significance, novelty and independent fidelity review remain outstanding. No campaign count changed.

A second ordinary obstruction, **372631**, uses central twisting in GL2(Fp) for odd primes. See `ATTEMPTS-372631.md`. It has no GL-specific Lean endpoint and shares the subgroup-classification mechanism; no separate credit is requested. The construction is elementary and should receive explicit significance/nonduplication adjudication before further formal investment.

## Actual finite coverage

| Route | Completed coverage and outcome |
|---|---|
| Singleton commutation classes, 372549 | Exhaustive consecutive-generator reduced walks for S9 and S16. At S16, 10,925,614 prefixes/words and 9,671,159 reached permutations, only counts 1,2,4. All other permutations have zero. No counterexample; source reduction strengthened only conjecturally. |
| Permutation families, 372630 | Exhaustive normalized maximum families in S4 and S5. S5 has 375 identity-containing maxima of size 8, 360 nonsubgroups. These maximum computations are diagnostics, not formal premises. S6 search hit its wall cap; no S6 coverage claim. |
| Linear groups, 372631 | Exhaustive GL2(2) and GL2(3). Central-twist examples additionally checked at ten odd primes 3 through 31. |
| Type B representations, 372759 | Full bipartition-branching ILPs for n=3..10, m=1..15. Returned solutions checked with exact integer arithmetic. 101 certificates, 19 unresolved timeouts; zero proved infeasible systems. n8 certificates at m=1..12,14; n9 at m=1..7; n10 at m=1..6. These remain parameter cases, not solutions of the full conjecture. |
| Conflict-free lists, 372693 | 759 connected labelled graphs of orders 2..5 excluding C5, one nested-prefix list assignment each; no failures. This is explicitly not exhaustive over arbitrary list assignments. |
| Small flows, 372616/372618 | Z2² flows found for all 264 bridgeless connected labelled simple graphs of orders 3..5. Half-integral unit l1 flows certified for Petersen and GP(7,2). No all-p/all-graph index claim. |
| Diagram duals, 372634 | Exhaustive subsets of radial graphs of wheels with rim size 3..9, hence 8..20 dual vertices and 6..18 medial crossings. Exact maxima 2..8. Structured subclass only. |
| Basis number, 372663 | All simple-cycle bases for each connected labelled graph on 2..4 vertices (1,4,38 graphs). No asymptotic conclusion. |
| Spanning trees, 372498 | K4 and K5, all eligible regular graphs through order 5, with 2 and 3 unlabelled spanning-tree types. Asymptotic conjecture parked. |
| Prime sums, 372684 | 100 odd starting primes, all odd lengths 3..999; all starts had prime-sum hits. No infinitude conclusion. |
| Primitive groups, 372796 | Natural symmetric/alternating actions in degrees 3..9, exact derived-series stabilization of two-point stabilizers. No universal constant claim. |

The 2–3 main sustained routes were the subgroup classifications, singleton-word reduction, and unrestricted representation branching. Explicit missing lemmas and search limits are recorded per ID. Hard asymptotic, complexity and transduction problems receive source-backed parked dispositions. A finite grid is not presented as a real-optimization theorem.

## Sources and novelty limits

The current primary bodies were fetched, along with dated arXiv abstract/history pages. The unavailable HTML for 2601.16039 returned 404; its PDF was then fetched and read. No 403/429/challenge route was retried. Later versions matter: current Weyl source 2601.16161v2 conjectures an opposite-direction existence statement, so 372713 is a source-revision stop, not a discovery. The prime-sum body excludes starting prime 2. Prior campaign screening already stopped 372593; that exclusion was retained without a repeated mathematical search.

Live GitHub registry reads used `/commits/HEAD` only: OpenAI `4eaee87548250b2682affda7d05d947c05554bae`; Omega `915cac44382e2ede76ea900c6c41233dc5957a15`. Complete current Omega D5 and Problems trees were fetched untruncated; the root-authorized unchanged OpenAI preprints cache was reused with its actual byte hash. Bounded ID/title/topic/path searches are retained. They are not proof-body reviews or global novelty certificates. The later Lindzey additive-matrix paper and the October multiset Eventown citing paper were inspected at their actual definitions/theorem frameworks; neither inspected framework gives the permutation-quotient uniqueness obstruction. This does not exclude unindexed prior work.

Author/citation followup is deepest for the candidate group routes. The other parked routes do not have exhaustive author-oeuvre or citation-graph checks. This pass produced a formal endpoint early and did not consume several hours; no such duration or exhaustive deep review of all twenty problems is claimed. Qualification must account for these limits.

## Reproduction and trust

Run `scripts/limited.py NAME COMMAND ...` from this lane for capped searches. Each expensive invocation used at most two affinity CPUs, CPU 120 s / wall 140 s, 12 GiB address space and sampled main-process RSS under 6 GiB. Logs retain failures, timeouts and later corrections. These are sampled resource checks, not cgroup peak guarantees. Searches use standard-library Python; graph-free MILP and group diagnostics use `/usr/bin/python3` with installed SciPy/SymPy. No package installation occurred.

`python scripts/package.py` writes and extracts the source-only packet inside this lane. Replay with `scripts/replay_lean.py packet-replay -o Eventown.olean Eventown.lean`, then `Audit.lean`, and `scripts/checker.py packet-replay`, each through the limiter. Dependencies are read-only cached oleans at the assigned Lean/mathlib versions; no full upstream rebuild or source-to-olean attestation is claimed. `scripts/validate.py` checks ID cardinality, literal provenance, strict replay receipts, audit counts, prohibited proof constructs and lane background processes. The final process audit found none.
