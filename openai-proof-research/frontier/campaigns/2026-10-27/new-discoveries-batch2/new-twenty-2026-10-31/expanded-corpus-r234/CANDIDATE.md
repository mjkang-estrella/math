# MathDB 356266: an Euler ordering that cannot be a universal cycle

Status: **candidate for independent review; zero accepted credit claimed**. The ordinary refutation and literal Lean certificate are complete. Novelty and significance are bounded investigations, not established priority or campaign acceptance.

## Exact source and scope

The reserved record is [MathDB 356266](https://mathdb.com/p/356266/hurlbert-s-ordering-conjecture-for-universal-cycles-of-permu), sourced to [Kirsch–Sibley–Sprangel, arXiv:2209.14198](https://arxiv.org/abs/2209.14198), Conjecture 6.3. The downloaded source has only v1. Definitions 6.1–6.2 identify each permutation of four letters with an edge from its reduced three-letter prefix to its reduced three-letter suffix. An Euler tour lists each of these 24 labelled edges exactly once, with suffix/prefix overlap including the cyclic last/first pair. A universal cycle is a cyclic sequence whose four-letter windows have precisely those order types, in the specified order. Arbitrarily many alphabet symbols are allowed.

The record asks whether **every** such Euler ordering has a realization. It is refuted by one Euler ordering of S4 with no realization over **any** linearly ordered alphabet. This is not a claim against existence of some universal cycle, nor a fixed-alphabet lower bound, nor a partial-word conjecture.

## Witness

Read the following cyclically, in rows from left to right:

```
1234 2341 2413 4231 3421 3214
2134 1243 1423 4123 1342 3412
4132 1324 3142 1432 4321 4213
3241 2314 2143 2431 4312 3124
```

All permutations occur once. Reduction of each suffix of length 3 equals reduction of the next prefix, including 3124 to 1234. These finite facts are proved in Lean by kernel `decide`, not `native_decide`.

Number the 24 cyclic word positions from 0 to 23. Suppose a word x realizes the displayed order. The indicated windows force:

| Window index | Permutation | Compared offsets | Consequence |
|---:|---:|---:|---|
| 2 | 2413 | 0, 3 | x2 < x5 |
| 5 | 3214 | 0, 3 | x5 < x8 |
| 8 | 1423 | 0, 2 | x8 < x10 |
| 10 | 1342 | 0, 3 | x10 < x13 |
| 13 | 1324 | 0, 2 | x13 < x15 |
| 15 | 1432 | 0, 3 | x15 < x18 |
| 18 | 3241 | 0, 2 | x18 < x20 |
| 20 | 2143 | 0, 3 | x20 < x23 |
| 23 | 3124 | 0, 3 | x23 < x2 |

Transitivity gives x2 < x2, a contradiction. This proves nonrealizability for every total order, with no computational assumption or omitted semantic bridge.

## Lean endpoint and semantics

`lean/Hurlbert.lean`, namespace `MathDB356266`, contains:

* `Permutation`: injectivity of a map Fin n → Fin n, hence the usual finite permutation.
* `Overlaps`: equivalence of every strict comparison between suffix and prefix offsets, exactly equality of reduced order types.
* `EulerOrdering`: every row is a permutation; rows are distinct; every permutation occurs; every successive pair overlaps cyclically.
* `position`: cyclic addition modulo the word length.
* `Realizes`: every comparison in every window agrees with its listed permutation.
* `tour_euler`: the displayed witness is an Euler ordering, including all four semantic clauses.
* `tour_not_realizable`: no word over any `LinearOrder` realizes it.
* `counterexample`: existential literal counterexample with the universal nonrealizability conclusion.

The endpoint does not use a surrogate checker proposition for the claimed conclusion. The finite verification is unfolded into the semantic Euler predicate. The nonrealizability proof is the nine inequalities above.

Fresh extracted source in `replay-v2/` built with Lean 4.34.1, `-j1 -M3500 -DwarningAsError=true`. All 13 local declarations, including generated auxiliary declarations, were inventoried, checked for unsafe/partial/axiom declarations, and audited transitively. Only `propext`, `Classical.choice`, and `Quot.sound` occur. The extracted local olean also passes `leanchecker Hurlbert`. `replay-result.json` records the exact certificate hash. The final archive is `proof-packet-v2.zip`; the first archive/replay are retained as failed audit history because direct references to generated declarations triggered a linter. The second audit disables only that auxiliary-name linter, not warnings on the proof source.

External dependency oleans are the pinned cache at mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612. No full upstream rebuild or source-to-cache attestation is claimed. `leanchecker` is Lean's internal replay tool, not an independent proof-assistant implementation.

## Discovery and reproducibility

`python3 -I -B scripts/limited.py tours python3 -I -B scripts/tours.py` reproduces the seeded Hierholzer search. The seed for n=4 is 356270. Trial 8465 gives this witness. The comparison graph has an edge from word position u to v for each required strict inequality; a topological sort detects failure. The certificate extractor recovers the explicit nine-cycle. This diagnostic search is separate from, and unnecessary to trusting, the Lean proof.

Coverage: all eight cyclic S3 tours with first edge 123; 8465 random S4 tours through the first failure; 5000 random S5 tours and 500 random S6 tours; an additional capped lexicographic S4 search of 100000 tours, with no failure in that lexicographic prefix. No exhaustive S4 count or minimality is claimed.

## Primary literature and printed construction comparison

1. [Chung–Diaconis–Graham, Universal cycles for combinatorial structures (1992)](https://fanchung.ucsd.edu/wp/universalcycle.pdf), Section 4, pages 50–51: after constructing an acyclic lifted order for a particular Euler circuit, they express the belief that the lifted relation is acyclic for any Euler circuit. Their displayed S4 word is `123412534153214532413254`; it is a positive example, not this obstruction.
2. Hurlbert's 1990 thesis, Conjecture 3.1.3, is identified by the reserved source. The thesis body was **not recovered**; one guessed author-site path returned 404 and was not used as evidence. Its exact original qualifications remain an independent-review limitation.
3. [Hurlbert–Isaak (1996)](https://glennhurlbert.github.io/Papers/ECUCPpub.pdf) uses a different difference-based equivalence representation. Its discussion of difficulties with order-isomorphic lifting does not print this counterexample or prove nonrealizability of an Euler ordering.
4. [Kitaev–Potapov–Vajnovszki, arXiv:1707.06110](https://arxiv.org/abs/1707.06110), both v1 and v2 retrieved: shortening words and partial cycles; the ordinary universal-word construction does not close arbitrary Euler tours. Their smaller compressed S4 examples are positive partial-cycle constructions.
5. [Kirsch–Lidický–Sibley–Sprangel, arXiv:2204.02910](https://arxiv.org/abs/2204.02910), both v1 and v2: Section 3 still asks whether every Euler tour lifts. Their theorem guarantees a specific family of tours containing a prescribed path. It supplies no source-ingredient refutation of the arbitrary-tour claim.
6. Reserved source arXiv:2209.14198, Section 6: Conjecture 6.3; Remark 6.4 distinguishes words from cycles. Figure 15 is a positive S3 example; Figure 17 is a compressed S4 graph cycle; Figure 18 is a 2-overlap cycle; Figures 19–21 are partial words. Earlier Figures 1–13 concern graphs, set partitions and threshold graphs. All figure/example references from the source and the companions are collected in `notes/source-example-inventory.txt`.
7. A 2026 citing-work search found Fillmore et al., Designs, Codes and Cryptography 94, 152, concerning ordinary alphabet words and partial cycles. The current full publisher page was retrieved. No claim resolving arbitrary permutation-tour lifting was identified there.

The witness was not seeded from a printed obstruction, and no printed obstruction was found in these papers. `scripts/printed_compare.py` compares the witness with the 1992 printed S4 cycle and all 64 twin-block expansions of the reserved source's Figure 17, allowing cyclic rotation, reversal and alphabet complement. At most 9/24 and 10/24 successor pairs agree, respectively. This is bounded evidence against a small reordering of those printed constructions, not a proof that every conceivable derivation from all literature is excluded. The proof's use of strict-cycle inconsistency is elementary, but the nonliftable Euler ordering is the substantive new witness. Independent significance review must decide whether it meets the campaign standard.

## Public proof registries and limits

Checks performed on 2026-11-05 before search and expanded after the witness:

* Lean Pool current head/tree 01db1d7049cf9668bda1e9e106875ee1278b43e6; recursive tree complete. No target-related path found; the Hackenbush hit concerns misere games.
* Current trureturing conjecture page, Omega current head, exact arXiv IDs and topic strings. The sole target-neighbourhood hit is ColorSym optimality, a different conjecture from the separation-number source.
* Current OpenAI/math head/root and complete preprints subtree 3f56f68a176b4494c346091ea0a319651bc217ec: no relevant title path. The initial full repository recursive tree was truncated and is explicitly not treated as complete code clearance.
* GitHub repository searches and bounded web searches for Hurlbert, arbitrary Euler tours, universal cycles, refutations and 2026 developments. A Go k-permutation generator was found; no prior proof located. This is not authenticated global GitHub code search.

HTTP receipts and body hashes are retained in `sources/`, indexed by `source-receipts.json`. Search outputs are retained as `sources/search*.json`. Crossref, Semantic Scholar, arXiv search API, ScienceDirect and DBLP were not directly requested. Search engines incidentally returned cached snippets from excluded publishers; no such snippet is relied on for the candidate. The first UCSD host failed TLS; verification was kept enabled and a distinct official author host supplied the PDF.

No worldwide priority, independent review, root acceptance, paper publication, or campaign credit is claimed. The strongest next action is an independent adversarial source-fidelity and novelty/significance review of this packet, especially the original thesis qualifications and any unindexed permutation-cycle literature.
