# Statement correspondence: MathDB 356266

This is a formalization supplement for root review, not an acceptance or novelty ruling. It follows hurlbert-root-ruling-r1.json and gates A and E of hurlbert-review-r1/REVIEW.md. No new historical or priority investigation was performed. The source file Hurlbert.lean is copied byte for byte from expanded-corpus-r234/lean/Hurlbert.lean, SHA256 ae2fba2c091759597999fd59fa147290cc9b2cfc1b863f9e0d0da3a73685c29f.

## Exact source statement

Kirsch, Sibley and Sprangel, *Graph Universal Cycles: Compression and Connections to Universal Cycles*, arXiv:2209.14198, Section 6.1, page 15, Definitions 6.1–6.2 and Conjecture 6.3. Cached primary text: ../expanded-corpus-r234/sources/356266.txt, lines 776–803. The supplied MathDB record is ../expanded-corpus-r234/raw/356266.jsonl. Source URL: https://arxiv.org/abs/2209.14198 . These quotations are from the cached primary text and supplied record, without a new network request.

The source defines order-isomorphism by: “for every i, j ∈ [n], we have σ(i) < σ(j) if and only if τ(i) < τ(j).” It defines universal cycles as “cyclic sequences of numbers in which every permutation on [n] is order-isomorphic to exactly one n-window”.

Definition 6.1: “An ordered pair of permutations (σ, τ) ∈ S_n² overlaps by s if σ_{n−s+1} ··· σ_n ≅ τ_1 ··· τ_s. An ordered pair of permutations (σ, τ) overlaps if it overlaps by n − 1.”

Definition 6.2: “The clustered graph of s-overlapping n-permutations, denoted by O(n, s), is a directed multigraph on vertex set S_s. For each π ∈ S_n, there is a directed edge (red(π_1 ··· π_s), red(π_{n−s+1} ··· π_n)). Thus we identify the edge set with S_n. The clustered graph of overlapping n-permutations, denoted by O(n), is O(n, n − 1), the graph of (n − 1)-overlapping n-permutations.”

Conjecture 6.3: “Given any Euler tour of the clustered graph of overlapping permutations (i.e., an ordering of S_n such that each consecutive pair of permutations overlaps), there is a universal cycle for permutations that covers S_n in the same order.”

The MathDB literal statement is:

> Let S_n be the set of permutations of [n], and let O(n) be the clustered graph of overlapping n-permutations: its edges are the permutations in S_n, and consecutive permutations overlap in their last and first n−1 entries up to reduction. **Hurlbert's ordering conjecture.** Given any Euler tour of the clustered graph of overlapping permutations (that is, an ordering of S_n such that each consecutive pair of permutations overlaps), there is a universal cycle for permutations that covers S_n in the same order. Universal cycles correspond to Euler tours in this graph, but it remains open whether every such ordering can be realized by a universal cycle.

The last sentence records the supplied record's historical status, not a new status assertion.

## Definitions and quantifiers

* `Permutation m p` is injectivity of `p : Fin m → Fin m`. On a finite set, an injective self-map is bijective. Thus these are precisely permutations, relabeled from 1,…,m to 0,…,m−1. Rank labels change, strict comparisons do not.
* `Overlaps` compares every ordered pair of positions in the suffix (indices `a.succ`) with the prefix (indices `a.castSucc`). Equality of all these comparison truth values is exactly order-isomorphism, so it implements Definition 6.1 at s = m−1.
* `next` adds one modulo N+1. It includes the last-to-first adjacency; an open Euler trail is insufficient.
* `EulerOrdering t` asserts that each edge is a permutation, no edge repeats, every permutation occurs, and all cyclic neighboring edges overlap. Since Definition 6.2 identifies edges with permutations, this is an Euler tour of the full graph, including parallel edges as distinct labels, rather than a tour in a restricted permutation class.
* `position i a` adds the window offset modulo the word length. It implements cyclic windows, including wraparound.
* `Realizes t w` asserts equality of all strict comparisons between a permutation and its corresponding word window. This is precisely the source order-isomorphism condition. Together with the permutation clause it forces all symbols within each window to be distinct: equal symbols at distinct offsets would contradict one of the two strict rank comparisons. Distant positions may repeat symbols.

`Conjecture` quantifies over every n,N : Nat and t on Fin (N+1) with permutation size n+1; it concludes existence of K : Nat and w with values in Fin K. Thus every positive permutation size and every possible cyclic length is included. The alphabet is unrestricted in size; K = 0 cannot furnish a word on the nonempty domain and is harmless. `ConjectureLinear` replaces Fin K with an existential linearly ordered type and its order instance. A word over any alphabet has finite image; sorting that image gives an order-preserving relabeling into Fin K. Hence finite alphabets lose no source realizations. No global bound such as n+1 symbols is imposed. The Type universe is sufficient to express every finite relabeling.

The source does not distinguish a starting edge. Any rotation of a realizing cycle may be rotated back to the displayed starting edge, so fixing t's starting index imposes no substantive restriction. The source concerns positive n; using n+1 covers exactly that range.

## Why the length is already forced

This packet uses the task's permitted documentation alternative instead of adding a cardinality theorem to Lean. Here is the precise deduction. For h : EulerOrdering t, let P = {p : Fin (n+1) → Fin (n+1) // Permutation (n+1) p}. Define f : Fin (N+1) → P by f(i) = (t i, h.1 i). The injectivity clause h.2.1 makes f injective, by equality of underlying functions. The coverage clause h.2.2.1 makes f surjective: for every (p,hp), choose i with t i = p; equality in the subtype follows by proof irrelevance. Thus f is a bijection. P is exactly the permutation group on n+1 elements, because an injective self-map of a finite set is bijective. Consequently |P| = (n+1)!, and N+1 = (n+1)!.

The `Conjecture` definition therefore introduces no extra Euler tours of incorrect length and omits none. It is already literal without a separately formalized factorial equality. The endpoints depend only on the explicit full S4 ordering, not on this prose cardinality calculation.

## Positive control

Chung, Diaconis and Graham, *Universal cycles for combinatorial structures* (1992), Section 4, printed page 50, cached ../expanded-corpus-r234/sources/chung-1992.txt lines 309–313, states “to produce the U-cycle” followed by `123412534153214532413254`. `w_cdg : Fin 24 → Fin 6` stores these exact integer symbols, including the unused symbol 0 in its ambient alphabet. `t_cdg` lists its reduced cyclic four-windows using ranks 0,…,3. The checked theorems `cdg_euler` and `cdg_realizes` establish that this is its own full S4 Euler ordering and realization. Both use kernel-reduced `decide`; the Python table generator is not trusted as evidence.

## Scope and historical limits

The endpoints negate the source's all-tour claim by the given S4 counterexample. They do not address optimal alphabet size, existence of some universal cycle, or compressed/graph universal cycles. The comparison-cycle mechanism is classical: Albert–West (2009), *Universal cycles for permutation classes*, DOI 10.46298/dmtcs.2727, already supplies a nonrealizable restricted-class ordering. That eight-edge example is not a tour of full S4. Root's existing ruling discusses why it does not by itself provide the supplied full-S4 witness; this lane does not extend that prior-art adjudication. Hurlbert's 1990 thesis body and Jackson's 1993 full text remain unread as recorded in the upstream review. Only root decides acceptance and credit.
