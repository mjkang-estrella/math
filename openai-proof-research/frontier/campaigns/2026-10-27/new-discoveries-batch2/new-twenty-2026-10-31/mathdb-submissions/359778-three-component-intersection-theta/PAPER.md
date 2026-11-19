# A theta-graph counterexample to the three-component intersection conjecture

## Abstract

Leader, Ranđelović and Tan conjectured an upper bound for families of simple graphs on an odd number of labelled vertices when every pairwise intersection has at most three connected components. For every integer $h\ge 1$, we construct a counterexample on $n=6h-1$ vertices. The construction starts with three internally disjoint paths of length $2h$ between two common terminals. Its cardinality is $(1+6h+12h^2)2^{\binom n2-6h}$, and its ratio to the conjectured bound tends to $4/3$. At $n=5$ the family has 304 members and the bound is 256. A Lean 4 formalization verifies the family, its cardinality and validity, the bound violation, and the limiting ratio.

## The conjecture and the result

Let $[n]=\{1,\ldots,n\}$ and let all graphs be undirected and simple, with vertex set $[n]$. The intersection $G\cap G'$ has vertex set $[n]$ and edge set $E(G)\cap E(G')$. Its connected components include its isolated vertices. A family is a set of such graphs.

Conjecture 7 of Leader, Ranđelović and Tan [1, §3], also recorded as MathDB 359778 [2] and restated as Conjecture 30 in Ranđelović's thesis [3, Ch. 4], gives the following implication. For every odd $n$, if the intersection of any two members of a family $\mathcal F$ on $[n]$ has at most three components, then
$$
|\mathcal F|\le B(n),\qquad
B(n)=\frac{(n+3)^2}{8}\frac{1}{2^n}\,2^{\binom n2}.
$$
The construction below satisfies the component condition for every ordered pair, including a graph paired with itself.

**Theorem.** For every integer $h\ge 1$, put $n=6h-1$. There is a family $\mathcal F_h$ of simple graphs on $[n]$ with at most three components in each pairwise intersection and
$$
|\mathcal F_h|=(1+6h+12h^2)\,2^{\binom n2-6h}>B(n).
$$
Moreover, $|\mathcal F_h|/B(6h-1)$ tends to $4/3$ as $h\to\infty$.

## Construction

Write $m=2h$. Take two distinct vertices $s,t$, and partition the remaining $n-2=3(m-1)$ vertices into three ordered lists of length $m-1$. For each list, connect $s$ to the first vertex, connect successive vertices of the list, and connect its last vertex to $t$. The resulting paths $P_1,P_2,P_3$ have $m$ edges each. They are internally vertex-disjoint, and $m\ge 2$ makes them edge-disjoint. Their union $T$ is a spanning theta graph with $3m=n+1$ edges.

For a graph $G$ on $[n]$, let $O(G)=E(T)\setminus E(G)$. Include $G$ in $\mathcal F_h$ if $O(G)$ has at most one edge from each path and at least one path has no edge in $O(G)$. Each edge outside $T$ may be present or absent independently.

## Validity of every pair

Fix $G,G'\in\mathcal F_h$, and let $Z=O(G)\cup O(G')$. Call a path cut at an edge of $Z$. Each path has zero, one or two cuts. Consider the spanning graph $T-Z$, which is contained in $G\cap G'$.

In $T-Z$, the vertices before the first cut on a path reach $s$ along that path, and the vertices after the last cut reach $t$. A path with exactly two cuts has one further segment between the cuts. This segment is nonempty even when the cut edges are consecutive, and each vertex in it reaches the first vertex after the earlier cut. A path with no cuts connects $s$ and $t$. Thus every vertex of $T-Z$ reaches one of the terminals or a representative of a segment between two cuts.

If some path is uncut, the terminal representatives belong to one component. There can be at most two paths with two cuts, since each such path uses an omission from each graph and each graph omits edges on at most two paths. Three representatives therefore suffice.

If every path is cut, there can be at most one path with two cuts. Indeed, two such paths would each use an omission from both graphs. This would exhaust both graphs' omissions and leave the third path uncut. In this case the two terminals and at most one further representative suffice. These two cases give at most three components of $T-Z$. Adding edges on the same vertex set preserves every existing path, so $G\cap G'$ also has at most three components.

## Cardinality and violation of the bound

The omission set can be empty, a single edge, or a pair from distinct paths. The counts are $1$, $3m$, and $\binom 32 m^2=3m^2$, respectively. Equivalently, one can choose one of $m$ edges or a no-omission option on each path, then remove the choices that omit an edge on all three paths. This gives $(m+1)^3-m^3=1+3m+3m^2$ choices. For any omission pattern there are $2^{\binom n2-3m}$ ways to choose the edges outside $T$. A graph uniquely determines both its omissions and its outside edges, so the product gives the stated cardinality.

Since $6h=n+1$ and $n+3=2(3h+1)$, the conjectured bound in the same units is
$$
B(n)=\frac{(n+3)^2}{4}\,2^{\binom n2-6h}
     =(3h+1)^2\,2^{\binom n2-6h}.
$$
The difference between the coefficients is
$$
1+6h+12h^2-(3h+1)^2=3h^2>0.
$$
At $h=1$, the core is $K_{2,3}$. There are 19 omission patterns and $2^4$ outside-edge choices, giving 304 graphs. The conjectured bound is $16\cdot 2^4=256$.

The ratio is
$$
\frac{|\mathcal F_h|}{B(6h-1)}
=\frac{1+6h+12h^2}{(3h+1)^2}
=\frac{h^{-2}+6h^{-1}+12}{(3+h^{-1})^2}
\longrightarrow \frac{12}{9}=\frac43.
$$
The orders $6h-1$ are odd and unbounded, so the counterexamples also rule out the same inequality restricted to all sufficiently large odd orders.

## The order-three case

At $n=3$, every graph has at most three components, and so does every intersection. The family of all $2^{\binom32}=8$ graphs satisfies the hypothesis, while $B(3)=9/2$. The literal conjecture already fails there. The theta construction gives violations at unbounded orders and the Lean proof of the literal negation uses the order-five theta family.

## Formal verification

The Lean namespace is `Theta359778`. Graphs in the statement are Mathlib `SimpleGraph (Fin n)`. The intersection is `G ⊓ H` and `compCount` is the `Fintype.card` of `G.ConnectedComponent`. Relabeling $[n]$ by `Fin n` preserves the graph and its components. The family is a `Finset`. The definition `Conjecture` quantifies over every odd natural order and every such family, and gives $B(n)$ using exact rational arithmetic. The unbounded endpoint clears its positive denominator.

| Step | Lean declarations |
|---|---|
| Indexed paths and distinct, loop-free core edges | `Vertex`, `vertex`, `edge_not_diag`, `edge_injective`, `card_vertex`, `card_core` |
| Admissible omissions and retained core | `Pattern`, `common`, `common_index_iff` |
| Reachability along uncut intervals and representative coverage | `reachable_interval`, `reachable_representative`, `reachable_terminals` |
| Representative count with or without an uncut path | `card_doublePaths_le_two`, `card_doublePaths_le_one`, `compCount_le_of_representatives`, `common_compCount_le_three` |
| Extension outside the core and validity of every pair | `makeGraph`, `common_le_inf`, `compCount_le_of_le`, `family_pair` |
| Pattern count, free edge count, and unique parameter recovery | `card_pattern`, `card_free`, `makeGraph_injective`, `family_card` |
| Relabeling, bound and endpoints | `compCount_overFin`, `core_fits`, `bound_lt_iff`, `strict_comparison`, `theta_family`, `odd_order`, `lrt_conj7_fails`, `not_conjecture`, `five_vertex_counterexample` |
| Exact common factor, ratio and real limit | `bound_factor`, `cardinal_ratio`, `ratio_tendsto` |

The endpoint and axiom outputs below come from the clean rebuild. The order-three observation is included as a written remark.

```text
Theta359778.Conjecture : Prop
Theta359778.theta_family (h : ℕ) (hh : 1 ≤ h) :
  ∃ (F : Finset (SimpleGraph (Fin (6 * h - 1)))),
    Valid F ∧ #F = (1 + 6 * h + 12 * h ^ 2) * 2 ^ ((6 * h - 1).choose 2 - 6 * h) ∧ bound (6 * h - 1) < ↑(#F)
Theta359778.lrt_conj7_fails (N : ℕ) :
  ∃ n > N, Odd n ∧ ∃ (F : Finset (SimpleGraph (Fin n))), Valid F ∧ (n + 3) ^ 2 * 2 ^ n.choose 2 < 8 * 2 ^ n * #F
Theta359778.not_conjecture : ¬Conjecture
Theta359778.five_vertex_counterexample : ∃ (F : Finset (SimpleGraph (Fin 5))), Valid F ∧ #F = 304 ∧ bound 5 = 256
'Theta359778.theta_family' depends on axioms: [propext, Classical.choice, Quot.sound]
'Theta359778.lrt_conj7_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
'Theta359778.not_conjecture' depends on axioms: [propext, Classical.choice, Quot.sound]
'Theta359778.five_vertex_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
{"stage": "compile", "module": "ThetaRefutation", "argv": ["/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean", "-j1", "-M3500", "-DwarningAsError=true", "-o", "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/theta-family-359778-formal-paper-sol62-20261118-r1/build/ThetaRefutation.olean", "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/theta-family-359778-formal-paper-sol62-20261118-r1/src/ThetaRefutation.lean"], "exit": 0, "source_sha256_before": "76ab3f7cc9bb2a2793d07b87fde7c3c25a0503f09559f7074c8e89afdb961734", "source_sha256_after": "76ab3f7cc9bb2a2793d07b87fde7c3c25a0503f09559f7074c8e89afdb961734", "olean_sha256_before": null, "olean_sha256_after": "49ecb43fd0eb5f673ea10651c5796839ae59af7090ce1d538097a2b9db848d16", "LEAN_PATH": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/theta-family-359778-formal-paper-sol62-20261118-r1/build:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/batteries/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/aesop/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/Qq/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/importGraph/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/plausible/.lake/build/lib/lean", "LEAN_NUM_THREADS": 1}

Theta359778.cardinal_ratio (h c : ℕ) (hh : 1 ≤ h)
  (hc : c = (1 + 6 * h + 12 * h ^ 2) * 2 ^ ((6 * h - 1).choose 2 - 6 * h)) :
  ↑c / bound (6 * h - 1) = (1 + 6 * ↑h + 12 * ↑h ^ 2) / (3 * ↑h + 1) ^ 2
Theta359778.ratio_tendsto : Tendsto (fun h => (1 + 6 * ↑h + 12 * ↑h ^ 2) / (3 * ↑h + 1) ^ 2) atTop (𝓝 (4 / 3))
'Theta359778.cardinal_ratio' depends on axioms: [propext, Classical.choice, Quot.sound]
'Theta359778.ratio_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
{"stage": "compile", "module": "ThetaRatio", "argv": ["/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean", "-j1", "-M3500", "-DwarningAsError=true", "-o", "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/theta-family-359778-formal-paper-sol62-20261118-r1/build/ThetaRatio.olean", "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/theta-family-359778-formal-paper-sol62-20261118-r1/src/ThetaRatio.lean"], "exit": 0, "source_sha256_before": "90abc28470e507b4bb067eb89f3de6cee993ea611033df1007466292c9e5c9b9", "source_sha256_after": "90abc28470e507b4bb067eb89f3de6cee993ea611033df1007466292c9e5c9b9", "olean_sha256_before": null, "olean_sha256_after": "93784d2dba3a05a76ad576188f1d28b64a712d077bb5773daa6ded7f13f47285", "LEAN_PATH": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/theta-family-359778-formal-paper-sol62-20261118-r1/build:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/batteries/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/aesop/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/Qq/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/importGraph/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/plausible/.lake/build/lib/lean", "LEAN_NUM_THREADS": 1}
```

The [Lean source appendix](LEAN-SOURCE-APPENDIX.md) contains all modules in import order. The [verification report](REPORT.md) records the toolchain and kernel checks.

## Scope of the literature check

The bounded literature search reported by the discovery and independent review examined the arXiv statement, the thesis restatement, the earlier connected-intersecting paper [4], and the citations and keyword searches documented in those reviews, including the later difference-isomorphic paper [5]. The searches located no matching refutation. The journal versions were unread, including the journal version of [1]. This AI-produced manuscript has no human peer review.

## References

1. Imre Leader, Žarko Ranđelović and Ta Sheng Tan, *A Note on Hamiltonian-Intersecting Families of Graphs*, arXiv:2309.00757v1, 1 September 2023, §3, Conjecture 7. Published in *Discrete Mathematics* (2024), article 114160. [arXiv preprint](https://arxiv.org/abs/2309.00757)
2. MathDB 359778, *The three-component-intersection extremal conjecture for odd $n$*. [Problem record](https://mathdb.com/p/359778/the-three-component-intersection-extremal-conjecture-for-odd)
3. Žarko Ranđelović, *Some Results in Combinatorics and Combinatorial Geometry*, PhD thesis, University of Cambridge, deposited 2025, Ch. 4, Conjecture 30.
4. Aaron Berger et al., *Connected-intersecting families of graphs*, arXiv:1901.01616. [arXiv preprint](https://arxiv.org/abs/1901.01616)
5. Lior Gishboliner, Zhihan Jin and Benny Sudakov, *Difference-isomorphic graph families*, arXiv:2312.06610. [arXiv preprint](https://arxiv.org/abs/2312.06610)
