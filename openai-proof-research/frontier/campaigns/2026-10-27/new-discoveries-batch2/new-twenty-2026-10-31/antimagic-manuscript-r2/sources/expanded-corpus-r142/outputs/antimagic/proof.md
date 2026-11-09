# MathDB 354228: the local antimagic chromatic number of complete full t-ary trees with t even

Status: ordinary proof written by the r142 lane on 2026-11-04 (UTC). It is not yet independently reviewed, it has no Lean certificate, and no credit is claimed. The construction is implemented in `scripts/antimagic/construct.py`. The independent checker `scripts/antimagic/check.py` verified it in 84 cases with t from 2 to 60 and up to 32 766 edges (`outputs/antimagic/check-r2.jsonl`). Those runs are diagnostics, not part of the proof.

## Source and exact statement

Source: M. Bača, A. Semaničová-Feňovčíková, R.-T. Lai and T.-M. Wang, "On local antimagic vertex coloring for complete full t-ary trees", arXiv:2204.04479v2 (14 April 2022), published in Fundamenta Informaticae 185(2) (2022), 99–113. The source's Section 6, first "Conjecture 6.0" (called Conjecture 6 in its text), reads: "For any complete full t-ary tree T, t ≥ 2 even, χ_la(T) = l + 1, where l is the number of degree one vertices (leaves) of T."

MathDB 354228 (corpus chunk 0003, line 3529) states the same thing: for every even integer t ≥ 2, χ_la(T) = l + 1.

Source definitions (Definitions 1.1 to 1.4):

- G = (V, E) is a finite simple graph without K_2 components.
- A bijection f : E → {1, …, |E|} is a local antimagic labeling if w(u) ≠ w(v) for every edge uv. Here w(u) = Σ_{e ∋ u} f(e).
- The induced colouring is v ↦ w(v).
- χ_la(G) is the minimum number of colours used by the colourings induced by local antimagic labelings of G.
- A complete full t-ary tree is a rooted tree in which every nonleaf has exactly t children and every leaf has the same depth.

We write T(t, n) for the complete full t-ary tree with n ≥ 1 levels. Its rows are V_0 = {root}, V_1, …, V_n with |V_h| = t^h. E_h is the set of t^h edges between V_{h−1} and V_h. The tree has m = t + t² + … + t^n edges and l = t^n leaves (the vertices of V_n). The depth-0 tree is a single vertex: it has no edges and is outside the source's scope.

## Theorem

For every even t ≥ 2 and every n ≥ 1, χ_la(T(t, n)) = t^n + 1 = l + 1.

The source proves the odd case (its Theorem 4.1). Together with this theorem, χ_la(T(t, n)) = l + 1 holds for every t ≥ 2.

## 1. Lower bound

Every local antimagic labeling f of T = T(t, n) uses at least l + 1 colours.

A leaf v has exactly one incident edge, so w(v) = f(e(v)). Distinct leaves have distinct edges, so the leaves already use l distinct colours, each at most m.

Let g be the edge with f(g) = m. It joins some u ∈ V_{h−1} to a child in V_h. The vertex u has at least t ≥ 2 incident edges, all with positive labels. Hence w(u) > m, so w(u) differs from every leaf colour. This gives at least l + 1 colours. ∎

The source cites this as Theorem 1.2 of its reference [3]. The proof is included here so that the argument is self-contained.

## 2. Upper bound: constructions

In every case below we exhibit a bijection f : E → [1, m] for which:

- the colouring w is proper, and
- every non-leaf vertex has a colour that is either a leaf-edge label or a single extra value c.

The colour set is then {leaf labels} ∪ {c}. It has exactly l + 1 elements: c is attained and is not a leaf label. (In case 2.1 the root colour is a value not used at a leaf, and it plays the role of c.)

### 2.1 Case n = 1

T is the star K_{1,t}. Take any bijection. The leaves get the colours 1, …, t. The root gets t(t+1)/2 > t, so the colouring is proper. It uses t + 1 colours.

### 2.2 Case n = 2, t = 2

Label the root edges 1 (to a) and 4 (to b). Label a's leaf edges 2 and 3, and b's leaf edges 6 and 5.

- The colours are w(root) = 5, w(a) = 6 and w(b) = 15. The leaves get 2, 3, 6 and 5.
- The colouring is proper: 5 ≠ 6 and 5 ≠ 15; 6 differs from 2 and 3; 15 differs from 6 and 5.
- The colour set is {2, 3, 5, 6, 15}, which has 5 = l + 1 elements.

### 2.3 Case n = 2, t ≥ 4

Let s = t/2 and M = m = t + t².

**Label sets.**

- Root edges: the edge to x* gets label 2. The edge to x_i gets ρ_i = 3s + 2 − i for 1 ≤ i ≤ t − 1. So R′ = {ρ_i} = [s+3, 3s+1].
- Leaf edges of x*: S* = {1} ∪ [3, s+2] ∪ [3s+2, 4s].
- B = [2t+1, M] is a run of t(t−1) consecutive integers.

The sets {2}, R′ and S* partition [1, 4s] = [1, 2t]. Together with B they partition [1, M].

**Sums.**

- Σ({2} ∪ R′) = 2 + (2s − 1)(2s + 2) = 4s² + 2s = t² + t = M.
- So ΣS* = 2s(4s + 1) − M = t².

**Tuple lemma (source Lemma 2.13 with Lemma 2.2, made explicit).** Let n′ = t − 1 = 2κ + 1, which is odd. Split B into t consecutive blocks of n′ elements each.

- For each b ≤ s − 1, pair the j-th element of block b with the (n′ + 1 − j)-th element of block t + 1 − b. Each such pair has the same sum, independent of j.
- The two middle blocks together form a run [β + 1, β + 4κ + 2]. Pair it as follows: (β + 2i + 1, β + 3κ + 2 − i) for 0 ≤ i ≤ κ, and (β + 2i, β + 4κ + 3 − i) for 1 ≤ i ≤ κ. These are pairs of a partition of the run, and their sums are 2β + 3κ + 3, …, 2β + 5κ + 3, which are consecutive.

Hence B splits into t − 1 t-tuples τ_1, …, τ_{t−1} with Στ_i = Γ + i for consecutive values of i.

**Assignment.** Give x_i the root label ρ_i and the leaf tuple τ_i. Give x* the root label 2 and the leaf labels S*.

**Colours.**

- w(x_i) = ρ_i + Γ + i = Γ + 3s + 2 =: c for every i.
- w(x*) = 2 + t².
- w(root) = M.
- The leaves carry the labels in S* ∪ B.

Every value t² + 2 and M lies in B = [2t+1, t² + t]. Also c > Στ_i ≥ t(2t+1) > M, so c is not a label. The colour set is therefore (S* ∪ B) ∪ {c}, of size t² + 1.

**Properness.**

- M ≠ t² + 2 because t ≠ 2.
- M < c.
- t² + 2 > 2t ≥ max S*, so x* differs from its leaves.
- c > M ≥ every label, so each x_i differs from its leaves.

### 2.4 Case n ≥ 3 (any even t ≥ 2)

**Notation.**

- N = t + t² + … + t^{n−1} is the number of internal edges.
- q = t^{n−1} = |V_{n−1}| and k = q/2.
- m = N + tq.
- R = (N − t)/2, which is an integer because N − t = t² + … + t^{n−1} is even.
- Z = R + 1.

**(a) Leaf labels.** E_n receives the top block Λ = [N+1, m]. The internal edges receive [1, N].

**(b) Shells around Z.** For 1 ≤ d ≤ R let π_d = {Z − d, Z + d}. These are disjoint pairs that cover [1, N−t+1] \ {Z}, because Z − R = 1 and Z + R = N − t + 1.

Split [1, R] into consecutive ranges:

- D_{n−1} = [1, k];
- then D_{n−2}, D_{n−3}, …, D_2, with |D_h| = t^h/2.

The total size is Σ_{h=2}^{n−1} t^h/2 = R. Put A_h = ⋃_{d ∈ D_h} π_d for 2 ≤ h ≤ n − 1, so |A_h| = t^h. Put A_1 = {Z} ∪ [N−t+2, N]. Then A_1, …, A_{n−1} partition [1, N], and E_h receives A_h.

**(c) Children sums.** For 1 ≤ h ≤ n − 2, split D_{h+1} into t^h groups of t/2 distances, one group per vertex u ∈ V_h. Give the t child edges of u the labels ⋃_{d in u's group} π_d. Each pair π_d sums to 2Z, so the children of every u ∈ V_h carry a total label of tZ. The labels of E_1 (the set A_1) are placed on the root's children; the order matters only when t = 2 (see (g)).

**(d) Leaf tuples.**

Define σ on [1, q] by σ(a) = 2a for a ≤ k and σ(k + j) = 2j − 1 for 1 ≤ j ≤ k. Then σ is a bijection: the first part maps onto the even numbers and the second part onto the odd numbers. Its displacement δ(a) = a − σ(a) takes the value −a for a ≤ k and k + 1 − j for a = k + j. So δ is a bijection from [1, q] onto {±1, …, ±k}.

Split Λ into blocks Λ_b = [N + (b−1)q + 1, N + bq] for 1 ≤ b ≤ t, and write λ_b(a) = N + (b−1)q + a. Put

T_a = {λ_b(a), λ_{t+1−b}(q+1−a) : 1 ≤ b ≤ t/2 − 1} ∪ {λ_{t/2}(a), λ_{t/2+1}(q + 1 − σ(a))}.

The sets T_a partition Λ, because a ↦ q + 1 − a and σ are bijections. Each outer pair sums to 2N + tq + 1. The middle pair sums to 2N + tq + 1 + δ(a). Hence ΣT_a = Γ + δ(a) with Γ = (t/2)(2N + tq + 1).

Each u ∈ V_{n−1} has a label Z + ε with ε ∈ {±1, …, ±k}, since A_{n−1} = ⋃_{d ≤ k} π_d. Give its t leaf edges the tuple T_a with δ(a) = −ε. This uses every tuple exactly once, and

w(u) = Z + ε + Γ − ε = Γ + Z =: c for every u ∈ V_{n−1}.

Moreover c > m, since Γ ≥ 2N + tq + 1 > m.

**(e) Colours for t ≥ 4.**

- A leaf's colour is its label, which lies in Λ.
- Every u ∈ V_{n−1} has colour c.
- A vertex u ∈ V_h with 1 ≤ h ≤ n − 2 has colour w(u) = f(e(u)) + tZ ∈ tZ + A_h.
- The root has colour ΣA_1 = Z + (t−1)N − (t−1)(t−2)/2.

Range checks:

- tZ ≥ N holds because it is equivalent to (t/2 − 1)(N − t) ≥ 0.
- tZ + N ≤ m is equivalent to Z ≤ q. This holds because N − t = t^{n−1} + Σ_{j=2}^{n−2} t^j ≤ t^{n−1} + (t^{n−1} − t²) ≤ 2t^{n−1} − 2.
- Hence every colour in rows 1 to n − 2 lies in [tZ + 1, tZ + N] ⊆ [N+1, m] = Λ.
- The root colour lies between N + 1 and tN < m.

So the non-leaf colours lie in Λ ∪ {c}. The number of colours is |Λ| + 1 = l + 1.

**(f) Properness for t ≥ 4.**

- A leaf versus its parent: c > m.
- V_{n−1} versus V_{n−2}: the colour c versus colours ≤ m.
- V_{h+1} versus V_h for 1 ≤ h ≤ n − 3: the colours lie in tZ + A_{h+1} and tZ + A_h, which are disjoint because A_h ∩ A_{h+1} = ∅.
- The root versus V_1: w(root) − tZ = (t−1)(N − Z − (t−2)/2) = (t−1)N/2 > N ≥ max A_1. So w(root) ∉ tZ + A_1.

**(g) Modification for t = 2.** Here N = 2^n − 2, Z = N/2, R = Z − 1, A_1 = {Z, N}, D_2 = {R−1, R}, and m = 4Z + 2. Let x_Z and x_N be the root's children with labels Z and N.

Instead of the plain pairs, give x_Z the child labels {Z − R + 1, Z + R} = {2, 2Z − 1}, and give x_N the child labels {Z − R, Z + R − 1} = {1, 2Z − 2}. Everything else is as in (b) to (d).

- Colours: w(root) = 3Z, w(x_Z) = 3Z + 1 and w(x_N) = 4Z − 1. All three lie in [2Z + 1, 4Z + 2] = Λ.
- Root against row 1: 3Z ≠ 3Z + 1, and 3Z ≠ 4Z − 1 because Z ≥ 3.
- Row 1 against row 2 when n ≥ 4: the row-2 colours are the labels plus 2Z, that is 2Z + 2, 4Z − 1, 2Z + 1 and 4Z − 2.
  - x_Z's children have colours 2Z + 2 and 4Z − 1. These differ from 3Z + 1 because Z ∉ {1, 2}; here Z = 2^{n−1} − 1 ≥ 7.
  - x_N's children have colours 2Z + 1 and 4Z − 2. These differ from 4Z − 1.
- Row 1 against row 2 when n = 3: the row-2 vertices have colour c.
- All other comparisons are as in (f).

So χ_la(T(t, n)) ≤ l + 1 in every case. With Section 1 this proves the theorem. ∎

## Remarks on the proof and on prior art

- The obstruction in the source is the parity fact (Lemma 2.15) that t-tuples with consecutive sums cannot exist when both t and the number of tuples are even. The source's level n − 1 labels form a consecutive block, so the second-last row receives two colours there. The construction above avoids this by making the level n − 1 labels symmetric with a hole at Z (the set A_{n−1}). The displacement permutation σ then makes all second-last-row colours equal. The nested shells around Z make every row from 1 to n − 2 a translate of a disjoint label set by the same amount tZ. This gives properness without any case analysis.
- The case n = 2 uses the source's Lemma 2.13 with Lemma 2.2, made explicit, together with a new choice of root and x* labels. The case n ≥ 3 does not use the source's level scheme.
- A prior-art search on 2026-11-04 found no later resolution of the even case. It covered web search, the citing preprint arXiv:2610.22783 (which disproves the general tree "leaf conjecture" but treats only odd t for full trees), the Omega registry at HEAD 3bb89bf7 (complete Problems listing and the D5/S3/Combinatorics subtree) and OpenAI/math at HEAD 4eaee875. This is not an exhaustive literature review.
