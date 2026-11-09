# 368752: undirected prefix-reversal graphs P_m(n) are not expanders in m

Status: complete elementary refutation of Blanco–Buehrle Conjecture 6.3 (arXiv:2506.08345v1), for every n ≥ 1. HIGH routine / source-ingredient risk; see Section 3. Zero credit unless root accepts.

## 1. Source definitions (arXiv:2506.08345v1, Section 2.3 and Section 6.3)

- **Vertices.** S(m, n) = C_m ≀ S_n, the colored permutations π₁^{e₁} ⋯ π_n^{e_n} with colors e_j ∈ Z_m.
- **Flips.** The i-th flip r_i⁺ reverses the prefix of length i and adds 1 to the color of each of those i entries. The flop r_i⁻ does the same but subtracts 1.
- **The graph P_m(n).** The undirected prefix-reversal graph has vertex set S(m, n) and edges {v, r v} for r ∈ R_n^± = { r_i^± : i ∈ [n] }. It is 2n-regular for m ≥ 3.
- **Expansion.** h(G) = min over S ⊆ V with |S| ≤ |V|/2 of |∂S|/|S|, where ∂S is the set of edges with exactly one end in S. This is the edge boundary, following Hoory–Linial–Wigderson.
- **Expander family.** A family is an expander family if some ε > 0 bounds h from below on all of its members.
- **Conjecture 6.3.** Given n ≥ 1, the sequence {P_m(n)}_{m>1} is an expander family.

## 2. Theorem and proof

**Theorem.** For every n ≥ 1 and every m ≥ 2n + 2,

h(P_m(n)) ≤ n(n + 1) / ⌊m/2⌋.

Hence h(P_m(n)) → 0 as m → ∞, and Conjecture 6.3 fails for every n ≥ 1.

The bound also holds with the vertex boundary, since the vertex boundary is at most the edge boundary. That covers the MathDB paraphrase, which leaves "expansion ratio" unspecified.

*Proof.*

1. **Color-sum map.** Let φ(v) = e₁ + ⋯ + e_n ∈ Z_m. A flip r_i⁺ changes exactly i colors by +1, so φ(r_i⁺ v) = φ(v) + i. Likewise φ(r_i⁻ v) = φ(v) − i.
2. **Fibers.** Each fiber of φ has m^{n−1} · n! vertices: the n! permutations, times the color vectors with a prescribed sum.
3. **The set S.** Let k = ⌊m/2⌋ and S = φ⁻¹({0, 1, …, k − 1}), using residues 0, …, m − 1. Then |S| = k · m^{n−1} · n! ≤ |V|/2.
4. **Counting exits.** An edge leaves S only along a pair (v, r) with v ∈ S and φ(rv) ∉ [0, k − 1].
   - Assume m ≥ 2n + 2, so i < k and m − k ≥ k > i.
   - For r = r_i⁺ this happens exactly when φ(v) ∈ [k − i, k − 1]: i residues.
   - For r = r_i⁻ it happens exactly when φ(v) ∈ [0, i − 1]: i residues.
5. **Bound.** Each boundary edge is counted at least once from its end in S. So

   |∂S| ≤ Σ_{i=1}^{n} 2i · m^{n−1} · n! = n(n + 1) · m^{n−1} · n!,

   and |∂S|/|S| ≤ n(n + 1)/k. ∎

**The case n = 1.** P_m(1) is the cycle C_m, already a non-expander family. That is a trivial endpoint case; the theorem covers every n.

**Numerical check.** I built P_m(n) literally from source Definition 2.1 (`scripts/prefix_check.py`, `outputs/prefix-reversal-check.json`) for (n, m) ∈ {1} × {6, 8, 12}, {2} × {6, 8, 10, 12} and {3} × {8, 10}. The measured |∂S|/|S| equals n(n + 1)/⌊m/2⌋ exactly in every case, so the bound is attained. For example, n = 3, m = 10 gives 7200/3000 = 2.4.

## 3. Prior art and routine risk (lessons 373367, 347138, 371637)

**Generic failure.** This is the classical obstruction (lesson 373367): Cayley graphs of groups with a cyclic quotient of unbounded order and a bounded generating set are never expanders. C_m ≀ S_n surjects onto Z_m through φ, and S_n has bounded index. This is the textbook abelian-quotient / Lubotzky–Weiss obstruction.

**Published-ingredient bridge.** Greaves–Zhu, arXiv:2509.09425v2 (fetched 2026-11-03), Lemma 2.5, shows:

- Spec Q(P_{m,n}) ⊇ ⊎_k Spec(2D_n + 2cos(2πk/m) E_n).
- With k = 1, λ₂(P_m(n)) ≥ λ₁(2D_n + 2cos(2π/m) E_n), which tends to λ₁(2D_n + 2E_n) = 2n.
- The Cheeger upper bound printed in the source, h ≤ √(2d(d − λ₂)), then gives h → 0.

So the refutation is a two-line bridge from a published lemma plus a source-printed inequality. Greaves and Zhu do not draw this conclusion: they settle Conjectures 6.1 and 6.2 and restate Conjecture 6.2 only. I found no paper stating that Conjecture 6.3 is false (web search 2026-11-03; Omega D5 tree at ada3bf0c contains PrefixReversal Hamiltonicity and generation files only).

**Published version.** The published journal version (Linear Algebra Appl., per the follow-up's reference [4]) was not read, because the ScienceDirect route is denied. Root should check whether Conjecture 6.3 survives there.

**Expected ruling: EXCLUDE** as a routine or generic-obstruction bridge, unless root values a recorded refutation of a live 2025 conjecture.

## 4. Lean

An UNCOMPILED draft is in `lean/368752/Refutation.lean`. Cost is moderate: wreath-product vertex type, the explicit edge relation, the fiber count of φ, and a Finset boundary count.
