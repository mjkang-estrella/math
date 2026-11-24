# A betweenness-uniform blow-up of a graph with a cut vertex: a counterexample to a conjecture of Hartman and Pokorná

MathDB 350694. Outcome: **the conjecture is false** (refuted by an explicit construction, formally verified in Lean 4 with Mathlib, kernel-checked, axioms limited to `propext`, `Classical.choice`, `Quot.sound`).

Produced with AI assistance and independent AI review; not human peer reviewed. The construction (two 5-cycles sharing a vertex, blown up with cliques and a disjoint union of cliques at the shared vertex) is from a GPT-6.1 Sol proof lane (pool 064); the 1061-vertex parameters are from the independent Claude Opus 5.5 review of that proof; the Lean formalization and this manuscript are from a separate Claude Opus 5.5 formalization lane. The final pre-listing check (definitions, independent recomputation, prior-art refresh, editorial revision) was done by a further Claude Opus 5.5 lane, i.e. by the same model family as the formalization and the review; no cross-model final check was available.

## Abstract

Hartman and Pokorná showed (Theorem 10 of their extended abstract, with the proof sketched) that no blow-up of a tree of diameter at least three is betweenness-uniform, and conjectured that the same holds for every graph of diameter at least three with a cut vertex. We give a counterexample. Let G be the wedge of two 5-cycles (order 9, diameter 4, the common vertex is a cut vertex). Replace the four neighbours of the cut vertex by K₁₀₀, the four remaining vertices by K₅, and the cut vertex by K₆₀₄ ⊔ K₈ ⊔ K₄ ⊔ 25·K₁. The resulting 1061-vertex blow-up is connected and every vertex has betweenness exactly 100. The proof is a general formula for the betweenness of a blow-up whose parts are disjoint unions of cliques, obtained from a lifting lemma for shortest paths; the formula is formalized in Lean in full generality and evaluated on the 9-vertex base. The proof's original 3176-vertex witness (value 288) is checked by the same formalization.

## 1. The conjecture and the source definitions

Source: David Hartman and Aneta Pokorná, *Constructions of betweenness-uniform graphs from trees*, arXiv:2105.06777v1 (14 May 2021), p. 6; published in *Extended Abstracts EuroComb 2021*, Trends in Mathematics 14, pp. 732–738.

**Conjecture 12 (verbatim).** "Let G be a graph of order n with diameter at least three having a vertex cut of size one. Then there are no graphs H₁, …, Hₙ such that G[H₁, …, Hₙ] is betweenness-uniform."

MathDB 350694 records the same statement ("Let G be a graph of order n with diameter at least three and having a vertex cut of size one. … There are no graphs H₁,…,Hₙ such that G[H₁,…,Hₙ] is betweenness-uniform.").

Source definitions (verbatim, p. 1–2), each followed by the Lean definition used (module `BlowupBetweennessDefinitions.lean`; `sigma`, `sigmaThrough`, `betweenness` are copied byte-for-byte from the accepted MathDB 382260 packet, only the namespace changed):

* "for a graph G = (V, E) with x ∈ V(G) we define betweenness centrality as B(x) = Σ_{{u,v} ∈ (V(G)∖{x} choose 2)} σ_{u,v}(x)/σ_{u,v}, where σ_{u,v} denotes the number of shortest paths between u and v and σ_{u,v}(x) is the number of shortest paths between u and v passing through x."

  ```lean
  noncomputable def sigma (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (v w : Fin n) : ℕ := (G.finsetWalkLength (G.dist v w) v w).card
  noncomputable def sigmaThrough (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (v w x : Fin n) : ℕ :=
    ((G.finsetWalkLength (G.dist v w) v w).filter
      (fun p => x ∈ p.support ∧ x ≠ v ∧ x ≠ w)).card
  noncomputable def betweenness (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (x : Fin n) : ℚ :=
    ∑ v, ∑ w, if v < w then (sigmaThrough G v w x : ℚ) / sigma G v w else 0
  ```
  Walks of length `dist v w` are exactly the shortest paths (`shortest_isPath`); the pairs `v < w` with `x ∉ {v, w}` are the unordered pairs of V ∖ {x}.

* "A graph is called betweenness-uniform, if the value of betweenness is the same for all vertices."

  ```lean
  def BetweennessUniform (X : SimpleGraph (Fin n)) [DecidableRel X.Adj] : Prop :=
    ∀ x y, betweenness X x = betweenness X y
  ```

* "Let G be a graph with vertex set {v₁, …, vₙ} and H₁, …, Hₙ be a set of graphs. The graph G[H₁, …, Hₙ] is defined on a vertex set obtained from V(G) via substituting each vᵢ ∈ V(G) by set of vertices V(Hᵢ) and has edge set E(G[H₁, …, Hₙ]) = ⋃ᵢ E(Hᵢ) ∪ {uv | u ∈ V(Hᵢ), v ∈ V(Hⱼ), vᵢvⱼ ∈ E(G)}."

  ```lean
  def blowUp (G : SimpleGraph (Fin n)) (π : Fin N → Fin n) (H : SimpleGraph (Fin N)) :
      SimpleGraph (Fin N) where
    Adj x y := (π x = π y ∧ H.Adj x y) ∨ G.Adj (π x) (π y)
  ```
  The vertex set is `Fin N`; `π x` is the index i of the part V(Hᵢ) containing x, and Hᵢ is the restriction of `H` to the fibre π⁻¹(i) (edges of `H` between different fibres are ignored). Every family of graphs H₁, …, Hₙ arises this way after relabelling, and `Function.Surjective π` says every Hᵢ is nonempty. The Hᵢ are arbitrary, in particular they may be disconnected: the source itself uses the edgeless graphs I_a (Observations 3 and 4, Lemma 7).

* Diameter: "We say that a graph G has diameter k if k = max_{u,v} d(u,v)." The source assumes, whenever it considers G[H₁, …, Hₙ], that "the underlying graph G has at least two vertices and is connected". Lean: `G.Connected → 3 ≤ G.diam` with Mathlib's `SimpleGraph.diam` (the maximum distance; 0 for a disconnected graph).

* A vertex cut of size one:
  ```lean
  def HasCutVertex (G : SimpleGraph (Fin n)) : Prop := ∃ c, ¬ (G.induce {v | v ≠ c}).Connected
  ```

The formal conjecture and the endpoint (module `BlowupWitness.lean`):

```lean
def Conjecture12 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.Connected → 3 ≤ G.diam → HasCutVertex G →
    ∀ (N : ℕ) (π : Fin N → Fin n) (H : SimpleGraph (Fin N)) [DecidableRel H.Adj],
      Function.Surjective π → ¬ BetweennessUniform (blowUp G π H)

theorem hartman_pokorna_conj12_false :
    ¬ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        G.Connected → 3 ≤ G.diam → HasCutVertex G →
        ∀ (N : ℕ) (π : Fin N → Fin n) (H : SimpleGraph (Fin N)) [DecidableRel H.Adj],
          Function.Surjective π → ¬ BetweennessUniform (blowUp G π H)
```

Restricting to nonempty Hᵢ only weakens the conjecture, so refuting this formal version refutes the source's statement. The other hypotheses are not looser than the source's: under `G.Connected`, `3 ≤ G.diam` says the maximum distance is at least 3 (so n ≥ 4), and then `HasCutVertex G` says that deleting some vertex c leaves a nonempty graph that is disconnected, i.e. {c} is a vertex cut of size one. (For n = 1 the Lean predicate `HasCutVertex` would hold vacuously, because Mathlib's `Connected` requires a nonempty vertex type, but such graphs are excluded by `3 ≤ G.diam`.) In any case the witness below is a concrete graph that satisfies the source's hypotheses literally. The endpoint is character-for-character the endpoint required by the independent review (REVIEW-350694.md §5); see REPORT.md for the comparison.

## 2. The counterexample

**Base graph.** G is the wedge of two 5-cycles c–A₁–B₁–D₁–E₁–c and c–A₂–B₂–D₂–E₂–c (in Lean: vertices 0, 1–4, 5–8 of `Fin 9`, ten listed edges). Deleting c leaves two disjoint paths, so c is a cut vertex; d(B₁, B₂) = 4 and every distance is at most 4, so G has diameter 4.

**Parts.** H_{Aᵢ} = H_{Eᵢ} = K₁₀₀, H_{Bᵢ} = H_{Dᵢ} = K₅ (i = 1, 2), and H_c = K₆₀₄ ⊔ K₈ ⊔ K₄ ⊔ 25·K₁ (641 vertices). The blow-up X has 4·100 + 4·5 + 641 = 1061 vertices.

**Theorem.** X is connected and every vertex of X has betweenness 100. In particular X is betweenness-uniform and Conjecture 12 is false.

The same argument shows that the 3176-vertex graph of the original proof (A, E parts K₂₈₈, B, D parts K₂₄, centre K₁₈₈₂ ⊔ K₄₁ ⊔ K₃ ⊔ K₁ ⊔ K₁) is betweenness-uniform with value 288; scaling all clique sizes by t gives an infinite family (value 288t). Only the t = 1 case is formalized.

## 3. Proof

Throughout, X = G[H₁, …, Hₙ] with G connected, every vertex of G having a neighbour, every part nonempty, and every Hᵢ a disjoint union of cliques (a *cluster graph*: x ~ y in Hᵢ iff x ≠ y and x, y lie in the same clique). Write mᵢ = |V(Hᵢ)|, π(x) for the part of x, and d, d_G for distances in X and G.

### 3.1 Distances in X

**Lemma 1.** For x ≠ y in X: if π(x) ≠ π(y) then d(x, y) = d_G(π(x), π(y)); if π(x) = π(y) then d(x, y) = 1 when x, y lie in the same clique and d(x, y) = 2 otherwise.

*Proof.* Call the right-hand side D(x, y) (with D(x, x) = 0). A function D with D(x, x) = 0, D(x, y) ≤ D(w, y) + 1 for every edge xw, and, for x ≠ y, some neighbour w of x with D(w, y) = D(x, y) − 1, equals the graph distance: the descending neighbours build a walk of length D(x, y), and the Lipschitz condition shows by induction along any walk that D(x, y) is at most its length. Both conditions for X follow from the same conditions for d_G by checking the cases (x, w in the same part or in adjacent parts; y in the part of x, of w, or elsewhere). For the descent between different cliques of one part, use any vertex of a neighbouring part (it exists because every base vertex has a neighbour and parts are nonempty). ∎

(Lean: `dist_eq_of_potential` in `BlowupWalkCounting.lean`, `distX_cert` in `BlowupCluster.lean`.)

### 3.2 Counting shortest paths (the lifting lemma)

In any connected graph, for u ≠ v the shortest u–v paths are counted by their second vertex:

  σ(u, v) = Σ_{w ~ u, d(w, v) = d(u, v) − 1} σ(w, v),   (R)

and for z ∉ {u, v}, splitting a shortest path at z gives

  σ_{u,v}(z) = σ(u, z)·σ(z, v) if d(u, z) + d(z, v) = d(u, v), and 0 otherwise.   (S)

(R) follows from counting walks of length k + 1 by their first step (Lean: from Mathlib's adjacency-matrix walk count) and the fact that there are no walks shorter than the distance; (S) is the bijection p ↦ (p up to z, p after z), whose inverse is concatenation; concatenation is injective when the first factors have equal length.

**Lemma 2 (lifting).** Let F be a function on pairs of base vertices with, for i ≠ j, F(i, j) = 1 if d_G(i, j) = 1 and otherwise

  F(i, j) = Σ_{k ~ i, d_G(k, j) = d_G(i, j) − 1} m_k F(k, j).

Then σ(x, y) = F(π(x), π(y)) whenever π(x) ≠ π(y). If π(x) = π(y) and x, y lie in different cliques, then σ(x, y) = W(π(x)), where W(i) = Σ_{k ~ i} m_k.

*Proof.* Induction on d_G(π(x), π(y)) using (R) and Lemma 1. When d_G(π(x), π(y)) ≥ 2, a neighbour w of x with d(w, y) = d(x, y) − 1 cannot lie in the part of x (it would have the same distance to y) nor in the part of y (that part is not adjacent to π(x)); so w runs over the vertices of the parts k ~ π(x) with d_G(k, π(y)) = d_G(π(x), π(y)) − 1, each contributing F(k, π(y)), and grouping the sum by parts gives the recursion for F. For two vertices of one part in different cliques the shortest paths have length 2 and their middle vertices are exactly the vertices of the neighbouring parts (no vertex of the same part is adjacent to both). ∎

If every pair of base vertices has a unique geodesic, F(i, j) is the product of the part sizes of the inner vertices of that geodesic; Lemma 2 is the statement that shortest paths of X project to base geodesics and choose one vertex in each inner part. Lean does not use uniqueness: F is any table satisfying the recursion, checked by evaluation on the base. (Lean: `sigma_rec`, `sigmaThrough_eq` in `BlowupWalkCounting.lean`; `sigmaX_cross`, `sigmaX_same` in `BlowupCluster.lean`.)

### 3.3 The betweenness formula

**Theorem 3.** For a vertex z of X with k = π(z),

  B(z) = ½ [ Σ_{i ≠ j, i ≠ k, j ≠ k} mᵢ mⱼ T(i, j, k) + Σ_{i ~ k} Pᵢ / W(i) ],

where T(i, j, k) = F(i, k) F(k, j) / F(i, j) if d_G(i, k) + d_G(k, j) = d_G(i, j) and 0 otherwise, and Pᵢ is the number of ordered pairs of vertices of Hᵢ lying in different cliques.

*Proof.* Since σ and σ(·)(z) are symmetric, B(z) is half the sum over ordered pairs (u, v), u ≠ v, of σ_{u,v}(z)/σ(u, v); by (S) each term is σ(u, z)σ(z, v)/σ(u, v) when u, v ≠ z and d(u, z) + d(z, v) = d(u, v), and 0 otherwise. Classify the pairs with Lemma 1 and Lemma 2:
* π(u) ≠ π(v), both different from k: the term is T(π(u), π(v), k).
* π(u) ≠ π(v), one of them equal to k, say π(u) = k: then d(z, v) = d(u, v) and d(u, z) ≥ 1, so the term is 0.
* π(u) = π(v) = k: d(u, z) + d(z, v) = d(u, v) ≤ 2 would force u, z and z, v into common cliques, hence u, v into one clique and d(u, v) = 1; the term is 0.
* π(u) = π(v) = i ≠ k: d(u, z) = d(z, v) = d_G(i, k) ≥ 1, so the term is nonzero only if d_G(i, k) = 1 and u, v lie in different cliques; then it equals 1·1/W(i).
Summing over vertices part by part (Σ_u g(π(u)) = Σᵢ mᵢ g(i)) gives the formula. ∎

(Lean: `summand_eq` and `betweenness_blowUp_cluster` in `BlowupFormula.lean`, stated for an arbitrary base, arbitrary part map and arbitrary clique labelling.)

### 3.4 Evaluation on the witness

Let a = 100 (parts Aᵢ, Eᵢ), b = 5 (parts Bᵢ, Dᵢ), s = 641 (centre). All base geodesics are unique; the only nonzero local term is P_c = s² − (604² + 8² + 4² + 25·1²) = 410881 − 364921 = 45960, i.e. M = 22980 unordered pairs in different centre cliques, each with W(c) = 4a = 400 common neighbours.

* z in the centre: the unordered base pairs whose geodesic passes through c are all cross-wing pairs ((2a + 2b)² = 44100 endpoint pairs) and the pairs {Aᵢ, Eᵢ} (2a² = 20000); B(z) = 64100/641 = 100. The neighbours of c are cliques, so there is no local term.
* z in A₁ (similarly E₁, A₂, E₂): the pair {c, B₁} (s·b = 3205) and the cross-wing pairs with endpoint B₁ (b·(2a + 2b) = 1050) give 4255/100 = 42.55; the local pairs of the centre give M/(4a) = 22980/400 = 57.45; B(z) = 100.
* z in B₁ (similarly D₁, B₂, D₂): only the pair {A₁, D₁} (a·b = 500) gives 500/5 = 100.

In Lean the part sizes and P are computed from the class description of the vertex set (36 cliques; a sum over the 1061 vertices is turned into a sum over cliques through `finSigmaFinEquiv`), the table F and the nine values of the formula of Theorem 3 are evaluated by `decide` on the 9-vertex base (`BlowupWitness.lean`: `fibre_sizes`, `cross_pairs`, `walk_counts`, `values`). No computation ever enumerates the 1061 vertices.

Finally X is connected (Lemma 1), every part is nonempty, G is connected with diameter 4 and cut vertex c; hence G satisfies the hypotheses of Conjecture 12 and G[H₁, …, H₉] is betweenness-uniform. ∎

### 3.5 Checks of the definitions

Using the same general theorem, Lean proves (`BlowupGuards.lean`): every vertex of C₅ (Mathlib's `cycleGraph 5`) has betweenness 1; in P₃ (`pathGraph 3`) the middle vertex has betweenness 1 and the ends 0, so P₃ is not betweenness-uniform; and the source's Observation 3: P₃[K₁, I₂, K₁] is a 4-cycle (explicit relabelling to `cycleGraph 4`) and is betweenness-uniform with value 1/2. These fix the normalization (unordered pairs, no factor 2) and show the uniformity predicate is not trivially true.

## 4. Formal verification

Lean 4.34.1, Mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612, ten modules (1388 lines), specific Mathlib imports only. The complete source is in LEAN-SOURCE-APPENDIX.md (byte-identical to `src/`). Each module was compiled and checked by the standalone kernel checker `leanchecker`; a fresh replay from the appendix reproduced identical `.olean` files. The endpoint `BlowupBetweenness.hartman_pokorna_conj12_false` and every auxiliary endpoint depend only on `propext`, `Classical.choice`, `Quot.sound`. There is no `sorry`, `admit`, `axiom`, `unsafe` or `native_decide`; finite checks use `decide` (kernel reduction) on the 9-vertex base, the 36 clique classes and the small guard graphs.

| Module | Content |
|---|---|
| BlowupBetweennessDefinitions | 382260 definitions of σ, σ(x), B; blow-up, cluster graph, cut vertex, uniformity, the conjecture |
| BlowupWalkCounting | distance certificates; recursion (R); symmetry; splitting formula (S); half-sum form of B |
| BlowupCluster | distances in cluster blow-ups (Lemma 1); lifting lemma (Lemma 2) |
| BlowupFormula | Theorem 3 |
| BlowupClasses | vertex sets `Fin (Σ sizes)` built from clique classes; class sums |
| BlowupWedgeBase | the two-C₅ base: distances, connectivity, diameter 4, cut vertex, formula specialised |
| BlowupWitness | the 1061-vertex witness; the endpoint |
| BlowupWitness3176 | the original 3176-vertex witness (value 288), supplementary |
| BlowupGuards | C₅, P₃, P₃[K₁, I₂, K₁] |
| BlowupAudit | statement equality with the conjecture, witness summary, printed definitions and axioms |

## 5. Significance

The conjecture asked whether the source's theorem for trees (no betweenness-uniform blow-up when the diameter is at least 3) extends to all graphs with a cut vertex. It does not. The obstruction for trees comes from leaves, whose parts carry no global betweenness; in the two-C₅ wedge every part lies on a cycle and carries global load, and a part of the cut vertex that is a disjoint union of cliques adds load only to the neighbouring parts, so the number of non-adjacent pairs in that part is a free parameter that balances the equations. The resolution is negative and elementary: an explicit graph and exact path counting. The conjecture appears only in a seven-page extended abstract that has, as far as we can tell, no citing papers; the result answers a question of modest visibility. The ingredients are known: clique inflation and disjoint-clique substitutes appear in Gago, Coroničová Hurajová and Madaras 2013 (Theorems 3.1–3.2; the proof of Theorem 3.2 already contains the observation that the non-adjacent pairs of a disjoint-clique substitute contribute only to the vertices of the neighbouring substitutes), the same paper computes the clique blow-ups of C₅ (Theorem 3.5), and the geodesic-lifting count is standard. A specialist could reasonably regard the construction as a clever but routine combination of them. What is new is using a disjoint-clique substitute at one vertex only, with its number of non-adjacent pairs as a free parameter, to balance an otherwise unbalanced base. Against the "routine" reading: the source's own analysis points to clique and edgeless parts, with which (as the review found) the symmetric two-C₅ family has no solution; exhaustive searches by the review over all cut-vertex bases of order at most 7 with small part sizes found no witness; and within the sub-family used here (cliques at the eight non-central vertices, a symmetric choice of sizes, a disjoint union of cliques at the centre) the uniformity equations force s = 6a + 8b + 4b²/a and M = 4a² − 4bs − 8ab − 8b², and the smallest order realisable by an actual partition of the centre is 1061 (orders 397, 562, 689 and 794 solve the equations but are not realisable; re-derived independently in the final check). We make no global minimality claim. The counterexample uses a disconnected part at the cut vertex, which the source's definition allows; whether the conjecture holds when all Hᵢ are required to be connected, and the source's Problem 11 (characterize the graphs with a betweenness-uniform blow-up), remain open as far as we know.

## 6. Prior art (from the independent review, 2026-11-20)

The arXiv record of 2105.06777 has only v1 and no journal reference; the published EuroComb 2021 chapter contains Conjecture 12 unchanged. OpenAlex (W3163396507) lists one citation (the EuroComb volume itself) and Semantic Scholar none. An extended web search found only the source and the authors' other betweenness papers (Hartman–Pokorná–Valtr, arXiv:2109.10594, on connectivity and diameter of betweenness-uniform graphs; Ghanbari et al., arXiv:2401.00347, on low values), neither of which treats blow-ups of cut-vertex bases; Gago–Hurajová–Madaras 2013 has general blow-up tools but no cut-vertex result. The Omega registry, its issues and pull requests (queries "2105.06777", "betweenness-uniform", "betweenness blow-up", "Hartman Pokorna", "350694") and the Principia list showed no resolution. The campaign's accepted MathDB 382260 concerns a different conjecture (betweenness-uniform graphs with value below 1). A refresh on 2026-11-20 (final check) found nothing new: OpenAlex still lists only the EuroComb volume as citing W3163396507, Semantic Scholar has no citations of arXiv:2105.06777, Crossref reports 0 citations of the chapter (DOI 10.1007/978-3-030-83823-2_117); a web search turned up only the source, its mirrors, arXiv:2401.00347 and its EuroComb 2023 extended abstract (Ghanbari, Hartman, Jelínek, Pokorná, Šámal, Valtr, on low betweenness values; no blow-ups); the Omega registry's issues and pull requests and GitHub code search (the arXiv id, "MathDB 350694") gave no hits; the Principia list and backup, and the mio-qwq and openai/math clones, contain nothing on this conjecture. This is a bounded search and not a worldwide-priority claim.

## References

1. D. Hartman, A. Pokorná, Constructions of betweenness-uniform graphs from trees, arXiv:2105.06777 (2021); Extended Abstracts EuroComb 2021, Trends in Mathematics 14, Birkhäuser, 2021, pp. 732–738, doi:10.1007/978-3-030-83823-2_117.
2. S. Gago, J. Coroničová Hurajová, T. Madaras, On betweenness-uniform graphs, Czechoslovak Math. J. 63 (2013) 629–642.
3. D. Hartman, A. Pokorná, P. Valtr, On the connectivity and the diameter of betweenness-uniform graphs, arXiv:2109.10594; in: Algorithms and Discrete Applied Mathematics (CALDAM 2021), Springer, 2021, pp. 317–330.
4. B. Ghanbari, D. Hartman, V. Jelínek, A. Pokorná, R. Šámal, P. Valtr, Structure of betweenness uniform graphs with low values of betweenness centrality, arXiv:2401.00347; extended abstract in Proc. EUROCOMB'23, doi:10.5817/CZ.MUNI.EUROCOMB23-066.
