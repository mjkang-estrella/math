# A cube-root construction refuting the exact rainbow-saturation formula of Chakraborti, Hendrey, Lund and Tompkins

MathDB 381790. Mathematical construction and written proof: GPT-6.1 Sol (`t1-pool055-proof-sol61-20261120-r1/PROOF-381790.md`). Independent review: Claude Opus 5.5 (`t1-prelean-X36-opus-20261120-r1/REVIEW-381790.md`). Lean formalization: stage 1 and stage 2 by GPT-6.1 Sol, completed in stage 3 by Claude Opus 5.5 (this packet). All results stated as theorems below are kernel-checked in Lean 4.34.1 with Mathlib, using only the axioms `propext`, `Classical.choice` and `Quot.sound`, except where a statement is explicitly marked as quoted from the source.

## Abstract

Chakraborti, Hendrey, Lund and Tompkins conjectured that for every k ≥ 4 the rainbow-saturation coefficient satisfies α_{k+2} = f(k) = k + ⌈(−1+√(4k−3))/2⌉, where f(k) is the least order of an edge-coloured graph in an explicit class \hat F_k. We show that f(t³+2) ≤ t³+3t for every t ≥ 2. For t = 8 this gives f(514) ≤ 536, whereas the formula gives 537; for every t ≥ 8 the formula fails at k = t³+2. A variable-core version of the construction gives f(k) ≤ k + 3⌈(k−2)^{1/3}⌉ for every k ≥ 4. With the source's lower bound (its Lemma 3.10), this shows f(k) − k = Θ(k^{1/3}). All of these statements, except the quoted lower bound, are proved in Lean.

## 1. The source statement and definitions

Debsoumya Chakraborti, Kevin Hendrey, Ben Lund and Casey Tompkins, *Rainbow saturation for complete graphs*, arXiv:2212.04640 (v1 2022-12-09, v2 2024-03-19; SIAM J. Discrete Math. 38(1) (2024) 1090–1112). Quotations are from the v2 text cached at `t1-pool055-proof-sol61-20261120-r1/sources/rainbow.txt` (SHA256 `9a8ee9c2…eaf`, line numbers in `source-evidence.txt`).

Colour convention (line 151):

> In this paper, we focus on rainbow saturation problems in the setting of edge-colored graphs with infinitely many allowed colors (for concreteness, we can take the set of colors to be the set of natural numbers).

Rainbow copies (line 147):

> a rainbow copy of a graph H (denoted \mathcal{R}(H)) is a graph isomorphic to H whose edges are all assigned distinct colors.

Section 3.1 (lines 306–313):

> Given a positive integer k, let \hat{\mathcal{F}}_k be the class of all edge-colored graphs Γ satisfying the following properties.
> 1. Γ does not contain \mathcal{R}(K_{k+1}),
> 2. for each v ∈ V(Γ), the edge-colored graph induced by V(Γ)∖{v} contains \mathcal{R}(K_k), and
> 3. for every color c, Γ contains a \mathcal{R}(K_k) that does not use c.
>
> Define f(k) to be the smallest integer such that there exists an edge-colored f(k)-vertex graph in \hat{\mathcal{F}}_k.

Conjecture 5.1 (lines 698–699):

> For every k ≥ 4, α_{k+2} = f(k) = k + ⌈(−1+√(4k−3))/2⌉.

The source's Theorem 1.3 defines α_r through sat(n, R(K_r)) = α_r(n − α_r) + β_r for large n and proves (r−2) + (1/2)(r−2)^{1/3} − 1/2 ≤ α_r ≤ (r−2) + √(r−1). It then says (line 342) that Lemma 3.3 "shows that the constant α_r in Theorem 1.3 is always equal to f(r−2)", and Lemma 3.10 (lines 485–487) states: "For each positive integer k, we have f(k) ≥ k + (1/2)k^{1/3} − 1/2." The authors write (line 168): "We believe that the value of α_r is closer to the upper bound."

The conjecture is a conjunction over k ≥ 4 of α_{k+2} = f(k) and f(k) = formula. We refute the second conjunct, so the conjecture is false whatever α is; no formalization of α is needed.

## 2. The Lean definitions

The definitions are those of the review's "Required Lean endpoint" (section 5), with one change to the palette described in section 3.

```lean
structure ECGraph (V C : Type) where
  G : SimpleGraph V
  col : Sym2 V → C

def RainbowCliqueIn {V C : Type} (Γ : ECGraph V C) (S : Set V)
    (m : ℕ) (avoid : C → Prop) : Prop :=
  ∃ s : Finset V, (↑s ⊆ S) ∧ s.card = m ∧ (s : Set V).Pairwise Γ.G.Adj ∧
    Set.InjOn Γ.col {e | e ∈ s.sym2 ∧ ¬ e.IsDiag} ∧
    ∀ e ∈ s.sym2, ¬ e.IsDiag → ¬ avoid (Γ.col e)

def InHatF {V C : Type} (k : ℕ) (Γ : ECGraph V C) : Prop :=
  ¬ RainbowCliqueIn Γ Set.univ (k+1) (fun _ => False) ∧
  (∀ v, RainbowCliqueIn Γ {v}ᶜ k (fun _ => False)) ∧
  (∀ c : C, RainbowCliqueIn Γ Set.univ k (· = c))

noncomputable def f (k : ℕ) : ℕ :=
  sInf {n | ∃ Γ : ECGraph (Fin n) ℕ, InHatF k Γ}

def conjFormula (k : ℕ) : ℤ :=
  k + ⌈(-1 + Real.sqrt (4 * (k : ℝ) - 3)) / 2⌉
```

How these match the source:

- An edge-coloured graph is a simple graph with a colour on each edge. `col` is total on unordered pairs, but only its values on edges inside cliques are ever read. Any source colouring by ℕ extends to a total function, so nothing is lost.
- `RainbowCliqueIn Γ S m avoid` says there is an m-vertex clique inside S whose distinct unordered edges get distinct colours (a copy of R(K_m)) and none of whose edges has a colour satisfying `avoid`. Property 1 is the negation with m = k+1. Property 2 takes S = V∖{v}; a rainbow clique inside S is exactly a rainbow clique of the induced graph. Property 3 asks for a rainbow K_k avoiding the colour c, for every c in the palette ℕ.
- `f k` is the least n for which some ℕ-coloured graph on n vertices is in the class. Any n-vertex graph can be relabelled onto `Fin n`; the relabelling preserves all three properties (proved in Lean as `relabel_member`).
- Property 3 is required for every c in the palette ℕ, used by Γ or not, as printed. Under the alternative reading "every colour used by Γ", the 0-vertex graph would belong to every \hat F_k (all three properties would be vacuous), contradicting the source's Proposition 3.4 (f(k) ≥ k+1). So that reading cannot be the intended one. For a graph with at least one vertex and k ≥ 1 the two readings agree: property 2 at any vertex gives a rainbow K_k, and that clique avoids every unused colour.
- The choice of ℕ does not matter among infinite palettes. A finite graph uses finitely many colours, so a member with any infinite palette P can be recoloured injectively into ℕ (and back). Properties 1 and 2 survive an injective recolouring. Property 3 for a colour outside the image holds because P has an unused colour, and property 3 for that colour gives a rainbow K_k, which avoids every unused colour. So every countably or uncountably infinite palette gives the same f.
- The source requires neither a proper colouring nor a complete graph. Its own examples have both features: the triangle of Lemma 3.5 has two adjacent edges of the same colour, and \Lambda'_3 in Lemma 3.7 has two non-edges. Our graph is not complete (each core part is independent). Its colouring happens to be proper, because each repeated colour class is a matching.

## 3. Stage-1 finding and the palette repair

The review's endpoint quantified over an arbitrary palette type: `f k = sInf {n | ∃ (C : Type) (Γ : ECGraph (Fin n) C), InHatF k Γ}`. Stage 1 proved in Lean that this is vacuous. The graph on `Fin 0` with palette `Empty` satisfies all three properties for every k: there are no vertices, so property 1 holds, property 2 is vacuous, and property 3 quantifies over an empty palette. So 0 is in the set and f k = 0 for every k. The packet keeps this as `zero_mem_minimization_set (k) : 0 ∈ {n | ∃ C Γ, InHatF k Γ}` (module `RainbowVacuity`).

Root's decision, which we follow, was to fix the palette to ℕ, as the source does ("we can take the set of colors to be the set of natural numbers"). With this repair the minimum is not trivial:

- `f_lower_bound (k) (hk : 1 ≤ k) : k + 1 ≤ f k`. For k ≥ 1 the set is nonempty: the graph made of two disjoint k-cliques with all edges coloured differently is a member on 2k vertices (`minimization_nonempty`). So `sInf` is attained (`f_minimum_attained`). Property 3 applied to any colour gives a k-clique, so a member has a vertex; property 2 at that vertex then gives k other vertices.
- `rainbow_K_succ_not_mem_nat (k)`: a rainbow K_{k+1} coloured injectively by ℕ is not in the class.
- The k = 0 case stays degenerate (the empty graph is a member), but the source defines \hat F_k only for positive k, and the conjecture concerns k ≥ 4.

Comparison with the review's endpoint: the endpoint statement `chlt_conj_5_1_false` is word for word the review's, and so are `ECGraph`, `RainbowCliqueIn`, `InHatF` and `conjFormula`. Only two things differ: the palette in `f` is ℕ, not an existentially quantified type, and the lower-bound check is `k + 1 ≤ f k` for k ≥ 1, not for all k.

## 4. The construction

Fix t ≥ 2. Take disjoint sets A = {a_1,…,a_t}, B = {b_1,…,b_t}, C = {c_1,…,c_t}, and a private vertex x_{abc} for each (a,b,c) ∈ A×B×C. The graph Γ_t has these edges:

- A ∪ B ∪ C induces the complete tripartite graph with parts A, B, C, so each part is independent;
- X = {x_{abc}} is a clique;
- every private vertex is adjacent to every core vertex.

So |V(Γ_t)| = t³ + 3t. Colours:

- for each (a,b) ∈ A×B, a colour R_{ab} is given to the edge ab and to the t edges c·x_{abc} (c ∈ C);
- every other edge gets its own fresh colour, distinct from all the others.

The two kinds of R_{ab} edges are disjoint, so each repeated class is a matching of t+1 edges. Colours are finitely many and are coded injectively into ℕ.

Write M = t³ and k = M + 2.

**Rainbow criterion.** A set S of vertices spans a rainbow clique when S is a clique, S contains at most one vertex of C, and S never contains a whole quadruple a, b, c, x_{abc}. *Proof.* Fresh colours occur once. Suppose two distinct edges of S share the colour R_{ab}. They cannot both be ab. If one is ab and the other is c·x_{abc}, then S contains a, b, c and x_{abc}, which is excluded. If they are c·x_{abc} and c'·x_{abc'}, then c = c' because S has at most one C vertex, so the edges are the same. ∎

**Property 1.** Every core part is independent, so a clique S has at most one vertex in each of A, B, C. Then S ⊆ X ∪ {a,b,c} for some a, b, c, a set of size M+3. A clique with M+3 = k+1 vertices is therefore exactly X ∪ {a,b,c}. It contains the distinct edges ab and c·x_{abc}, both coloured R_{ab}, so it is not rainbow.

**Property 2.** For each vertex v we give a rainbow k-clique avoiding v.
- If v ∈ A, use X ∪ {a', b} with a' ≠ a (possible since t ≥ 2). If v ∈ B, use X ∪ {a, b'} with b' ≠ b. If v ∈ C, use X ∪ {a, b}. Each of these is a clique of size M+2 with no C vertex, so it is rainbow by the criterion. (The written proof uses X ∪ {b,c} and X ∪ {a,c} for the first two cases. The Lean proof uses the variant above, and both are valid.)
- If v = x_{abc}, use T_{abc} = (X ∖ {x_{abc}}) ∪ {a,b,c}. This is a clique of size M+2. It has one C vertex and lacks x_{abc}, so it is rainbow by the criterion. This is the case the review flagged as riskiest: injectivity of the colouring on unordered pairs of a clique that drops one private vertex. In Lean it is `erased_box` (balanced family) and `triSet_erase_rainbow` (variable family).

**Property 3.** Take a colour c ∈ ℕ.
- If c codes R_{ab}, use X ∪ {a', b} with a' ≠ a. It has no C vertex, and its only A–B edge has colour R_{a'b} ≠ R_{ab}.
- If c codes a fresh colour of an edge uv, use the property-2 clique avoiding u; uv is the only edge with that colour.
- If c is not used at all, any rainbow k-clique avoids it.

Hence Γ_t ∈ \hat F_{t³+2}, and **f(t³+2) ≤ t³+3t for every t ≥ 2.** In Lean: `tripartite_family`, `f_family_le`.

**The violation.** At t = 8: k = 514 and f(514) ≤ 536. Here 4k − 3 = 2053 and 45² = 2025 < 2053 < 2116 = 46², so 22 < (−1+√2053)/2 < 22.5 and the ceiling is 23. The formula gives 537 (`conjFormula_514`). In general, put s = 3t−2 and k = t³+2. Then 4k − 3 − (2s+1)² = 4t³ − 36t² + 36t − 4 = 4(t−1)(t² − 8t + 1), which is positive for t ≥ 8 since t² − 8t + 1 = t(t−8) + 1 ≥ 1. Hence √(4k−3) > 2s+1, so (−1+√(4k−3))/2 > s and its ceiling is at least s+1. The formula's value is then at least k + s + 1 = t³ + 3t + 1 > t³ + 3t ≥ f(k). In Lean: `conj_fails_on_family (t) (ht : 8 ≤ t) : (f (t^3+2) : ℤ) < conjFormula (t^3+2)`.

## 5. Every k: variable cores

Let A and B have t ≥ 2 vertices each with all A–B edges present. Let C be a nonempty independent set where each c ∈ C has an arbitrary neighbourhood N_A(c) ⊆ A and N_B(c) ⊆ B. A core triangle is a triple (a,b,c) with a ∈ N_A(c) and b ∈ N_B(c); let T be the number of core triangles. Add one private vertex x_p for each core triangle p. As before, X is a clique joined to every core vertex. R_{ab} colours ab and every c·x_{abc} that exists; all other edges get fresh colours. The proof of section 4 carries over with one change. In property 1, the (T+3)-clique X ∪ {a,b,c} is a clique only if ac and bc are edges. Then (a,b,c) is a core triangle, so x_{abc} exists and lies in X, which gives the colour clash. The criterion, the witnesses (X ∖ {x_p}) ∪ {a,b,c} for p = (a,b,c), the witnesses X ∪ {a,b}, and property 3 are unchanged. Two different private vertices on the same c have different (a,b), because each triangle has exactly one private vertex. Hence the graph is in \hat F_{T+2} with T + 2t + |C| vertices (Lean: `Variable.member`, `Variable.exists_member`). Also T = Σ_c |N_A(c)|·|N_B(c)| (`card_tri`).

Given k ≥ 4, put M = k − 2 ≥ 2, and let t be the least integer with M ≤ t³. Then t ≥ 2 and (t−1)³ < M. Write M = q t² + u t + v with q = ⌊M/t²⌋ ≤ t and 0 ≤ u, v < t. Let C have:
- q vertices joined to all of A and B (t² triangles each);
- one vertex joined to all of A and to u vertices of B (tu triangles);
- one vertex joined to v vertices of A and to one vertex of B (v triangles).

Zero counts leave a C vertex with no triangles, which is harmless. Then T = M and |C| = q + 2 ≤ t + 2, so f(k) ≤ M + 2t + q + 2 ≤ k + 3t (`f_le_cube_root`). Finally (t−1)³ < M gives t − 1 < M^{1/3}, so t ≤ ⌈M^{1/3}⌉. This yields

**f(k) ≤ k + 3⌈(k−2)^{1/3}⌉ for every k ≥ 4** (Lean: `f_le_all_k`, with the real cube root `((k:ℝ) - 2) ^ ((1:ℝ)/3)`).

Combined with the source's Lemma 3.10 (f(k) ≥ k + (1/2)k^{1/3} − 1/2, quoted, not formalized), this gives f(k) − k = Θ(k^{1/3}). By the source's Lemma 3.3 (α_r = f(r−2), quoted, not formalized), the same holds for α_r − (r−2).

## 6. Lean endpoints

All of these are in the appendix modules and are printed by `RainbowMain`:

```lean
theorem chlt_conj_5_1_false (α : ℕ → ℝ) :
    ¬ ∀ k : ℕ, 4 ≤ k → α (k+2) = f k ∧ (f k : ℤ) = conjFormula k
theorem f_514_le : f 514 ≤ 536
theorem f_514_lt_conjFormula : (f 514 : ℤ) < conjFormula 514
theorem conjFormula_514 : conjFormula 514 = 537
theorem explicit_514_member : ∃ Γ : ECGraph (Fin 536) ℕ, InHatF 514 Γ
theorem tripartite_family (t : ℕ) (ht : 2 ≤ t) :
    ∃ Γ : ECGraph (Fin (t^3+3*t)) ℕ, InHatF (t^3+2) Γ
theorem f_family_le (t : ℕ) (ht : 2 ≤ t) : f (t^3+2) ≤ t^3+3*t
theorem conj_fails_on_family (t : ℕ) (ht : 8 ≤ t) :
    (f (t^3+2) : ℤ) < conjFormula (t^3+2)
theorem f_le_all_k (k : ℕ) (hk : 4 ≤ k) :
    (f k : ℤ) ≤ k + 3 * ⌈((k : ℝ) - 2) ^ ((1 : ℝ) / 3)⌉
theorem f_lower_bound (k : ℕ) (hk : 1 ≤ k) : k + 1 ≤ f k
theorem rainbow_K_succ_not_mem_nat (k : ℕ) : ¬ InHatF k (recolour (rainbowComplete (Fin (k+1))) (finiteColourCode _))
```

Each depends only on [propext, Classical.choice, Quot.sound]. `f_514_le` comes from the explicit member `explicit_514_member`, not from `sInf ∅ = 0`. The construction is proved symbolically for every t, and the 536-vertex case is a specialization. Nothing decides a property over 536-vertex subsets and no `native_decide` is used; the only `decide` calls prove `2 ≤ 8`, `4 ≤ 514` and a fact about `Bool`.

How the Lean proof follows the written one:
- The vertex type is an inductive type (`a | b | c | x`), and the colour type is `(I × I) ⊕ Sym2 Vertex`.
- The colour function is defined on ordered pairs, proved symmetric, and lifted to `Sym2`.
- The repeated colour classes are classified exactly (`colour_shared_iff`, `colour_shared`), and fresh colours determine their edge (`colour_fresh`).
- The rainbow criterion is `rainbow_injective`.
- Each clique lies in a "box" X ∪ {a,b,c} (`clique_subset_box`); this gives property 1 by cardinality.
- The finite palette is coded into ℕ by an injection, and vertices are moved to `Fin n` by an equivalence. Both transports are Lean-proved (`recolour_member`, `relabel_member`).

## 7. Significance

This is a short, elementary construction. Its main idea is one colour class that mixes a core edge ab with one C–private edge per c ∈ C, where C is an independent part. That idea yields one private vertex per core triangle instead of per core pair. It refutes an explicitly stated conjecture of a refereed paper. For large r it also goes against the authors' stated belief (line 168) that α_r is closer to their upper bound (r−2) + √(r−1): together with the source's own lower bound, it determines the order of the gap in their Theorem 1.3, α_r − (r−2) = Θ(r^{1/3}).

The counterexamples are far from the range the source settles. The source determines f(k) only for k ≤ 7 (Proposition 3.4, Lemmas 3.5–3.8, Theorem 3.9), and there the formula is correct. k = 514 is also the smallest k at which any graph of our variable-core form (any |A|, |B| ≥ 2 and any C-neighbourhoods) has fewer vertices than the formula. The next are k = 554, 555 and 556. This is a dynamic-programming computation over the parameters (the review's `smallest_k.py`, reproduced independently by the final check), not part of the Lean. We do not know the smallest k at which f(k) is below the formula, and we do not know f(k) exactly or the constant in front of k^{1/3}.

The source's second, stronger conjecture says that for k = 2·C(t,2)+1 the Lemma 3.8 graph, which has k + t − 1 vertices (the formula's value), is the unique graph in \hat F_k with f(k) vertices. In particular it implies that f(k) equals the formula at those k. So it fails whenever f(k) is below the formula at such a k. The Lean bound `f_le_all_k` gives this first at t = 32, where f(993) ≤ 993 + 30 < 1024. The construction with tuned parameters gives it already at t = 27 (k = 703; not in Lean). We have not formalized the stronger conjecture itself.

The review estimates a 0.20 chance that a referee would call the construction routine once seen. The formal content here certifies correctness. It does not certify novelty.

## 8. Prior art (independent review, plus the final-check refresh)

The review (Claude Opus 5.5, 2026-11-20) reports:
- The arXiv abs page lists v1 2022-12-09 and v2 2024-03-19 and no v3. Conjecture 5.1, the definition of \hat F_k and Lemmas 3.3, 3.8 and 3.10 are identical in v1 and v2. v2 thanks "the anonymous referee".
- An OpenAlex search for "rainbow saturation" returned the later papers: weak rainbow saturation (arXiv:2401.11525, arXiv:2609.03823), proper rainbow saturation (arXiv:2409.15258, 2409.15444, 2403.15602), cycles (arXiv:2501.06782) and Behague et al. (arXiv:2211.08589). The ones read around their K_r mentions only cite the bounds of Chakraborti et al. Behague et al.'s Lemma 5.1 uses the pair mechanism at √ scale.
- Web searches found no r + O(r^{1/3}) upper bound and no claim that the conjecture is false. The Omega registry and Principia searches found nothing.

Its residual-gap paragraph reads:

> **Residual gap:** the journal body is unread, but v2 is the refereed text posted five days after journal publication, and it still prints the conjecture. Searches of 2026 preprints are bounded.

The SIAM PDF request returned 403 to the proof lane. That refusal was respected and has not been retried.

Final-check refresh (2026-11-20, Claude Opus 5.5, a separate lane from the packager but of the same model family):
- The arXiv abs page still lists only v1 (2022-12-09) and v2 (2024-03-19), with journal DOI 10.1137/23M1565875. In a fresh fetch of the v2 HTML, Section 3.1, Lemma 3.10 and Conjecture 5.1 match the quotations above.
- Semantic Scholar lists three citing papers: arXiv:2401.11525, 2501.06782 and 2609.34898. OpenAlex lists two: the journal version of 2401.11525, and 2609.34898. The newest, 2609.34898 (*On rainbow saturated graphs with minimum number of edges*, 2026-09-28), cites the source only for the existence of lim sat(n, R(K_r))/n and for its rainbow-semisaturation theorem, which it uses as a lower bound. It does not touch α_r or f(k).
- An arXiv API search for "rainbow saturation", sorted by date, returned nothing newer than 2609.34898. Two web searches found no upper bound of the form r + O(r^{1/3}) and no claim that the conjecture is false.
- Omega registry: `gh search issues` and `gh search prs` for "2212.04640", "rainbow saturation" and "Chakraborti Hendrey rainbow" all returned []. `gh search code` for "mathdb-381790" and "2212.04640" also returned [].
- Principia: 381790 is not in `principia-ids.txt`. The neighbouring Principia write-ups (381792, 381794 and 381795) come from other papers. MathDB 381789, the other record from this source, is the Girão–Lewis–Popielarz conjecture that the source itself refutes; it has no accepted result.
- Greps of the Principia, mio-qwq, openai/math and omega clones for the arXiv id, "rainbow saturation" and "Chakraborti" found only unrelated numeric matches.

## 9. Reproduction

The appendix `LEAN-SOURCE-APPENDIX.md` contains the 14 modules (1,333 lines) in import order, byte-identical to `src/`. `C/root-intake-r60/root-replay.py` extracts them into an empty directory, rebuilds them and kernel-checks them; this lane's replay is in `fresh-replay/ROOT-REPLAY.json` (`all_ok: true`, every olean identical to the author build). Details and receipts are in `REPORT.md`.
