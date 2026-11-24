# A counterexample to supermultiplicativity of the clique immersion number under the strong product

## Abstract

There are finite simple connected bipartite graphs G and H with 14 and 22 vertices, respectively, such that im(G)=8, im(H)=12, and im(G ⊠ H)<96. The obstruction is a degree-forced terminal set separated by a cut of size 2,224, whereas a K96 immersion would require 2,304 distinct crossing edges. A Lean 4 formalization proves this strict inequality and the negation of the universal conjecture, using ordinary weak immersion.

## 1. Statement and definitions

Collins, Heenehan and McDonald, *Clique immersion in graph products*, arXiv:1908.10457v1, Section 6, Conjecture 2, states:

> Let G and H be graphs with im(G)=t and im(H)=r then im(G⊠H)≥tr.

[Source, Conjecture 2 and Section 2](https://arxiv.org/html/1908.10457v1).

Here and below graph means finite and simple. The following short literal excerpts identify the source definitions; the accompanying mathematical transcriptions give their complete content rather than reproducing long passages.

The source's alternative immersion definition in Section 2 specifies an “injective function” φ:V(J)→V(G) and “edge-disjoint” paths. Precisely, for every edge uv of J there is a path P_uv from φ(u) to φ(v), and two paths for different edges have no undirected edge in common. Internal vertices may coincide with other terminals: this is weak immersion. Taking J=K_q gives exactly the following Lean structure (the full field declarations are in the appendix):

```lean
structure CliqueImmersion {V : Type} (G : SimpleGraph V) (q : ℕ) where
  branch : Fin q → V
  injective : Function.Injective branch
  -- len, vertex, start, finish, adjacent, simple, disjoint
```

The remaining fields represent each path as a finite simple vertex sequence, with the stated endpoints and adjacency, and prohibit common edges for distinct unordered terminal pairs, in either orientation. Both orientations are stored; they need not be reverses. Choosing one orientation gives a source immersion; conversely a source immersion supplies both orientations by path reversal. No condition forbids interior terminals. If paths are initially described as walks, deleting cycles gives the simple paths used here without creating any edge overlap.

In Section 1 the immersion number uses the phrase “largest value”: mathematically it is max{q: G has a K_q immersion}. Next to this source definition, the actual Lean definition is

```lean
noncomputable def immersionNumber (G : SimpleGraph V) : ℕ := by
  classical
  exact Nat.findGreatest (fun q => Nonempty (CliqueImmersion G q)) (Fintype.card V)
```

The finite cap is justified by the proved lemma `CliqueImmersion.card_bound`: an injective branch map forces q≤|V|. The lemma `immersionNumber_is_largest` proves that every feasible q is at most this number. Restriction of an immersion to fewer terminals is proved in `exists_immersion_mono`; `immersionNumber_eq` and `immersionNumber_lt` then establish the exact factor numbers and the product bound from genuine existence and nonexistence proofs. The zero convention on the empty graph has no role in the counterexample.

Section 2 defines strong-product edges by the formula

> E(G□H)∪E(G×H).

Its vertex set is V(G)×V(H). Expanding the Cartesian and direct conditions gives exactly the Lean definition:

```lean
def strongProduct {V W : Type} (A : SimpleGraph V) (B : SimpleGraph W) :
    SimpleGraph (V × W) where
  Adj x y := (x.1 = y.1 ∧ B.Adj x.2 y.2) ∨
    (x.2 = y.2 ∧ A.Adj x.1 y.1) ∨
    (A.Adj x.1 y.1 ∧ B.Adj x.2 y.2)
  -- symmetry and looplessness are proved
```

The finite-graph formulation of the conjecture and its negation are therefore:

```lean
def StrongProductConjecture : Prop :=
  ∀ (V W : Type) [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W),
    immersionNumber G * immersionNumber H ≤ immersionNumber (strongProduct G H)

theorem strong_product_conjecture_false :
    ¬ ∀ (V W : Type) [Fintype V] [Fintype W]
      (G : SimpleGraph V) (H : SimpleGraph W),
      immersionNumber G * immersionNumber H ≤ immersionNumber (strongProduct G H)
```

These declarations are inside `ProductImmersion`. The universe-zero `Type` formulation agrees with the copied definitions: arbitrary finite vertex sets and all finite orders are included. `Fintype` supplies the enumeration, not any additional graph restriction. An explicit instance on Fin 14 and Fin 22 disproves the assertion, so the result is not vacuous.

## 2. The two factors

For even a≥2, take two disjoint sets A and B, each of size a. Include every A–B edge. Factor the complete graph on A into a−1 perfect matchings, and add one new vertex for each matching, adjacent to every vertex of A. Add another a−1 vertices in the same way for B. Call the resulting graph F_a. There are no other edges. In particular a shared vertex belongs to one matching and one side only. Matching edges themselves are represented by two-edge paths; they are not edges of F_a.

For completeness, a one-factorization can be constructed on {∞}∪Z/(a−1). For each residue c use {∞,c} and {c+i,c−i}, 1≤i≤(a−2)/2. Every vertex occurs exactly once in a matching, since the nonzero residues occur in opposite pairs. An edge between finite residues x,y occurs in the unique matching c=(x+y)/2, and an edge incident with ∞ occurs in its named matching. Division by 2 is valid because a−1 is odd. Thus these matchings partition all edges. This proves everything needed for a=4 and a=6 without an external factorization theorem.

Use A∪B as the 2a terminals. A cross pair is joined by its edge. For a same-side pair, use the two-edge path through its matching's shared vertex. Paths from one matching use distinct incident edges because its pairs are disjoint. Paths from different matchings use different shared vertices. The two sides' shared vertices are disjoint, and none of these edges is a cross edge. This proves a K_(2a) immersion, in fact a strong one.

Each original vertex has degree a+(a−1)=2a−1; each added vertex has degree a. A terminal in any weak K_q immersion needs q−1 distinct first edges, one for each other terminal, so q−1≤Δ. It follows that im(F_a)=2a. The construction is connected because A–B is complete and every added vertex has neighbors. It is bipartite with sides A together with the added vertices for B, and B together with the added vertices for A. Each side has 2a−1 vertices. Counting gives

\[
|V(F_a)|=4a-2,\qquad |E(F_a)|=a^2+2a(a-1)=3a^2-2a.
\]

Set G=F_4 and H=F_6. Thus (|V(G)|,|E(G)|,im(G))=(14,40,8) and (|V(H)|,|E(H)|,im(H))=(22,96,12). In Lean, the original vertices are 0,…,2a−1, the A shared vertices are 2a,…,3a−2, and the B shared vertices are 3a−1,…,4a−3. This is exactly `factor a (4*a-2)`. The finite peg formula in `FactorDefinitions` assigns the matching containing a pair: with ∞ labeled a−1, the finite label is (a/2)(i+j) modulo a−1, the inverse-of-two formula above. The concrete factor paths and edge-owner identities are proved by kernel decision procedures in `FactorOwners` and `FactorImmersions`.

## 3. Forced terminals in the product

For simple graphs the strong-product degree satisfies

\[
d_{G\boxtimes H}(g,h)+1=(d_G(g)+1)(d_H(h)+1).
\]

Indeed the closed neighborhood is the product of the two closed neighborhoods. Equivalently the three disjoint neighbor classes change only the first coordinate, only the second, or both. This is proved generically by `closedN_product` and `product_degree`.

An original–original pair in our product has degree 8·12−1=95. The remaining degrees are 5·12−1=59, 8·7−1=55, and 5·7−1=34. There are exactly 8·12=96 vertices of degree at least 95. Consequently every terminal of a putative K96 immersion must be an original–original pair, and injectivity forces all 96 of them to occur. No assumption about the branch choices of an arbitrary immersion has been made. In Lean this is `degree_eligible`, `eligible_card`, and the bijection argument in `no_immersionP`.

## 4. The checkerboard cut

Let L_G,R_G and L_H,R_H be the bipartitions from Section 2 and set

\[
X=(L_G\times L_H)\cup(R_G\times R_H),\qquad
Y=(L_G\times R_H)\cup(R_G\times L_H).
\]

A diagonal strong-product edge flips both bipartition coordinates and stays on its checkerboard side. An edge changing only one coordinate crosses. Thus each G edge contributes |V(H)| crossing edges and each H edge contributes |V(G)|, with no duplicates between these two types. The cut has

\[
|\partial X|=40\cdot22+14\cdot96=2224.
\]

The original vertices of G split 4/4 across its bipartition; those of H split 6/6. Therefore the forced 96 terminals split 48/48 across X and Y. For each of the 48·48=2304 pairs with opposite-side terminals, its immersion path must traverse a cut edge. Choose one such edge per path. Distinct pairs give distinct edges by edge disjointness, even if paths pass through other terminals. This injects 2304 pairs into 2224 cut edges, a contradiction. Hence K96 does not immerse in G ⊠ H. Restricting larger clique immersions to 96 terminals excludes them too. We conclude

\[
\operatorname{im}(G\boxtimes H)<96
 =\operatorname{im}(G)\operatorname{im}(H),
\]

refuting Conjecture 2.

The Lean proof establishes the generic injection in `CliqueImmersion.cut_bound`. `product_cut_card_le` proves a sufficient upper bound on cut capacity using a surjective cover by the axial edges; it does not need the equality proved above. `bipartiteG`, `bipartiteH`, `factor_cutG`, `factor_cutH`, and the two `eligible` side counts are kernel-checked finite statements. `cut_card_bound` combines them. The final contradiction is arithmetic, not a negative solver certificate.

## 5. Formal scope and verification

The eleven reviewed source modules are copied unchanged, totaling 811 lines. Nine supply the counterexample and its definitions; `SelfProductGap` and `CheckerboardLower` are retained quantitative supplements. The added module `StrongProductConjecture` instantiates a putative universal inequality at the two explicit factors and contradicts `literal_immersion_number_counterexample`. It also packages the result as `mathdb343652 : ¬ StrongProductConjecture`.

The supplements certify 72≤im(H ⊠ H)≤130. They are not needed for the refutation. Their lower construction uses the 72 original–original pairs in (A×A)∪(B×B), direct diagonal edges between the two blocks, and coordinatewise matching routes within a block. An unchanged coordinate is kept fixed. The symmetric edge-owner function certifies disjointness. For the upper bound, any 131 terminals must lie among 144 original pairs, at most 72 per cut side; their side sizes l,r satisfy l+r=131 and l,r≤72, hence lr≥59·72=4248. The same cut has capacity 96·22+22·96=4224, a contradiction. These supplement endpoints are included in the axiom report but no general infinite-family statement is represented as formalized here.

Each module is compiled and its actual olean checked by the pinned standalone `leanchecker` through the supplied 32 GiB runner. Only `propext`, `Classical.choice`, and `Quot.sound` occur as endpoint axioms. No placeholder or native decision procedure is used. The runner suppresses only the unused-section-variable linter in the unchanged sources and retains warnings-as-errors. Receipts, exact endpoint output, pins, source hashes, and appendix byte checks are in REPORT.md and companion files.

## 6. Prior work and significance

The source already supplies the terminal-degree bound (Remark 1) and the cut obstruction (Lemma 12); neither is new here. Wu and Deng, *Counterexamples to Clique Immersion Conjecture for Direct Products*, arXiv:2605.28518v2, refute the direct-product sibling. Their family subdivides each same-side clique edge separately. Our use of bipartite factors, forced terminals and parity is conceptually close. Matching-based sharing reduces the number of added vertices from quadratic to linear, keeping their degrees below terminal degrees; the strong product then has too few axial edges across the parity cut. [Wu–Deng, Sections 1–2](https://arxiv.org/html/2605.28518v2).

The final bounded review found no public strong-product counterexample. Wu–Deng's 2025 strong-product note, *A note on clique immersion of strong product graphs*, Discrete Mathematics 348 (2025), 114237, describes positive cases in its accessible abstract and introduction, including a clique subgraph factor. [Wu–Deng 2025](https://doi.org/10.1016/j.disc.2024.114237). No open full-text copy was found; OpenAlex marks it closed without repository full text. The earlier HTTP 403 refusal was respected. The direct-product note's introduction independently confirms the positive scope. Bipartite factors here have no clique subgraph of order three and no totally odd clique immersion of order three, since two of any three terminals lie on the same side. The bounded review cannot certify the contents of inaccessible or unpublished work.

This is a short elementary counterexample once the compressed family is given. The substantive construction step is the sharing of a vertex across a perfect matching while preserving edge-disjoint routes. This is one structural modification of Wu–Deng’s subdivision construction, so the result should be presented as a close continuation of that work. The degree and parity arguments follow established tools, and the conceptual distance from Wu–Deng's direct-product note is small. No novelty is claimed for the factor graph class or for the general cut method. The result resolves the strong-product inequality in the negative; the assessment of its publication significance should reflect this close predecessor rather than portray it as a new immersion technique.
