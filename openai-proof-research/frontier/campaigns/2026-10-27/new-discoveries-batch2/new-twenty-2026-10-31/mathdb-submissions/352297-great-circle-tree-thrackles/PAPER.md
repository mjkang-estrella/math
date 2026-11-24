# Great-circle thrackleable trees form a proper subclass of the augmented caterpillars

**MathDB 352297 (duplicate record 247589).** Source: Karen Collins and Cleo Roberts, *Great-circle Tree Thrackles*, arXiv:2110.09679v1 (19 Oct 2021, the only arXiv version); Discrete Mathematics 346(1) (2023), article 113121 (online 29 Aug 2022), DOI 10.1016/j.disc.2022.113121. Conjecture 3.4. Quotations below are from arXiv v1; the journal text was not read (the publisher refuses automated access and no open copy of it was found).

**Provenance.** The proof (the 14-vertex witness, the determinant-sign encoding and the SAT certificates) is by a GPT-6.1 Sol lane (`t1-pool065-proof-sol61-20261120-r1`). An adversarial review by a Claude Opus 5.5 lane (`t1-prelean-X38-opus-20261120-r1`) re-derived the encoding and re-checked the certificates. This manuscript and the Lean 4 formalization are by a Claude Opus 5.5 lane (`gc-thrackle-352297-formal-paper-opus55-20261122-r1`). The Lean statement and proof are in `LEAN-SOURCE-APPENDIX.md`. The endpoint is `GC.mathdb_352297 : GC.Conjecture34`, and it depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

## 1. The conjecture

> **Conjecture 3.4.** The class of great circle thrackleable trees is properly contained in the class of augmented caterpillars.

**Theorem.** Conjecture 3.4 holds for trees with at least three vertices. Both parts are proved:

1. **Containment** (source Theorem 3.2, re-proved here). Every great-circle thrackleable tree with at least three vertices is an augmented caterpillar.
2. **Strictness** (new). The 14-vertex tree T below is an augmented caterpillar but has no great-circle thrackle drawing in general position.

The restriction to at least three vertices is forced by the literal Definition 3.1. A tree with one or two vertices is great-circle thrackleable, but its longest path has no internal vertex, so it is not an augmented caterpillar. The Lean file proves this for K₂ (`GC.K2_gcThrackleable`, `GC.K2_not_augCat`). The source plainly does not intend these trivial cases: the same restriction is needed for the source's own Theorem 3.2, which read literally also fails for K₁ and K₂. The strictness half, which is the open part of the conjecture, needs no restriction, since the witness has 14 vertices.

## 2. Source definitions and their Lean transcriptions

Each source passage is quoted verbatim from arXiv:2110.09679v1, followed by the Lean definition (namespace `GC`, module `GCStatement`).

**Definition 1.1.** "A thrackle is a drawing of a simple, undirected graph in which 1. no curve crosses itself and 2. every pair of curves intersects at exactly one point. If a graph can be drawn as a thrackle, it is called thrackleable."

**Definition 1.3** (Cairns, Koussas, Nikolayevsky). "A great circle thrackle is a thrackle drawn on the sphere, whose vertices are represented as points on the sphere and whose edges are represented by the arcs of great circles. A great-circle thrackle is said to be drawn in general position if no three vertices lie on the same great circle and no two vertices are antipodal."

**Convention (§1).** "As we are concerned with trees, we consider connected great-circle thrackles in general position, but we do not require the absence of leaves."

**Definition 2.4** (CKN). "We represent the great circle containing edge e as C(e) … If e is shorter than π we call it a short edge and if e is longer than π we call it a long edge."

```lean
abbrev E3 := EuclideanSpace ℝ (Fin 3)
def S2 : Set E3 := Metric.sphere 0 1
def IsGreatCircle (C : Set E3) : Prop :=
  ∃ nrm : E3, nrm ≠ 0 ∧ C = {x | x ∈ S2 ∧ inner ℝ nrm x = 0}
def greatCircle (u v : E3) : Set E3 := {x | x ∈ S2 ∧ ∃ α β : ℝ, x = α • u + β • v}
def shortArc (u v : E3) : Set E3 :=
  {x | x ∈ S2 ∧ ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ x = α • u + β • v}
def longArc (u v : E3) : Set E3 :=
  {x | x ∈ greatCircle u v ∧ (x ∉ shortArc u v ∨ x = u ∨ x = v)}
def GeneralPosition {V : Type*} (p : V → E3) : Prop :=
  (∀ i, p i ∈ S2) ∧ Function.Injective p ∧ (∀ i j, p i ≠ -p j) ∧
  ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
    ¬ ∃ C : Set E3, IsGreatCircle C ∧ p i ∈ C ∧ p j ∈ C ∧ p k ∈ C
def edgeArc {V : Type*} (p : V → E3) (long : Sym2 V → Bool) (u v : V) : Set E3 :=
  if long s(u, v) then longArc (p u) (p v) else shortArc (p u) (p v)
def IsGCThrackleDrawing {V : Type*} (G : SimpleGraph V) (p : V → E3)
    (long : Sym2 V → Bool) : Prop :=
  GeneralPosition p ∧
  ∀ u v w x, G.Adj u v → G.Adj w x → s(u, v) ≠ s(w, x) →
    ∃! z, z ∈ edgeArc p long u v ∧ z ∈ edgeArc p long w x
def GCThrackleable {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ p long, IsGCThrackleDrawing G p long
```

Between two distinct, non-antipodal points of the sphere there are exactly two great-circle arcs: the short one (length < π) and the long one (length > π). The Lean file proves that `shortArc u v ∪ longArc u v` is the whole great circle, that the two arcs meet exactly in `{u, v}`, and that the long arc contains `−u` and `−v` while the short arc does not (`GC.shortArc_union_longArc`, `GC.shortArc_inter_longArc`, `GC.antipodes_long_not_short`). The long arc therefore contains a pair of antipodal points, so its length exceeds π.

Readings, each with a reason:

- *"no curve crosses itself"*: a great-circle arc shorter than 2π is a simple curve, so this condition holds automatically and is not stated.
- *"every pair of curves"*: read as every pair of distinct edges, and "exactly one point" as `∃!`. For two edges that share a vertex, the common point is that vertex.
- *Distinct vertices at distinct points* (`Function.Injective p`) is part of what a drawing is. It also follows from the non-antipodality and great-circle conditions whenever the graph has a third vertex.
- *Connected*: every tree is connected.
- *General position*: the source considers only drawings in general position (§1 convention above). Cairns, Koussas and Nikolayevsky (arXiv:1412.7252, §2) note that a spherical thrackle drawing can be put in general position by small adjustments of the vertices. The MathDB record's paraphrase leaves general position out but refers to the source for the definitions. We follow the source.

**Definition 3.1.** "An augmented caterpillar, G is a tree consisting of a spine, which is its longest path, and legs, which are paths that are edge-disjoint from the spine, but which terminate at internal vertices of the spine. Every vertex in G is at most distance two from an internal vertex of G's spine."

```lean
def IsInternal {V : Type*} {G : SimpleGraph V} {a b : V} (P : G.Walk a b) (w : V) : Prop :=
  w ∈ P.support ∧ w ≠ a ∧ w ≠ b
def IsAugmentedCaterpillar {V : Type*} (G : SimpleGraph V) : Prop :=
  G.IsTree ∧ ∃ (a b : V) (P : G.Walk a b), P.IsPath ∧
    (∀ (c d : V) (Q : G.Walk c d), Q.IsPath → Q.length ≤ P.length) ∧
    (∃ legs : Set (Σ c d : V, G.Walk c d),
      (∀ L ∈ legs, L.2.2.IsPath ∧ (∀ e ∈ L.2.2.edges, e ∉ P.edges) ∧ IsInternal P L.2.1) ∧
      (∀ e ∈ G.edgeSet, e ∈ P.edges ∨ ∃ L ∈ legs, e ∈ L.2.2.edges)) ∧
    ∀ v, ∃ w, IsInternal P w ∧ G.dist v w ≤ 2
```

"Its longest path" means that no path is longer. "Consisting of a spine … and legs" means that every edge lies on the spine or on a leg. Legs may share vertices or edges with each other, since the source does not forbid it. The witness T satisfies the stricter reading as well: its four legs are pairwise disjoint 2-paths.

**Statement.** Graphs are labelled graphs on `Fin n`:

```lean
def Conjecture34 : Prop :=
  (∀ (n : ℕ) (G : SimpleGraph (Fin n)), 3 ≤ n → G.IsTree → GCThrackleable G →
      IsAugmentedCaterpillar G) ∧
  (∃ (n : ℕ) (G : SimpleGraph (Fin n)), 3 ≤ n ∧ G.IsTree ∧ IsAugmentedCaterpillar G ∧
      ¬ GCThrackleable G)

theorem mathdb_352297 : Conjecture34
```

**Non-vacuity (all proved in Lean, module `GCVacuity`).**

- The star K₁,₃, a tree with a vertex of degree three, is great-circle thrackleable (`GC.star3_gcThrackleable`). Its centre is drawn at (2/3, 2/3, 1/3) and its leaves at the coordinate vectors, with all arcs short.
- The 3,3,3 spider is not an augmented caterpillar (`GC.spider_not_augCat`).
- The witness T is an augmented caterpillar (`GC.t14_isAugCat`).
- The arcs have the properties stated above.

## 3. The witness

T has vertices 0, …, 13 and edges

```
01,  02 23,  04 45,  06 67,  18 89,  1-10 10-11,  1-12 12-13.
```

So the two adjacent centres 0 and 1 each carry three pendant paths of length two. T is a tree with 13 edges (`GC.t14_isTree`).

- **Longest paths.** Every vertex is within distance 2 of a hub, 0 or 1, and the hubs are adjacent. So any two vertices are at distance at most 5. In a tree, a path is the unique path between its ends, so its length equals their distance and is at most 5.
- **Spine and legs.** The path 3-2-0-1-8-9 has length 5, so it is a longest path. Its internal vertices include 0 and 1, so every vertex is within distance 2 of an internal vertex. The legs 5-4-0, 7-6-0, 11-10-1 and 13-12-1 are paths, edge-disjoint from the spine, ending at internal vertices 0 and 1. Together with the spine they cover all 13 edges.

Hence T is an augmented caterpillar under Definition 3.1.

T does not contain the 3,3,3 spider: at each branching vertex only one branch is longer than two. So its non-drawability does not follow from Theorem 3.2 or Corollary 3.3.

T is the tree that the source's own Conjecture 3.5 points to. Conjecture 3.5 says that if a 2-path separates at a spine vertex v, then no 2-path separates at an adjacent spine vertex v′. In any drawing of T, the hubs 0 and 1 have degree 4, so by the source's Lemma 2.9 at least two edges separate at each of them. At least one of these is the first edge of a pendant 2-path, so a 2-path separates at both 0 and 1. Conjecture 3.5 would therefore imply that T is undrawable. The present proof does not use or prove Conjecture 3.5.

**Why this tree.** The certificate for T existed and had already been checked twice (by the proof lane and by the review). Using the same sign system, the review's computations (not formalized) found smaller undrawable augmented caterpillars: 10 to 12 vertices if two legs may share their first edge, and 13 vertices with disjoint path legs. T satisfies Definition 3.1 under every reading of "legs" and needs no new certificate. A kernel-checking pilot showed that T's certificate fits comfortably in 14 Lean modules, so no smaller witness was needed.

## 4. Proof of strictness: T has no great-circle thrackle drawing

Suppose p₀, …, p₁₃ ∈ S² and long-flags give a great-circle thrackle drawing of T in general position. Write D(a,b,c) = det(p_a, p_b, p_c). It is nonzero for distinct a, b, c, since a zero determinant gives a nonzero normal vector orthogonal to all three points, that is, a great circle through them.

**4.1 Grassmann–Plücker.** For distinct a, b, c, d, e,

  D(abc)D(ade) − D(abd)D(ace) + D(abe)D(acd) = 0

(a polynomial identity). The three products are nonzero, so they cannot all have the same sign.

**4.2 Two disjoint edges uv and wx.**

- *The two candidate points.* The dependency identity D(vwx)u − D(uwx)v + D(uvx)w − D(uvw)x = 0 shows that y := D(vwx)u − D(uwx)v = −D(uvx)w + D(uvw)x lies in both planes. Also y ≠ 0, because det(y, v, w) = D(vwx)D(uvw) ≠ 0. Any point z on both great circles is a multiple λy: write z = αu + βv, and from det(z, w, x) = 0 get α D(uwx) + β D(vwx) = 0. A unit z is therefore one of z₊ = y/|y| and z₋ = −y/|y|.
- *Short-arc membership.* Coefficients in span(u, v) are unique, since D(uvw) ≠ 0, and likewise in span(w, x). So z_σ = λ_σ y lies in the short arc uv iff λ_σD(vwx) ≥ 0 and −λ_σD(uwx) ≥ 0. Similarly, z_σ lies in the short arc wx iff −λ_σD(uvx) ≥ 0 and λ_σD(uvw) ≥ 0.
- *Long-arc membership.* z_σ is never an endpoint. For example, z = u would put u on the great circle wx and force D(uwx) = 0. So z_σ lies on the long arc exactly when it is not on the short arc.

With s₁ = [D(uvw) > 0], s₂ = [D(uvx) > 0], t₁ = [D(wxu) > 0] and t₂ = [D(wxv) > 0], the number of common points of the two arcs is

  pairCount = Σ_{σ ∈ {+,−}} [z_σ ∈ arc(uv)] · [z_σ ∈ arc(wx)],

with z_σ ∈ short(uv) ⟺ (t₂ = σ ∧ t₁ ≠ σ) and z_σ ∈ short(wx) ⟺ (s₁ = σ ∧ s₂ ≠ σ). This is the exact crossing table of the proof lane. Generating clauses from this formula reproduces the lane's CNF clause-for-clause (§5). The thrackle condition says that pairCount = 1.

**4.3 Adjacent edges.** Two adjacent edges cannot both be long. A long arc from c contains both c and −c, so two long arcs at c would meet at two points. This is source Lemma 2.5.

**4.4 The finite contradiction.** The drawing gives Boolean values to 364 triple variables (sign of D on increasing triples) and 13 edge variables (long or not). These values satisfy every clause forbidding:

- an assignment of the six signs in a Grassmann–Plücker relation with three equal product signs;
- an assignment of four signs and two flags of a disjoint edge pair with pairCount ≠ 1;
- two adjacent long edges.

This CNF has 162,578 clauses and is unsatisfiable. The proof lane's LRAT refutation, trimmed to its dependency core, has 1,171 derived clauses and 40,097 hints. Every hint names either an earlier derived clause or an input clause, and each such clause is unit or falsified under the current assignment (reverse unit propagation). The certificate ends with the empty clause. So no drawing exists.

## 5. How the Lean proof is organised

- **Encoding soundness** (`GCGeom`, `GCBridge`). The identities of §4 are proved over ℝ³ (`GC.gp_identity`, `GC.yv_eq'`, `GC.pairCount_eq_one`, `GC.longArc_contains`). The main bridge, `GC.inputsSound_of_drawing`, says: for any drawing of the graph with edge list E in general position, the assignment `tauOf` read off it satisfies every input clause that `Thr.decodeInput` accepts. The bridge is proved for an arbitrary edge list on at most 16 vertices, and is then applied to T and to the spider.
- **Input clauses are generated, not listed.** A hint code names an input clause by a descriptor:
  - (a; b,c,d,e; 6 bits) for a Grassmann–Plücker clause;
  - (i, j; 6 bits) for a disjoint edge pair;
  - (i, j) for an adjacent pair.

  `decodeInput` checks the descriptor (distinct vertices; the bits really are forbidden: `gpBad`, `pairCountBits ≠ 1`) and builds the clause. `scripts/thr_gen.py` mirrors the Lean generator. It reproduces both of the proof lane's CNFs exactly as clause sets (21,249 and 162,578 clauses), so the certificates transfer unchanged.
- **Reflective checker** (`ThrCNF`, `ThrSound`). The checker uses:
  - literals coded as 2v and 2v+1;
  - partial assignments as natural-number bitmasks (the kernel accelerates `Nat.land`, `lor`, `shiftLeft` and `shiftRight` with GMP);
  - a binary trie of derived clauses;
  - a packed hint stream.

  `Thr.blockOK_sound` proves that acceptance implies every derived clause holds under any assignment that satisfies all valid input clauses.
- **Kernel evaluation.** Each certificate block is checked by `decide +kernel`. This is plain kernel reduction, with no `native_decide`, no `bv_decide` and no `Lean.ofReduceBool`. T's certificate is split into 14 blocks of about 2,860 hints. Each block proves that its derived clauses follow from the input clauses together with all earlier blocks (`T14Blk1` … `T14Blk14`). `Thr.T14_refute` chains the blocks to the empty clause. Each block takes about 15 s of CPU and at most 3.4 GB peak RSS. The spider certificate (299 clauses, 3,248 hints) is a single block.
- **Containment** (`GCContain`). The proof follows the proof lane's §7 argument (spelled out under Containment below) and does not depend on the source's proof of Theorem 3.2. Drawability restricts along injective homomorphisms (`GC.gcThrackleable_of_embedding`), and the spider's sign system is refuted by `Thr.Spi_refute`, so a tree containing the spider is not drawable.

**Containment (source Theorem 3.2).** Let G be a drawable tree with at least three vertices, and let P (from a to b, of length L) be a longest path.

1. *The projection R.* For a vertex v off P, choose an index k minimising dist(v, P_k) and a geodesic R from v to P_k. By minimality, R meets P only at P_k.
2. *P_k is internal.* Concatenating R with either part of P gives a path. Since P is longest, |R| ≤ k and |R| ≤ L − k. As |R| ≥ 1, the vertex P_k is internal.
3. *|R| ≤ 2.* If |R| ≥ 3, the last three vertices of R, the three vertices before P_k on P and the three after it span a 3,3,3 spider. Its ten vertices are distinct because P and R are paths meeting only at P_k. This contradicts drawability, so dist(v, P_k) = |R| ≤ 2.
4. *Vertices on P.* L ≥ 2. If P contains all n ≥ 3 vertices, then L = n − 1 ≥ 2. Otherwise some vertex lies off P, and its P_k is internal by step 2, which forces L ≥ 2. So the endpoints a and b are adjacent to internal vertices, and internal vertices are at distance 0 from themselves.
5. *Legs.* Let the legs be all paths that are edge-disjoint from P and end at an internal vertex.
   - An edge xy of G with both ends on P lies on P, since in a tree two adjacent vertices of a path are consecutive.
   - Otherwise say x is off P, and let R be its projection. If y ∈ R, then y is the second vertex of R, by distances in the tree, and R is a leg containing xy. If y ∉ R, then y is off P as well: if y were on P, then dist(x, P) = 1 and, since a tree has no cycle, y would be the only vertex of P adjacent to x, so R = x·y. So y·x·R is a path, edge-disjoint from P, ending at the internal vertex P_k: a leg containing xy.
   - The edges of R avoid P, because an edge with both ends on P would have both ends equal to P_k.

So G is an augmented caterpillar.

## 6. Significance

The source authors asked whether the class of great-circle thrackleable trees is exactly the augmented caterpillars, and conjectured that it is not. They suggested that crossing orientations might be needed. This work proves the conjecture with an explicit 14-vertex witness.

The method is a standard style of computational geometry: an exact encoding of the order type by determinant signs and Grassmann–Plücker relations, with a SAT refutation. The genuinely new ingredients are:

- the exact intersection count of short and long great-circle arcs in terms of four determinant signs;
- the finite certificate for this specific tree.

A specialist may view the result as a natural application of oriented-matroid and SAT methods rather than a conceptual advance. Once the encoding is written down, finding undrawable augmented caterpillars is a fast SAT sweep: the review's sweep of all 1,099 non-caterpillar augmented caterpillars with at most 13 vertices found 223 unsatisfiable sign systems. The witness T is also the tree that the source's Conjecture 3.5 points to (§3). The new step is the certified non-realizability, not the choice of the tree. The review rated the probability that the result is not routine at 0.55. The result does not classify the great-circle thrackleable trees, does not claim T is minimal (smaller witnesses exist under the same encoding), and says nothing about Conway's thrackle conjecture. The formal proof is complete: the geometric bridge from real drawings to the Boolean system is proved in Lean, not assumed.

## 7. Prior art (from the adversarial review, X38, 2026-11-20)

- arXiv:2110.09679 has only v1 (19 Oct 2021). The journal version is Discrete Mathematics 346(1) (2023), article 113121.
- The journal Section 3 was not read (ScienceDirect body not fetched). That the journal version changed Conjecture 3.4 is possible but considered unlikely.
- OpenAlex lists no citing works.
- No hits in Omega institute issues and PRs (`2110.09679`, "great-circle thrackle", "thrackle caterpillar"), in the Principia list or clone (352297, 247589, the arXiv id), or in the campaign's LANES and claim evidence beyond this pool's entry.
- A web search finds only the source and older thrackle papers, neither of which settles this conjecture:
  - Cairns–Koussas–Nikolayevsky, *Spherical Thrackles*, assume no leaves.
  - Fulek–Pach, *A computational approach to Conway's thrackle conjecture*, concern planar thrackles, for which T is drawable.
- The review found no short hand argument from the source's Lemmas 2.5–2.11.
- MathDB 247589 is a duplicate record of the same conjecture and counts once.

**Refresh (final check, 2026-11-23).**

- arXiv abs page: still only v1, with no journal reference.
- OpenAlex (W3206172396) and Semantic Scholar (CorpusId 239024756): 0 citing works.
- Omega registry `the-omega-institute/trureturing`: no hits in issues or pull requests for `2110.09679`, "thrackle", "great-circle thrackle", "Collins Roberts caterpillar", 352297 or 247589.
- GitHub code search: for `2110.09679` the only hits are in an Erdős-99 project that cites the source for Woodall's theorem; for "augmented caterpillar thrackle" there are none.
- cmu-l3/reuF2F: no entry for this source; its two thrackle or caterpillar entries are different problems.
- Principia id list and clone, the mio-qwq clone, the omega clone and the openai/math clone: no hits.
- Web searches, including Zenodo: nothing beyond the source and older thrackle papers.
- The journal text remains unread.

## 8. Lean declarations

| Statement | Declaration | Module |
|---|---|---|
| Conjecture 3.4 | `GC.mathdb_352297 : GC.Conjecture34` | GCMain |
| Strictness | `GC.mathdb_352297_strict` | GCMain |
| Containment (Thm 3.2) | `GC.mathdb_352297_containment`, `GC.isAugCat_of_gc` | GCMain, GCContain |
| T not drawable | `GC.t14_not_gc` (from `Thr.T14_refute`) | GCWitness |
| T augmented caterpillar, tree | `GC.t14_isAugCat`, `GC.t14_isTree` | GCWitness |
| Spider not drawable | `GC.spider_not_gcThrackleable` (from `Thr.Spi_refute`) | GCContain |
| Encoding soundness | `GC.inputsSound_of_drawing` | GCBridge |
| Crossing table | `GC.pairCount_eq_one` | GCGeom |
| Checker soundness | `Thr.blockOK_sound` | ThrSound |
| Non-vacuity | `GC.star3_gcThrackleable`, `GC.spider_not_augCat`, `GC.K2_gcThrackleable`, `GC.K2_not_augCat`, `GC.antipodes_long_not_short` | GCVacuity |
