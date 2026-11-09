# Power-domination TAR uniqueness for complete bipartite graphs

DRAFT - MathDB 353203 - 3 November 2026

AI-assisted research manuscript prepared in lane pdtar-manuscript-r1. No human author or affiliation is asserted. This is a draft for independent root adjudication; no acceptance, credit or priority is claimed.

## Abstract

For all positive integers s and t, the power-domination token addition/removal graph of K_{s,t} determines its base graph among finite simple graphs without isolated vertices if and only if neither part has size two. The new ingredient is a labelled rigidity theorem for s,t ≥ 3 outside (3,3). Fort duality converts a small collection of PD and non-PD sets into pair-supported fort neighbourhoods. A two-sided cross-degree argument forces all cross edges, and then excludes internal edges. Published small cases and a published relabelling reduction finish the characterization. A source-only Lean certificate proves the literal iff, including a self-contained Hamming-isometry replacement for the reduction. Root reports a fresh 76-step replay with no audit violations.

## 1. Scope, definitions and statement

All graphs are finite, simple and undirected. The source [1] requires a nonempty vertex set, and defines uniqueness only for a graph with no isolated vertices. Accordingly s,t ≥ 1 throughout the theorem; zero parts and empty graphs lie outside that source scope. For a vertex v write N(v) for its neighbours, N[v] = N(v) ∪ {v}, and N[S] = ∪ {N[v] : v ∈ S}.

Power domination uses simultaneous rounds: P⁰[S] = S, P¹[S] = N[S], and, for i ≥ 2,

Pⁱ[S] = Pⁱ⁻¹[S] ∪ {u : N(v) ∖ Pⁱ⁻¹[S] = {u} for some v ∈ Pⁱ⁻¹[S]}.

A set S is power dominating (PD) if some round is the full vertex set. Each round is monotone in S: if a forcing vertex has more of its neighbours observed, its previously unique missing neighbour is either already observed or remains uniquely missing. Thus PD sets form an upward closed family.

The graph PD^TAR(G) has all PD subsets as vertices, with adjacency when the symmetric difference has cardinality one. There is no extra size cutoff. As in source §3.3, for G without isolated vertices its TAR graph is unique when every graph H without isolated vertices with PD^TAR(H) isomorphic to PD^TAR(G) is itself isomorphic to G. H need not be connected or have a prescribed order.

**Theorem.** For every s,t ≥ 1, PD^TAR(K_{s,t}) is unique if and only if s ≠ 2 and t ≠ 2.

The conjecture occurs immediately after source Proposition p:K33. That source proves stars, the two-vertex-part obstruction and K_{3,3}. The survey [3, arXiv v2] still lists the remaining range as open. Our new mathematical claim is the Core Theorem below, specifically Lemmas 1–6. Fort duality is standard; Lemma 7 was already in the exploratory notes. These attributions are bounded by the access limits in §10.

<!-- PAGE -->

## 2. From a TAR isomorphism to a labelled PD family

**Theorem R** (Bong, Carlson, Curtis, Haas and Hogben, *Graphs Combin.* 39(4) (2023), DOI 10.1007/s00373-023-02677-1; restated as Theorem t:main of arXiv:2406.05509v2).

> Let X be a robust X-set parameter and let G, G′ be base graphs with X^TAR(G) ≅ X^TAR(G′). If X(K₁) = 0 or G and G′ have no isolated vertices, then there is a relabeling of the vertices of G′ such that G and G′ have exactly the same X-sets.

- Power domination is an original, hence robust, X-set parameter. This is stated in the survey ("power domination is an original X-set parameter, so Theorem t:main applies"). The original axioms are checked in the source (§3, "Observe that power domination satisfies the conditions in Definition 2.1").
- The relabeling is a bijection V(G′) → V(G). Equal orders also follow independently from Corollary `pd-deg-dist`(1) (survey `x-deg`): |V(G)| = Δ(PD^TAR(G)). Corollary `c:pd-iso-props`(1) states equality of the two base orders under TAR isomorphism.
- Applicability: both graphs in the uniqueness definition have no isolated vertices, which is exactly the theorem's hypothesis. No connectedness or order assumption on H is needed; the theorem itself yields the equal order and the bijection.

**Consequence.** Let G = K_{s,t} on V = A ⊔ B with |A| = s and |B| = t, and let H have no isolated vertices with PD^TAR(H) ≅ PD^TAR(G).

- Theorem R gives a bijection ψ : V(H) → V. The graph H′ = ψ(H) on V satisfies PD(H′) = PD(K_{A,B}) and H′ ≅ H.
- Conversely, H′ = K_{A,B} gives H ≅ K_{s,t}.

So uniqueness of PD^TAR(K_{s,t}) for s, t ≥ 3 and (s,t) ≠ (3,3) follows from the following.


**Core Theorem.** Let V = A ⊔ B with |A| = s ≥ 3 and |B| = t ≥ 3, excluding (s,t) = (3,3). If H on V has exactly the labelled PD sets of K_{A,B}, then H = K_{A,B}. H need not initially be assumed to have no isolated vertices.

The reduction is published, not a new uniqueness theorem here. To avoid an imported unproved assertion, the Lean certificate proves its PD specialization by the following replacement argument.

Every TAR neighbour of S toggles one base coordinate, so degree is at most n. In a graph without isolated vertices every co-singleton is PD, so the full set attains degree n. TAR isomorphism therefore gives equal base orders. It does not imply that only the full set attains maximum degree.

Let φ be the TAR isomorphism and C the image of the full set. Images of its distinct co-singleton neighbours toggle distinct coordinates of C. Equal orders give a bijection e between base coordinates. Any two PD sets S,T admit a path of length |S Δ T|: add vertices to reach S ∪ T, then delete down to T. Upward closure keeps this path within the PD family. Every TAR path has at least that length because one step changes one coordinate. Mapping paths through φ and its inverse proves preservation of all Hamming distances.

Distances to the full set and its co-singletons recover every coordinate of a subset. Comparing these distances on both sides gives φ(S) = e(S) Δ R for a fixed flip set R. Surjectivity gives the corresponding equivalence for arbitrary subsets, including non-PD subsets. The flip can be removed at the family level: if P(S) iff Q(S Δ R), with P,Q upward closed, then P(S) implies P(S ∪ R), hence Q(S ∖ R), hence Q(S); reversing P and Q gives the converse. After relabelling by e the two PD families are equal.

Finally transport H along the coordinate bijection. The certificate proves that closed neighbourhoods, propagation steps and every observation round transport exactly, giving SamePD for the actual transported graph. No assumption that φ itself is a pure coordinate permutation is required; the possible flip has been normalized at the family level.

<!-- PAGE -->

## 3. Fort duality and pair blockers

**Lemma 0 (standard fort duality).** For every graph G and S ⊆ V(G): S is PD ⇔ F ∩ N[S] ≠ ∅ for every fort F of G.

*Proof.*

(⇐) Suppose S is not PD. The sequence P^i[S] is increasing and stabilises at some O ≠ V. Stability means no v ∈ O has exactly one neighbour outside O. So F = V \ O is nonempty, and every vertex outside F (that is, in O) has 0 or at least 2 neighbours in F. Hence F is a fort, and F ∩ N[S] = ∅ because N[S] = P¹[S] ⊆ O.

(⇒) Let F be a fort with F ∩ N[S] = ∅, and suppose some vertex of F is eventually observed. Let i ≥ 2 be the least round with P^i[S] ∩ F ≠ ∅; then P^{i−1}[S] ∩ F = ∅. Take u ∈ P^i[S] ∩ F, and let v ∈ P^{i−1}[S] with N(v) \ P^{i−1}[S] = {u}.

- v ∉ F, and v has the neighbour u ∈ F. Because F is a fort, v has a second neighbour u′ ∈ F.
- u′ ∉ P^{i−1}[S], so N(v) \ P^{i−1}[S] ⊇ {u,u′}. This is a contradiction.

So F is never observed, and S is not PD. ∎

**Fort facts.** Let F be a fort.

- (F1) If x ∈ F then N[x] ⊆ N[F].
- (F2) If x ∈ N[F] \ F then |N(x) ∩ F| ≥ 2.
- (F3) If {x} is a fort, then x is isolated.

Note also that y ∈ N[x] ⇔ x ∈ N[y]. So F ∩ N[S] = ∅ ⇔ N[F] ∩ S = ∅.

From now on, s, t ≥ 3, and H is a graph on V = A ⊔ B with PD(H) = PD(K_{A,B}). For a ∈ A and b ∈ B write β(a) = N_H(a) ∩ B and α(b) = N_H(b) ∩ A.

**Facts about K = K_{A,B}.**

- (K1) For a ∈ A and b ∈ B, the set {a,b} is PD in K, since N[{a,b}] = V.
- (K2) For x ∈ A, A \ {x} is PD in K: N[A\{x}] ⊇ (A\{x}) ∪ B, and then any b forces x.
- (K3) For distinct x, y ∈ A, A \ {x,y} is not PD in K. The set {x,y} is a fort of K (every b sees both x and y, and every other a sees neither) and it avoids N_K[A\{x,y}] = (A\{x,y}) ∪ B. Then apply Lemma 0.
- The same three facts hold with A and B exchanged.

**Lemma 1.**

- (a) For every fort F of H: either A ⊆ N[F] and |N[F] ∩ B| ≥ 2, or B ⊆ N[F] and |N[F] ∩ A| ≥ 2.
- (b) H has no isolated vertex.

*Proof.*

(a) By (K1) and Lemma 0, N[F] meets {a,b} for all a ∈ A and b ∈ B. So A ⊆ N[F] or B ⊆ N[F]. Suppose B ⊆ N[F]. By (K2) and Lemma 0, N[F] meets A\{x} for every x ∈ A, so N[F] ∩ A is not contained in any singleton, that is, |N[F] ∩ A| ≥ 2. The other case is symmetric.

(b) If v ∈ A were isolated, then {v} would be a fort (vacuously) with N[{v}] = {v}, contradicting (a). The same holds for v ∈ B. ∎

**Lemma 2 (pair forts).**

- For distinct x, y ∈ A there is a fort Ψ = Ψ_{xy} of H with N[Ψ] = B ∪ {x,y}.
- For distinct u, v ∈ B there is a fort Φ = Φ_{uv} of H with N[Φ] = A ∪ {u,v}.

Consequently Ψ_{xy} ⊆ B ∪ {x,y} and Φ_{uv} ⊆ A ∪ {u,v}.

*Proof.* By (K3), A \ {x,y} is not PD in H. Lemma 0 gives a fort Ψ with N[Ψ] ∩ (A\{x,y}) = ∅. Since s ≥ 3, A ⊄ N[Ψ], so Lemma 1(a) gives B ⊆ N[Ψ] and |N[Ψ] ∩ A| ≥ 2. Hence N[Ψ] ∩ A = {x,y}. The B case is symmetric, using t ≥ 3. ∎

The whole problem is symmetric under (A, s) ↔ (B, t), because the PD family of K_{A,B} equals that of K_{B,A}. Every lemma below therefore has a mirror statement.

<!-- PAGE -->

## 4. Cross-degree rigidity and the exceptional pair

**Lemma 3.** β(a) ≠ ∅ for every a ∈ A, and α(b) ≠ ∅ for every b ∈ B.

*Proof.* Suppose β(p) = ∅, so N(p) ⊆ A. Let y ∈ A \ {p} and Ψ = Ψ_{py}. Then p ∈ N[Ψ].

- If p ∉ Ψ, then by (F2) p has two neighbours in Ψ. They lie in Ψ ∩ A ⊆ N[Ψ] ∩ A \ {p} = {y}. That is impossible.
- So p ∈ Ψ, and (F1) gives N(p) ⊆ N[Ψ] ∩ A \ {p} = {y}.

Doing this for two distinct y, y′ ∈ A \ {p} (possible since s ≥ 3) gives N(p) = ∅, contradicting Lemma 1(b). The mirror statement uses t ≥ 3. ∎

**Lemma 4.** No a ∈ A has N(a) = {c} with c ∈ B. Mirror: no b ∈ B has N(b) = {a} with a ∈ A.

*Proof.* Take distinct c′, c″ ∈ B \ {c} (t ≥ 3) and Φ = Φ_{c′c″}. Then a ∈ N[Φ]. Since deg a = 1, (F2) forces a ∈ Φ, and (F1) gives c ∈ N[Φ] = A ∪ {c′,c″}. That is a contradiction. ∎

**Lemma 5.** If |β(a)| = 1 for some a ∈ A, or |α(b)| = 1 for some b ∈ B, then s = t = 3.

*Proof.* Let β(a) = {c}.

**Step (i): the structure around a.** By Lemma 4, N_A(a) ≠ ∅. For y ∈ A \ {a}, put Ψ = Ψ_{ay}. Then a ∈ N[Ψ], and there are two cases.

- (α) a ∈ Ψ. Then by (F1), N_A(a) ⊆ {y}.
- (β) a ∉ Ψ. Then by (F2), a has two neighbours in Ψ ⊆ B ∪ {a,y}. They must be c and y. So a ~ y, c ∈ Ψ and y ∈ Ψ.

Now consider the possible y.

- If some y ∈ A \ {a} were not adjacent to a, case (β) is excluded. Case (α) gives N_A(a) ⊆ {y}, but y ∉ N_A(a), so N_A(a) = ∅, which is impossible. Hence N_A(a) = A \ {a}.
- Since s ≥ 3, |N_A(a)| ≥ 2, so case (α) never occurs. Case (β) holds for every y ∈ A \ {a}, so c, y ∈ Ψ_{ay}.
- By (F1), α(c) ⊆ {a,y} and N_A(y) ⊆ {a}. Using two values of y gives α(c) = {a}. Also N_A(y) = {a} for every y ∈ A \ {a}, since y ~ a.

**Step (ii): the mirror structure around c.** Since |α(c)| = 1, the mirror of step (i) applies to c. So c is adjacent to all of B \ {c}, and N_B(b) = {c} for every b ∈ B \ {c}.

**Step (iii): counting.** Let y, y′ ∈ A \ {a} be distinct and Ψ = Ψ_{yy′}.

- Since a ∈ A \ {y,y′}, Ψ ∩ N[a] = ∅. Here N[a] = A ∪ {c}, so Ψ ⊆ B \ {c}.
- Every b ∈ B \ {c} lies in N[Ψ]. If b ∉ Ψ, it would need a neighbour in Ψ ⊆ B \ {c}, but N_B(b) = {c}. So Ψ = B \ {c}.
- Then {y,y′} = N[Ψ] ∩ A = ∪_{b ∈ B\{c}} α(b). The right-hand side does not depend on the pair {y,y′}.
- So A \ {a} has only one pair, that is, s = 3. The mirror argument with Φ_{bb′} for b, b′ ∈ B \ {c} gives t = 3.

The case |α(b)| = 1 is the mirror image. ∎

**Corollary 5′** (Lemmas 3 and 5). **If (s,t) ≠ (3,3), then |β(a)| ≥ 2 for all a ∈ A and |α(b)| ≥ 2 for all b ∈ B.**

(At (s,t) = (3,3) the structure in Lemma 5 really occurs: it is K_{3,3} with its bipartition relabelled, A′ = {a} ∪ (B\{c}) and B′ = {c} ∪ (A\{a}). This explains why (3,3) is "unique" only up to relabelling.)

<!-- PAGE -->

## 5. Completeness and independence

**Lemma 6.** Let s, t ≥ 3 with (s,t) ≠ (3,3). Then every a ∈ A is adjacent to every b ∈ B.

*Proof.* By symmetry we may assume t ≥ 4. If s ≥ 4 and t = 3, swap the roles of A and B; all ingredients used below have mirror versions.

Suppose a ≁ b with a ∈ A and b ∈ B. Fix b′ ∈ B \ {b} and let Φ = Φ_{bb′}.

- If Φ ∩ A = ∅, then Φ ⊆ {b,b′}. By (F3) and Lemma 1(b), Φ = {b,b′}. Then a ∈ N[Φ] makes a adjacent to b or b′, hence to both by the fort property. This contradicts a ≁ b.
- So there is p ∈ Φ ∩ A. The ensuing contradiction is independent of the initially chosen nonadjacent a; in fact it excludes this branch for every pair {b,b′}. By (F1), β(p) ⊆ {b,b′}. By Corollary 5′, β(p) = {b,b′}.

Since t ≥ 4, pick distinct c, c′ ∈ B \ {b,b′}, and let Φ′ = Φ_{cc′}.

- p ∉ Φ′, since otherwise β(p) ⊆ {c,c′} by (F1).
- p ∈ N[Φ′], so by (F2) p has two neighbours in Φ′ ⊆ A ∪ {c,c′}. Both lie in A because p ≁ c, c′.
- Hence |N_A(p)| ≥ 2. Pick one such neighbour p′ ∈ Φ′ ∩ A. By (F1) and Corollary 5′, β(p′) = {c,c′}.

Symmetrically, p′ ∉ Φ_{bb′} and p′ ∈ N[Φ_{bb′}], and p′ ≁ b, b′. So |N_A(p′)| ≥ 2.

Now let Ψ = Ψ_{pp′}, which uses s ≥ 3.

- If p ∈ Ψ, then N_A(p) ⊆ {p′} by (F1), which is impossible. Likewise p′ ∉ Ψ. So Ψ ⊆ B.
- p ∈ N[Ψ] \ Ψ, so by (F2) p has two neighbours in Ψ ⊆ B. These lie in β(p) = {b,b′}, so b ∈ Ψ.
- By (F1), α(b) ⊆ N[Ψ] ∩ A = {p,p′}. But p′ ≁ b, because β(p′) = {c,c′}. So α(b) ⊆ {p}.

This contradicts Corollary 5′ (|α(b)| ≥ 2). ∎

**Lemma 7** (as in the r119 notes). If A–B is complete and s, t ≥ 3, then A and B are independent, so H = K_{A,B}.

*Proof.* Let x, y ∈ A be distinct and Ψ = Ψ_{xy}.

- Pick z ∈ A \ {x,y}. Then Ψ ∩ N[z] = ∅ by Lemma 2, and N[z] ⊇ B by completeness. Since Ψ ⊆ B ∪ {x,y}, this gives Ψ ⊆ {x,y}.
- By (F3) and Lemma 1(b), Ψ = {x,y}.
- So no z ∈ A \ {x,y} is adjacent to x (or to y).

As every edge xz inside A has some y ∉ {x,z} (s ≥ 3), A is independent. B is independent symmetrically. ∎

**Core Theorem** follows from Lemmas 6 and 7. ∎

The proof establishes a slightly stronger local statement: the core uses only the sets specified in K1–K3, on both sides. Full equality of PD families supplies these facts, but every later appeal is to them or to a consequence of fort duality. This strengthening follows by reading the dependency chain of the argument, independently of the finite checks.

<!-- PAGE -->

## 6. Small cases and the full iff

**Theorem.** For all positive integers s, t: PD^TAR(K_{s,t}) is unique ⇔ s ≠ 2 and t ≠ 2.

*Proof.* By symmetry, assume s ≤ t.

- **s = 2 (any t ≥ 2).** Source Corollary labelled `mPDS:n-3:K2t`: PD^TAR(K_{2,t}(e)) ≅ PD^TAR(K_{2,t}). The graph K_{2,t}(e) has no isolated vertices and one more edge, so it is not isomorphic to K_{2,t}. Hence the TAR graph is not unique.
- **t = 2, s = 1.** K_{1,2} = P₃. In P₃ and in K₃ every nonempty set is PD: a leaf of P₃ dominates the centre, and the centre then forces the other leaf. On a common 3-element vertex set the two TAR graphs are equal, and K₃ ≇ P₃. So the TAR graph is not unique.
- **s = t = 1.** PD^TAR(K₂) ≅ P₃. If H has no isolated vertices and PD^TAR(H) ≅ P₃, then |V(H)| = Δ(P₃) = 2 by source Corollary `pd-deg-dist`(1), equivalently survey `x-deg`. So H = K₂.
- **s = 1, t ≥ 3.** Source Theorem labelled `upperPDn-3` (journal numbering is unverified and omitted).
- **s = t = 3.** Source Proposition labelled `p:K33` (journal numbering is unverified and omitted).
- **s, t ≥ 3, (s,t) ≠ (3,3).** Theorem R together with the Core Theorem, as in §2. **This is the new part.** ∎

Here K_{2,t}(e) means adding the edge between the two vertices in the size-two part. For completeness, the family equality used for this witness has a uniform direct description for all t ≥ 1: a set is PD precisely when it is nonempty and either meets the size-two part or omits at most one vertex of the other part. A chosen vertex in the two-part observes all opposite vertices, and any opposite vertex then forces the other two-part vertex if necessary. A nonempty set on the other side observes both two-part vertices and can finish exactly when at most one opposite vertex remains. Two missing opposite vertices form a fort in both graphs and obstruct completion otherwise. The added edge does not change this reasoning. Non-isomorphism follows from a triangle in the witness, whereas every complete bipartite graph is triangle-free. When t = 1 this is exactly P₃ versus K₃.

The Lean star proof re-proves the published conclusion by forts. A centre singleton is PD while leaf singletons are not when there are at least three leaves. Pair-fort neighbourhoods are supported on a leaf pair and the centre. A supported fort containing the centre either forms a proper component, incompatible with a PD centre singleton, or is a two-vertex fort. Transposing the vertices of a two-vertex fort is an automorphism, forcing equal singleton PD status for the centre and a leaf, a contradiction. Thus the fort is the leaf pair. Its neighbourhood forces both centre edges, and a third leaf excludes all leaf edges. This gives labelled equality in both orientations.

For K_{3,3}, every pair is PD and every singleton is not. The formal proof first forces at least three neighbours at every vertex using forts avoiding singletons. A fourth neighbour would leave at most one vertex unobserved after domination; no isolation would allow completion, contradicting singleton failure. Hence every degree is three. Fix v and a fort avoiding N[v]. Its complement support has two vertices, so no isolation makes the fort exactly that pair F. Every pair {v,u} is PD, so N[F] is all vertices except v. The set F ∪ {v} and its complement both have size three. Each vertex of the complement is adjacent to v and, by the fort property, to both members of F. Degree three excludes every internal edge. This proves isomorphism to K_{3,3} without graph enumeration or the source’s odd-cycle classification.

This explains the difference between labelled rigidity and uniqueness: at (3,3) there are distinct labelled copies with the same PD family, but all are isomorphic. The separate six-vertex argument is essential.

<!-- PAGE -->

## 7. Formal statement and correspondence

The source-only archive has SHA256

3a599c52f33e8fcbed9294de07b9b6a549606b7d6bd693fdfd834304a67173b4.

It is byte-identical to pdtar-formal-r4/pdtar-source.zip. The final theorem is unconditional:

PDTAR.mathdb_353203 (s t : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t) :
TARUnique (completeBipartiteGraph (Fin s) (Fin t)) ↔ (s ≠ 2 ∧ t ≠ 2).

The following table records interfaces, not additional assumptions. Every Remaining Prop is discharged in the final import closure.

| Interface | Mathematical meaning / discharge |
| Defs.closed | closed neighbourhood N[S] |
| Defs.step; obs | simultaneous propagation; rounds 0 and 1 as in §1 |
| Defs.IsPD; IsFort | eventual full observation; nonempty fort |
| Defs.NoIsolated | every vertex has a neighbour |
| Defs.tar; TARUnique | one-token TAR; quantification over comparison graphs |
| Remaining Props | Reduction, Core, Edge, Stars, ThreeThree, Two specifications |
| reductionRemaining | ReductionProof: full PD relabelling reduction |
| coreRemaining | CoreSmallProof and CoreProofFinal: Lemmas 1–7 |
| twoWitnessRemaining | SmallTwoWitness: actual added-edge witnesses, both orientations |
| starRigidityRemaining | SmallStarComplete: fort proof of star rigidity |
| threeThreeRigidityRemaining | SmallK33Complete: degree/fort partition proof |
| Final | core endpoint and conditional small-case assembly |
| FinalComplete | supplies both rigidity proofs; unconditional iff |

SmallEdge supplies EdgeRemaining from reductionRemaining. StarsRemaining and ThreeThreeRemaining follow from the corresponding rigidity theorem and the reduction. TwoRemaining follows from the witnesses. Historical comments about open obligations describe earlier packets; they do not survive as endpoint hypotheses. The source archive contains 34 mathematical modules.

SamePD means pointwise equivalence of the two labelled PD predicates; it asserts no graph isomorphism. Parts specifies disjoint covering subsets. The target is mathlib’s actual completeBipartiteGraph on Fin s ⊕ Fin t, with precisely the cross edges. Exact observation-round transport proves invariance under relabelling, rather than substituting an abstract closure predicate for power domination.

TARUnique omits the source’s separate prerequisite that G has no isolated vertices. This is harmless here: sum_noIsolated proves it for all positive s,t by choosing a vertex in the other part. Lean also permits an empty comparison type W. On W the empty set is PD and TAR has one vertex. The theorem small_empty_comparison excludes an isomorphism to the positive target using the unconditional reduction and an inverse base-vertex bijection; it does not assume W nonempty. Universe-zero finite types include Fin n representatives of every finite graph isomorphism class.

SmallStatement proves literal agreement of step with the unique-unobserved-neighbour equation and of IsFort with the cardinality definition. The empty set is never PD on a nonempty graph. Fort duality is proved from the actual rounds and finite stabilization.

<!-- PAGE -->

## 8. Certificate audit, replay and trust

Root’s fresh replay, dated 2026-11-03T08:16:10.834781+00:00, records status PASS with 34 strict module builds, 34 leanchecker calls, one declaration audit and seven expected-failure controls: 76 of 76 steps. The complete replay-result.json is reproduced verbatim in the appendix, so this report can be compared directly with its frozen source.

The audit enumerates all 318 distinct local declarations, including generated declarations. Its 34-module set equals the entire local import closure of FinalComplete: “34 modules, checked inside Lean (CLOSURE_EQUALS_AUDITED 34)”. Root independently parsed every DECL record. All 318 declaration flag records are false; violations and unsafe_rec counts are zero. The transitive axiom union and the endpoint’s axioms are exactly propext, Classical.choice and Quot.sound. No sorry, admit, added axiom, unsafe or native_decide is admitted into the final mathematical closure. The audit also checks partial declarations, implemented_by and extern.

The seven negative controls are NegK23, NegK34, NegEndpointTwo, NegFort, NegCorruptedFamily, NegStarTwo and NegK33Added. Root reports all return code 1 with substantive errors. These test false PD/degree or endpoint claims, an empty fort, a corrupted family bridge, uniqueness at K_{1,2}, and an added-edge rigidity assertion at K_{3,3}. In the added-edge test the actual witness and its triangle obstruction compile before the intended false isomorphism claim fails. These controls test the checking pipeline; they are not mathematical assumptions or replacements for the theorem.

The independent fidelity lane separately compiled all 34 modules, ran the final leanchecker and full declaration audit, and checked concrete round examples. That bounded check is distinct from root’s decisive full fresh replay. No Lean, lake or leanchecker process was run in this manuscript lane. This lane only checks packet path safety and hashes, writes prose, renders the PDF and packages the dossier.

The packet pins Lean 4.34.1 and mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612. Its manifest binds the Lean binary, leanchecker binary and mathlib Basic source by SHA256. Trust includes prebuilt pinned mathlib oleans; leanchecker shares the installation. The audit is of the local closure and its transitive axiom budget, not a fresh rebuild of all mathlib or an independently implemented kernel. Formal correctness does not establish novelty, significance or source access beyond the documented correspondence.



Toolchain SHA256 pins: Lean binary e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550; leanchecker binary ccef1bfe9bfeecea65137d94a69033c1a89f360711f50fa3178e7ba3e696fcbe. The manifest additionally binds mathlib Basic.lean with SHA256 97f49ff9b52fe1906b6a2071422b35ec496cd6b3d9d81043e77e56efceb0a73f.

The unchanged packet includes a resumable replay driver. In a fresh directory inside the manuscript lane, copy pdtar-source.zip and scripts/replay.py from the safe extraction, preserving the scripts subdirectory. Run the driver with --init, then --resume --steps 10 repeatedly until complete. It rechecks source and binary pins, previous log hashes and build-object inventory. Each heavy child is limited independently to two CPUs, CPU 120 s, wall 140 s, sampled RSS 6 GiB and MALLOC_ARENA_MAX=2. The reproducibility note gives full commands; these are instructions for a future authorized replay, not commands executed here.

The manuscript lane claims zero accepted credit. Root alone assesses the paper and acceptance.

<!-- PAGE -->

## 9. Computational evidence, separate from proof

The exploratory r119 SAT work encoded the labelled-family problem using forcing chronologies for PD sets, forts for non-PD sets, and an edge-set inequality excluding K itself. Its recorded UNSAT instances are exactly (3,4), (3,5), (4,4), (4,5), (3,6), (4,6), (5,5), (3,7), (5,6), (3,8), (3,9), (4,7), using s ≤ t. Equivalently, these cover the core range with s+t ≤ 11 and the extra (3,9). The notes summarize this as “every s + t ≤ 11” plus (3,8), (3,9), (4,7); the small-case exceptions are excluded from that phrase. Controls at (2,3) and (2,4) were SAT as expected. At (3,3), SAT solutions were relabelled copies. These logs are evidence, without a claimed independent UNSAT certificate replay here.

The adversarial review independently enumerated all labelled graphs at five sizes and tested the lemmas under their stated hypotheses. Its H2 condition consists of K1–K3 on both sides. The number of full PD-family matches agrees with the H2 survivors in these runs:

| Parts | All graphs examined | H2 survivors / full-family matches |
| (3,3) | 32,768 | 10 / 10 |
| (3,4) | 2,097,152 | 1 / 1 |
| (4,3) | 2,097,152 | 1 / 1 |
| (4,4) | 268,435,456 | 1 / 1 |
| (3,5) | 268,435,456 | 1 / 1 |

Every completed lemma check reports zero failures. At (3,3) the ten graphs are precisely labelled copies of K_{3,3}, and nine show the single-cross-neighbour structure of Lemma 5. At the other sizes the sole survivor is the prescribed K. In particular the (4,4) and (3,5) tests are exhaustive over all 2²⁸ graphs, not samples. Per-lemma hypotheses and batching details are in the frozen review. One batch reached its CPU cap and was rerun as two smaller batches; only successful disjoint batches entered the aggregate.

Fort duality was separately checked over all graph/subset pairs at orders five and six, with no mismatch, and on a reported partial range at order seven. These finite checks helped locate and test the argument; none proves an infinite parameter range. The proof of the Core Theorem is the fort argument in §§3–5, and the full positive-integer endpoint is supported by its Lean certificate.

## Related work and novelty boundary

Source [1] gives the star and K_{3,3} positive cases and the K_{2,t}(e) obstruction. The robust-parameter relabelling theorem is from [2], read here through the self-contained survey treatment [3]. The survey’s domination analogue uses dominating-set arguments that do not supply the power-domination cross-degree step. We claim Lemmas 1–6 as the new mathematical ingredient of this dossier, not fort duality, the general reduction, the published small-case conclusions, or their formalization alone.

The cached review’s bounded arXiv, author-listing, OpenAlex and web searches found no resolution. Root’s later registry refresh screened complete Omega D5 and Problems trees by paths with targeted body reads, not an exhaustive full-body search. It records OpenAI head 4eaee87548250b2682affda7d05d947c05554bae and Omega head b576c901e75413f0e844a94b3b237ebced23b75b. The refresh reports no matching PD-TAR resolution. These are bounded historical checks, not universal novelty clearance or a priority claim.

<!-- PAGE -->

## 10. Access limits, bibliography and dossier

The arXiv TeX of [1] and [3] was available and is copied with web receipts. The La Matematica journal text of [1] was not read directly: the Springer route returned a challenge page and the Swarthmore route returned HTTP 403. Search-engine snippets about journal numbering or the conjecture’s continued presence are unverified indirect evidence. We therefore use source TeX labels, including pd-deg-dist(1), c:pd-iso-props(1), upperPDn-3, mPDS:n-3:K2t and p:K33, rather than asserting journal theorem numbers.

The earlier review additionally records an Iowa State timeout, an AIM 404 and a retired SelectedWorks route. The read survey arXiv v2 still lists the conjecture as open, and the review records indirect evidence that its journal version, dated 31 March 2026, does also. That is evidence about the survey’s treatment; it is not direct reading of the source journal paper. No new external access, messages, browser tabs or uploads were used in this manuscript lane. We do not claim to have exhaustively searched the literature.

## Bibliography

[1] Beth Bjorkman, Chassidy Bozeman, Daniela Ferrero, Mary Flagg, Cheryl Grood, Leslie Hogben, Bonnie Jacob and Carolyn Reinhart. Power domination reconfiguration. arXiv:2201.01798 (2022); La Matematica 5 (2026), article 8. DOI 10.1007/s44007-025-00187-5. The DOI and journal metadata are supported by the frozen metadata receipts; the mathematical text used here is the arXiv TeX.

[2] N. H. Bong, J. Carlson, B. Curtis, R. Haas and L. Hogben. Isomorphisms and properties of TAR reconfiguration graphs for zero forcing and other X-set parameters. Graphs and Combinatorics 39(4) (2023). DOI 10.1007/s00373-023-02677-1. Article numbering is omitted. The reduction is used through [3, Theorem t:main and its proof chain], not a claimed direct reading of the journal text.

[3] Bryan Curtis, Mary Flagg and Leslie Hogben. TAR reconfiguration for vertex set parameters. arXiv:2406.05509v2, 28 September 2025; journal version recorded in the review as published 31 March 2026. No unverified journal DOI is supplied. Relevant labels: t:main, x-deg, isomorph-isometry-u and isomorph-same-zfs.

## Reproducibility and provenance

The dossier contains this Markdown source, its PDF, the corrected ordinary PROOF.md, exact MathDB raw record including its terminating newline, source copies and access receipts, the two review reports, root’s replay and registry JSON, exploratory SAT logs and the review’s exhaustive-check logs. The MathDB line is chunk-0008, one-based line 2515; its raw SHA256 is fb3b4a73e92d8196e75e36cb9ee60ad6ad119a70c59be6cb44744734c24f3935.

The source-only proof packet is reused byte for byte, not repackaged. A separate safe extraction checks all member paths, rejects symlinks and build objects, and matches all manifest file hashes without executing Lean. The before and after input manifests bind the frozen inputs. The outer dossier manifest inventories deliverables; its ZIP checksum is recorded externally to avoid circular self-hashing. Every PDF page is rendered and visually inspected, with page images and a QA receipt retained.

These artifacts make the draft reviewable. They do not self-accept it. Root alone decides whether the mathematical and campaign acceptance requirements are met.

<!-- PAGE -->

## Appendix. Root’s replay result (verbatim)

The following is the complete frozen pdtar-parent-final-r1/replay-result.json, including its stated trust limits.

```json
{
 "utc": "2026-11-03T08:16:10.834781+00:00",
 "mathdb_id": 353203,
 "status": "PASS",
 "source_archive": {
  "file": "pdtar-formal-r4/pdtar-source.zip",
  "sha256": "3a599c52f33e8fcbed9294de07b9b6a549606b7d6bd693fdfd834304a67173b4",
  "copied_to": "pdtar-parent-final-r1/pdtar-source.zip"
 },
 "driver": "scripts/replay.py from the packet (byte-identical to the lane copy); fresh --init extraction with path-safety and no build objects; every step re-checks source, pin and log hashes and the build-object inventory",
 "steps": {
  "builds": 34,
  "leanchecker": 34,
  "audit": 1,
  "negative_controls": 7,
  "total": 76
 },
 "audit": {
  "records": 318,
  "distinct": 318,
  "flags_all_false": 318,
  "axiom_union": [
   "Classical.choice",
   "Quot.sound",
   "propext"
  ],
  "closure_equals_audited": "34 modules, checked inside Lean (CLOSURE_EQUALS_AUDITED 34)",
  "violations": 0,
  "unsafe_rec": 0,
  "root_parse": "root parsed every DECL record independently"
 },
 "negative_controls": "NegK23, NegK34, NegEndpointTwo, NegFort, NegCorruptedFamily, NegStarTwo, NegK33Added: all returncode 1 with substantive errors",
 "endpoint": {
  "name": "PDTAR.mathdb_353203",
  "statement": "(s t : \u2115) (hs : 1 \u2264 s) (ht : 1 \u2264 t) : TARUnique (completeBipartiteGraph (Fin s) (Fin t)) \u2194 (s \u2260 2 \u2227 t \u2260 2)",
  "axioms": [
   "propext",
   "Classical.choice",
   "Quot.sound"
  ]
 },
 "trust_limits": [
  "Prebuilt pinned mathlib oleans trusted",
  "leanchecker shares the installation"
 ]
}```
