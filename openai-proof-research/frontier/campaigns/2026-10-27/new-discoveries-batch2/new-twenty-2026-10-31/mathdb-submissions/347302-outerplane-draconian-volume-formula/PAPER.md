# Normalized volumes of PQ-type adjacency polytopes of outerplane graphs: the Davis–Chen formula with the isolated-vertex correction

Claude Opus 5.5 produced the proof, the Lean formalization, the first review and the original manuscript. GPT-6.2 Sol independently reviewed the proof and formal statement, ran the checks described in §6 and revised this manuscript. The Lean code and its appendix are from the original packet.

## Abstract

Davis and Chen conjectured (Conjecture 36 of arXiv:2007.11051, Electron. J. Combin. 29(1) (2022) #P1.61) that their Eq. (9) gives the normalized volume of the PQ-type adjacency polytope of every outerplane graph. They proved it for blocks that can be built by their subdivision and triangle recurrences. The printed formula assigns an isolated vertex a factor of 2 even though its normalized volume is 1. With that factor corrected, the source's volume and product theorems reduce the assertion to a count for polygon dissections, which represent the 2-connected outerplane blocks. If B is a dissection of an n-gon with bounded faces F, then the number of D(B)-draconian sequences equals 2^{1+S(B)} ∏_F deg_{B^{(**)}}(v_F). We prove this statement for every polygon dissection and formalize it in Lean 4 with Mathlib. For a dissection, bounded faces are represented by the vertex sets inducing cycles. The extended-weak-dual degree counts neighbouring bounded faces and edges on the outer boundary. The key new ingredient is an exact count of draconian sequences when a cycle is glued along an edge. The count is multiplicative when the edge is *good*, and every outer edge of a dissection is good.

## 1. The conjecture and the source's definitions

### 1.1 Source statement and notation

In Davis–Chen, a \(D(G)\)-draconian sequence on a graph \(G\) with \(N\) vertices is a nonnegative integer assignment of sum \(N-1\). For every nonempty subset \(S\) of vertices, its sum over \(S\) must be strictly smaller than the size of the closed neighbourhood of \(S\) (Definition 1, rephrased after Theorem 8). Definition 33 forms the extended weak dual from the dual on bounded faces by adding a pendant edge at a bounded face for each edge that also borders the outer face. For a block \(B\), write \(S(B)=\sum_{F}(\deg_{B^{(**)}}(v_F)-3)\), with sums and products over its bounded faces.

Corollary 35 gives the following product over the blocks \(B\) of the connected components, assuming that every block of order at least three is obtainable from a cycle by the permitted subdivision and triangle recurrences.

\[
\operatorname{NVol}(\nabla^{\mathrm{PQ}}_G)
=\prod_B \left(2^{1+S(B)}\prod_{F}\deg_{B^{(**)}}(v_F)\right). \tag{9}
\]

Conjecture 36 extends Eq. (9) to all outerplane graphs. Theorem 8 identifies the normalized volume of a connected graph with its draconian count. Proposition 12 gives the product over disjoint components. The leaf-block case of Theorem 13 gives the product within each connected component. [Davis–Chen, arXiv v4](https://arxiv.org/abs/2007.11051v4)

### 1.2 Two remarks on the statement

**The MathDB record.** The record prints the block factor as 2^{|V(B)| − 2|F(B)|} ∏ deg. This is a transcription error. For a 2-connected outerplane block, deg_{B^{(∗∗)}}(v_F) = |F| and 1 + S(B) = |V(B)| − |F(B)| − 1 (Corollary 5.7 below). The two exponents agree only when |F(B)| = 1. The record's formula is already false for K_2 (it gives 4, the true value is 2) and for two triangles sharing an edge (9 against 18). The theorem below uses the source exponent and corrects the isolated-vertex factor.

**Isolated vertices.** The source says that a block may be an isolated vertex. Eq. (9) then assigns it the factor 2^{1+0} = 2, but NVol(∇^{PQ}_{K_1}) = 1 (source, proof of Proposition 12). So Eq. (9), read literally, is false for any graph with an isolated vertex. Corollary 35 has the same slip and Proposition 12 gives the intended factor. The statement we prove is Eq. (9) with one-vertex blocks contributing 1, or equivalently Eq. (9) verbatim for outerplane graphs without isolated vertices.

## 2. What is proved, and what is formalized

**Theorem A (block form, formalized).** Let n ≥ 3 and let B be a polygon dissection with vertices 0, …, n−1, outer cycle 0 — 1 — ⋯ — (n−1) — 0, and a set of pairwise non-crossing chords. Let F(B) be the vertex sets inducing a cycle in B. Then
|D(B)| = 2^{1+S(B)} ∏_{F∈F(B)} deg_{B^{(∗∗)}}(v_F),
where deg_{B^{(∗∗)}}(v_F) is the number of other bounded faces sharing an edge with F plus the number of edges of F on the outer cycle, and S(B) = Σ_F (deg_{B^{(∗∗)}}(v_F) − 3) ≥ 0.

**Corollary B (Conjecture 36 with the isolated-vertex correction).** For every outerplane graph G on at least one vertex, NVol(∇^{PQ}_G) is given by Eq. (9), with one-vertex blocks contributing 1.

*Proof of Corollary B from Theorem A.* Proposition 12 gives the product over components and assigns volume 1 to the point polytope of an isolated vertex. In a connected component with more than one block, take a leaf block \(B\) of the block-cut tree and its unique cut vertex \(v\). Apply the leaf-block case of Davis–Chen Theorem 13 to \(B\) and the connected remainder \(B'\), which meet only at \(v\). Repetition gives the connected block product.

For clarity, the proof of Theorem 13 applies to a one-vertex union of two connected graphs \(A,B\) with at least two vertices on each side and no edges between their private vertices. Combine two draconian vectors by summing their entries at the common vertex \(v\). For a subset meeting both sides, the two closed neighbourhoods overlap in at most \(v\), so the two strict inequalities together imply the required strict inequality. For a subset confined to one side, its inequality follows directly if it avoids \(v\). If it contains \(v\), the other side is tested on \(\{v\}\) and the two neighbourhoods overlap at \(v\). Conversely, from a draconian vector \(x\) of the union keep the private entries on each side and choose the entry at \(v\) to make each side total its order minus one. These entries are nonnegative by testing the private vertices of each side, and their sum is \(x_v\). For a subset of one side avoiding \(v\), its neighbourhood is the same in the union. For a subset containing \(v\), test its union with the entire other side and subtract that other side's total. This proves the bijection and, by Theorem 8, the needed product of volumes. The leaf-block hypothesis supplies this separation. The unrestricted wording of Theorem 13 allows an internal block such as the middle edge of a four-vertex path, for which its proposed remainder need not be connected.

A bridge block is \(K_2\). Its two draconian vectors are \((1,0)\) and \((0,1)\), so Theorem 8 gives volume 2, agreeing with Eq. (9). Every larger outerplane block is 2-connected. Its outer boundary is a Hamiltonian cycle and all other edges are noncrossing chords. Label the vertices in cyclic boundary order to obtain a polygon dissection. The geometric bounded faces are exactly the induced cycles: at each ear step of Propositions 5.3 and 5.4 the new face is the ear polygon, and the old bounded faces persist. The same induction in Proposition 5.6 shows that two distinct bounded faces share at most one edge, so counting adjacent faces counts weak-dual edges with the correct multiplicity. Theorem A and Theorem 8 now give the claimed factor for every larger block. ∎

**Formal endpoint.** Lean proves Theorem A as `mathdb347302 : Conj36Block` and proves `Dissection.S_nonneg`. It also computes the draconian count for \(K_2\) in the induction base. The reduction to volumes uses Davis–Chen Theorem 8, whose proof applies the root-polytope volume and lattice-point results of Postnikov (2009), Theorems 12.2 and 11.3. The product over all blocks, the identification with an outerplane embedding and the isolated-vertex correction are on paper. [Postnikov](https://arxiv.org/abs/math/0507163)

### 2.1 The Lean definitions next to the source

| Source | Lean (`src/Drac.lean`, `src/Statement.lean`) |
|---|---|
| D(G)-draconian sequence: (a_i) ∈ Z^N_{⩾0}, Σ a_i = N − 1, and a_{i_1} + ⋯ + a_{i_k} < \|{i_1,…,i_k} ∪ ⋃ N_G(i_j)\| | `Drac.IsDraconian G x := ∑ i, x i = card V - 1 ∧ ∀ S, S.Nonempty → ∑ i ∈ S, x i < (cnbhd G S).card` with `cnbhd G S := S ∪ univ.filter (fun j => ∃ i ∈ S, G.Adj i j)`; `Drac.draconian G` is the finite set of such `x : V → ℕ` (`mem_draconian`: the coordinate bound used to make it a `Finset` is automatic) |
| 2-connected outerplane graph (block with ≥ 3 vertices) with its outerplane embedding | `Dissection n`: chords `(i,j)` with `i + 2 ≤ j`, `(i,j) ≠ (0,n−1)`, pairwise non-crossing (`¬(c.1 < d.1 < c.2 < d.2)`); `D.graph`: outer cycle plus chords |
| F(B), bounded faces | `Drac.faces G`: vertex sets `A` with `3 ≤ \|A\|`, every vertex of `A` with exactly two neighbours in `A`, and no nonempty `B ⊆ A`, `B ≠ A`, closed under neighbours inside `A` (that is, G[A] is a connected 2-regular graph, a cycle) |
| deg_{B^{(∗∗)}}(v_F): dual edges to other bounded faces plus o(F) pendant edges | `Dissection.ewdDeg D F`: number of faces `F' ≠ F` with an edge of `B` inside both, plus number of outer-cycle edges `(i,j)` (`j = i+1` or `(0,n−1)`) inside `F` |
| S(B) = Σ_F (deg − 3) | `Dissection.S D : ℤ` |
| Eq. (9) for one block, draconian form | `Conj36Block := ∀ n ≥ 3, ∀ D : Dissection n, (draconian D.graph).card = 2 ^ (1 + D.S).toNat * ∏ F ∈ faces D.graph, D.ewdDeg F` |

The `toNat` is harmless: `Dissection.S_nonneg` proves `0 ≤ D.S`.

## 3. Notation and two elementary facts

G is a finite simple graph on V, N = |V|. For S ⊆ V, N[S] = S ∪ ⋃_{s∈S} N(s), and x(S) = Σ_{i∈S} x_i. D(G) is the set of x ∈ Z^V_{≥0} with x(V) = N − 1 and x(S) ≤ |N[S]| − 1 for all S ≠ ∅.

(F1) N[S ∪ T] = N[S] ∪ N[T] and N[S ∩ T] ⊆ N[S] ∩ N[T]. Hence |N[S∪T]| + |N[S∩T]| ≤ |N[S]| + |N[T]|.

(F2) |D(G)| is invariant under relabelling the vertices (Lean `card_draconian_congr`).

## 4. Gluing a cycle along an edge

Let uv be an edge of G, p ≥ 1, and let H = G ∪_{uv} C_{p+2} be G with a new path u — w_1 — ⋯ — w_p — v (Lean `glue G u v p` on V ⊕ Fin p). Put positions 0 = u, 1, …, p = w_1, …, w_p, p+1 = v. For z ∈ Z^p_{≥0} put d_t = z_t − 1, P_0 = 0, P_j = d_1 + ⋯ + d_j, and T = P_p.

### 4.1 Neighbourhoods

For S = S_G ⊔ S_W (S_G ⊆ V, S_W ⊆ {1,…,p}):
|N_H[S]| = |N_G[S_G] ∪ J(S_W)| + |Ω_σ(S_W)|,
where J(S_W) ⊆ {u, v} contains u iff 1 ∈ S_W and v iff p ∈ S_W, σ = ([u ∈ S_G], [v ∈ S_G]), and Ω_σ(S_W) is the set of positions t ∈ [1,p] with t ∈ S_W, t ± 1 ∈ S_W, or (σ_u and t = 1) or (σ_v and t = p) (Lean `cnbhd_glue`). Write φ_σ(S_W) = |Ω_σ(S_W)| − z(S_W) and ψ(S_W) = |N_P[S_W]| − z(S_W), where N_P is the closed neighbourhood in the path 0, …, p+1.

### 4.2 The path inequalities (run induction)

**Lemma 4.1 (intervals).** For 0 ≤ i < j ≤ p and the interval I = {i+1, …, j}:
φ_σ(I) = [i ≥ 1] + [j < p] + [σ_u ∧ i ≥ 2] + [σ_v ∧ j ≤ p−2] − (P_j − P_i), and ψ(I) = 2 − (P_j − P_i).

**Lemma 4.2 (fill and split).** If t ∉ S and both t−1 and t+1 belong to S, then Ω_σ(S ∪ {t}) = Ω_σ(S) and N_P[S ∪ {t}] = N_P[S]. Hence φ_σ and ψ do not increase when the gap is filled. If S = I ⊔ B with I an interval ending at j and B nonempty with every element at least j + 3, then φ_σ(I ∪ B) = φ_{(σ_u,0)}(I) + φ_{(0,σ_v)}(B) and ψ(I ∪ B) = ψ(I) + ψ(B).

**Lemma 4.3 (run induction).** A property of subsets of {1,…,p} that holds for ∅ and for all intervals, is inherited by S from S ∪ {t} when t fills a gap of size one, and is inherited by I ∪ B from B in the situation of Lemma 4.2, holds for all subsets. *Proof:* strong induction on the number of holes, max S − min S + 1 − |S|. Filling a gap of size one removes one hole. Splitting off the first run gives B at least two fewer holes. ∎

Say z satisfies (R) if P_j − P_i ≤ 1 for all i < j, and (Fl) if P_i − P_j ≤ 2 for all i < j. Define
C_u = 1 if T ≤ −1 and all P_j ≤ 0, else 0;  C_v = 1 if T ≤ −1 and all P_j ≥ T, else 0.

**Proposition 4.4.** Assume (R) and T ≤ 0. Then for all S ⊆ {1,…,p}: φ_{00}(S) ≥ 0, φ_{10}(S) ≥ C_u, φ_{01}(S) ≥ C_v. Under (R) alone, ψ(S) ≥ 1 for S ≠ ∅. If also (Fl), then C_u + C_v ≥ −T and φ_{11}(S) ≥ −T.
*Proof.* Lemma 4.3. For (00), every proper interval contributes at least one boundary position, and the full interval has value −T. For (10) only C_u=1 needs an additional check. A proper prefix has P_j ≤ 0, an interval strictly inside has at least two boundary positions, and a suffix either has two such positions or starts just after position 1, where T−P_1 ≤ 0. The full interval contributes −T ≥ 1. Reversing the path gives (01). Every nonempty interval gives ψ ≥ 1 by (R).

For (11) put k=−T. By (Fl), k≤2. The case k=0 follows from (00). For k=1 the endpoint step bound covers a proper prefix ending at p−1, since P_{p−1}≤T+1=0. Any shorter prefix has two boundary positions and P_j≤1 by (R). Reverse for suffixes. An interior interval has at least two boundary positions and rise at most one. For k=2, (R) and (Fl) applied against 0 and p force −2≤P_j≤0 throughout, so C_u=C_v=1. A proper prefix has two boundary positions unless it ends at p−1, in which case P_{p−1}≤−1 suffices. Reverse for suffixes. An interior interval has at least three boundary positions unless i=1 and j=p−1, where P_j≤−1≤P_i. For either k the full interval has value k.

For the run induction, the empty-set bounds hold directly. Filling a single-position gap preserves the required bounds by Lemma 4.2. Splitting at a larger gap gives the required (00), (10), (01) and ψ bounds from the interval and remaining pieces. The (11) split uses the (10) and (01) bounds and C_u+C_v≥k. This last inequality is immediate for k=0 and was checked above for k=2. For k=1, failure of both conditions would give a prefix level at least 1 and one at most −2, a rise or a fall of at least 3. ∎

**Witnesses.** S = ∅ gives φ_{10} = 1. S = {1,…,p} gives φ_σ = −T. If P_j ≥ 1 with j < p, S = {1,…,j} gives φ_{10} = 1 − P_j ≤ 0. Symmetrically for φ_{01}. If P_i − P_j ≥ 3 for some i < j, a set of the form {1,…,i} ∪ {j+1,…,p} (one part possibly empty) has φ_{11} ≤ −T − 1. Thus under (R) and T≤0 the minima of φ_{10} and φ_{01} are C_u and C_v, respectively, and the minimum of φ_{11} equals −T exactly when (Fl) holds.

### 4.3 The fibres

Write x = (y, z) with nonnegative integer coordinates y on V and z on the ear. Put k = −T and assume the total x(V(H)) = |V(H)|−1 throughout the fibre tests.

**Theorem 4.5 (fibres).**
(a) If x ∈ D(H), then z satisfies (R), (Fl) and T ≤ 1.
(b) If (R), (Fl) and T ≤ 0, then (y, z) ∈ D(H) iff y = x′ + a e_u + (k − a) e_v with x′ ∈ D(G) and k − C_v ≤ a ≤ C_u.
(c) Call uv *good* if for every y with y + e_u, y + e_v ∈ D(G), and every nonempty S ⊆ V ∖ {u,v} with u, v ∈ N[S], we have y(S) ≤ |N[S]| − 2. If uv is good, (R) holds and T = 1, then (y, z) ∈ D(H) iff y + e_u ∈ D(G) and y + e_v ∈ D(G).

*Proof.* (a) (R) is ψ ≥ 1 on intervals. Taking S_G = V gives φ_{11}(S_W) ≥ −T for all S_W. A fall of 3 would contradict the witness above. T ≤ 1 is (R) for (0, p).
(b) "⇐": check all S = S_G ⊔ S_W. If S_G = ∅, use ψ ≥ 1. If S_G meets {u, v}, then J ⊆ N_G[S_G], and the bound needed is a ≤ φ_{10}, k − a ≤ φ_{01}, or k ≤ φ_{11}, which is Proposition 4.4. If S_G avoids u and v, use φ_{00} ≥ 0. "⇒": the H-constraints at S_G ⊔ (witness set) give, for every S ∋ u ∌ v, y(S) − |N[S]| + 1 ≤ C_u. Similarly for v, ≤ k for S ⊇ {u,v}, and y(S) ≤ |N[S]| − 1 for S avoiding u, v. Let L_u and L_v be the maxima of y(S) − |N[S]| + 1 over S ∋ u ∌ v and over S ∋ v ∌ u. Take a = max(k − C_v, k − y_v, L_u). The following nine comparisons show k − C_v, k − y_v, L_u ≤ C_u, y_u, k − L_v. The bounds L_u≤C_u and L_v≤C_v are the one-endpoint constraints. Removing the endpoint from the maximizing set and using monotonicity gives L_u≤y_u and L_v≤y_v. Applying the one-endpoint constraints to V∖{u} and V∖{v}, and using y(V)=|V|−1+k, gives k−C_v≤y_u and k−C_u≤y_v. The avoiding constraint on V∖{u,v} gives k≤y_u+y_v, also when the set is empty. Proposition 4.4 gives k≤C_u+C_v. Finally L_u+L_v≤k follows by adding the inequalities for the union and intersection of two maximizing sets and using (F1). For an empty intersection, v lies in both closed neighbourhoods and supplies the one-unit overlap. Then x′ = y − a e_u − (k − a) e_v ∈ D(G).
(c) The total is y(V)=|V|−2. For nonempty S⊆V, testing S alone gives the old bound |N[S]|−1. Testing it together with all p ear vertices tightens that bound by one if both endpoints lie in N[S]. These bounds suffice: for every nonempty ear subset, the change in slack over the old bound is
ψ(S_W)−|J(S_W)∩N[S]| plus the number of new ear positions contributed by σ beyond N_P[S_W]. By (R), ψ≥1. Thus the slack change is at least −1 when both endpoints lie in N[S] and at least 0 otherwise. The ear-only tests also follow from ψ≥1. Every set meeting {u,v} has both endpoints in N[S] because uv is an edge. The constraints for y+e_u and y+e_v give the tightened bound on those sets and the old bound on avoiding sets. Goodness supplies the tightened bound on avoiding sets whose closed neighbourhood contains both endpoints. ∎

### 4.4 Counting

**Lemma 4.6 (fibres of D(G)).** Fix all coordinates except those at u and v. The admissible values of x_u form an integer interval (each constraint is linear in x_u with slope −1, 0 or 1). Hence |D(G) + {a e_u + (k−a) e_v : lo ≤ a ≤ hi}| = |D(G)| + (hi − lo)·#fib, and |{y : y + e_u, y + e_v ∈ D(G)}| = |D(G)| − #fib, where #fib is the number of nonempty fibres (Lean `card_mink`, `card_mminus`).

**Lemma 4.7 (path constants).** Let Z_p = {0,1,2}^p. Then
2·#{z : (R), (Fl)} = (p+2)·2^p,  2·#{z : (R), T = 1} = 2^p,  2·Σ_{z : (R),(Fl),T≤0} (C_u + C_v + T) = 2^p.
*Proof.* For the first count, append one letter at a time and track the state (P_p − min P, max P − P_p). Under (R) and (Fl) the state is one of (0,0), (1,0), (0,1), (0,2), (1,1). The counts satisfy A′ = A, B′ = C′ = A + B + C, (D+E)′ = C + 2(D+E). So A = 1, B = C = 2^p − 1, and 2(D+E) = (p−2)2^p + 2, and the total is (p+2)2^{p−1}. The tight words (T = 1) are exactly the walks staying in {0,1}, and C_u + C_v + T is 1 exactly on the walks staying in {−1,0} with T = −1 and 0 otherwise. Each of these two-valued windows has 2^{p−1} words. ∎

**Theorem E (good edges).** If uv is a good edge of G, then 2|D(G ∪_{uv} C_{p+2})| = (p+2)·2^p·|D(G)|.
*Proof.* Sum Theorem 4.5 over z using Lemma 4.6. Write X = |D(G)| and f = #fib. The non-tight z contribute X + (C_u + C_v + T)·f each, and the tight z contribute X − f each. By Lemma 4.7, 2|D(H)| = (p+2)2^p X + f·2^p − f·2^p. ∎

This route does not use the source's Corollary 22 (|D(C_m)| = m 2^{m−2}); that formula is the case G = K_2.

## 5. Dissections

### 5.1 Outer edges are good

**Proposition 5.1 (Prop. 4.1 of the proof).** Let a finite simple graph G have injective positions such that no two edges cross (pos a < pos c < pos b < pos d is impossible for edges ab and cd). Let uv be an edge with u in the smallest position and v in the second smallest. Then uv is good.
*Proof.* (O2): a vertex strictly inside the span of an edge has all its neighbours in the closed span. Let y and S be as in the definition of goodness. If S splits as S_1 ⊔ S_2 with N[S_1] ∩ N[S_2] = ∅, apply y + e_u ∈ D to S_1 and S_2. Otherwise let Z′ be the set of vertices reachable from v avoiding S ∪ {u}, and R = V ∖ N[S]. Claim: no r ∈ Z′ ∩ R is adjacent to u. Suppose r is. Every neighbour a of u in S lies beyond r: otherwise every vertex reachable from v stays before a, by (O2) for the edge ua. A neighbour b of v in S lies before r: this is (O3), (O2) for the edge ur. Since S does not split, the graph on S joining pairs with intersecting closed neighbourhoods is connected. Along a path from a to b in that graph there is a pair s, s′ on opposite sides of r, with a common closed neighbour x. Noncrossing for ur confines each side to its closed arc, so x is u or r. The choice r lies outside N[S], and the choice u would give a neighbour of u in S before r. Given the claim: N[S ∪ Z′] ⊆ N[S] ∪ (Z′ ∩ R). The upper bound from y + e_v on S ∪ Z′ and the lower bound y(Z′) ≥ |Z′ ∩ R|, obtained by testing the complement of Z′ with y + e_u (every vertex of Z′ ∩ R has its closed neighbourhood inside Z′), give y(S) ≤ |N[S]| − 2. ∎

In a dissection, for an edge ab joining positional neighbours, rotating the positions so that a comes first keeps the non-crossing property (Lean `nc_rot`). So Proposition 5.1 applies.

### 5.2 The minimal ear and the induction

A *position dissection* is a graph with injective positions, no two crossing edges, positionally consecutive vertices adjacent, and the first and last vertices adjacent. Every `Dissection n` is one, with positions 0, …, n−1 (Lean `Dissection.pd`).

**Lemma 5.2 (minimal ear).** If |V| ≥ 3, there is an edge ab with pos a < pos b and some vertex strictly between them, such that the number of vertices strictly between is minimal. The first and last vertices furnish a candidate. Every vertex strictly between a and b has all its neighbours in the closed span by noncrossing. Any edge within that span from such a vertex to a nonconsecutive vertex would have a smaller positive span, contradicting minimality. The consecutive-position edges supply its two neighbours.

**Proposition 5.3 (ear step).** Let I be the set of vertices strictly between a and b, p = |I|, and G′ the graph induced on V ∖ I. Then G ≅ G′ ∪_{ab} C_{p+2}, and G′ is a position dissection in which ab joins positional neighbours. By Proposition 5.1 and Theorem E, 2|D(G)| = (p+2)2^p |D(G′)|. The relabelling sends the vertices of I to the ear by rank.

**Proposition 5.4 (faces).** The faces of G are F_0 = {x : pos a ≤ pos x ≤ pos b} together with the faces of G′. A face of G that meets I must contain both neighbours of each of its ear vertices, and propagation gives I together with a and b. These vertices induce the ear cycle, so their two neighbours in the face already lie within that cycle. Connectivity of the induced face forces it to equal F_0. A face avoiding I is a face of G′.

**Theorem 5.5 (count).** For every position dissection with |V| ≥ 2, |D(G)| = 2^{1 + Σ_F (|F| − 3)} ∏_F |F|. *Proof.* Induction on |V|. For |V| = 2, G = K_2 and |D| = 2. The step is Propositions 5.3 and 5.4, with |F_0| = p + 2. ∎

**Proposition 5.6 (extended-weak-dual degree).** For a position dissection on at least three vertices, the extended-weak-dual degree of every face F equals |F| and each outer edge lies in exactly one bounded face. *Proof.* Induction along the same ear steps. Two cases. If G′ = K_2, G is a cycle and its only face has |V| outer edges. Otherwise ab is not an outer edge of G, and lies in exactly one face of G′. The new face F_0 shares an edge only with that face and contains p + 1 outer edges. An old face F gains the neighbour F_0 exactly when it contains ab, and in that case loses ab as an outer edge. Each new outer edge belongs only to F_0, and each retained outer edge belonged to a unique old face and is absent from F_0. ∎

**Proof of Theorem A.** Combine Theorem 5.5 and Proposition 5.6. Since every face has ewdDeg(F) = |F| ≥ 3, S ≥ 0 and 1 + S = 1 + Σ_F (|F| − 3). ∎

**Corollary 5.7.** For a dissection of an n-gon with f bounded faces, 1 + S(B) = n − f − 1 (Euler's formula and Σ_F |F| = n + 2(f − 1)). This identity is not needed for the formal proof.

## 6. Checks (kernel computation, independent of the proof)

`src/Checks.lean` evaluates both sides by `decide` (kernel reduction, no `native_decide`):

| Dissection | \|D(B)\| by `decide` | 2^{1+S} ∏ deg by `decide` |
|---|---|---|
| triangle | 6 | 6 |
| square with chord 02 | 18 | 18 |
| pentagon with chord 02 | 48 | 48 |
| pentagon with chords 02, 03 | 54 | 54 |
| hexagon with chords 02, 24, 04 | (derived from the endpoint) | 162 |

The faces of the square with a chord are {0,1,2} and {0,2,3} (`decide`). The theorem gives |D| = 162 for the hexagon (`hex_count`). `polygon_count` instantiates the theorem with empty chord sets for every n ≥ 3. The proof lane and the first review recorded exact checks for all 5,439 dissections with 3≤n≤9. The cross-model review independently enumerated all 257 dissections with 3≤n≤7, comparing each draconian count by weak compositions and closed-neighbourhood tests, its geometric faces by successive chord splits, and its induced cycles and dual degrees. This independently gives 162 for the hexagon.

## 7. Significance

Davis and Chen proved Eq. (9) for blocks built by restricted subdivision and triangle recurrences. Both recurrence theorems require a degree-two endpoint. Consider the hexagon with chords 02, 24 and 04. Reversing a subdivision at any degree-two vertex creates a parallel edge. Reversing a triangle addition would require applying the triangle recurrence to an attachment edge whose endpoints both have degree three even after removal of the ear. The ear formula here applies to those outer edges and also to longer ears. The distinction between outer edges and general edges matters: adding a triangle along the diamond's chord gives 52, whereas multiplicativity would give 54. The proof uses exact segment counts for the non-tight fibres and a noncrossing separation argument to characterize the tight fibres on outer edges.

## 8. Prior work

The closest earlier result is Davis–Chen Theorem 34 and Corollary 35 for blocks covered by the two recurrences. Davis–Jakovleski–Pan extend the triangle recurrence to attachments along a matching of a complete graph (Theorem 2.9) and leave the general validity of the recurrence open. The independent literature and registry screen found no prior proof for all polygon dissections. [Davis–Chen](https://arxiv.org/abs/2007.11051v4) [Davis–Jakovleski–Pan](https://arxiv.org/abs/2202.09853)

## 9. The formal proof

21 modules, 4,875 lines (`LEAN-SOURCE-APPENDIX.md`), Lean 4.34.1 with Mathlib (revision in `PINS.json`), specific imports only. No `sorry`, `admit`, `axiom`, `unsafe` or `native_decide`. Every endpoint depends only on `propext`, `Classical.choice`, `Quot.sound` (`src/Axioms.lean`). Correspondence:

| Paper | Lean |
|---|---|
| §4.1 | `Glue.lean` (`glue`, `cnbhd_glue`, `mem_draconian_glue`) |
| Lemmas 4.1–4.3 | `PathRuns.lean` (`phi_Ioc`, `psi_Ioc`, `phi_insert_le`, `phi_union_gap`, `run_induction`) |
| Prop. 4.4, witnesses | `PathBounds.lean` (`lb_main`, `lb11`, `lb_psi`, `Csum`, `wit10`, `wit01`, `wit_fall`) |
| Theorem 4.5 | `FibreH.lean` (`Rc_of_mem`, `Fc_of_mem`, `fibre_nontight`, `fibre_tight`, `Good`) |
| Lemma 4.6 | `FibreCount.lean` (`uvals_convex`, `card_mink`, `card_mminus`) |
| Lemma 4.7 | `WordCount.lean` (`card_good_total`, `card_tight`, `sum_ell`) |
| Theorem E | `TheoremE.lean` (`theoremE`) |
| Prop. 5.1 | `Prop41.lean` (`good_of_outer`) |
| Lemma 5.2, rotation | `DissA.lean` (`exists_minEar`, `nc_rot`) |
| Prop. 5.3 | `DissB.lean`, `DissC.lean` (`relabE`, `relab_adj`, `PD_sub`, `good_sub`, `ear_step`) |
| Prop. 5.4 | `DissD.lean` (`isFace_F0`, `face_eq_F0`, `isFace_map_iff`, `faces_decomp`) |
| Theorem 5.5 | `DissE.lean` (`count_PD`) |
| Prop. 5.6 | `DissF.lean`–`DissH.lean` (`inv_PD`) |
| Theorem A | `Endpoint.lean` (`Dissection.pd`, `Dissection.main`, `Dissection.S_nonneg`, `mathdb347302`) |
| §6 | `Checks.lean` |

Differences from the proof lane's write-up (PROOF-347302.md): the c-values are explicit functions of the walk rather than minima. The constants n_p, s_p, b_p are computed directly by word counting rather than from the source's Corollary 22. The induction is on a minimal-span edge rather than a leaf of the weak dual. Faces are defined as induced cycles, and their extended-weak-dual degree is proved equal to |F| by a separate invariant. Only the δ = 0 case of Theorem E is formalized; the defect formula for bad edges is not.
