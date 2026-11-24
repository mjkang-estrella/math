# Every extremal triangular choice multigraph can be taken 2-recursive: a proof of the Peaslee–Sali–Yan conjecture H(m, α) = H₂(m, α)

*Proof:* GPT-6.1 Sol lane `t1-pool074-proof-sol61-20261120-r1`. *Adversarial review:* Claude Opus 5.5, lane `t1-prelean-X39-opus-20261120-r1`. *Lean 4 formalization and this manuscript:* Claude Opus 5.5, lane `exp-forbidden-config-361202-formal-paper-opus55-20261120-r1` (2026-11-20). Every statement in Sections 3–6 is kernel-checked. The proof in Section 4 follows the Lean development, which differs from the Sol write-up in two small places. Section 7 lists the differences.

## Abstract

Peaslee, Sali and Yan (arXiv:2312.11446; Art Discrete Appl. Math. 2026) reduced a forbidden-configuration problem for multivalued matrices to an optimization over *triangular choice multigraphs* (TCMs). A TCM chooses one edge in every vertex triple, and its weight is ∑ α^(edge multiplicity). They conjectured that the maximum weight H(m, α) over all TCMs equals the maximum H₂(m, α) over the recursively built "2-recursive" TCMs, for m ≥ 3 and α ≥ 2 (Conjecture 6.3; for α = 2, Conjecture 1.10). We prove a stronger statement for every real α > 1: every TCM is dominated in weight by a 2-recursive TCM. Hence H(m, α) = H₂(m, α) for all m and all α > 1. The proof starts from an extremal TCM and a partition into singleton blocks. It repeatedly merges two blocks, using two ingredients. A size-normalized score selects a pair of blocks whose union is closed. A cloning step uses convexity of x ↦ α^x and replaces the TCM by another extremal one in which the merged block behaves uniformly. The equality, with the source definitions transcribed literally, is formalized in Lean 4 with Mathlib. It uses only the axioms propext, Classical.choice and Quot.sound. The "in particular" limit clause of the conjecture is not formalized: it follows from the equality and the source's Theorem 6.2.

## 1. The conjecture and the source definitions

**Conjecture (MathDB 361202; Peaslee–Sali–Yan, arXiv:2312.11446v1, Conjecture 6.3, p. 34), verbatim:**

> Conjecture 6.3. H(m, α) = H₂(m, α) for all m ≥ 3 and α ≥ 2. In particular,
> lim_{m→∞} 2H(m, α)/(mα^m) = lim_{m→∞} 2H₂(m, α)/(mα^m) = λ(α).

Here λ(α) = ∑_{j≥1} 2^{j−1}/α^{2^j}.

**Source definitions, verbatim (Definition 1.3 and Question 1.4):**

> Definition 1.3. A multigraph G on vertex set V is called a triangular choice multigraph (TCM) if it can be obtained as follows. Start with the empty graph on V. For every unordered triple u, v, w of distinct vertices in V, choose exactly one of edge uv, uw, vw and add a copy of it to the multigraph. In particular, the total number of edges in G, counting multiplicities, is (|V| choose 3).
>
> A triangular choice multigraph G on V is 2-recursive if |V| = 1, 2 and G is the empty graph, or |V| ≥ 3 and there exists a partition V = V₁ ∪ V₂, with V₁, V₂ ≠ ∅, and multigraphs G₁, G₂, G₃ such that
> • G = G₁ ∪ G₂ ∪ G₃, where the union is taken with edge multiplicity.
> • G₁ is a 2-recursive TCM on V₁ and G₂ is a 2-recursive TCM on V₂.
> • G₃ is obtained by adding a copy of edge uv for every unordered triple u, v, w ∈ V with u, v ∈ V₁ and w ∈ V₂, and adding a copy of edge vw for every unordered triple u, v, w ∈ V with u ∈ V₁ and v, w ∈ V₂.
>
> Question 1.4. Let G be a triangular choice multigraph on [m]. For every ij ∈ [m]^(2), let m^G_ij denote the multiplicity of the edge ij, which is also the number of unordered triples i, j, k in which the edge ij is chosen. For every α ∈ ℝ, define
> w(G, α) = ∑_{xy∈[m]^(2)} α^{m^G_xy},
> H(m, α) = max {w(G, α) : G is a TCM on [m]},
> H₂(m, α) = max {w(G, α) : G is a 2-recursive TCM on [m]}.

**Lean transcription** (module `TCMDefs`, namespace `PSY`; this is the endpoint fixed by the review and is unchanged):

```lean
def Triple (m : ℕ) := {t : Finset (Fin m) // t.card = 3}
def TCM (m : ℕ) := ∀ t : Triple m, {x : Fin m // x ∈ t.1}          -- the excluded vertex
def mult (q : TCM m) (x y : Fin m) : ℕ :=
  (Finset.univ.filter (fun t : Triple m =>
    x ∈ t.1 ∧ y ∈ t.1 ∧ (q t).1 ≠ x ∧ (q t).1 ≠ y)).card
def w (q : TCM m) (α : ℝ) : ℝ :=
  ∑ e ∈ (Finset.univ : Finset (Fin m)).offDiag.filter (fun p => p.1 < p.2), α ^ mult q e.1 e.2
inductive TwoRec (q : TCM m) : Finset (Fin m) → Prop
  | small {S} : S.card ≤ 2 → TwoRec q S
  | split {S V₁ V₂} : V₁.Nonempty → V₂.Nonempty → Disjoint V₁ V₂ → V₁ ∪ V₂ = S →
      TwoRec q V₁ → TwoRec q V₂ →
      (∀ t : Triple m, t.1 ⊆ S → (t.1 ∩ V₁).card = 2 → (q t).1 ∈ V₂) →
      (∀ t : Triple m, t.1 ⊆ S → (t.1 ∩ V₂).card = 2 → (q t).1 ∈ V₁) →
      TwoRec q S
noncomputable def H (m : ℕ) (α : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun q : TCM m => w q α)
noncomputable def H₂ (m : ℕ) (α : ℝ) : ℝ :=          -- under `open Classical`
  (Finset.univ.filter (fun q : TCM m => TwoRec q Finset.univ)).sup' (twoRec_nonempty m)
    (fun q => w q α)
```

*Correspondence.* A TCM is recorded by its choice function: for each triple, the vertex *not* on the chosen edge. Different choice functions can give the same multigraph. For m = 4 the 81 choice functions give 66 distinct multigraphs. But w depends only on the multigraph. A multigraph is a TCM on [m] exactly when it is the multigraph of some choice function. By induction on Definition 1.3, it is a 2-recursive TCM exactly when it is the multigraph of some choice function q with `TwoRec q [m]`: put q₁, q₂ on the parts and the forced choice on mixed triples. So both maxima are unchanged. For m ≤ 5, a direct enumeration confirms that the multigraphs of the choice functions satisfying `TwoRec` are exactly the 2-recursive multigraphs of Definition 1.3. `mult q x y` counts the triples containing x and y whose chosen edge is xy, which is m^G_xy. `TwoRec q S` is Definition 1.3 restricted to the triples inside S. G₁ and G₂ are the restrictions to V₁ and V₂. G₃ says that a triple with two vertices in V_i excludes its vertex in the other part. The Lean predicate also allows the base case for |S| = 0 and splits for |S| ≤ 2. Neither matters, since every set of size ≤ 2 is accepted by `small` and the endpoint uses S = [m] with m ≥ 3. Both maxima are over nonempty finite sets, with no default values. Nonemptiness of the 2-recursive set (`twoRec_nonempty`) is proved with the explicit TCM `maxTCM`, in which every triple excludes its largest vertex. It is 2-recursive on every vertex set via the split S = (S ∖ {max S}) ∪ {max S}.

**Main theorem (Lean, module `TCMMain`).**

```lean
theorem PSY.recursive_dominates {m : ℕ} (α : ℝ) (hα : 1 < α) (q : TCM m) :
    ∃ r : TCM m, TwoRec r Finset.univ ∧ w q α ≤ w r α
theorem PSY.H_eq_H₂ (m : ℕ) (α : ℝ) (hα : 1 < α) : H m α = H₂ m α
theorem PSY.psy_conj_6_3 (m : ℕ) (hm : 3 ≤ m) (α : ℝ) (hα : 2 ≤ α) : H m α = H₂ m α
```

## 2. Scope: the limit clause

The Lean development proves the equality H(m, α) = H₂(m, α), which is the main clause of the conjecture. **It does not prove the limit.** The limit is the following statement about H₂, which we cite (arXiv:2312.11446v1, Theorem 6.2, p. 34; journal version pp. 38–39):

> Theorem 6.2. For every m ≥ 3 except 6, let k = k(m) be the unique integer such that 2^k + 2^{k−1} ≤ m < 2^k + 2^{k+1}. For m = 6, let k = k(6) = 3 if 2 ≤ α < √2 + 1, and let k = k(6) = 4 if α ≥ √2 + 1. Then for all α ≥ 2, we have H₂(m, α) = H₂(2^k, α)α^{m−2^k} + H₂(m − 2^k, α)α^{2^k} + 2^k(m − 2^k). Moreover, if λ(α) = ∑_{j=1}^∞ 2^{j−1}/α^{2^j}, then lim_{m→∞} 2H₂(m, α)/(mα^m) = λ(α).

(The m = 6 clause looks misprinted, since 2^3 > 6, as does the matching clause of Theorem 1.9. It is not used here. Only the "Moreover" sentence is used.)

Since H(m, α) = H₂(m, α) for every m, the two normalized sequences coincide termwise. The "In particular" limit therefore follows from the "Moreover" sentence for every α ≥ 2. This last step is the only part of the conjecture that is not kernel-checked.

Note on the status of the cited theorem. The source introduces Theorems 6.1 and 6.2 with the sentence "By suitably modifying Section 4 and Section 5, we can also prove the following generalisation of Theorem 1.6 and Theorem 1.9 for all α ≥ 2". No separate proof is printed, either in arXiv v1 or in the journal version.
- For α = 2 the limit is the second part of Theorem 1.9, whose proof is printed in Section 5.
- For every α > 1 the lower bound lim inf ≥ λ(α) is the source's Theorem 1.8, whose proof is printed.
- For α > 2 the upper half of the limit therefore rests on the authors' statement.
The MathDB record describes the asymptotics of H₂ as proved by the paper and the equality as the open part.

## 3. Notation and basic facts

Fix m, write V = [m], and fix α > 1. Let q be a TCM.

* For distinct x, y, z, write ex(x, y, z) for the excluded vertex of {x, y, z}. It is symmetric in its arguments and lies in {x, y, z} (Lean: `ex`, `ex_comm12`, `ex_comm23`, `ex_rot`, `ex_mem`).
* **Bridge.** For x ≠ y, mult(x, y) = #{z ∉ {x, y} : ex(x, y, z) = z}. A triple counted by mult(x, y) is {x, y, z}, where z is its excluded vertex (`mult_eq`). mult is symmetric (`mult_comm`).
* **Ordered weight.** F(q) = ∑_{x ≠ y} α^{mult(x, y)} = 2w(q) (`two_mul_w`). All comparisons of weights below are made on F.
* A set S ⊆ V is **closed** if ex(x, y, z) = z whenever x ≠ y are in S and z ∉ S (`Closed`).
* S has **uniform exterior choices** if for x, x' ∈ S and distinct z, w ∉ S: ex(x, z, w) = z ⇔ ex(x', z, w) = z (`Unif`). Equivalently, the choices on {x, z, w}, x ∈ S, follow one common pattern (`unif_self` also gives ex(x, z, w) = x ⇔ ex(x', z, w) = x').
* A **labelling** lab : V → V defines blocks B_i = lab⁻¹(i). Some blocks may be empty. lab is **good for q** if every block is closed, has uniform exterior choices, and q is 2-recursive on it (`Good`). The identity labelling (singleton blocks) is good for every q (`good_id`).
* `TwoRec` depends only on the choices on triples inside the set (`TwoRec.congr`).

## 4. The proof

### 4.1 Lemma 2 (cloning a closed set): weight

Let U be closed for q and u ∈ U. Define the TCM clone_u = `clone q U u`. A triple t with exactly one vertex v in U is sent to t' = (t ∖ {v}) ∪ {u}. If q excludes u on t', then clone_u excludes v on t; otherwise clone_u excludes the same vertex as q on t'. All other triples keep their choice. Concretely, for x ∈ U and distinct y, z ∉ U (`ex_clone_one`):

ex_clone(x, y, z) = x if ex(u, y, z) = u, and ex(u, y, z) otherwise.

Triples with zero, two or three vertices in U are unchanged (`ex_clone_ne`, `ex_clone_two`, `ex_clone_zero`).

**Loads in the three edge classes.** Write mult_u for the loads of clone_u.
1. x, y ∈ U: mult_u(x, y) = mult(x, y), since every triple through x and y has at least two vertices in U (`mult_clone_in`).
2. x ∈ U, y ∉ U: mult_u(x, y) = mult(u, y) (`mult_clone_mixed`). A third vertex z ∈ U never selects xy, in clone_u or in q (for the pair u, y). This is because {x, z} ⊆ U, U is closed and z ≠ y, so ex = y. A third vertex z ∉ U selects xy in clone_u exactly when it selects uy in q, by the displayed formula.
3. x, y ∉ U: let R = #{z ∉ U ∪ {x, y} : ex(x, y, z) = z} and I_v = [ex(x, y, v) = v] for v ∈ U. Then mult(x, y) = R + ∑_{v∈U} I_v and mult_u(x, y) = R + |U|·I_u (`mult_q_out`, `mult_clone_out`).

**Two-point Jensen** (`jensen_nat`). For integers 0 ≤ k ≤ n and α > 0: n·α^k ≤ k·α^n + (n − k). This is convexity of t ↦ exp(t log α) at the points 0 and n with weights (n − k)/n and k/n.

**Proposition 4.1** (`clone_avg`). If U is closed, then ∑_{u∈U} F(clone_u) ≥ |U|·F(q).

*Proof.* Expand both sides as ∑_x ∑_y and split each sum over U and its complement (`split4`). Write n = |U|.
* Pairs in U × U: the terms agree by class 1.
* Pairs (x, y) ∈ U × Uᶜ: by class 2 the left side contributes ∑_{x∈U} ∑_{y∉U} ∑_{u∈U} α^{mult(u, y)} = n ∑_{y∉U} K(y), where K(y) = ∑_{u∈U} α^{mult(u, y)}. The right side contributes n ∑_{x∈U} ∑_{y∉U} α^{mult(x, y)} = n ∑_{y∉U} K(y). These are equal.
* Pairs in Uᶜ × U: for each fixed x ∉ U the two contributions are both n·K(x), by class 2 and the symmetry of mult.
* Pairs in Uᶜ × Uᶜ with x ≠ y: let k = ∑_v I_v. By class 3, ∑_{u∈U} α^{mult_u(x, y)} = k·α^{R+n} + (n − k)·α^R. Multiplying Jensen by α^R gives n·α^{R+k} ≤ k·α^{R+n} + (n − k)·α^R, which is the required pointwise inequality. ∎

**Corollary 4.2** (`exists_clone_ge`). If U is closed and nonempty, some u ∈ U has w(clone_u) ≥ w(q). In particular, if q is a maximizer of w, so is clone_u.

This is the proof's inequality (3), with all |U| clones averaged instead of two clones weighted a and b. The weight inequality needs only that U is closed; it does not use the uniform exterior choices of the two merged blocks.

### 4.2 Lemma 2 (cloning a closed set): invariants

**Proposition 4.3** (`good_merge`). Let lab be good for q. Let i ≠ j with B_i and B_j nonempty, U = B_i ∪ B_j closed for q, and u ∈ U. Let lab' relabel block j as i (`merge`), so its blocks are U, ∅, and B_k for k ∉ {i, j} (`blk_merge_i`, `blk_merge_j`, `blk_merge_k`). Then lab' is good for clone_u.

*Proof.*
* *U is closed* for clone_u: triples with two vertices in U are unchanged (`clone_closed_U`).
* *U has uniform exterior choices* for clone_u: for x ∈ U and distinct z, w ∉ U, ex_clone(x, z, w) = z ⇔ ex(u, z, w) = z. This does not depend on x (`ex_clone_one_eq`, `clone_unif_U`).
* *clone_u is 2-recursive on U.* First, q is 2-recursive on U by the split B_i | B_j (`twoRec_union`). Both parts are 2-recursive. A triple inside U with two vertices in B_i excludes its B_j-vertex, by the closure of B_i (`split_cond`), and symmetrically. The choices of clone_u agree with q on triples inside U (`clone_agree_of_subset`), so `TwoRec.congr` applies.
* *The empty block* is trivially good.
* *Every other block C = B_k*, k ∉ {i, j}, is disjoint from U.
  * C is closed for clone_u (`clone_closed_C`). Take x ≠ y in C and z ∉ C. If z ∉ U the triple is unchanged. If z ∈ U, the clone copies q on {x, y, u}, which excludes u by the closure of C (u ∉ C). Hence ex_clone(x, y, z) = z.
  * C has uniform exterior choices (`clone_unif_C`). Take x, x' ∈ C and distinct z, w ∉ C, and consider how many of z, w lie in U.
    - If both lie in U, the triples are unchanged.
    - If exactly one lies in U, say z, then ex_clone(x, z, w) = z ⇔ ex(x, u, w) = u. The uniform exterior choices of C in q, for the exterior pair (u, w), give the same condition for x'.
    - If neither lies in U, the triples are unchanged.
  * clone_u is 2-recursive on C, because the triples inside C are unchanged (`clone_agree_of_disjoint`). ∎

### 4.3 Lemma 1 (a pair of blocks with closed union)

Let lab be good for q.

**Uniform loads and triangles.**
* For x, x' in one block and y, y' in another block, mult(x, y) = mult(x', y') (`mult_uniform`).
  - A third vertex in the block of x or of y never selects the pair, by closure.
  - For any other third vertex, the uniform exterior choices of the two blocks let us replace x by x' and then y by y' (`mult_step`).
* If blocks i, j, k are distinct and ex(x, y, z) = x for some x ∈ B_i, y ∈ B_j, z ∈ B_k, then ex(x', y', z') = x' for *all* x' ∈ B_i, y' ∈ B_j, z' ∈ B_k. This uses the uniform exterior choices of the three blocks in turn (`triangle_uniform`).

**The switch** (`switch q lab i j k`). Every triple meeting B_i, B_j, B_k once each now excludes its B_k-vertex; all other triples are unchanged. Assume the pattern above, where every such triple excludes its B_i-vertex. Write a, b, c for the block sizes. The loads change as follows:
* every pair in B_i × B_j gains c (`mult_sw_ij`);
* every pair in B_j × B_k loses a (`mult_sw_jk`);
* every other pair is unchanged (`mult_sw_other`). For B_i × B_k pairs the changed triples select neither before nor after (`perm_j`).

With L the common B_i–B_j load and L' = K + a the common B_j–B_k load (so K is the new B_j–B_k load), summing over ordered pairs gives exactly (`switch_gain`):

F(switch) − F(q) = 2[ab(α^{L+c} − α^L) + bc(α^K − α^{K+a})].

**Score.** For x, y in different blocks of sizes a_x and a_y, set (`score`)

score(x, y) = a_x a_y α^{mult(x,y)} / ((α^{a_x} − 1)(α^{a_y} − 1)).

It is symmetric and depends only on the two blocks (`score_comm`, `score_congr`).

**Lemma 4.4** (`delta_pos`). Let α > 1, a, b, c ≥ 1, and suppose bcα^{K+a}/((α^b − 1)(α^c − 1)) ≤ abα^L/((α^a − 1)(α^b − 1)). Then ab(α^{L+c} − α^L) + bc(α^K − α^{K+a}) > 0.

*Proof.* Cross-multiplying gives bcα^{K+a}(α^a − 1) ≤ abα^L(α^c − 1). The gain equals abα^L(α^c − 1) − bcα^K(α^a − 1), which is therefore at least bc(α^a − 1)(α^{K+a} − α^K) > 0. ∎

**Proposition 4.5** (`no_bad_triangle`, `union_closed`, `exists_closed_pair`). Let q maximize w, let lab be good for q, and suppose two labels occur. Choose (x₀, y₀) with lab x₀ ≠ lab y₀ maximizing the score. Then B_{lab x₀} ∪ B_{lab y₀} is closed.

*Proof.* Take x ≠ y in the union and z outside it.
* If x and y lie in the same block, closure of that block gives ex(x, y, z) = z.
* Otherwise let x ∈ A = B_{lab x₀}, y ∈ B = B_{lab y₀} (or the reverse, using symmetry of ex), and let C be the block of z.
  - If ex(x, y, z) = x, the triangle pattern holds for (A, B, C). By score maximality, score(y, z) ≤ score(x₀, y₀) = score(x, y). Lemma 4.4, with L = mult(x, y) and L' = mult(y, z) = K + a, makes the switch strictly heavier than q, a contradiction.
  - If ex(x, y, z) = y, apply the same argument with A and B interchanged, using score(x, z) ≤ score(y, x).
  - Hence ex(x, y, z) = z. ∎

### 4.4 The iteration and the conclusion

**Theorem 4.6** (`descent`). If q maximizes w and lab is good for q, then some maximizer of w is 2-recursive on V.

*Proof.* Use induction on the number of labels used.
* If all vertices share one label, the block is V and goodness gives 2-recursiveness. If m = 0, `small` applies.
* Otherwise Proposition 4.5 gives labels i ≠ j with B_i ∪ B_j closed. Corollary 4.2 gives u with clone_u again a maximizer. Proposition 4.3 shows that the merged labelling is good for clone_u. The merged labelling uses strictly fewer labels (`card_image_merge`). ∎

**Theorem 4.7** (`recursive_dominates`, `H_eq_H₂`, `psy_conj_6_3`). For α > 1, every TCM q is dominated by a 2-recursive one. Consequently H(m, α) = H₂(m, α) for every m and every α > 1, and in particular for m ≥ 3, α ≥ 2.

*Proof.*
* A maximizer q₀ exists because there are finitely many TCMs and at least one. Theorem 4.6, applied to q₀ and the identity labelling, gives a 2-recursive maximizer r. Then w(q) ≤ w(q₀) = w(r).
* H₂ ≤ H holds because the 2-recursive TCMs form a subset of all TCMs.
* H ≤ H₂ follows from the domination. ∎

## 5. Sanity checks (Lean module `TCMSanity`)

* `H_3_2 : H 3 2 = 4` and `H₂_3_2 : H₂ 3 2 = 4`. All three TCMs on 3 vertices have weight 4 (`decide`).
* `H_4_2 : H 4 2 = 12`, proved by exhausting all 81 TCMs on 4 vertices (`decide`), independently of the main theorem. `H₂_4_2 : H₂ 4 2 = 12`.
* `H₂_5_2 : H₂ 5 2 = 30` and `H₂_6_2 : H₂ 6 2 = 73`.
  - Lower bounds: explicit 2-recursive TCMs with splits {0,1}|{2,3,4} and {0,1,2}|{3,4,5}, with weights computed by `decide`.
  - Upper bounds: the H₂ recurrence (source, Lemma 5.1) in the form W_S ≤ 2h(|S|) for 2-recursive TCMs (`WS_le`, module `TCMRecBound`), with the table h = 0, 0, 1, 4, 12, 30, 73.
* `H_5_2 : H 5 2 = 30` and `H_6_2 : H 6 2 = 73` follow from the main theorem.
* `exists_not_twoRec : ∃ q : TCM 4, ¬ TwoRec q Finset.univ`. In the cyclic TCM, the triple missing k excludes k + 1 (mod 4). No split satisfies the conditions, so `TwoRec` is not trivially true.
* The H(4, 2) = H₂(4, 2) = 12 agreement is an independent check: exhaustion on one side and the recurrence on the other. It guards against an inverted split condition.
* Outside Lean, an exact computation of H(m, α) over all TCMs agrees with the H₂ recurrence for m ≤ 7 and α ∈ {2, 3, 5/2, 3/2, 11/10, 10}. It was done by dynamic programming over multiplicity vectors in the final-check lane, for example H(7, 2) = 172 and H(7, 3) = 1011. This is evidence, not part of the proof.

## 6. Formalization summary

| Module | Lines | Content |
|---|---:|---|
| `TCMDefs` | 122 | endpoint definitions, `maxTCM`, `twoRec_nonempty`, H, H₂ |
| `TCMBasic` | 171 | `ex`, `mult_eq` bridge, `two_mul_w`, `TwoRec.congr`, `Closed`, `Unif` |
| `TCMClone` | 355 | clone, loads in three edge classes, Jensen, `clone_avg`, `exists_clone_ge` |
| `TCMMerge` | 231 | labellings, `good_merge` (all invariants) |
| `TCMSwitch` | 215 | uniform loads and triangles, the switch, `ex_switch_iff` |
| `TCMLemma1` | 359 | loads under the switch, `switch_gain`, score, `delta_pos`, `union_closed`, `exists_closed_pair` |
| `TCMMain` | 95 | `good_id`, `descent`, `recursive_dominates`, `H_eq_H₂`, `psy_conj_6_3` |
| `TCMRecBound` | 227 | restricted weights, split identities, recurrence upper bound `WS_le` |
| `TCMSanity` | 181 | sanity values and the non-2-recursive TCM |
| `TCMEndpoint` | 38 | prints definitions, statements and axioms |
| **Total** | **1994** | |

All endpoints depend only on `[propext, Classical.choice, Quot.sound]`. There is no `sorry`, `admit`, `axiom`, `unsafe` or `native_decide`, and only specific Mathlib imports are used. The sources appear byte-identically in `LEAN-SOURCE-APPENDIX.md`. A fresh replay from that appendix, using the root replay script, rebuilt and kernel-checked every module, with oleans identical to the author build (see REPORT.md).

## 7. Relation to the written proof being formalized

The mathematics is the GPT-6.1 Sol proof (block merging with a size-normalized score, then cloning with convexity of α^x). The Lean route differs in two places, neither affecting the statement:
1. The weight inequality averages over all |U| clones clone_u (u ∈ U), not the two clones q_A and q_B weighted by a and b. Its proof therefore needs only that U is closed. It is an equivalent form of inequality (3): grouping the u ∈ A and the u ∈ B recovers (3) when A and B have uniform exteriors.
2. Partitions are labellings lab : V → V with possibly empty blocks, rather than finite partitions. Merging relabels one block.

## 8. Significance

**What this settles.**
* The main clause of Conjecture 6.3 of Peaslee–Sali–Yan, with Conjecture 1.10 (α = 2) as the special case. The journal version (2026) still lists both as open. MathDB lists Conjecture 1.10 as a separate record (361201). It is the case α = 2 of the present theorem, and its consequences follow from the source's Theorems 1.5 and 1.9. It is not a separate result.
* The source's Theorem 1.5 (cited, not formalized; proved in its Section 3) states, verbatim: "For every m ≥ 0, r ≥ 3, H₂(m, (r−1)/(r−2))·(r−2)^{m−2} ≤ forb(m, r, M) − (r−1)^m − m(r−1)^{m−1} ≤ H(m, (r−1)/(r−2))·(r−2)^{m−2}." Our equality holds for every m and every α > 1, including α = (r−1)/(r−2) ∈ (1, 3/2] for r ≥ 4. So both bounds coincide for every r ≥ 3 and m ≥ 0, and forb(m, r, M) = (r−1)^m + m(r−1)^{m−1} + H₂(m, (r−1)/(r−2))·(r−2)^{m−2}. The source analyses H₂ through its recurrence. For r = 3 this is the first consequence the source states under Conjecture 1.10. With Theorem 1.9 (proved in the source) it also gives lim forb(m, 3, M)/(m2^{m−1}) − 1 = λ(2). The source writes that for r ≥ 4 it has no good conjecture on where H is attained. Our theorem answers that structural question: an extremal TCM can always be taken 2-recursive. It does *not* give the asymptotics of H₂(m, α) for 1 < α < 2, which remain as open as the source leaves them.

**What it is not.**
* The argument is short (about one page). Its method is close to Zykov symmetrization: closed blocks act as weighted vertices, and cloning homogenizes the exterior behaviour of a merged block. The source's Section 6 explicitly suggests merging closed sets as a possible route.
* The review rates the probability that a specialist calls the argument "not routine" at 0.65. The new ingredients are the normalization (α^a − 1)(α^b − 1) in the score, which makes the switching gain factor exactly, and the convexity-based cloning that keeps the weight extremal for blocks of unequal size. Neither appears in the source. The source spent a nine-page analysis to reach only H(m, 2) ≤ (83/192)·m·2^{m−1}.
* This is a solution of a specific conjecture in a recent, rarely cited paper (zero citing works in OpenAlex at review time). It is not a broad advance.

## 9. Prior art (from the review, REVIEW-361202.md, Section 1)

* **Versions.** arXiv:2312.11446 has only v1 (18 Dec 2023). The journal version is Art Discrete Appl. Math. (2026), DOI 10.26493/2590-9770.1898.8b5, published 2 July 2026. Its open-access accepted manuscript still states Conjectures 1.10 and 6.3 as open, with the same text.
* **Later work.** The same authors' later paper arXiv:2502.04741 (DMTCS 28:3 #17, 2026) concerns two-rowed configurations and does not mention H, H₂ or TCMs. Talbot–Yan arXiv:2311.00110 treats degree sequences of triangular multigraphs and is unrelated. The Anstee–Sali survey DS20v2 (2025) cites the paper and reports no resolution.
* **Citations and searches.** OpenAlex showed zero citing works for both records. Web searches for "triangular choice multigraph", "2-recursive", the authors and the thesis found nothing that settles the conjecture.
* **Registries.** Searches of the omega registry (issues and PRs for "2312.11446", "multivalued forbidden configuration" and "triangular choice"), the local Principia index, the mio-math and omega clones, and the campaign's LANES.json and claim-evidence.json found no hit.
* **Limits.** These searches are bounded. The proof lane also records two access limits: Semantic Scholar rate limits and ProbXiv HTTP 402. They cannot prove absence of prior literature.
* **Public formal statement (found 2026-11-20).** Conjecture 6.3 is problem `peaslee2026intermediate` of the public ReuF2F benchmark: cmu-l3/reuF2F, released 2026-10-16; Zheng et al., arXiv:2610.27046. Its Lean statement is `Peaslee2026Intermediate.conjecture_6_3`, with `sorry`. It bundles the equality for all m ≥ 3 with both limits, for every α ≥ 2.
  * The endpoint here proves the equality conjunct. It does not prove that theorem as stated, because the limit conjuncts are not formalized.
  * The benchmark paper reports only aggregate results. Its per-problem leaderboard (probxiv.com) returned HTTP 402. The repository has no issue or pull request that mentions the problem.
  * We found no public report that the problem was resolved.
* **Refresh (2026-11-20).**
  * The arXiv abstract page still shows only v1.
  * OpenAlex shows zero citing works for the arXiv record (W4389974715) and for the journal record (W7167054501).
  * The omega registry's issues and pull requests contain nothing on "2312.11446", "triangular choice multigraph", "Peaslee Sali Yan", "forbidden configuration multivalued", "361202" or "361201".
  * A GitHub code search for "2312.11446" found the ReuF2F statement file and nothing else relevant; the other hits are unrelated data files.
  * The local Principia, mio-math, omega and openai/math clones have no entry.

## References

1. W. Peaslee, A. Sali, J. Yan, *An intermediate case of exponential multivalued forbidden matrix configuration*, arXiv:2312.11446v1 (2023); Art Discrete Appl. Math. (2026), DOI 10.26493/2590-9770.1898.8b5.
2. R. Anstee, *A survey of forbidden configuration results*, Electron. J. Combin. Dynamic Survey DS20v2 (2025).
3. A. A. Zykov, On some properties of linear complexes, Mat. Sbornik 24 (1949) (symmetrization method).
4. The Mathlib Community, *Mathlib*, revision d13f23b723b8a846827a245b89c10fc7d3f11612; Lean 4.34.1.
