# CANDIDATE 373112: Tyomkyn's finiteness conjecture for symmetric 2-rigidity matroids is false

Lane: expanded-corpus-r167 (Claude). Status: **candidate, ordinary proof complete, Lean draft UNCOMPILED** (the Claude lane may not run Lean). Zero accepted credit until the root accepts it. Nothing here is self-accepted.

## 1. Literal target and provenance

- MathDB 373112, "Finiteness conjecture for symmetric abstract 2-rigidity matroids". The literal record is in `raw/373112.jsonl`, and its chunk, line and hashes are in `extracted.json`.
- MathDB literal statement: "There are only finitely many values of n for which there exists a symmetric abstract 2-rigidity matroid M_n ≠ R_n in which K_{3,3} is independent."
- Source: M. Tyomkyn, *On plane rigidity matroids*, arXiv:2602.11892. Both versions were read:
  - v1: `sources/373112-v1.pdf`, sha256 075707189b43…
  - v2 (6 Aug 2026, current): `sources/373112-v2.pdf`, sha256 c7325ca71dac…
- Conjecture 6.1 is word-for-word the same in v1 and v2: "There are only finitely many values of n for which there exists a symmetric abstract 2-rigidity matroid M_n ≠ R_n in which K_{3,3} is independent." It is v2 line 690 of `sources/373112-v2.txt`.
- The context (v2 §6) says such a matroid exists for n = 6: delete every prism from the bases of R_6. The author is "not aware of any further examples" and "checked by hand that (barring human error) there are none for n = 7". He then asks "if this distinction can occur for arbitrarily large n".

Source definitions used, quoted from v2 §1:

- **Definition 1.1** (Nguyen's form of Graver's axioms). A matroid M_n on the edge set of K_n (that is, the set of 2-subsets of [n]) is an abstract 2-rigidity matroid if
  1. it has rank 2n − 3, and
  2. every copy of K_4 is an M_n-circuit.
- **Definition 1.2.** R_n is the matroid whose independent graphs G are those in which every set of 2 ≤ m ≤ n vertices induces at most 2m − 3 edges (Laman / Pollaczek-Geiringer).
- **Definition 1.4.** M_n is *symmetric* if every isomorphic copy of an M_n-independent graph is M_n-independent.

## 2. Result

**Theorem.** For every even n ≥ 8 there is a symmetric abstract 2-rigidity matroid M_n on E(K_n) with M_n ≠ R_n in which K_{3,3} (every copy) is independent. In particular, Conjecture 6.1 is false.

(The source's n = 6 example and these examples together give the values n = 6, 8, 10, 12, …)

## 3. Proof

Notation: for a graph B and vertex set X, e_B(X) is the number of edges of B with both ends in X. A *Laman basis* is a spanning graph B on [n] with 2n − 3 edges and e_B(X) ≤ 2|X| − 3 for every X with |X| ≥ 2. These are exactly the bases of R_n. A set X with e_B(X) = 2|X| − 3 is *tight*.

**Definition (free).** A Laman basis B of R_n is *free* if B − a + b is a basis of R_n for every edge a ∈ B and every non-edge b ∉ B.

**Lemma A (freeness criterion).** Let n ≥ 4. A Laman basis B on [n] is free if and only if B has no tight set X with 4 ≤ |X| ≤ n − 1.

*Proof.*

(⇐) Take a ∈ B and b = uv ∉ B, and let X be any vertex set.
- If X does not contain both u and v, then e_{B−a+b}(X) ≤ e_B(X) ≤ 2|X| − 3.
- Suppose X ⊇ {u, v}.
  - If |X| = 2, the count is 1.
  - If |X| = 3, then e_B(X) ≤ 2 because uv ∉ B, so the count is ≤ 3.
  - If 4 ≤ |X| ≤ n − 1, then e_B(X) ≤ 2|X| − 4 by hypothesis, so the count is ≤ 2|X| − 3.
  - If X = [n], the count is 2n − 3.

So B − a + b is a Laman basis.

(⇒) Let X be tight with 4 ≤ |X| ≤ n − 1. Since 2|X| − 3 < C(|X|, 2), X contains a non-edge b. Some vertex lies outside X, and it has positive degree, so some edge a of B is not inside X. Then e_{B−a+b}(X) = 2|X| − 2, so B − a + b is dependent. ∎

**Lemma B (deleting a free orbit).** Let 𝓑 be the set of bases of a matroid. Let F ⊆ 𝓑 be a family such that

- (P1) every X ∈ F is free in the matroid sense: X − a + b ∈ 𝓑 for all a ∈ X and b ∉ X; and
- (P2) no two distinct members of F differ by a single exchange (|X Δ X′| ≥ 4).

Suppose also that 𝓑′ := 𝓑 ∖ F is nonempty. Then 𝓑′ is the set of bases of a matroid.

*Proof.* Take B₁, B₂ ∈ 𝓑′ and x ∈ B₁ ∖ B₂. Let Y = {y ∈ B₂ ∖ B₁ : B₁ − x + y ∈ 𝓑}. This set is nonempty because 𝓑 satisfies the exchange axiom.

- If some y ∈ Y has B₁ − x + y ∉ F, we are done.
- Otherwise every y ∈ Y gives a member of F. If Y had two elements y₁ ≠ y₂, the members B₁ − x + y₁ and B₁ − x + y₂ of F would differ by one exchange, contradicting (P2). So Y = {y}, and X := B₁ − x + y ∈ F.
- If B₂ ∖ B₁ = {y}, then B₂ = X ∈ F, which is impossible. So there is y′ ∈ B₂ ∖ B₁ with y′ ≠ y. Then y′ ∉ X, and by (P1), X − y + y′ = B₁ − x + y′ ∈ 𝓑. So y′ ∈ Y, a contradiction. ∎

Equivalent independence form, convenient for Lean: I is independent in the new matroid if and only if I is R_n-independent and I ∉ F. By (P1), every proper subset of a member of F lies in another basis. The augmentation axiom follows by the same argument: if I + e ∈ F for the unique R-augmenting e ∈ J ∖ I, then |J| = 2n − 3 and J ≠ I + e, so there is e′ ∈ J ∖ I with e′ ≠ e, and freeness gives that I + e′ is R-independent.

**Lemma C (edge split preserving freeness).** Let n ≥ 5 and let B on V, |V| = n, be a free Laman basis. Take an edge uv of B and a vertex z ∉ {u, v} with zu, zv ∉ B. Let B′ = B − uv + {wu, wv, wz} on V ∪ {w}, where w is a new vertex. Then B′ is a free Laman basis on n + 1 vertices.

*Proof.* B′ has 2(n + 1) − 3 edges. Take X′ ⊆ V ∪ {w} with |X′| ≥ 2 and write X = X′ ∖ {w}.

- **Case w ∉ X′.** Then e′(X′) = e(X) − [u, v ∈ X].
  - This is ≤ 2|X| − 3.
  - It is ≤ 2|X| − 4 when 4 ≤ |X| ≤ n − 1, by the freeness of B.
  - For X = V it equals 2n − 4 = 2|X′| − 4, so X′ is not tight (here |X′| = n is a proper subset size).
- **Case w ∈ X′.** Put s = |X ∩ {u, v, z}|. Then e′(X′) = e(X) − [u, v ∈ X] + s. We need e′ ≤ 2|X| − 1, and e′ ≤ 2|X| − 2 when 3 ≤ |X| ≤ n − 1.
  - |X| = 1: e′ ≤ 1.
  - |X| = 2: e′ ≤ 3 (if X = {u, v}, then e′ = 2).
  - |X| = 3: if X = {u, v, z}, then e(X) = 1 (because zu, zv ∉ B), so e′ = 3. If X = {u, v, t} with t ≠ z, then e′ ≤ 3 − 1 + 2 = 4. If X ⊇ {u, z} or X ⊇ {v, z} but not both u and v, then e(X) ≤ 2 (non-edge zu or zv), so e′ ≤ 4. If s ≤ 1, then e′ ≤ 4.
  - 4 ≤ |X| ≤ n − 1: e(X) ≤ 2|X| − 4 and s − [u, v ∈ X] ≤ 2, so e′ ≤ 2|X| − 2.
  - X = V: e′ = 2n − 1 = 2|X′| − 3.

So B′ is Laman and has no tight set of size 4 to n. By Lemma A, B′ is free. ∎

**Lemma D (no exchange-adjacent copy).** Suppose the degree set of B contains no two consecutive integers. Then for every edge a ∈ B and non-edge b ∉ B, the degree multiset of B − a + b differs from that of B. In particular, B − a + b ≇ B.

*Proof.*
- If a and b share a vertex, exactly one vertex p loses a degree and one vertex q gains one. Equal multisets would force {d_p − 1, d_q + 1} = {d_p, d_q}, so d_p = d_q + 1.
- If a and b are disjoint, b = cd gains: d_c + 1 must equal some old degree among d_a, d_b, d_c, d_d. It cannot equal d_c. Each of the other options makes two degrees of B consecutive. ∎

**Construction.** Let B₈ be the graph on {0, …, 7} with edges 03, 05, 07, 14, 15, 17, 25, 26, 27, 36, 37, 46, 47 (graph6 `GCR`vo`).

- Its degrees are 3 (seven times) and 5 (vertex 7).
- B₈ is a Laman basis with no tight set of size 4 to 7. This is checked over all 256 vertex subsets in `scripts/family373112.py` and `scripts/freelaman.py`, with logs in `logs/freelaman-8.log` and `outputs/family373112.json`. A short hand check: B₈ − 7 is a theta graph θ(2, 3, 3) with branch vertices 5 and 6, and 7 is joined to its five internal vertices. One verifies sets containing 7 using e(X) = 2|Y| − comp(Y) − |Y ∩ {5, 6}| + cyc(Y) with Y = X ∖ {7}. Sets avoiding 7 have at most |X| + 1 edges.

Given B_n (n even, degrees in {3, 5}, free Laman), obtain B_{n+2} by two applications of Lemma C, both using the same vertex z of degree 3.

- Each split keeps the degrees of u and v and gives the new vertex degree 3. The vertex z goes 3 → 4 → 5.
- So B_{n+2} again has degrees in {3, 5}, and it is free by Lemma C (twice).
- Suitable edges exist:
  - For n = 8, the explicit moves are: split 14 with z = 0 (new vertex 8), then split 26 with z = 0 (new vertex 9). This gives B₁₀, listed in `outputs/family373112.json`.
  - For n ≥ 10, a degree-3 vertex z exists, since the number of degree-5 vertices is (n − 6)/2 < n.
  - First split: at most Σ_{y ∈ N[z]} deg y − e(N[z]) ≤ (3 + 15) − 3 = 15 < 2n − 3 edges meet N[z]. So there is an edge uv with u, v ∉ N[z].
  - Second split (z now has degree 4, and N[z] contains the new degree-3 vertex): at most (4 + 15 + 3) − 4 = 18 < 2n − 1 edges meet N[z]. So again an edge avoiding N[z] exists.
- Brute-force verification of the produced B_n for n = 8, 10, …, 20 over all vertex subsets (2^20 subsets at n = 20): all are free Laman with degree set {3, 5}. The log is `outputs/family373112.json`.

**Proof of the Theorem.** Fix an even n ≥ 8. Let F be the S_n-orbit of B_n, that is, all copies of B_n on [n]. Let M_n be the matroid with bases 𝓑(R_n) ∖ F. Each requirement holds:

- **Matroid.** Freeness is isomorphism-invariant, so (P1) holds by Lemma A and the construction. (P2) holds by Lemma D. 𝓑′ is nonempty, for example any basis containing K₄ − e. Lemma B applies.
- **Rank 2n − 3.** Every member of 𝓑′ has 2n − 3 edges.
- **K₄ is a circuit.** K₄ is R_n-dependent, so it lies in no basis of 𝓑′. Each K₄ − e is R_n-independent and tight on 4 < n vertices, so every R_n-basis containing it has a tight 4-set. Such a basis is not in F (Lemma A), so K₄ − e is M_n-independent.
- **Symmetric.** F is a union of S_n-orbits.
- **M_n ≠ R_n.** B_n is R_n-independent but not M_n-independent.
- **K₃,₃ independent.** K₃,₃ is a tight 6-set and n ≥ 8, so every R_n-basis containing a copy of K₃,₃ lies outside F. Such a basis exists, since K₃,₃ is R_n-independent.

So M_n is a symmetric abstract 2-rigidity matroid, M_n ≠ R_n, with K₃,₃ independent, for infinitely many n. ∎

**Sanity checks** (`scripts/exchange6.py`, `logs/exchange6.log`):
- R_6 has 3355 bases.
- Deleting the 60 prisms leaves a matroid: the full basis-exchange axiom was checked. This reproduces the example of the source and of Patkar–Servatius–Subrahmanyam.
- Deleting the 10 copies of K₃,₃ also leaves a matroid.
- Control: deleting the orbit of a non-free basis (one containing a tight 4-set) breaks the exchange axiom, as Lemma A predicts.

Consistency with the source: for n = 7, my exhaustive search over connected graphs with 11 edges and minimum degree ≥ 3 finds exactly two free Laman bases. Both have exchange-adjacent copies (`logs/freelaman-7.log`), so this method gives nothing at n = 7. That matches the author's hand check, which this lane neither confirms nor refutes in general.

## 4. Prior art and registry screen (bounded)

- **Patkar, Servatius and Subrahmanyam**, "Abstract and generic rigidity in the plane" (JCTB 1994; author copy `sources/prior-servatius-dualjctb2004.pdf`, sha256 116e0e79…). They give the same n = 6 example (bases of R_6 minus prisms), proved through circuit axioms, using "the triangles are the only proper rigid subgraphs of a prism". They say "there are many abstract rigidity matroids on K_n for n ≥ 6" without giving symmetric examples for n ≥ 7. Non-symmetric examples are easy: delete a single free basis. **The deletion method is therefore old.** What this lane adds:
  - the general orbit-deletion Lemma B;
  - the freeness criterion (Lemma A);
  - the free-preserving split (Lemma C);
  - the degree-parity device (Lemma D) that makes the orbit deletion valid for infinitely many n.
- **Jackson–Tanigawa** arXiv:2503.14780 and arXiv:2607.06228 were fetched and grepped for prism, relax, K3,3, tighten, free basis and Tyomkyn. Only unrelated K3,3 rank computations turned up. The bodies were not fully read.
- **Web search** (2 standard queries) found no later work on Conjecture 6.1.
- **Lean Pool** HEAD 01db1d70 (unchanged): keyword scan, no hit. **GitHub repository search**: "Tyomkyn" and "2602.11892" both give 0. "rigidity matroid lean" returns only pw/cn-rigidity-matroid, which is about point-group-symmetric frameworks and is unrelated.

## 5. Honest credit risk: MEDIUM–HIGH

For credit:
- This is a genuine refutation of a conjecture posed in Feb 2026 and kept in v2 (Aug 2026). The author explicitly asks whether the phenomenon extends to arbitrarily large n.

Against credit:
- The mechanism is the source's own n = 6 deletion example, which is itself classical (PSS 1994).
- The new part is about one page: Lemmas A–D plus the explicit base graph.
- Under the 336565 / 347138 precedents ("source example + standard technique; new part under a page"), the root may rule this a source-ingredient bridge. I flag this rather than argue it away.

Mitigating points:
- Lemma B for orbits and Lemma C are not stated in the source or in PSS.
- The degree trick is needed because the obvious generalizations fail: n = 7 has free bases, but all of them have adjacent copies.

## 6. Lean plan (Lean cost: MEDIUM)

The heavy prerequisite already exists publicly: `SimpleGraph.countMatroid V 2 3` in bryangingechen/CombinatorialRigidity at sha 021c2284bc387efee3c3b20a18eb5f769638b578 (`sources/registry/combrig-CountMatroid.lean`, `combrig-Laman.lean`; toolchain leanprover/lean4:v4.36.0-rc1). That toolchain differs from the campaign pin (Lean 4.34.1, Mathlib d13f23b7), so root must decide between vendoring and porting `CountMatroid.lean` plus its dependencies (`SparsityIComponents.lean`, `Sparsity.lean`), or replaying in the repo's own pinned environment.

Statement correspondence:
- R_n is `countMatroid (Fin n) 2 3`. Its independent sets are exactly the (2,3)-sparse edge sets, which is Definition 1.2 literally.
- Abstract 2-rigidity matroid: `M.E = (⊤ : SimpleGraph (Fin n)).edgeSet`, `M.rk = 2n−3` (or `M.eRank = 2n−3`), and `∀ f : Fin 4 ↪ Fin n, M.IsCircuit (K4edges f)`.
- Symmetric: `∀ σ : Equiv.Perm (Fin n), ∀ I, M.Indep I → M.Indep (Sym2.map σ '' I)`.
- K₃,₃ independent: `∀ f : Fin 6 ↪ Fin n, M.Indep (K33edges f)`.
- Endpoint: `¬ {n | ∃ M, Abstract2Rig M ∧ Symm M ∧ M ≠ countMatroid (Fin n) 2 3 ∧ K33Indep M}.Finite`, which is the literal negation of the MathDB statement.

Draft sources are in `lean/Rigidity373112.lean`. They are **UNCOMPILED**: proofs are outlines with explicit `sorry` placeholders, and nothing was run. The proof chain:
1. `free_of_noTight`: Lemma A, a counting argument.
2. `split_free`: Lemma C, a case analysis on Finset cardinalities.
3. `degSet_noConsec → no adjacent copy`: Lemma D, a degree-multiset argument.
4. The base graph B₈ by `decide` over 256 subsets (kernel `decide`, no `native_decide`).
5. Existence of the split edge for n ≥ 10, a counting lemma.
6. M_n built with `IndepMatroid.ofFinite` (Indep I := R.Indep I ∧ I ∉ F), with augmentation by the argument after Lemma B.
7. The rank, K₄-circuit, symmetry, ≠ R and K₃,₃ fields.

Estimated size: 800 to 1500 lines on top of CountMatroid.
