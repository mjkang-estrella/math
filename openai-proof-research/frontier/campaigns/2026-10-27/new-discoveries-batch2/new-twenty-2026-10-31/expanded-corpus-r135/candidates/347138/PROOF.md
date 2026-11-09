# MathDB 347138: refutation of the rooted non-separating out-branching conjecture

Status: CANDIDATE (lane r135, Claude). Ordinary proof complete. Lean draft UNCOMPILED, so there is no accepted credit. Root review, independent fidelity and significance review, and a Lean build are still required. I do not self-accept this.

## 1. Exact statement

Source: J. Bang-Jensen, S. Bessy, A. Yeo, "Non-separating spanning trees and out-branchings in digraphs of independence number 2", arXiv:2007.02834 v1, 6 July 2020 (the only arXiv version). Published in Graphs and Combinatorics 38 (2022), article 187, published 11 November 2022 (Springer full text read on 2026-11-03; `sources/gc2022-springer.html`).

Conjecture 35 (identical in arXiv v1 and in the published version):

> There exists an integer L such that every digraph D on at least L vertices with λ(D) ≥ 2 and α(D) = 2 has a non-separating out-branching B_s^+ for every choice of s ∈ V.

MathDB 347138 states the same thing: "There exists an integer L such that every digraph D on at least L vertices with λ(D) ≥ 2 and α(D) = 2 has a non-separating out-branching B_s^+ for every choice of s ∈ V."

Source definitions (Section 1 and the abstract):
- An out-branching B_s^+ is a spanning out-tree rooted at s. Every vertex except s has exactly one entering arc of the tree, and s reaches every vertex using tree arcs.
- A subdigraph X = (V, A') is non-separating if D \ A' is strongly connected.
- λ(D) is the arc-strong connectivity. α(D) is the maximum number of pairwise non-adjacent vertices.
- Digraphs have no loops and no parallel arcs. Directed 2-cycles are allowed (the source uses them, for example W1 and the complete digraph).

The negation, which is what we prove: for every L there is a digraph D with |V| ≥ L, λ(D) ≥ 2 and α(D) = 2, and a vertex s with no non-separating out-branching rooted at s.

## 2. The family D_m (m ≥ 3)

Vertex set: A = {a_1, ..., a_m} and B = {p_1, p_2, p_3, p_4}, so n = m + 4.

Arcs:
- A-internal: a_i a_j for all i ≠ j (D[A] is the complete digraph).
- B-internal: the source's semicomplete digraph W1 (Theorem 19(b), Figure 3), which is the Hamiltonian cycle p_1 p_2 p_3 p_4 p_1 plus p_1 p_3, p_2 p_4 and p_4 p_2. That gives seven arcs: p1p2, p2p3, p3p4, p4p1, p1p3, p2p4, p4p2.
- Entries (A to B): a_1 p_1 and a_2 p_3. There are no other A to B arcs.
- Exits (B to A): p_3 a_1 and p_3 a_m. There are no other B to A arcs.

Useful local facts about W1:
- d^-(p_1) = 1, with in-arc p4p1 only.
- d^+(p_3) = 1 inside W1, with out-arc p3p4 only.
- The in-neighbours are N^-(p_2) = {p_1, p_4}, N^-(p_3) = {p_1, p_2} and N^-(p_4) = {p_3, p_2}.

(In the lane scripts, B is indexed 0, 1, 2, 3 for p_1, p_2, p_3, p_4.)

## 3. Lemma 1: α(D_m) = 2

D[A] and D[B] are cliques of the underlying graph. D[B] = W1 is semicomplete; check the six pairs. Any three vertices therefore include two on the same side, which are adjacent, so α ≤ 2. The vertex p_2 has no arc to or from A, so a_1 and p_2 are non-adjacent and α = 2.

## 4. Lemma 2: λ(D_m) = 2 (for m ≥ 3)

We show that every nonempty proper X ⊂ V has at least two arcs leaving it. Write X_A = X ∩ A and X_B = X ∩ B.

- If ∅ ≠ X_A ≠ A: then |X_A| · |A \ X_A| ≥ m − 1 ≥ 2 complete-digraph arcs leave X.
- If X_A = A: then X_B ≠ B, and the out-arcs are the W1 arcs from X_B to B \ X_B plus the entries into B \ X_B.
- If X_A = ∅: then X_B ≠ ∅, and the out-arcs are the W1 arcs from X_B to B \ X_B plus the exits out of X_B. Both exits leave from p_3, so p_3 contributes 2.

The last two cases involve only the 15 + 15 subsets of B. Their minimum is 2, from the exhaustive table in `scripts/gadget_certificate.py`, claim C3 (`logs/gadget-certificate.log`). By Menger's theorem, equivalently by the definition of arc-strong connectivity, λ ≥ 2. Also λ = 2 exactly, because X = B has exactly the two exits as out-arcs.

## 5. Theorem: D_m has no non-separating out-branching rooted at a_1 (in fact at any a ∈ A)

Fix a root s ∈ A, let F be an out-branching rooted at s, and let R = D \ A(F). Suppose, for a contradiction, that R is strongly connected.

**Crossing lemma (path suffix and prefix).** Take a directed path from a vertex of A to a vertex y ∈ B. Its last arc going from A to B is followed by a subpath that stays inside B. Symmetrically, a path from x ∈ B to A has its first B to A arc preceded by a subpath inside B.

**Step 1: F contains exactly one entry.** The F-path from s to p_1 crosses from A to B, so F contains an entry. R is strong, so the R-path from s to p_1 crosses too, so R contains an entry. There are exactly two entries, so exactly one of them lies in F. Call its head e ∈ {p_1, p_3}; the other entry lies in R, with head e'.

**Step 2: the B-part of F.** Let T be the set of arcs of F with both ends in B. Take any q ∈ B. The F-path from s to q has its last A to B arc in F. Its only F-entry is the arc into e. By the crossing lemma, T contains a path from e to q. So T ⊆ A(W1) and e reaches all of B in T.

**Step 3: the B-part of R.** The arcs of R inside B are exactly W1 − T.
- For q ∈ B, the R-path from s to q ends with an R-entry followed by a path inside B. The only R-entry is the arc into e'. So e' reaches all of B in W1 − T.
- For q ∈ B, the R-path from q to s starts with a path inside B followed by an exit. Every exit has tail p_3. So every vertex of B reaches p_3 in W1 − T.

**Step 4: finite contradiction inside W1.**

Case e = p_1, e' = p_3. By Step 3, W1 − T is strongly connected, and T contains an out-branching T_0 of W1 rooted at p_1. Since W1 − T ⊆ W1 − T_0, the digraph W1 − T_0 is strong as well. This contradicts the source's Theorem 19(b) (W1 has no non-separating branching). Direct argument:
- p_1 needs an out-arc in W1 − T_0, and it needs a child in T_0. Its only out-arcs are p1p2 and p1p3, so T_0 contains exactly one of them.
- If p1p2 ∈ T_0: then p_3's T_0-parent is p_2, which forces p2p4 into W1 − T_0 (p_2 needs an out-arc there). Then p_4's parent is p_3, so p3p4 ∈ T_0, and p_3 has no out-arc in W1 − T_0.
- If p1p3 ∈ T_0: then p_2's parent is p_4, so p_4's parent cannot be p_2 (that would be a cycle). Hence p3p4 ∈ T_0, and again p_3 has no out-arc in W1 − T_0.

Case e = p_3, e' = p_1. Take an out-branching T_0 ⊆ T of W1 rooted at p_3. Then p_1 reaches all of B, and every vertex reaches p_3, in W1 − T_0. Now:
- p3p4 ∈ T_0, because it is p_3's only out-arc.
- p4p1 ∈ T_0, because it is p_1's only in-arc.
- If p_2's parent is p_1: the arcs of W1 − T_0 are p1p3, p2p3, p2p4 and p4p2. From p_1 only p_3 is reachable, and p_3 has no out-arc. Contradiction.
- If p_2's parent is p_4: then p_4 has no out-arc in W1 − T_0 (p4p1 and p4p2 are both in T_0), so p_4 cannot reach p_3. Contradiction.

(The monotone subset form of both cases is checked exhaustively in `scripts/gadget_weak.py`: all 128 subsets T ⊆ A(W1) such that e reaches all of B in T, with zero counterexamples. Separately, `scripts/gadget_certificate.py` checks claims C1 and C2 over all out-branchings.)

So R is not strongly connected. Since n = m + 4 is unbounded, Conjecture 35 is false. ∎

## 6. Machine cross-checks (diagnostic, Python, capped)

- `scripts/gadget.py`: brute-force search over all two-block digraphs, with D[A] the complete digraph on 3 vertices, D[B] semicomplete on b ≤ 4 vertices, and exactly two arcs each way. It found 24 hits, all with every root in A failing for m = 3, 4, 5, 6 (`logs/gadget-b4.log`). b ≤ 3 gave no hits.
- `scripts/gadget_check.py`: full brute force on D_m, checking λ ≥ 2, α = 2 and the failing roots, for m = 2 to 7. For every m the failing roots are exactly the m vertices of A; every root in B has a non-separating out-branching. The m = 8 run was stopped by the 120 s CPU cap (`logs/gadget-check.log`).
- `scripts/goodpair_check.py`: for m = 2 and 3, every root s ∈ A and every t ∈ V, D_m has arc-disjoint B_s^+ and B_t^-. The failure is therefore NOT inherited from good-pair obstructions such as W in Bang-Jensen–Bessy–Havet–Yeo (arXiv:2003.02107), Proposition 22.
- `scripts/gadget_fast.py` and `scripts/gadget_fast5.py`: the reduced criterion reproduces the 24 hits at b = 4. It finds no gadget at b = 5: 55,404 semicomplete digraphs with minimum in-degree ≥ 1 and 6,060,075 attachments with λ ≥ 2 were tested (`logs/gadget5-all-min1.log`). Restricted to minimum in-degree ≥ 2, the counts are 30,234 digraphs and 5,167,995 attachments (`logs/gadget5-all.log`).
- `scripts/gadget_iso.py`: all 24 hits at b = 4 are labelings of W1.

## 7. Prior-art, novelty and source checks (bounded)

- The published version (Graphs Combin. 38 (2022) 187) keeps Conjecture 35 verbatim. arXiv has only v1. There is no retraction or erratum on either page.
- Web searches on 2026-11-03 ("non-separating out-branching", Conjecture 35 wording, the authors) found no refutation or later resolution.
- The source's own small examples are W1 and W2 (semicomplete, but α = 1 so outside the conjecture's α = 2), and D̃ (Figure 6, a single digraph with no non-separating out-branching at all). The conjecture's "at least L vertices" clause excludes any finite list of small examples. The source contains no construction of arbitrarily large α = 2 digraphs with a failing root. The source notes that the Proposition 12 family has non-separating branchings from every vertex.
- The cited companion paper (arXiv:2003.02107, J. Graph Theory 2020) has:
  - W (8 vertices, α = 2): no arc-disjoint B^+_{c2}, B^-_{c1}. This is one small digraph, so it does not refute a statement about all digraphs with at least L vertices.
  - The infinite family W'_n (Proposition 23): α = 3, so outside scope.
  - WS (Theorem 24): α ≤ 7, so outside scope.
  - None of these is an α = 2 infinite family. Moreover, our D_m HAS all prescribed good pairs for roots in A (§6), so even an α = 2 good-pair family would not be the same mechanism.
- Registries:
  - OpenAI/math HEAD 4eaee87548250b2682affda7d05d947c05554bae (unchanged).
  - Omega HEAD a41b3dc77a15de8ceeabfcba85d60b17bad3df6b, which is 22 commits after 86172888 and changes 19 files (finite groups, Weil, meta), none relevant (`sources/omega-compare.html`).
  - A path screen of the cached complete D5/Problems trees at 86172888 and of the complete OpenAI preprint listing found no branching, digraph or independence-number-2 item (`outputs/registry-screen-targets.json`).
  - These are path and title screens only.

## 8. Risk flags for root (honest)

1. **Source-ingredient risk (lessons 364079, 371637, 374241).** The gadget is the source's own W1. Case e = p_1 is exactly the source's Theorem 19(b). Case e = p_3 is a 2-line check. The new ingredients are the co-bipartite gluing with exactly two arcs each way, which creates arbitrarily large α = 2, λ = 2 digraphs, and the crossing argument.
   - The source's Lemma 21 handles co-bipartite digraphs, but only under δ^- ≥ 3, which excludes W1-blocks, and only for the existence of some root.
   - Theorem 19(e) and Corollary 20 already show that roots can be restricted in semicomplete pieces. This suggests the authors did not foresee that a W1 block could survive inside large α = 2 digraphs.
   - Root should judge whether this is a "routine bridge". In its favour: the conjecture is a published (2022) conjecture of three experts, stated after Theorem 19 was proved, and the counterexample needs a construction absent from both the source and its cited papers.
2. **Significance.** The refutation is of the rooted version (Conjecture 35) only. Conjecture 34 (some root) is NOT refuted: D_m has non-separating out-branchings rooted in B. λ(D_m) = 2 exactly, and the minimum in-degree is 2. Theorem 8 needs δ^- ≥ 5 (or an oriented graph with δ^- ≥ 3) and gives only some root, so there is no conflict with the source's theorems.
3. **Uniqueness.** In the two-block design with two arcs each way, W1 is the only gadget for b ≤ 5. We did not search other designs.
4. **Fidelity.** "Digraph" means no loops and no parallel arcs; D_m is simple, so the refutation applies to multidigraph readings as well. λ(D) ≥ 2 is the source's notion (2-arc-strong). α(D) = 2 holds exactly.

## 9. Lean plan

See `statement-correspondence.md` and `lean/NonSepBranching.lean` (UNCOMPILED). The formal endpoint is `¬ Conjecture35`. The definitions are literal: Prop-valued arc relation on a Fintype, ReflTransGen strong connectivity, 2-arc-strong as "strong after deleting any single arc", α = 2 as "a non-adjacent pair exists and no independent triple", and out-branching as root without in-arc, unique in-arc elsewhere, and reachability from the root.
