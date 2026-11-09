# Ordinary audit — 359209

PASS as an ordinary helper, with zero endpoint or novelty credit. No finite checker, solver, or Lean execution was used.

Let H=K_{n×s}. Its only edges join different host parts. An injective monochromatic K_{2,n} exists if and only if some unordered pair u,v has at least n common neighbors in one color among vertices outside the endpoint host part(s). The n common neighbors can occupy several host parts and can have edges between themselves; the copy is a subgraph, not an induced subgraph. The pair u,v can itself be an edge or a host nonedge. Self-neighbors are never allowed. This equivalence covers every injective copy.

For s=5 and an avoiding coloring, fix a part A. At each vertex outside A, put r=number of red neighbors in A. The number of monochromatic wedges with center that vertex and endpoints in A is C(r,2)+C(5-r,2)=(r−2)(r−3)+4≥4, with equality exactly for r=2,3. Thus at least 20(n−1) such wedges occur. On the other hand each of the ten endpoint pairs admits at most n−1 centers of either color: at most 20(n−1). Equality forces every external vertex's degree into A to be 2 or 3 and every pair in A to have exactly n−1 common neighbors of each color.

For u,v∈A all possible neighbors belong to the SAME set of 5(n−1) vertices; no host nonedges in A can be counted as blue edges. Inclusion–exclusion gives blue-common-count =5(n−1)−d_R(u)−d_R(v)+(n−1). Equality with n−1 gives d_R(u)+d_R(v)=5(n−1). Comparing these equations using a third vertex shows all five degrees equal 5(n−1)/2. Hence n is odd. The sum of red degrees over the 5n vertices is 25n(n−1)/2; for n≡3 mod4 it is odd, contrary to the handshaking lemma.

For the global wedge count let D=5(n−1). At any vertex with red degree r, C(r,2)+C(D−r,2)≥D(D−2)/4 (also for odd D, when this real lower bound is weaker than the integer minimum). Count every unordered pair as endpoints, including same-part nonedges. Absence of the forbidden graph implies

5n·D(D−2)/4 ≤ 2(n−1)C(5n,2).

Since n≥2, division by 5n(n−1)>0 is legitimate and gives 5(5n−7)/4≤5n−1, hence 5n−31≤0. Therefore n≤6. Even n are excluded by degree integrality, and n=3 by handshaking. Only n=5 survives. This proves m_n≤5 for all n≥2 except possibly 5, conditional on no other unproved lemmas. It does NOT prove m_n≥5 for all n, and is not the conjecture.

At n=5 every vertex has total red degree 10. Its degrees into the four other parts are 2 or 3 with sum 10, hence two are 2 and two are 3. Same-part pairs have common counts (4,4). These are necessary constraints, not an existence proof.

Encoding audit (ordinary arithmetic only): n=3,s=4 has 12 vertices and C(3,2)·16=48 edge bits. Eighteen same-part pairs have eight eligible neighbors and 48 cross-part pairs have four. For each pair and eligible 3-set forbid the six edges all red and all blue: 2[18 C(8,3)+48 C(4,3)]=2400 clauses, each length six. No clause uses a host nonedge. UNSAT implies m_3≤4; SAT only m_3≥5. Combined with the old lower bound in source-comparison.md, UNSAT gives m_3=4.

At n=5,s=5 there are 250 edge bits, 50 same-part pairs (20 eligible neighbors) and 250 cross-part pairs (15 eligible neighbors). Thus 300 pairs and 4750 pair-neighbor triples per color. A direct forbidden-5-set encoding has 2[50 C(20,5)+250 C(15,5)]=3,051,900 clauses of length ten. For compressed encodings each auxiliary conjunction must satisfy y↔(edge(u,w)=color ∧ edge(v,w)=color); an at-most-four encoding must have a proved existential-extension equivalence. Missing either direction can manufacture a false UNSAT. Balancing constraints require their own proved implication. No symmetry restriction is justified merely by apparent regularity.

The n=5 SAT endpoint is m_5>5, while UNSAT proves only m_5≤5 (and, with the already printed lower construction, m_5=5). The latter is a parameter instance, not a full resolution of 359209. No truth value of either diagnostic is claimed here.
