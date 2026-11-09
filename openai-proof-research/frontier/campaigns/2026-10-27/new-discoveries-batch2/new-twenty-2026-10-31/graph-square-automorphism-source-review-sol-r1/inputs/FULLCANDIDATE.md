# Ordinary candidate: MathDB 332935

Status: complete ordinary refutations of BOTH literal clauses, personally derived and self-reviewed only. Zero accepted credit. No formal execution, no independent review, no demonstrated literature novelty.

## Exact statement and source

The unchanged literal object is originals/332935.jsonl. Its clause (i) quantifies over connected finite simple graphs of radius r and diameter d satisfying r<d<=2r-2; clause (ii) over connected bipartite graphs of radius r>2. Both assert equality of the permutation groups Aut(G) and Aut(G^2) on the SAME vertex set. A nonedge-preserving permutation of G that preserves the square disproves equality; an abstract group comparison is unnecessary.

The actual latest available arXiv PDF 1604.03839v1, SHA256 2bcc115c4a05b01871e5108a6d5b0d49a4cce67f80ee4716dd740d6a6c96d425, printed p.7 Conjecture 2.17 contains exactly these two clauses. Printed pp.1-2 define finite simple graphs, distance, eccentricity, radius, diameter and natural power by distance at most k. The current abstract metadata exposes only v1, submitted 13 April 2016. The PDF itself prints November 8, 2018 as its internal date; this is not evidence of a second arXiv version. No journal reference was found in the read metadata. Final journal/correction search is incomplete, and no unread later theorem is attributed.

## Clause (ii): C6

Use vertices 0,1,2,3,4,5 and edges 01,12,23,34,45,50. Consecutive paths prove connectivity. Even versus odd indices is a bipartition. Every vertex has an opposite vertex at distance three, every other vertex at distance at most three, so every eccentricity, the radius, and the diameter are three. In the square, the ONLY nonedges between distinct vertices are {0,3},{1,4},{2,5}. The transposition tau=(0 3), fixing all four other vertices, preserves this unordered matching and hence its complement, the square. It does not preserve G: edge {0,1} maps to nonedge {3,1}. Thus tau is in Aut(G^2) but not Aut(G). The literal radius condition is strictly >2 and is paid by r=3.

This is not enough for clause (i), since C6 has r=d. That shortcut was explicitly rejected for the first clause. It also contradicts the source's printed Theorem 2.15 for n=6,k=2; that theorem is NOT relied on. The source proof's asserted common-neighbor list omits wraparound common neighbors in this case. An error in that printed theorem alone would be a source correction and does not establish significance of the new first-clause construction.

## Clause (i): an infinite family, not a boundary example

For every integer m>=4, take a cycle C_(2m) with vertices c_0,...,c_(2m-1) in cyclic order, and a cycle C5 with vertices x_0,x_1,x_2,x_3,x_4 in cyclic order. Identify x_0 with c_0 and make NO further identifications or edges. Call this vertex o. The graph has 2m+4 vertices and is finite, simple and connected.

The two cycles meet at the cut vertex o. A shortest path with endpoints on one cycle never makes a nontrivial excursion into the other: such an excursion returns to o and can be deleted. Therefore distances within each cycle are unchanged. A path between a nonroot x_i and a cycle vertex c_j must pass through o. Its distance is exactly d_C5(x_i,o)+d_C_(2m)(o,c_j), since shortest paths on the two cycles concatenate. These facts prove ALL distance assertions below, rather than assuming a small distance table.

Every c_j has its antipode c_(j+m) at distance m, so its eccentricity is at least m. Every x_i other than o has distance m+d_C5(x_i,o) to c_m, at least m+1. The root has eccentricity max(m,2)=m. Hence the radius is exactly m.

Within the large cycle distances are at most m; within C5 at most 2. Cross-cycle distances are at most m+2, and x_2 to c_m attains m+2. Thus the diameter is exactly m+2. Consequently r<d and d<=2r-2 are equivalent here to m<m+2 and m+2<=2m-2, both true for every m>=4. This checks the full strict/weak combination, including m=4 (r=4,d=6).

Let sigma transpose x_2 and x_3 and fix every other vertex. In C5 every two distinct vertices have distance at most two; that whole five-vertex set is a clique in G^2. Both x_2 and x_3 are at distance two from o, and their distance to each c_j other than o is 2+d(o,c_j)>=3. Thus neither is adjacent in G^2 to any large-cycle vertex other than o. They have identical closed neighborhoods in G^2, exactly the five vertices of C5. Every pair not incident with either vertex is fixed; the pair between them stays an edge; pairs with exactly one of them have equal adjacency under exchange. This proves sigma preserves square adjacency in BOTH directions. Its inverse is itself, so it is an automorphism. But {x_1,x_2} is an edge of G and {x_1,x_3} is not. Therefore sigma is not an automorphism of G.

This disproves clause (i) in its literal domain for an infinite family. Clause (i) does not demand bipartiteness. The family contains a five-cycle and is not offered for clause (ii), which has its own valid witness above. No graph programs, finite enumeration, solver, numerical experiment or theorem checker were used.

## Sustained route, checks and limits

The initial C6 mechanism pays only the bipartite clause. Adding a pendant tail to C5 retains square twins but creates tree-like radius/diameter behavior and does not automatically pay d<=2r-2. The cut-vertex construction instead adds a long self-centered cycle. Its antipodes force radius m while the shallow C5 raises diameter by exactly two. This repairs the actual failed hypothesis, rather than extrapolating from the six-cycle.

Both counterexamples are independently reproducible from distance arguments. This author's self-review is NOT independent review. The actual conjecture and definitions are read; source theorem 2.15 is explicitly contrary and is not silently accepted. C6 and complete multipartite squares are classical mechanisms; the wedge construction may likewise be known. A complete applicable earlier counterexample to Conjecture 2.17 was not read in this bounded run, so neither a novelty PASS nor a fabricated routine-exclusion is assigned. The strongest objection is that this could be a routine application of known square-twin constructions or a previously published correction. It requires an exact comparison, not a judgment based on proof length.

## Gate disposition

Literal PASS. Source statement/definitions PASS at arXiv v1 depth; journal/corrections HOLD. Ordinary math SELF-PASS for both clauses. Current registry roots and bounded searches were checked, but no complete relevant registry theorem body was obtained and no global absence claim is made. Prior/novelty HOLD. Significance HOLD pending independent evaluation of the full first-clause family against existing square-root/twin literature. Formal UNEXECUTED. Independent UNREVIEWED. Acceptance NO; credit 0.
