# Five positive matchings refute MathDB 366974

This is a candidate for independent root review, with zero accepted credit.

The source is Farrokhi Derakhshandeh Ghouchan and Yazdan Pour, arXiv:2502.02826v1, Conjecture 4.7 (PDF p. 23). Its current arXiv history contains only v1. It asserts pmd(C_m box C_n)=6 when m+n is even or (m,n) is (3,4), (3,6), or (5,6). We refute its explicit (3,4) case. This does not correct a MathDB-only paraphrase or contradict a source theorem: Theorem 4.5 deliberately excepts this case, and Proposition 4.6 treats only (3,3) and (4,4).

Use vertices 0 through 11, where vertex 4a+b means (a,b) in Z/3 x Z/4. Join equal first coordinates when second coordinates are cyclic neighbors, and equal second coordinates when first coordinates are cyclic neighbors. There are 24 edges. Here is an ordered partition into matchings:

1. {2,10}, {3,7}, {5,9}, {8,11}.
2. {0,8}, {1,5}, {2,3}, {4,7}, {6,10}.
3. {0,4}, {1,2}, {3,11}, {6,7}, {9,10}.
4. {0,3}, {1,9}, {4,8}, {5,6}, {10,11}.
5. {0,1}, {2,6}, {4,5}, {7,11}, {8,9}.

For stage i, give vertices 0 through 11 the following integer weights.

| i | weights in vertex order |
|---|---|
| 1 | -10, -10, -3, 2, -10, 8, -10, -1, 6, -7, 4, -5 |
| 2 | -5, -3, 2, -1, -7, 4, -9, 8, 6, -12, 10, -12 |
| 3 | -9, -3, 4, 8, 10, -12, -5, 6, -12, 2, -1, -7 |
| 4 | -9, 8, -12, 10, -5, 4, -3, -12, 6, -7, 2, -1 |
| 5 | 10, -9, 8, -12, 6, -5, -7, 4, 2, -1, -12, -3 |

Each listed pair is an edge, the pairs in each row are disjoint, and the five rows partition the 24 edges. At each stage every edge in its row has weight sum exactly 1, while every other still-present edge has strictly negative sum. The full residual-edge arithmetic is in `outputs/pmd-signs.json`; it is also checked directly by kernel `decide` against the Cartesian adjacency in Lean, independently of the search implementation. Thus every row is a positive matching in the graph left by deleting earlier rows. This proves pmd(C_3 box C_4) <= 5 and therefore disproves the conjectured value 6. The general lower bound for a 4-regular graph in source Lemma 4.3 also gives equality 5, but the refutation endpoint does not depend on that source lemma.

The Lean file uses real vertex weights (the integer table is cast into R), nonempty parts, symmetric edge colors, the matching condition at shared vertices, and positivity on exactly the current color among remaining edges. `parts_partition` proves every edge belongs to exactly one color; `residual_partition` proves the remaining-edge comparison equals deleting earlier parts; `pmd_minimum` proves the natural infimum is an attained minimum whenever a decomposition exists. The theorem `refutes_conjecture_4_7` negates the full parameterized equality statement, not a bounded diagnostic or an uninterpreted checker property.

Novelty limits: the search and arithmetic constitute a mathematical certificate, not a novelty certificate. Current public registry HEAD receipts and complete Omega D5/Problems path listings are retained. No matching positive-matching torus statement was found in those path screens; unrelated Cartesian or dihedral paths are false-positive topic hits, not unread proof matches. OpenAI/math HEAD is unchanged, permitting reuse of the cached complete preprints listing. Targeted title, parameter, 2026 and thesis searches found the source, the 2022 companion, and general LSS literature, without locating this decomposition. The source's proof of Theorem 4.5 and neighboring Proposition 4.6 were read; they do not print a construction for (3,4). The cited 2022 arXiv:2110.12168 handles, among other things, circular ladders C_n box K_2 and cubic generalized Petersen graphs, not this degree-4 torus. A Genova thesis PDF route returned 403 and was not retried; its body remains unread. Independent root novelty/subsumption review remains required, including that institutional lead. No priority claim or acceptance is made.
