# Candidate ordinary refutation of MathDB 330264

This is not a complete Lean MathDB solution and earns zero credit. Independent review and prior-art comparison remain required.

## Exact statement

Ciobanu–Kolpakov, arXiv:1504.02774v3 (17 January 2020), Conjecture 1.3: two trees whose adjacency graphs, complements and line graphs are respectively cospectral have the same geodesic growth in their right-angled Coxeter groups, with standard generators. This is exactly the normalized MathDB assertion. There is no genericity, connectivity relaxation or asymptotic restriction in this refutation.

## Witness

Both graphs have vertex set {0,...,18}. Edges are unordered; the displayed order is used only to enumerate the edge states.

G: `[[1, 0], [1, 2], [1, 9], [0, 10], [2, 3], [3, 4], [4, 5], [5, 6], [5, 8], [6, 7], [10, 11], [11, 12], [11, 17], [12, 13], [13, 14], [14, 15], [15, 16], [17, 18]]`

H: `[[1, 0], [1, 2], [0, 11], [2, 3], [2, 9], [3, 4], [4, 5], [5, 6], [5, 8], [6, 7], [9, 10], [11, 12], [12, 13], [12, 18], [13, 14], [14, 15], [15, 16], [16, 17]]`

Each graph is connected (breadth-first search from 0 reaches all 19 vertices), has 18 edges, and therefore is a tree. None has triangles. These elementary finite checks can also be made by following the edge lists; no planarity hypothesis is needed.

## Three exact spectral equalities

For each of the adjacency, complement and line matrices, the following lists are characteristic-polynomial coefficients in descending order. The line-graph vertices are the 18 displayed edges, adjacent when the edges share an endpoint. Complement adjacency is J-I-A. Both matrices of each kind have precisely the same coefficient list:

adjacency: `[1, 0, -18, 0, 133, 0, -522, 0, 1179, 0, -1558, 0, 1177, 0, -473, 0, 85, 0, -4, 0]`

complement: `[1, 0, -153, -1366, -5283, -9226, -255, 26518, 36212, -5482, -49704, -28056, 19616, 22666, 847, -5160, -1273, 156, 42, 0]`

line: `[1, 0, -20, -6, 161, 88, -658, -484, 1433, 1242, -1637, -1542, 937, 892, -249, -212, 24, 14, -1]`

These are finite integer identities. An explicitly reproducible ordinary arithmetic proof is `exact_spectra.py`: start B0=I and c0=1; for k=1,...,n set Ck=A B(k-1), ck=-tr(Ck)/k, Bk=Ck+ck I. Each division is exact. The coefficient list is [1,c1,...,cn] by the Faddeev–LeVerrier identity (equivalently Newton identities). `independent-spectra.json` independently verifies all six polynomials using SymPy's exact characteristic-polynomial implementation. There is no floating-point equality assumption in this step. Real symmetric matrices with equal characteristic polynomials have equal eigenvalue multisets, which is the precise cospectrality notion used by the source.

## Exact geodesic discrepancy

For a tree with vertex set V and edge set E, enumerate states Q={empty} union V union E, 38 states here. For each state S and letter v in V, disallow the transition if v belongs to S; otherwise its target is {v} union (S intersect N(v)). Because the graph is triangle-free, this is again a listed state. The source's Definition 2.2 states precisely this automaton. Antolin–Ciobanu arXiv:1203.2752v2 Proposition 3.2 and its proof derive it as the product of the modified C2 factor automata. It accepts precisely shortest words in the presented group, and all nonfail states accept.

Let a0 have value 1 at empty and 0 elsewhere. If b(S,T) counts letters giving transition S to T, put a(k+1)(T)=sum_S a(k)(S)b(S,T). Induction by the last letter shows that sum_T a(k)(T) is the number of accepted words of length k; it counts WORDS, not distinct group elements. This distinction is essential.

The two sums agree for k=0,...,17. At k=18 they are

G: 37769749324097905710910
H: 37769749324097905710906.

The difference is 4. Thus their geodesic-growth coefficients and hence their series differ. Together with the three exact spectral equalities, this contradicts Conjecture 1.3 in full scope.

`AutomatonCertificate.lean` is an attempted partial kernel certificate for the graph-derived transition tables and all 18 vector recurrences. It does not redefine geodesic growth as an automaton count and call that a group theorem. The missing group/normal-form and spectral bridges are explicitly listed in FORMAL-GAPS.md.

## Existing-theorem test and novelty limits

The source's Theorem 1.1 / Lemma 3.3 produces triple-cospectral trees with EQUAL growth. Its Theorem 1.2 / Lemma 5.2 produces unequal growth while allowing different line spectra, with a discrepancy at length10. Our pair has all three spectra equal and no discrepancy before length18. Neither source theorem alone plus the displayed routine bridge proves this counterexample. The proof bodies of both source mechanisms were read. The 2013 Theorem3.7 and 2021/2022 Antolin–Foniqi link-regular formulas require regularity: our trees have degrees1,2,3 and are not link-regular. The general automaton theorem is a tool, not a prior refutation.

This comparison does not prove novelty. McKay1977 and Godsil's full spectral-construction bodies have not yet been compared to determine whether this exact pair or a direct transformation was already known. No direct prior refutation was located in the bounded searches recorded in research-notes.md. The absence of a search hit and the MathDB open label have no positive evidentiary weight. Current OpenAI registry path screening and its recent head receipt are bounded; AIM returned a page-not-found response, giving no listing evidence. There is no complete registry clearance or worldwide priority claim.
