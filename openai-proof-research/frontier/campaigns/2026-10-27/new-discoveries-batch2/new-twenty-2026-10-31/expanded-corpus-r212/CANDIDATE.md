# Provisional counterexample to MathDB 369935

Status: ordinary proof complete; no accepted credit. Literal Lean endpoint and independent novelty/significance review remain mandatory. The Lean source is an unfinished attempt, not a certified result.

## Exact source scope

Kottari–Sahni, arXiv:2508.17854v1, Conjecture 6.1 (p. 20), is the reserved statement. The source defines connectedness as `(n−1,n)`-connectedness, and a simplicial tree as connected and acyclic (Definition 5.1). Its `(m,n)` circuits alternate distinct m-faces and distinct n-facets, with the initial m-face repeated at the end. A simplicial cycle imposes additional restrictions (Definition 4.1). Thus proving absence of all `(2,3)` circuits is stronger than the required absence of `(2,3)` simplicial cycles.

The current v3 changes terminology and asks the corresponding question as Question 4.11 (p. 25), with no `(m,n)` circuits for some m, a prescribed intermediate face number and top face count. Its desired conclusion is an `(n−1,n)`-complete facet ordering. The example below also refutes that current question. All three versions were fetched with immutable, dated HTTP/hash receipts, and their relevant bodies compared. The statements were not simply assumed unchanged.

## Construction

Take the downward closure of these nine tetrahedra:

```
0123, 1234, 1235, 1356, 1456, 1457, 0147, 0467, 89AB
```

Here A = 10 and B = 11; vertices are 0 through 11. Facet indices below start at 0 in this order. Every maximal face has four vertices, so the complex is pure of dimension 3.

Its face vector is

```
(alpha_0, alpha_1, alpha_2, alpha_3) = (12, 30, 29, 9).
```

For a transparent edge count, the first eight facets have all pairs on vertices 0 through 7 except `05, 26, 27, 37`, hence 24 edges. The disjoint tetrahedron adds six. The top count is nine. Therefore, with p = 12, n = 3 and k = 1,

```
alpha_1 = 30 = (p−n) C(n,1) + C(n,2),
alpha_3 = 9 = p−n.
```

The first eight tetrahedra form one component through their common triangles, while the last tetrahedron has a disjoint vertex set. Consequently the complex is not connected in the source sense, and cannot be its simplicial tree. It cannot admit an `(n−1)`-complete facet ordering either: the first facet from the second vertex component would have empty attachment to all preceding facets from the first component.

## No `(2,3)` circuits: a direct proof

For each facet i, every triangle shared with a later facet is the following single triangle (or there are no such triangles):

| i | possible triangle shared with a later facet |
|---|---|
| 0 | 123 |
| 1 | 123 |
| 2 | 135 |
| 3 | 156 |
| 4 | 145 |
| 5 | 147 |
| 6 | 047 |
| 7 | none |
| 8 | none |

This table is obtained by intersecting each of the 36 distinct facet pairs. Suppose a `(2,3)` circuit existed, and choose its least-indexed facet. The two neighboring circuit facets have strictly larger indices, since circuit facets are distinct. Both incident circuit triangles must therefore equal the table's single possible shared triangle. That contradicts distinctness of the circuit's triangles. This excludes every circuit length, rather than only a bounded enumeration of cycles.

In particular there is no `(2,3)` simplicial cycle in v1. Choosing m = 2 meets its existential acyclicity hypothesis. The same choice meets the current v3 circuit hypothesis. Together with the counts and disconnectedness, this is a full ordinary refutation of the exact reserved record and the current source question.

## Independent verification and search provenance

`verify-simplicial.py` independently enumerates all subsets of every facet, counts faces, constructs the facet–triangle incidence graph and removes its leaves. Its components have respectively 33 vertices/32 edges and 5 vertices/4 edges. Thus it independently confirms the forest assertion and the exact f-vector. These are ordinary computations, not substitutes for a formal semantic certificate.

The initial exhaustive sweep covered all C(70,5) = 12,103,014 five-tetrahedron families on eight labelled vertices. Of these, 552,916 used all vertices and met an intermediate face count; 229,376 also had circuit-free incidence graphs. None was disconnected. The structured search then generated ridge-attached tetrahedral families with reused vertices and disjoint simplex components, using seed 369935. It completed 15,000 dimension-3/size-6 trials and found the displayed witness during the size-8 block. The exact within-block discovery trial was not logged. No minimality is claimed.

## Prior art, significance and formalization limits

Searches before computation covered the source, its versions, related titles/authors, GitHub repository searches, current Lean Pool project/candidate metadata and complete current Omega D5/Problems path listings. A subsequent witness-specific literature search found no exact counterpart. The evidence is bounded: path screens are not proof-body review, inaccessible/unindexed literature remains, and no worldwide priority is claimed. Source receipts and search outputs are retained in `sources/` and `outputs/`.

The source's printed disconnected examples have dimension 2. The current source's Figure 5 has four triangles on six vertices, satisfying the top count but missing its intermediate count. The proposed example has dimension 3, has nine tetrahedra, and meets both counts. It is not merely that printed example with labels changed. However, root must independently assess whether a short cone, gluing or vertex-identification augmentation of a printed/cited construction subsumes it. This dossier does not self-certify the campaign's significance standard.

Lean 4.34.1 was invoked under the 120-second CPU/140-second wall and -M3500 limits, with cached mathlib read-only. Initial startup required `-j1` after a thread-allocation failure. Subsequent interpreter-based attempts hit Lean's memory threshold; a kernel-reduction attempt is separately logged. The source currently formalizes finite face counts, a general least-facet circuit argument and a connectivity invariant, but is not represented as checked. No `sorry`, `admit`, new axiom, `unsafe`, `native_decide` or `ofReduceBool` is intentionally present. Error-generated `sorryAx` in failed elaboration logs does not constitute certification. No fresh extracted rebuild, leanchecker audit or literal endpoint is claimed.

Decisive next step: obtain a resource-safe kernel certificate with all source cycle/facet-index and path semantics bridges, then independent fidelity and significance review. Until then the candidate earns zero credit.
