# Candidate 332371: common-basis conjecture

Status: exact finite candidate; no self-acceptance. Lean verification status is recorded in SUMMARY.md and results.json. No claim to worldwide priority.

The target is Lasoń, *On the toric ideals of matroids of a fixed rank*, arXiv:1601.08199v5, Conjecture 2.5, also present in the Selecta Mathematica journal body (2021), DOI 10.1007/s00029-021-00633-6. For rank r and |E| = kr+1, if E−x and E−y partition into k bases, the conjecture asks for partitions sharing a base. The exact target appears as Conjecture 13 in v2–v3; v1 predates this formulation. All five arXiv PDFs and the journal HTML are retained, with immutable HTTP receipts. The statement permits parallel elements.

Take k = 2, r = 4, E = {0,…,8}. Represent a binary matroid by the following columns, whose four binary coordinates are read from the integers:

    9, 6, 4, 11, 6, 14, 5, 1, 12.

Let x = 1 and y = 6 (element labels, not column values). A base is any four-element subset whose columns are independent over F₂. There are 76 bases. Equivalently, define the matroid by the explicit base family in matroid-certificate.json; its nonemptiness and ordinary basis-exchange axiom suffice independently of the vector representation.

The following are disjoint-base partitions:

- E−x = {0,2,3,5} ⊔ {4,6,7,8}.
- E−y = {0,1,2,7} ⊔ {3,4,5,8}.

The complete list of bases extendible to a two-base partition of E−x has 32 members; the analogous list for E−y has 24. The lists, retained in matroid-certificate.json and logs/matroid-independent-check.log, are disjoint. Thus no partitions can share a base. A common base B would have to avoid both x and y, and both (E−x)−B and (E−y)−B would have to be bases. This is the finite obstruction tested in the proposed literal Lean theorem CommonBasis332371.counterexample, using an actual Mathlib Matroid and its rank, not a surrogate predicate.

Independent ordinary verification: scripts/matroid_certificate.py recomputes independence by all nonempty XOR combinations, checks basis exchange for every ordered base pair and every eligible element, and recomputes the two complementary-base lists. It does not use the Gaussian-elimination rank routine of the discovery script. Its full output and resource receipt are retained.

## Novelty and eligibility screen

Before numerical investment, the lane searched the target, source and citing literature, GitHub, and current raw Lean Pool candidate indexes. Additional candidate-specific searches after discovery examined exact common-basis wording, Lasoń, Seymour–White, binary matroids, and possible common-complementary-base terminology. No earlier resolution was located. This is bounded evidence, not novelty certification. The current Lean Pool head and candidate raw files, OpenAI and Omega heads and path screens, GitHub repository-search responses, and journal body have receipts. The OpenAI and Omega recursive root trees are truncated; their negative path screens are not complete semantic clearance. The OpenAI overview was also retrieved at the recorded current head.

No concrete printed obstruction or figure occurs in the inspected Lasoń source versions. This candidate was found by random binary representation sampling, not by extending a source construction, evaluating a source formula, or applying the source high-k proposition. Proposition 2.7 proves a high-k range and does not include k = 2, r = 4. Proposition 2.6 relates other conjectures but does not itself settle Conjecture 2.5. The 2016 workshop problem booklet independently states the same quantifiers. Earlier papers in the citation neighborhood, unindexed specialist results, and inaccessible/deleted proofs have not been exhaustively cleared. Independent adversarial novelty/significance review is required.

No claim is made that nine elements or rank four is minimal, that the example is new as an underlying matroid, or that it refutes White's conjectures. The source only proves a conjunction involving this conjecture implies a White conjecture; the converse must not be inferred.

## Misprint and source-ingredient check

The finite witness does not exploit a discrepancy between MathDB and the source: Conjecture 13 in arXiv v2/v3, Conjecture 2.5 in v4/v5, and the journal body retain the same deletion-partition quantifiers. There is no printed simplicity restriction or claimed numerical range contradicted by this example. Rank four is not the first parameter case. No result is claimed for a source-adjacent conjecture, and no correction to a printed construction is used. The matroid's repeated column is a pair of distinct parallel labeled elements, which is permitted in the source setting. The literal formal endpoint does not need representability: it directly constructs and checks the matroid's base axiom.

Primary references:

- [Lasoń, source and version history](https://arxiv.org/abs/1601.08199).
- [Lasoń, journal statement and proof bodies](https://link.springer.com/article/10.1007/s00029-021-00633-6).
- [2016 Order & Geometry problem booklet](https://orderandgeometry2016.tcs.uj.edu.pl/docs/OG2016-Problem-Booklet.pdf), independent restatement of this same conjecture.

The computational data prove a counterexample, not a characterization of all failing matroids or a new infinite family. The root should assess prior-art coverage and significance independently before assigning any credit.
