# Candidate: MathDB 346167

This is an internal candidate, with zero accepted credit unless root accepts it.

The exact source is Li–Weng, arXiv:2004.06285, Conjecture 6.12, page 18:
for connected G and its complement, of common order n ≥ 8, their rainbow
vertex-disconnection numbers have sum at least n. The current arXiv PDF was
downloaded on 2026-11-04 UTC; exact bytes and SHA-256 are in sources/receipts.jsonl.
The conjecture follows the proof of Theorem 6.11, whose n ≥ 24 hypotheses are
different. The conjecture itself explicitly starts at n = 8.

Use vertices 0,...,7. The adjacency masks of G are
202, 225, 232, 149, 232, 22, 23, 31.
Bit j of mask i says that i and j are adjacent. The masks of its complement are
52, 28, 19, 98, 7, 201, 168, 96.

Both are simple undirected connected graphs. In G every vertex is within
distance two of 0: 1,3,6,7 are neighbors, and 2,4,5 are reached through
3,3,1 respectively. In the complement, 2,4,5 are neighbors of 0, and 1,3,6,7
are reached through 2,5,5,5 respectively.

Color G with the vector (0,1,2,2,3,0,3,1) and its complement with
(0,1,0,1,2,0,2,0). These use four and three colors, respectively.
These colorings are not required to be proper; neither the primary definition
nor the conjecture imposes properness.

For every ordered pair x ≠ y, outputs/rainbow-certificate.json supplies two
masks S and A. Each row has the following easily checked properties:

* x and y are outside S; x is in A and y is outside A.
* The colors on S are distinct.
* If xy is an edge, at least one of the colors of x and y is absent from S.
* Every edge from A to its complement, after deleting xy, has an endpoint in S.

The last property rules out any path from x to y after deleting S and xy:
a path starting in A cannot leave A. If xy is absent, deleting it changes
nothing. Thus S is exactly a rainbow vertex cut in the source definition;
in the adjacent case S together with x or with y is rainbow.

The JSON contains all 112 ordered pair certificates. The search program
checks separation by reachable-set expansion. A separately written verifier
uses Floyd–Warshall and verifies all 112 cuts independently. More decisively,
the Lean packet verifies the displayed finite cut and side tables by kernel
decide and proves the path argument for arbitrary graphs and arbitrary walks.

Therefore rvd(G) ≤ 4 and rvd(complement G) ≤ 3, so the sum is at most 7 < 8.
This disproves the source's literal Conjecture 6.12 and MathDB 346167.
No equality claim for the two individual invariants is necessary.

## Formal semantics

Base.lean defines a simple graph on Fin 8 and the graph cutGraph H S x y.
Its adjacency is explicitly H.Adj u v, with both endpoints outside S,
and with the unordered pair xy removed. Deleted vertices are isolated.
Because x,y are outside S, reachability between them in this graph is precisely
reachability after vertex deletion: walks cannot visit an isolated deleted
vertex. This is the conventional vertex-cut interpretation, expressed directly
as adjacency restrictions rather than a search surrogate.

CutCert is only an intermediate certificate. cert_sound proves its implication
for arbitrary mathlib SimpleGraph.Walk values, without a bound on walk length.
SourceValid uses the source's rainbow condition on S ∪ {x} or S ∪ {y}.
Semantics.lean proves its equivalence with the color-inequality version used
by the certificate checker, proves sourceRvd = rvd, and proves that rvd is
the least admissible number whenever an admissible coloring exists.
The endpoint Rainbow.mathdb_346167_literal negates the conjecture quantified
over every natural order and every simple graph on Fin n. It uses actual
mathlib connectivity and unbounded graph reachability, not a bounded BFS
diagnostic.

## Novelty and significance limits

The object is a deliberately searched irregular 8-vertex graph; neither it
nor its complement is one of the standard Petersen, complete multipartite,
circulant, nut, or Latin-square examples. Its degree sequences are
(3,4,4,4,4,4,4,5) and (2,3,3,3,3,3,3,4). There are no isolated or pendant
vertices, and neither graph is a tree. The source's tree-complement lemma
does not apply. The positive n ≥ 24 theorem is not being corrected.

The source introduction, preliminary definitions, Section 6 theorem and proof
bodies, and neighboring statements were inspected. There is no printed
counterexample with these parameters. The 2018 introductory paper,
Weng's 2023/2024 minor-free and complexity paper, and the 2025 AIMS bounds
paper were also inspected for explicit examples, product constructions,
and generic upper bounds. The latter's K(2,a) with pendant edges construction
has a different structure. The 2023 Δ upper bound for K4-minor-free graphs
does not give this candidate's G upper bound: G has 16 edges, greater than
2*8-3, so it is not K4-minor-free. The result is a modest finite refutation,
not a full determination of the correct universal lower bound.

Current public registry heads and complete D5, Problems, and OpenAI preprints
trees are retained in sources. Initial recursive root trees were truncated;
the relevant subtrees were subsequently fetched separately and are not
truncated. This is a bounded path screen, not a proof-body audit of every
registry item. No matching target path was found. Web searches for the exact
parameter, source conjecture, counterexamples, theses, and 2026 developments
found no preexisting refutation; this is not a guarantee of global novelty.
The published journal version of the source and a 2024 Springer paper were
not fetched through the web connector (non-retryable access failures);
the corresponding current arXiv bodies were read. Root must adjudicate
whether these bounded checks suffice or require further review.
