# I165 primary comparison and retrieval limits

Date: 2026-10-10. Searches used the provided WebSearch service. This is a
human-readable query/result log, not a claim to preserve raw provider responses.
Search snippets do not establish the contents of an unread theorem.

## Early searches, before implementing enumeration

Queries:

- `"bipartite planar" "Hamiltonian cycles" "n/2"`
- `"Hamiltonian" "square expansion" number cycles`
- `"Hamiltonian cycles" "affine" "bipartite" dimension`
- `Barnette graphs minimum number Hamiltonian cycles linear bound prisms`
- `"Hamiltonian cycle polytope" "dimension" "cubic"`
- `"Hamiltonian cycles" "span" "bipartite planar"`

The relevant primary leads were:

1. Björklund--Kaski--Nederlof, *Another Hamiltonian Cycle in Bipartite
   Pfaffian Graphs*, arXiv:2308.01574v2 and ICALP 2024,
   https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2024.26 .
   The actual locally held primary text was read at lines 80-324.
   Corollaries 4-5 give four cycles through an edge when present and six
   total when Hamiltonian, not a sharp order-dependent bound.
   Lines 161-179 explicitly limit the reach of repeated switching.
2. Gorsky--Steiner--Wiederrecht, *Matching Theory and Barnette's Conjecture*,
   https://arxiv.org/abs/2202.11641v3 .
   Actual primary text lines 288-1097 was read, not just a search summary.
   Theorem 5.1 and the preceding precise expansion contract support
   structural generation; the text does not supply counting monotonicity.
3. Holton--Manvel--McKay, JCT B 38 (1985), 279-297.
   The already owned author-hosted primary PDF was read visually on the
   eight pages recorded in reading-ranges.json. Theorem 4 on printed
   page 294 supplies the original R0/R4 generation theorem. The table on
   page 295 counts graphs, not Hamiltonian cycles. The empty extracted
   text was not used to infer its contents.

Other returned leads included *Approximating Barnette's Conjecture*
(GD 2025), *Barnette Graphs with Faces up to Size 8 are Hamiltonian*
(arXiv:2508.03531), *Hamiltonian cycles in planar cubic graphs with facial
2-factors* (JGT 2021), and Chia--Ong, *Hamilton Cycles in Cubic Graphs*
(2007). Only their returned snippets were examined. They supply no
theorem premise or exact-duplicate verdict here. Search results about
Hamiltonicity of prisms over arbitrary graphs do not count Hamiltonian
cycles in the even cycle prisms under study.

## Renewed comparison after finding the counterexample

Queries:

- `"C4-expansion" "Hamiltonian" cycles number`
- `"Barnette" "number of Hamiltonian cycles" linear`
- `"Hamiltonian" "splice" "affine"`
- `"Hamiltonian cycles" "square" "decrease" cubic bipartite`
- `"Hamiltonian cycles" "n/2+2"`
- `"Hamiltonian cycles" "linear lower bound" "bipartite"`
- `"Barnette" "multiplicity" Hamiltonian`
- `"Hamiltonian cycles" "affine hull" cubic bipartite planar`
- `"Matching theory and Barnette" "expansion" Hamiltonian`

No returned primary theorem was verified to assert Q164, all-step (M), the
specific 50-to-54-vertex counterexample, or the all-graphs affine-span
criterion. This is NOT proof of absence, novelty, or worldwide priority.
Most exact-keyword searches were low-quality/noisy. The renewed GSW search
returned its arXiv HTML and journal landing page; its locally held full
text, rather than the landing-page snippet, provides the operative
comparison.

The search result for an MPI lecture handout displayed `403 Forbidden`.
That is blocked retrieval, not a negative theorem search. No new primary
PDF was downloaded. Existing GSW, HMM and BKN primary copies were available
and were actually read in the stated ranges. The 2007 article and the
2025 leads were NOT retrieved in full. No MathDB ranking or priority
metadata was verified. Bibliographic dates supplied by search engines,
including the displayed web date of the 1985 HMM article, are not treated
as publication evidence.

## Contribution comparison

The new negative result has a complete reduction to one finite exact
32-vertex port-count table, the standard splice product formula, and
the classical prism traversal counts. It is a focused refutation of an
unpaid proof strategy, not a proposed substantial positive finding.
The short-side injection is deletion/addition of one forced edge.
The affine splice formula is a complete elementary fibre-product rank
calculation. These narrow contributions may be called technical; Q164
itself cannot, because no full-scope reduction proving it was obtained.
