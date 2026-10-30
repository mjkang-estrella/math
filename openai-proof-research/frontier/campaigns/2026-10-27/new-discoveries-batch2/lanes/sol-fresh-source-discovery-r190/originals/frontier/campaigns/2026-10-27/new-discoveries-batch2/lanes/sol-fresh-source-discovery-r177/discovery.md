# Scientific record and precise outstanding gap

## Selection and historical gate

Read ancestor/batch AGENTS, ledger, prior-campaign context and NEXT; copies
are administrative snapshots, not assertions that live files are immutable.
history-receipt.json unions r170/r172/r173/r174 qualified ORIGINAL records,
rehashes their bytes and refreshes immediate original SUMMARY/discovery/PROOF/
review/DECISION documents. It retains all 1,755 records, including original
r111/r112/r113 coverage 5/2/2, with eleven changed/new entries and no missing
inherited paths. No scientific record is dropped due to age or lane number.
inherited-history-qualification.json preserves older counterpart/provenance
exclusions. No new echo exclusions are asserted. Differently named historical
notes and arbitrary semantic aliases are not exhaustively covered.

Initial public discovery queries suggested the W2 expansion theorem, but the
early exact screen found r68/r85/r121 and the actual-public-proof exclusion.
It was not reopened or fetched. Likewise the Bastien–Khormali tournament
lead was rejected by r159 before source investment. These are lead rejections,
not freshly investigated statements. A published mutual d-visibility body was
read in full relevant introductory/concluding sections: its §7 asks broad
characterizations and investigations, not a selected precise universal bound.
No instance or tautological characterization is nominated from that source.
Only one exact statement was selected for sustained mathematical work here.

The preinvestment irregular-screen and exact-screen cover DOI, arXiv, title,
all five authors, irregularising/irregularizing and 3m/walk aliases. The author
Bensmail hits concern the already credited edge-DELETION problem, not the
walk-multiplicity problem. The full edge-deletion family is not reopened.
The present target is retained as an unresolved, distinct-operation question,
not declared eligible for new family credit. Registry path hits are ordinary
regularization paths or coincidental SHA substrings, not matching theorem
bodies; their absence cannot establish novelty. No fresh current GitHub head
claim is made: denied API/raw/codeload/patch routes and missing historical
merge trees/capped intervals are PARKED. Current public searches returned the
original source and bibliographic records, no exact counterpart located, but
this bounded search is not worldwide priority clearance.

## Primary scope and versions

Source: Julien Bensmail, Romain Bourneuf, Paul Colinot, Samuel Humeau,
Timothée Martinod, arXiv:2506.21254, live abs lists only v1, submitted
26 June 2025. Downloaded PDF is the 30-page v1 body. Source author pages
independently identify TCS1067(2026)115773 and DOI10.1016/j.tcs.2026.115773.
They point to the publisher DOI, not a separate full published copy. The
ScienceDirect route is already denied and was not retried. The actual
published Conjecture number/scope is therefore NOT authenticated here.
All theorem references below are explicitly to arXiv v1, not silently to VoR.

Source §2 conventions: finite simple connected graphs without the isolated
edge obstruction (in connected nontrivial scope, G != K2). Walks may repeat
vertices/edges and can be empty or closed. G+W adds one parallel copy for
each traversal of an edge. Local irregularity requires distinct degrees only
at adjacent vertices. ML^W(G) minimizes number of traversals, not distinct
edges, not vertex count, and not total edges of G+W. Conjecture7.1 p28 asks
ML^W(G)<=3m for every such G, with no additive constant or asymptotic escape.
The isolated vertex, if allowed by the conventions, is immediate with empty
walk and does not change the gap.

Actual source proof bodies read: Theorem4.1's guiding closed walk and last-two-
vertices half-turn repair; Corollary4.2; Theorem4.3's scaled-weighting conversion;
Proposition4.4's walk rearrangement; Theorem4.5 and Corollary4.6; §6.3 tree
dynamic-programming proof discussion; §7's 3m conjecture and subdivided-star
motivation. This is substantially more than an abstract-based selection.

Closest classical primary obtained: Ralph Keusch, arXiv:2303.02611v4,
6 January2024 (PDF title-page date9January2024), *A Solution to the 1-2-3
Conjecture*, published JCTB166(2024)183–202,
DOI10.1016/j.jctb.2024.01.002. Read Theorem1, main-strategy discussion and
the main proof body pp11–14, including the good R-B partition cases and
cycle-weight adjustment immediately before Lemma10. The conclusion controls
weights in {1,2,3} and neighbor sums. It does not assert that excess edge
copies form one Euler trail. No full classical bridge or exclusion of the
walk conjecture follows merely from that theorem. Auxiliary proof bodies in
Keusch are not independently audited in their entirety here; the theorem is
used only to explain the proposed conversion, not as a new certified proof.
The minimum-label-sum companion Algorithmica84(2022)1030–1063,
DOI10.1007/s00453-021-00903-x, was identified late in search; its full journal
body has NOT been obtained/read. The accessible 2020 PMC conference search
representation has omitted mathematical formulas and is not body clearance.
This is an additional material companion qualification, not an exclusion.

Chronology: sourcev1 June2025 and Keuschv4 January2024 predate this lane's
actual UTC30October2026 acquisitions. No later independent counterpart was
located, and no chronology is inferred from search crawl dates. Exact UTC,
URLs, final URLs, bytes and hashes appear in http.jsonl/primary-hashes.json.

## Exact multiplicity formulation — complete classical equivalence

For each e in E let x_e be a nonnegative integer and put
a_v=sum_{e incident v} x_e. Define H_x as the multigraph having x_e copies
of e, omitting vertices of degree zero. A nonempty walk has these traversal
multiplicities iff H_x is connected and exactly zero or two a_v are odd.
Necessity: the traversed support is connected; all visits contribute pairs
of incidences except the two distinct endpoints, which contribute one each.
Sufficiency: if all degrees are even, the ordinary Euler circuit construction
splices unused-edge circuits until all edges are used; connectedness ensures
an unused edge touches a circuit already built unless none remains. With
two odd vertices s,t, insert a new edge st, use the even case, then cut the
circuit at the inserted edge. Removing it yields an Euler s-t trail. Mapping
parallel copies back to G gives the desired walk. Length equals sum_e x_e.
The all-zero assignment is allowed separately, and works exactly when G is
already locally irregular.

Hence the PRECISE UNIVERSAL GAP is to produce, for every source graph G,
either zero counts with G locally irregular, or integer x>=0 satisfying ALL:
(i) connected positive support; (ii) zero or two odd a_v;
(iii) sum x_e<=3|E|; (iv) d_G(u)+a_u != d_G(v)+a_v for EVERY uv in E,
including edges unused by the walk. Conditions (i)–(iv) are jointly necessary
and sufficient. This is a reformulation, not a resolution or a new theorem.

## Sustained routes, bridges and obstructions

1. Source guiding-walk route. Source Theorem4.1 gives p+2m from a spanning
closed walk of length p. Doubling a spanning tree gives p=2(n-1), hence
2m+2(n-1). If m>=2(n-1), this is <=3m. For an Eulerian connected graph,
an Euler tour has p=m, also giving3m. Hamiltonian graphs permit p=n<=m.
Every implication just stated is a complete classical/source adaptation and
receives zero credit. General sparse graphs, notably trees with long arms,
do not satisfy these sufficient inequalities. The missing step is a global
bound on extra half-turns compensated by the required guiding traversal;
the source's per-edge charge only yields4m. We have not supplied that bound.

2. Direct classical-weighting conversion fails. From a proper weighting w,
putting x=w-1 preserves the desired neighbor sums and costs at most2m, but
does not impose Euler feasibility. On P4 with edge weights(2,1,3), weighted
vertex degrees are(2,3,4,3), so the weighting is proper. Positive x support
consists of two disconnected edges. On K1,3 with every edge weight2,
weighted degrees are(6,2,2,2), proper, but x has four odd vertices. Neither
x is the multiplicity vector of one walk. These examples refute only the
proposed automatic conversion, not the conjecture. Even connected support
alone is insufficient. Source Theorem4.3's scaling repairs properness while
paying a maximum-degree factor, so does not meet3m in full scope.

3. Closed spanning tree ansatz. Set x_e=2+2*1_F(e). Every edge is used,
all degrees are even, and its cost is2m+2|F|. Thus finding |F|<=m/2 with
3d(u)+2d_F(u) unequal across EVERY edge would suffice for trees. The exact
Prüfer check finds such F for all18,247 labeled trees of orders3..7. There
is no all-tree proof of this assertion here. Further, the same ansatz cannot
prove the full graph claim: on a triangle, every original degree is2, so
proper sums would require the three edge counts pairwise different; two
allowed counts cannot do that. The triangle nevertheless has a length2
irregularising path, so the ansatz failure is not a source counterexample.

A complete uncredited special-class bridge illustrates what is missing at
branching vertices. Let a spider have k>=3 arms of arbitrary positive
lengths n_i. On each arm, from center to leaf, repeat counts2,2,4,4.
Each four-edge block costs12; its prefixes cost2,4,8, respectively, all
<=3 times their lengths. Every count is positive and even, so an Euler
circuit exists and length<=3m. Adjacent interior degree2 vertices differ
because x_j != x_{j+2}. A leaf has odd final degree1+x_last whereas its
degree2 neighbor has even degree. The center has degree k+2k=3k>=9;
each neighbor has degree3 on a length1 arm and degree6 on a longer arm.
Thus all center edges distinguish too. This proves the full3m bound for
all such spiders, but is a direct periodic-path/source-inspired class
adaptation, NOT the universal source resolution and NOT a nominee. With
multiple branching vertices, the final degree at both ends of a connecting
arm depends on independently chosen phases; this argument does not jointly
control those constraints. No general phase-selection lemma is proved.

## Exact checks, objections and disposition

checks.py uses pure integer BFS on states(current vertex, added-degree
vector), seeded by all starts. Each transition traverses one graph edge.
States with the same pair have identical futures and validity conditions,
so merging them is sound. First valid layer is the exact minimum. Source4m
gives a finite cutoff; every tested case finishes earlier. All770 connected
labeled graphs of orders3,4,5 (counts4,38,728) pass; maximum minimum/m=1.
Stored witnesses are independently checked for degrees, cost, connected
support and odd-degree counts. This is SMALL finite evidence, not evidence
for worst-case asymptotics. tree_route.py enumerates all Prüfer sequences
for3..7, counts3,16,125,1296,16807, and all restricted F of allowed sizes
until a witness is found. Its outputs certify only that restricted finite
search, not shortest walks or all trees. No floats enter either search;
the displayed maximum ratio is merely a report statistic.

Strongest objections: universal existence (i)–(iv) is open in this lane;
positive closed ansatz fails even K3; finite small instances do not control
source star asymptotics; published/latest body and material label-sum journal
body are not authenticated; bounded history/registry coverage is not global
priority clearance; same broad irregularity vocabulary does not itself
certify distinct credited-family eligibility. Consequently ZERO eligible
complete results, no PROOF.md, no Lean or manuscript. Do not invest merely
to extend finite checks. Reopen only with a decisive universal lemma or a
fully certified counterexample and concrete source-body access route.
