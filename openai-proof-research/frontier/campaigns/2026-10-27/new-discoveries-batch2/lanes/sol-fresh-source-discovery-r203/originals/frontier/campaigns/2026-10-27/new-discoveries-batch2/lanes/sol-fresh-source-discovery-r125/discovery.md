# Fresh source, full question unresolved; credit zero

Target: Boštjan Brešar, Iztok Peterin, Babak Samadi and Ismael G. Yero,
*Independent mutual-visibility coloring and related concepts*, Aequationes
Mathematicae 100, article 48 (published 18 April 2026),
DOI 10.1007/s00010-026-01280-y, arXiv 2505.04144. Conjecture 2 asks, for
every positive integer n, whether chi_IMV(S(K_n))=rho(n)+1. Here every edge
of K_n is subdivided once, rho(n) is the minimum number of K4-free classes
partitioning E(K_n), and an IMV color class must be independent and admit
an avoiding shortest path between every pair of its vertices. The whole
all-n question is the target. No bounded-n statement is nominated.

The journal HTML was retrieved as actual full text, saved and hashed.
Definitions, Theorem 2 and its entire proof, Observation 3, Conjectures 1–2,
Problems 1–3 and Proposition 26 were read. No assertion of equality of the
arXiv and journal versions is made. The harmless n=1 convention for a partition
of an empty edge set is not used to manufacture a counterexample or credit.
All nontrivial reductions below concern n>=2. No solution is claimed even
for the convention-free full n>=2 scope.

## Target-specific historical screen before substantive computation

The initial all-date pass streamed 464077 text paths, representing 284152
distinct nonbinary bodies; 179914 duplicate bodies were mapped to their
paths and not rescanned. No global match cutoff was used; each matching
body would retain at most six excerpts. Exact title, DOI and author-pattern
screening found no hit. Before mathematical checks, a second pass over the
distinct bodies added exact arXiv ID 2505.04144 and more permissive title and
author spellings. It found one author-name coincidence: a bibliography in
2026-10-14/fresh-structural-discovery-r165/private/primary/hss-v4.txt cites
Brešar and Peterin's 2007 nonrepetitive-tree-coloring paper. The original
r165 FINAL.md, REPORT.md and actual matching bibliography were read: that
lane was an incomplete hypercube-Ramsey construction, not this source or
a resolution. There are no matching prior target decisions to inherit.

This is lexical freshness, not semantic literature clearance. The compressed
hash/path mapping and SQLite hash-to-first-path table contain metadata only,
not an aggregate content inventory. No entire r111–r113 lane was excluded.
Original summaries, discoveries, proofs and reviews remain eligible. Generated
cache roles are excluded by filename and oversized-content status; the
supplement additionally rejects explicit screen-content/required-content/
supplement-content/hash-cache roles. Eleven NUL-containing texts, 66 files
larger than 12MB and 191373 unselected-extension paths are outside the initial
pass. The 66 paths are recorded individually. PDFs, archives, semantic aliases,
unselected extensions, malformed text and possible small generated caches
under opaque names remain real gaps. The initial pass is slightly noisier than
the supplemental role filter; no scientific r111–r113 blanket exclusion occurs.

## Full-scope proof route and the exact unpaid step

An IMV k-coloring of S(K_n) is equivalent to the following finite data:

* an edge coloring f:E(K_n)->[k] with no monochromatic K4;
* for each original vertex v a color c(v) absent from all incident edges.

Necessity follows from independence at each original/subdivision incidence.
If four original vertices had all six subdivision vertices colored a, take
opposite edges: every length-four geodesic between their subdivision vertices
contains another subdivision vertex of color a, contradicting visibility.

For sufficiency, color the original vertices by c and subdivision vertices
by f. Two originals of color a have the length-two path through their common
subdivision vertex, whose color is not a. For an original i and a nonincident
subdivision vertex e_jk both colored a, j and k are not colored a, and e_ij
is not a because it is incident with i. Thus i,e_ij,j,e_jk is an avoiding
length-three geodesic. Incident pairs cannot share a color. Two subdivision
vertices of color a sharing an original endpoint have an avoiding length-two
path. For two disjoint edges ij,rs of color a, K4-freeness gives a cross-edge,
say ir, whose color is not a. The originals i,r are also not a, giving the
avoiding length-four geodesic e_ij,i,e_ir,r,e_rs. These exhaust all pair types.

Consequently the source question, in its substantive n>=2 range, is equivalent
to K4 being r-admissible for EVERY integer r>=1: every locally r-colored
complete graph on R_r(K4) vertices using at most r+1 total colors contains
a monochromatic K4. 'Locally r' means each vertex sees at most r colors.
Indeed, each missing incident color supplies c. If admissibility holds, a
k-color IMV coloring would force n<R_(k-1)(K4), hence rho(n)<=k-1; combine
with the source's upper bound chi_IMV<=rho+1. Conversely failure of
r-admissibility at n=R_r(K4) gives an IMV coloring with at most r+1 colors,
while rho(n)=r+1, contradicting the asserted rho+1. The last identity uses
strict increase of diagonal Ramsey numbers (also stated in source Observation 3).
The one-color boundary is elementary. Empty unused color classes do no harm.

This equivalence is routine support, not a new theorem nomination. The exact
uniform gap is admissibility for every r, particularly r>=3. Neither the
translation nor a finite list of Ramsey bounds closes it.

Primary closest proof: Gyárfás, Lehel, Schelp and Tuza, *Ramsey Numbers for
Local Colorings*, Graphs and Combinatorics 3 (1987), 267–277, actual author-hosted
11-page PDF. Read definitions and introduction pp267–268, Proposition 6–7
and their structural discussion p271, and the complete Theorem 11 proof
pp272–273. It proves local-two-color equality for complete graphs via a
three-part palette structure and recoloring. It settles the corresponding
r=2 bridge, not a read all-r bridge. Theorem 11 uses K_m minus the edges of
K_n; n=1 supplies K_m. The paper explicitly defines Chung's r-admissibility.
Chung1983's actual body and the later Schelp1997 body were not retrieved/read;
search abstracts do not clear them. The remainder of the 1987 paper was
not audited semantically. This is a material classical-subsumption gap.

The strongest routine objection is therefore especially concrete: the entire
route is an exact translation to an old admissibility problem, and low-color
cases already follow from its classical recoloring proof. An all-r published
admissibility theorem, or a short complete adaptation of such a theorem,
would exclude a candidate under this campaign's rules. No new argument
overcomes that objection here.

## Sustained route test: a recoloring obstruction, not a counterexample

A tempting uniform route is to merge one pair of the k colors globally,
retaining K4-freeness. That route fails even with one missing color per vertex.
Take three blocks of four vertices. All cross-block edges have color 0.
The internal palettes are {1,2}, {1,3}, {2,3}, respectively; in each block
give its first edge the smaller palette color and its other five edges the
larger color. This four-coloring is locally three-colored and K4-free.
A nonzero-color K4 would have to lie within one block, where both colors
occur. A color-0 K4 would need four distinct blocks, but there are only three.

Merging any two nonzero colors makes their palette block monochromatic K4.
Merging 0 with a nonzero color a creates a K4 using a color-a internal edge
and one vertex from each other block. Thus NONE of the six pair-merges works.
This does not prohibit more sophisticated recoloring or refute admissibility:
there are only 12 vertices, below R_3(K4), and Theorem 2 already supplies a
different three-color IMV coloring here since rho(12)=2. No source counterexample
or new credited statement arises.

The runnable checker independently builds the literal subdivision graph and
checks properness and shortest-path visibility by BFS. It agrees with the
edge/missing-color criterion for 92913 complete assignments: n2,3,4,5 with
two colors and n4 with three colors. It additionally checks the 12-vertex
construction literally and lists a K4 witness for each of six merges.
These are finite consistency tests and a method obstruction only.

Falsifier for the source: for some r, an explicit K4-free locally r coloring
of K_(R_r(K4)) using r+1 total colors, with certified Ramsey threshold (or an
equivalent certified lower bound rho(n)>=k), plus the literal translation.
None was found. Formal feasibility: finite paths, palette conditions and
the equivalence are accessible through graph/Finset encodings. The all-r
admissibility premise is unproved and cannot be an assumed Lean bridge.
No PROOF.md, Lean work or paper was created.

## Other lead, chronology and registry limits

Same-source Conjecture 1 is excluded from new investment: Babu, Di Stefano,
Lakshmanan, arXiv2512.12251v2, Theorem2.3, publicly supplies the NP-completeness
result. Its actual full theorem and both directions of the NAE3-SAT reduction
were read, with graph construction and color-pair logic; prerequisite Lemma2.2
was not independently audited. This suffices to avoid claiming a new proof,
not to certify the external result independently. Its initial submission is
December2025, preceding the journal source's April2026 publication; the source
preprint itself is May2025. Do not conflate source-publication and resolution
chronology. Other search leads (game visibility, geometric polygons, Hamming
Problem3) were not advanced as full candidates.

Inherited registry receipts retain their actual scope: Rényi's fixed
0d4→d254 interval has 9 steps/28 commits/538 paths; factorial final review
reaches c3e8754; r119 observed a7769c3 at22:21:24UTC with uncapped
d254→a776 47 commits/207 paths but no all-body semantic clearance.
One new observation at22:41:53UTC records Omega9a026fe5527cacf8d3aed5f9291f08bc520ea90b;
the fixed a776→9a026 comparison returns43/43 commits and23 paths, below the
300-path cap, with base ancestry confirmed. A permissive patch screen yields
one 'admission' false positive. Its actual complete immutable problem body
was fetched and read: Hanna's triangular-EGF mod-three congruence, unrelated.
OpenAI remains7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a at22:41:54UTC.
No moving HEAD chase, full-history semantic clearance, or worldwide priority
claim. Searches for exact source/conjecture and local Ramsey terminology found
no full resolution used here; citation databases and all live registry bodies
were not exhausted. No novelty PASS is assigned.

All output is lane-local. NEXT is frozen separately as mutable context; source
bytes have a separate scientific lock. Python, extraction and diagnostics use
the unchanged assigned helper guard, AS and sampled process-group RSS512MiB,
CPU210s, wall230s, nominal40ms, BLAS1. Unsampled transients are not certified.
Early oversized combined reads were truncated; later bounded/parsed reads
recover the relevant context, not omitted mathematics. The first extractor
failed because bs4 was absent and was replaced by a standard-library parser;
no package was installed. No HTTP challenge/failure occurred. No shared,
count, git, browser, account, upload or public-message action was taken.
Credit0; counts9additional/39total unchanged.
