# Precise target and terminal disposition

UNRESOLVED. No full ordinary proof or counterexample and no eligible nomination.
This report does not award credit or change any shared record.

For every integer d>=3 and finite simple connected graph G of order n>=d+1,
assume that for every NONEMPTY S subset V(G),

    (d-2)i(G-S) < 2|S|.

The full claim is existence of a spanning tree T such that every two distinct
degree-one vertices have T-distance at least d. Distances are in the tree,
not the host graph. This is Kaneko's conjecture, explicitly printed in
Lin–You, arXiv:2411.06699v3 (January14,2025), Conjecture3.1, manuscript p3,
and the actual published companion *Spectral radius and spanning trees of
graphs with leaf distance at least four*, Filomat39:32(2025)11607–11619,
Conjecture1.2 p11608, DOI10.2298/FIL2532607L. The live abstract identifies
v3 as latest. The published paper has a narrower title and different contents;
it is not represented as a typeset identical v3. Both literal statements agree.
The original attribution is Kaneko, DAM115(2001)73–76, actual correct DOI
10.1016/S0166-218X(01)00216-5. Its full body was not obtained.

The entire conjecture, not one remaining d or graph class, is the target.
Source-known d=3, d=4, alpha<=5 and d>=n/3 cases are uncredited. Actual v3
Proposition3.3, Theorem3.4, Proposition3.5, Corollary3.6 and the proof setup
of its sufficient edge/spectral conditions were read. Published definitions,
Theorems1.1/1.3–1.10 and preliminary/proof interfaces were compared.
The 2017 Erbes–Molla–Mousley–Santana theorem is quoted in v3 with its exact
alpha<=5 hypothesis and even independent-neighborhood conditions. Its original
proof body is blocked (publisher403); the quotation is not an independent
reading of that proof. The 2007 author's host fails DNS; a distinct mirror
returns404. No unread body is asserted to settle the full claim.

# History and current public proof checks

Before downloading this source, complete original report bodies were queried
for exact IDs, title/author and claim aliases. The qualified r145 inherited
role index (r133 compressed alias index) and r146 retained original aliases
were reused; changed/new immediate batch originals were refreshed. No giant
filesystem inventory was reconstructed. The final role-filtered screen reads
1153 distinct complete bodies without a match cutoff; history-exact.json and
history-leaf.json retain aliases, changed paths, hashes and original r111–r113
science. Active r147/r148 were excluded. This is lexical report-role coverage,
not semantic clearance of every historic source file.

The strong-geodetic lead had exact original r101 dispositions: already public
prism refutation. Its complete original report was reopened, along with the
other five broad author hits. No source download or renewed attack on that
family followed. The source pool changed. The leaf-distance screen had one
hit, r102's complete report: Lihua You's unrelated clique–path saturation
conjecture. It supplies no leaf-distance attempt or rejection. These original
dispositions were read, rather than inferring freshness from a snippet.

An initial excessively broad `Ir.i.` regex matched ordinary words and generated
copies inherited in the r146 aliases. Its results and copied false positives
remain in history-geodetic.json/reopened; they are superseded, not evidence.
The corrected role/echo exclusions apply to both retained indexes, preserve
r111–r113 science, and use exact accented/unaccented author aliases. Initial
false-positive copied bodies are excluded from the scientific freeze.

Before the sustained attempt, the live primary abstract, latest statement,
published companion, current author publication page and exact public
title/Kaneko/leaf-distance/GitHub searches were checked. No source-facing full
public proof link was located in this bounded search. The author page lists
the 2017 article without a proof link. Unlike r146, no historical PR was taken
as the current proof state. Search failures/absence are not novelty evidence.

Registry revisions are fixed at Omega490f6bccbf445ab8e111a16b0b8670a5dd7c9a9c
and OpenAI7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a. Retained baseline streams
were queried without rebuilding inventories; exact current matched bodies
were read: OpenAI KMedianRecovery/Geometry/LeafDistances concerns a metric
sampling kernel, and Omega assani2025robinkaneko concerns Robin inequalities.
Their actual definitions/statements are unrelated, not public counterparts.
Both aa026->a19a and a19a->490f lists have300 paths and remain capped.
Their actual retained file/patch lists were searched and r145/r146 limited
walk receipts preserved. Neither these paths nor the unchanged baseline
establish global semantic clearance. There was no new HEAD chase.

# Sustained full-scope mathematical attempt

Put c=(d-2)/2. The hypothesis is equivalent to

    |N(A)| > c|A| for every nonempty independent set A.       (E)

This is already source Proposition3.3, not a new result. For completeness,
take S=N(A); connectedness gives S nonempty, and A is isolated in G-S,
so the source condition gives (E). Conversely let A be the isolated vertices
of G-S. It is independent and N(A) subset S. If A nonempty, (E) gives
c|A|<|S|; if empty the desired inequality follows from S nonempty.
For a maximum independent set, N(A) subset V minus A gives
alpha(G)<2n/d. Thus d>=n/3 implies alpha<=5, exactly explaining the
source-known reduction. Any genuinely unresolved source counterexample must
have d>=5, n>3d and alpha>=6. This does not prove the residual assertion.

One promising general route uses r=floor(c). Fix any independent A. Duplicate
each a in A into r left vertices, all with neighbor set N(a). For a nonempty
set X of duplicates, let A_X be its original centers. Then
|X|<=r|A_X|<|N(A_X)|, by (E). Hall's theorem yields distinct assigned neighbors
for all copies: disjoint r-stars centered on A. This supplies local material
for long pendant arms. But the assigned neighbors need not be adjacent to
one another, the stars need not span, and joining components can create new
short leaf pairs. A star is not a length-r path. No conversion theorem with
the needed all-leaf distances is established. Hall alone therefore stops
before the requested spanning-tree conclusion.

I also examined induction by removing a d-vertex path. The required expansion
condition is not inherited: K_(d+2) satisfies (E), yet deletion of any d
vertices leaves K2, which fails (E) for d>=5. This is not a counterexample
to the conjecture (the complete host has a Hamilton path); it invalidates
the naive unmodified induction premise. A useful induction would need a
boundary invariant tracking leaves and attachment distances, not just (E).

# Strongest objections and exact route obstructions

Hamiltonicity or any uniform leaf bound is too strong, even inside the
residual n>3d, alpha>=6 domain. Let t=ceil(d/2), q>=7, and form W(q,t) by
identifying one vertex z of q disjoint copies of K_(t+1). An independent set
is either {z} or picks one noncentral vertex from k different petals. In the
latter case |N(A)|=1+k(t-1)>k(d-2)/2; in the former |N(A)|=qt>(d-2)/2.
Hence the COMPLETE original hypothesis holds, by the equivalence above.
Deleting z leaves q components, so any spanning tree has at least q leaves:
each connected subtree within a petal has a vertex farthest from z, a leaf
of the entire tree. In particular no Hamilton path exists when q>2. However,
each petal has a path through all its vertices beginning at z. Their union
is a spanning tree with exactly q leaves, every leaf pair at distance2t>=d.
Thus this family confirms the conjecture and defeats only the too-strong
route. The construction is routine and receives no nomination.

A strictly improving single-edge minimum-distance potential also fails.
Start with the spanning star of K_n, n>=6. A non-tree edge joins two leaves;
its cycle has just the two corresponding spokes. Every possible exchange
removes one of those spokes. At least n-3>=3 untouched leaves remain adjacent
to the center, so minimum leaf distance stays2. The complete host satisfies
the hypothesis whenever n>=d+1, and has a suitable Hamilton path. Thus strict
one-step improvement can stall far from a solution. This does not rule out
lexicographic potentials, leaf-count reductions or multi-edge exchanges.

The missing universal step is conversion of independent-neighborhood
expansion into a spanning tree whose pendant-arm lengths and branch distances
control ALL pairs of leaves, while permitting unboundedly many leaves. No
terminating exchange rule, preserved induction boundary invariant or complete
counterexample is supplied. These gaps are mathematical, separate from the
original/2017 proof-body and registry completeness gaps.

A genuine falsifier would provide one d,G with n>=d+1, certify the strict
inequality for every nonempty deletion set (equivalently every independent
set), and certify that EVERY spanning tree has a leaf pair closer than d.
No such graph was found. A star of a complete graph or a failed matching
relaxation is not such a falsifier.

# Exact checks, failures, and limits

run-checks.sh runs under the unchanged mandated helper guard, with BLAS/OMP1,
AS/groupRSS512MiB, CPU210s, wall230s, nominal40ms. checks.py exhaustively
tests every nonempty S of W(6,3), n19, at d5 (524287 sets), all independent
sets of W(7,ceil(d/2)) for d5–10, and the six explicit trees. It verifies all
220 possible one-edge star exchanges for n6–10. This tests the obstructions,
not the full conjecture. No exhaustive graph/spanning-tree census is claimed.
Observed peak group RSS99893248 bytes, wall0.883s, exit0. Samples cannot
certify unsampled transients. No cap increase or retry of a resource failure.

Primary retrievals are October30UTC / October29 Pacific. HTTP bytes, dates,
URLs and hashes are retained. A guessed original DOI404 and a wrong Omega
repository404 were corrected using actual references; neither cleared a source.
The EMMS publisher returned403 through web and once through the direct
retrieval path; the latter was an inadvertent duplicate failed access, not a
bypass. No further attempt followed. The original Kaneko publisher403,
author-host DNS failure and mirror404 remain explicit. No abstract was used
as a read proof. No public full counterpart rejection is asserted here.

No PROOF.md is written because no full ordinary result was obtained. No Lean
or manuscript investment, children, git, shared edits, browser tabs or public
actions occurred. Scientific freeze excludes mutable NEXT and superseded
exploratory copied echoes; final manifest still authenticates all retained files.
