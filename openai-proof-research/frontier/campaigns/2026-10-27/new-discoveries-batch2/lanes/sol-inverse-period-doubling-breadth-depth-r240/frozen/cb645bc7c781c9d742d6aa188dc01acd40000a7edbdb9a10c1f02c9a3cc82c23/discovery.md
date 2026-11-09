# r131 — isolation-game source resolution audit

Status: NO ELIGIBLE NOMINATION. No PROOF.md, Lean, paper, acceptance or credit.
Root alone adjudicates. Three precise source statements were selected after the
source-pool change below. Two remain unresolved; the third has only an excluded
routine source-known obstruction. None of the finite checks proves a universal
statement.

## Source selection and original dispositions

Before paper retrieval I searched original SUMMARY/discovery/PROOF/review/DECISION
filenames for source topics, then exact IDs/authors/titles. Parking functions and
sandpiles had original attempted dispositions (r80 and r58) and were not pursued.
The burning pool (Bonato–Jones–Marbach–Mishura–Zhang 2412.04389) had no exact
original-report hit, but its final section offers broad characterization and
design-dimension directions, not a precise conjecture suitable for this task.

The weighted-bond pool initially had no hit in those report filenames. Its
literal 2608.08692v1 Conjecture 4.13(2), however, has a full public refutation in
the original cached Omega Problems dossier and actual Lean proof bodies. The
all-date scan found these before the prepared polynomial checker was run.
I read the original dossier and the current fixed-head result/claim body:
three disjoint triangle fibers versus path fibers give A^3-B^3 with a strictly
positive quartic factor on the real line. This is the very disconnected-product
obstruction independently considered here. It is public, excluded, and not
rebranded as a connected-only target. `check.py` was prepared but NEVER RUN.
The companion 2609.15784v1 proves the nestohedron recurrence relation and the
main source already credits the earlier associahedron inequality as proved.
No novelty is claimed for either.

I then changed pools to isolation games. The exact lightweight screen of the
three IDs 2409.14180, 2507.08503, 2601.03363 and the isolation-game titles gave
no report/disposition match. A broad author token search had irrelevant hits
and was replaced by exact phrases. The complete deduplicated rescreen found
three bodies: two unrelated general-position survey bibliographies and one
old queued MathDB listing 372424. I reopened their original matching text,
retained bytes and aliases. A catalog listing is prior exposure, not an
attempted resolution; no original proof/disposition on these targets was found.

## Exact selected statements

All graphs below are finite simple undirected graphs, with n vertices. Players
alternate legal vertices, Dominator minimizing and Staller maximizing the
total number of selected vertices. D and S denote who starts, not static
minimum-cardinality isolation parameters.

T1: Henning–Rall, *Total isolation game in graphs*, 2601.03363v1, Conjecture 1.
For every graph each of whose components has at least three vertices,
the D-start total isolation game length is at most 2n/3. This includes
disconnected graphs. At selected set X, put R=V\N(X), with OPEN neighborhood.
A legal vertex has a neighbor in a nontrivial component of G[R], or a neighbor
in X that is isolated in G[R]. The second condition cannot be dropped.

T2: Bujtás–Dravec–Henning–Klavžar, *Bounds on the game isolation number and
exact values for paths and cycles*, 2507.08503v3 (latest June 10, 2026),
Conjecture 5.4: every tree T of order n>=3 has ordinary D-game length <=3n/7.
Here R=V\N[X], with CLOSED neighborhood, and a legal vertex dominates a
vertex of a nontrivial component of G[R]. Isolated residual vertices are
irrelevant. The source's Theorem 4.1 proves the weaker 5n/11 bound by a
three-stage potential/discharging strategy; that proof was read. Its constants
leave a gap (5/11-3/7)n=2n/77, which cannot be removed by integrality for all n.

T3: same source, Conjecture 5.3: for every graph of minimum degree at least two,
BOTH ordinary D- and S-game lengths are <=3n/7, with no ceiling printed.
EXCLUDED as a rounding/domain issue: C6 already has ordinary D-game value 3,
which exceeds 18/7. This exact C6 value is explicitly public in the earlier
source 2409.14180, and the companion itself gives cycle values. Its cycle proof
and the literal last-page quantifiers were read. The 288-case checker also
finds a nine-vertex minimum-degree-two graph with S-value 4>27/7; this supplies
no eligible new outcome. Do not claim it refutes the earlier CEILING 3n/7
conjecture. There is no nomination of either small-order example.

The actual journal download obtained from the DMTCS article page is retained
as journal.pdf (SHA256 3c4c969d881ae4ad7dcaf3ea6f1c09e5683bf68be16c27a521dec137dcb94a12).
Its text retains Conjectures 5.3/5.4. This is not an abstract-only reading.
The latest arXiv histories, primary HTML bodies and the earlier game's rule
and Continuation Principle are retained. No unavailable source was silently
treated as read.

## Sustained T1 argument and exact missing step

I pursued the total game rather than converting the excluded T3 correction into
a discovery. Let X be the selected set. Define the active set

U(X)={v in V\N(X): v has a neighbor in V\N(X), or v is in X}.

Then legal v are exactly those outside X with N(v) intersecting U(X).
Previously selected vertices cannot be legal because all their neighbors are
already in N(X). The graph and X therefore determine all continuations.
For player p, the exact Bellman recursion is

F_p(X)=0 if no legal vertex exists;
F_D(X)=1+min_v F_S(X union {v});
F_S(X)=1+max_v F_D(X union {v}),

with min/max over the literal legal vertices. This terminates because each
move adds one vertex to X. Induction on n-|X| proves this recursion represents
optimal play; it is a finite characterization, not a universal bound.

The source's closest proof (Theorem 1 and Theorem 4, actual proof bodies) uses
a greedy first stage, then a tail in which each move marks one vertex. At the
stage boundary after k first-stage D/S pairs, let q be the remaining active
vertices. Source structural claims make these selected, independent, and a
packing. The tail has q moves, so t=2k+q. Write the already marked count as
M=3k+e; then n=3k+e+q. The desired t<=2n/3 is EXACTLY q<=2e in this branch.
This identifies the necessary quantitative improvement to this route: charge
at least half a unit of excess marking to each late selected obligation.

The source only obtains e>=Delta-2 together with packing/neighborhood
inequalities. Those do not imply q<=2e. For example, the abstract integer
data n=10,k=2,q=3,e=1,delta=2,Delta=3 satisfy n=3k+e+q,
q<=n-t, M>=3k+Delta-2, and the source A/B/U size lower bounds
(|A|>=1, |B|>=6, |U|=3). They give t=7>20/3. These numbers are NOT a
realizable counterexample graph or game history. They falsify only the
attempt to derive the conjecture from those displayed counting inequalities.
The missing task is a new history-sensitive charging invariant or another
strategy, including odd-ended first stages. No such invariant was established.

A second obstruction is the full disconnected quantifier. One cannot sum
component D-game values or transfer the ordinary Continuation Principle to
the total game. The primary source already proves the failure of that principle
on P5: total D=2, S=4. Our exact minimax diagnostic gives
total D(2 disjoint P5)=6, whereas D(P5)+D(P5)=4; for three P5 it gives D=8,S=10.
Thus even an eventual connected-graph proof needs a response/tempo argument
that controls component switches. These computations are helper obstructions,
not a source resolution, and receive no credit.

## Checks, falsifiers and limits

`games.py` deterministically checks 12 labeled Prüfer trees and 12 cycle-plus-
random-chord graphs for each n=3..14, 288 sampled graph instances in total.
It solves both start players for ordinary, total and total-greedy games using
exact integer subset minimax. The P5 fixture is checked against (2,4).
No sampled tree violates T2 and no sampled graph violates T1; five T3
violations are four repeated C6 samples and the n9 S-example. These are not
an exhaustive graph census. Greedy tie choices are optimized, so absence of
greedy failure does not certify every tie rule. `sustain.py` separately checks
five disconnected path collections. All runs are capped by the unchanged
helper_guard, with logs retained on the final replay.

The strongest objection to T1 remains the missing q<=2e/history invariant and
component-switching control. The strongest possible falsifier would be an
exact legal-play minimax certificate with 3*F_D(empty)>2n, satisfying every
component's order>=3; none was found. For T2 it would be a tree with
7*F_D(empty)>3n; none was found. No routine source theorem currently closes
either full claim in the bodies read.

The all-date scan covers 426491 eligible aliases and 278002 SHA256-distinct
bodies, excluding generated retrieval content by filename role, not by whole
r111-r113 lanes. Their original scientific representatives are enumerated.
Four shard receipts list all omitted extensions, over-12MB files, binary
paths, error paths and role exclusions. PDF/archive bytes are not searched as
text unless extracted text is retained. No OCR of all historical binaries,
semantic equivalence oracle, hidden material, or transactional filesystem view
is claimed. The new pool rescreen reuses this exact body/alias scope.

Current default Omega HEAD observed once at 23:09:12 UTC was
e1ff281c3881e633b86be1072f049a778bdbdc1b. The fixed comparison from inherited
2108cd1 has 14 commits, 15 paths, ancestor/merge-base verified, below caps.
OpenAI remains 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a. Historical qualified
receipts are reused; the 14-commit delta is not generic semantic clearance.
No relevant isolation-game body was found in the retained lexical corpus or
new delta paths. No full fresh all-registry semantic audit, exhaustive
specialist literature search, or worldwide priority claim is made.
