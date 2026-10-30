# Full source question; no resolution

Haynes and Henning, *Augmenting graphs to partition their vertices into a total
dominating set and an independent dominating set*, Opuscula Math.45(2)(2025),
179–198, DOI10.7494/OpMath.2025.45.2.179. Conjecture6.1 printed p192 asks:
for EVERY finite simple graph G=(V,E), n=|V|, delta(G)>=3, can at most
floor(n/6) previously absent edges be added on the SAME vertex set so that
V=I disjoint-union S, I is independent and dominating, and S totally dominates
the augmented graph? Disconnected graphs are included. Conjecture7.4 p196
restates this as c_ti,3=1/6, using K3,3 for the lower bound. This is the full
attributed question, not a cubic-only restriction or a new parameter instance.

The actual journal PDF bytes, extracted text, dated HTTP receipt and SHA256
are saved. Definitions pp179–181, Theorems5.1/5.3 and proofs pp190–191,
Corollaries5.4–5.7, Conjecture6.1, the complete Proposition6.2 construction
and counting proof pp192–195, and final conjectures pp195–196 were read.
Rendered p192 confirms the literal inequality and degree condition.

## Exact all-scope route, with its missing step

For any isolate-free G on n>=3 vertices and any nonempty independent I with
S=V\I of size at least two, define A={v in S:N(v) intersect I is empty},
T={v in S:N(v) intersect S is empty}, a=|A|, t=|T|.
The exact cost for this fixed final independent part is

    Phi(I)=a+ceil(t/2),       ti(G)=min_I Phi(I).

Here is the ordinary justification, included only as uncredited support.
Each vertex in A needs a new S-I edge, and one such edge can repair only one
vertex of A. Every vertex of T needs an added S-S edge, which can repair at
most two members of T. These two edge types are disjoint, giving the lower
bound. Conversely connect every member of A to one fixed member of I. Pair
members of T by missing S-S edges. If one remains, join it to any other
member of S; that edge is missing because this member of T originally has no
S-neighbor. Independence of I persists. Each vertex of I already has a neighbor
in S because G is isolate-free and I is independent. Thus S is total dominating
and I dominating after exactly the stated cost. Every final TI partition has
I independent in the original graph and |S|>=2, so minimizing is exhaustive.

The full remaining gap is precisely:

    delta(G)>=3 => exists such I, |A(I)|+ceil(|T(I)|/2)<=floor(n/6).

Neither the exact formula nor finite enumeration establishes this inequality.
Its proof must allow I to be nonmaximal and control both deficit types plus
the parity of t. There is no unconditional all-scope theorem here.

A concrete exchange direction is to minimize Psi=2a+t over independent I,
with a secondary objective to navigate ties. For v in I with |I|>=2, let p_v
count vertices in S having v as their only I-neighbor, and r_v count neighbors
of v in T. Moving v to S changes Psi by exactly 2+2p_v-r_v: v becomes
undominated by I, the p_v private vertices lose domination, and r_v isolates
gain an S-neighbor. Minimum degree>=3 guarantees v has an S-neighbor.
At a deletion-local minimum r_v<=2+2p_v. If this holds for all v, summing
uses sum r_v>=3t and sum p_v<=n-|I|-t-a, giving only 5t+2a<=2n.
For |I|=1 the graph is already TI at minimum degree>=3, so this boundary
is harmless. The summed estimate is too weak to force 2a+t<=n/3, and
even that real inequality needs its integer/parity treatment. Joint exchanges,
not an unproved charging claim, are required. This route remains open.

## Exact failed routes, none a source refutation

1. Restricting to maximal independent I: K3,3 has only its two partite sets
   as maximal independent sets. They have a=0,t=3,cost2. Taking two vertices
   of one part has a=1,t=0,cost1, which equals ti(K3,3). The maximum-set
   approach of source Theorem5.1 is valid but cannot deliver the desired sharp
   bound unchanged. Theorem5.3 itself already uses a deletion repair; the
   present deficit formulation is a routine extension of that source method.
2. Monotonicity under adding edges: the crown K4,4 minus a perfect matching
   (the cube graph) is TI, but K4,4 is not TI. Both have minimum degree>=3.
   Their exact augmentation numbers are0 and1. Hence a spanning cubic TI
   subgraph does not by itself transfer a partition to a supergraph.
3. Strict one-add/delete/swap descent: two disjoint K3,3, with I one full
   part in each component, has Phi=3>12/6. Every feasible single add/delete
   or one-for-one swap has cost at least3, while the global optimum is2.
   Deleting one chosen vertex from each part reaches cost2 through a tie.
   This falsifies strict local descent, not an exchange scheme permitting ties.

checks.py verifies all three witnesses exactly. The independent literal checker
enumerates absent-edge subsets and actual TI partitions; it agrees with the
formula on all isolate-free labeled graphs n3,4,5 (4,41,768 cases) and all
delta>=3 labeled graphs n6 (1858). The source bound holds on every eligible
case. Seed122 random n7..16 accepts219 of1000 sampled graphs after filtering
delta>=3; all have cost0. These easy dense samples are weak evidence, not
a universal certification, an extremal graph census, or a discovery.

## Closest prior bodies and substantive objection

Haynes–Henning2024, Opuscula44(4),543–563, actual journal PDF: read
Propositions2.2/2.4/2.5 and proofs, Theorem4.5 and its full exchange proof,
Proposition6.5 and proof, and concluding Theorem6.6. These give TI sufficient
conditions and non-TI regular families, not a read full-degree n/6 augmentation
bridge. The entire21-page body was not semantically audited.

Dorfling–Goddard–Hattingh–Henning, *Augmenting a graph of minimum degree2 to
have two disjoint total dominating sets*, author-hosted PDF: read introduction,
definitions, Lemma2, Claim3 proof and deficit-repair expectation argument.
It pairs own-color deficits and repairs opposite-color deficits, closely related
to Phi. Its two total dominating parts do not impose independence. No direct
independence-preserving n/6 bridge is established here. The downloaded author
preprint footer is8September2006 while the original journal reference is2005;
identity with the published version is not asserted. Later portions unreviewed.

Strongest genuine routine objection: a successful proof could still be a short
adaptation of the original independent-set repair and this older two-color
deficit machinery. The exact cost formula alone certainly fails the campaign's
substantive threshold. No candidate defeats that objection. A primary published
all-degree bridge would exclude nomination even if independently rediscovered.
An exact graph with min_I Phi(I)>floor(n/6), together with its literal source
translation, would falsify the source. None was found.

Formal feasibility is conditional: finite independent sets, missing-edge
matchings and the cost identity are accessible in mathlib graph/Finset tools;
a finite counterexample could use exhaustively checked partitions. A universal
Lean endpoint still needs the unproved independent-set existence inequality,
which cannot be replaced by a certificate assumption. No Lean or paper begun.

## Reconciliation, chronology, and actual limits

Read ancestor/batch rules, ledger and prior context, NEXT, Renyi acceptance,
factorial final exclusion, r119 SUMMARY/discovery. context-reconciliation.json
extracts126 excluded/held/candidate records without copying their full bodies.
Their bounded lexical target screen identifies no same-source overlap, not a
proof that none exists. Accepted39 includes the source-distinct edge-irregulator
family; no variant of that family is proposed. r119's Beck–Sam–Woods public
refutation and repeated-chain attempt are not relabeled fresh here.

research.py streams selected all-date original/rejection/copied-review text,
hashes each body, saves a compressed hash/path mapping and scans distinct
bodies once.381959paths/276209bodies completed in116.17seconds;56hits all
retained below100limit. The permissive TI.graph regex also matches multigraph
and Riccati graph strings; all retained hits were inspected and none establishes
this source's resolution. The one single-line graph catalogue was parsed into
records and exact-target screened separately, with no target record. The
catalogue's other graph questions were not selected. Other title-search leads
were not investigated as candidates.

Exact exclusions and oversized path/size gaps are in screen-receipt.json.
r111-r113 lane bodies are entirely excluded as echoes. Other generated
inventory/matches/corpus/pathmap filenames are excluded; some copied search
JSON with other names remains as visibly identified noise. PDFs, compressed
text and unselected extensions are outside this pass. This lexical all-date
coverage is not an all-body semantic novelty clearance. No aggregate content
cache was produced; screen.sqlite contains only hash-to-first-path entries.

Registry receipts are reused, with no repeated HEAD chase: r119 observed Omega
a7769c386bd6072628a21cf4680756d2a49bf221 at22:21:24UTC and OpenAI
7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a. The d254db→a776 interval
has47/47commits and207paths, uncapped; target filename screen is not proof-body
clearance. Factorial's actual fresh-coverage reports12intervals to c3e8754b,
including the formerly300-path step expanded to379 by filecommit pagination,
and8target bodies/8hits. It is factorial-specific, not TI semantic coverage.
Renyi acceptance closes its fixed interval separately. No coverage claim here
repairs or supersedes those reviews. No full current-prior clearance is claimed.

Public search29October2026 queried exact TI-augmentation/title strings and
closest augmentation work; source publication and author bodies were retrieved.
Search absence is not literature clearance; no MathSciNet/zbMATH or exhaustive
citer audit. No source-resolution chronology is asserted: there is no own full
proof, and an unlocated public solution remains possible.

Failures preserved: initial combined context read was truncated, then relevant
records were parsed/bounded and frozen. A lookup confirmed the assigned lane
did not yet exist. A later raw read of factorial fresh-coverage echoed excessive
patch text and was truncated; bounded parsed fields subsequently establish
only the recorded structural coverage. Long excluded-record output was also
truncated; compact126-record reconciliation is saved. None counts as reading
omitted mathematics. No HTTP failure or access challenge was encountered on
the three successful source retrievals. Browser/account/network mutations,
git, shared-file writes and children were not used.

All Python and extraction helpers run beneath the unchanged assigned guard:
AS/group sampledRSS512MiB, CPU210s/wall230s, nominal40ms, BLAS1. Sampling
does not certify unsampled RSS transients. Scientific source-lock is separate
from the frozen mutable NEXT context. Final manifest is verified independently
after writing. Credit0;9additional/39total unchanged.
