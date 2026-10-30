# Independent ordinary-math and eligibility review

Review target: `sol-fresh-source-discovery-r108`, root-designated commit
`e8c894f905`, frozen by `root-fresh-source-r108-r109-handbacks/r108-freeze.json`.
I verified all 61 listed original paths against that manifest before copying
them into `inputs/r108/`; the review and checker use this private byte copy.
The final original/copy recheck is in `after-hashes.json`. The commit designation
is supplied provenance, not a separately performed git-object audit.

**Recommendation: source PASS; ordinary math PASS; substantive eligibility FAIL
(routine same-object source adaptation); novelty HOLD. Credit 0; unchanged
8 additional / 38 total. Root alone decides acceptance.** FAIL here is a
campaign eligibility judgment, not a claim that the source question remains
unanswered or that a prior author already printed this representative.

## Source and literal scope

I read the copied PROOF, SUMMARY, discovery and provenance; actual primary
`sources/covers.raw.txt`, and relevant original HTML bodies. HTML anchors
`S5.Thmtheorem24` and `S7.p9` contain the tree formula and uniform question.
The precise source is [Blitvić–Kammoun–Steingrímsson, arXiv:2610.29846v1](https://arxiv.org/html/2610.29846v1),
Definitions 2.2/2.6, Remark 2.7, Lemma 5.1/Theorem 5.3,
Propositions 5.24–5.28, and Section 7 items 5–8.
The saved text locators are lines 632–675, 2250–2310, 3421–3558,
4211 onward, and 4274 onward (line numbers refer to the private copy).

Item 6 really asks for representatives at every integer m>2 and K>2m,
in the class with counts (2j−1)!! for every j>=1. This is not a claim
about exactly j total occurrences: prescribed starts are 1+t(K−m),
0<=t<j, and additional occurrences are explicitly permitted. The
pattern is chosen from m,K alone, uniformly in j. The candidate answers
this full explicit representative question. The following speculative
remarks about other shifted factorials and Catalan-preserving operations
are not thereby all resolved. Neither item 5's full separator classification
nor item 8's all-pattern cutoff question is proved or credited.

## Independent mathematical audit

Write r=K−2m−1>=0 and d=K−m=m+r+1. The candidate word is

    (1,...,m−1, K−1, m+1,...,K−m−1, K, m, K−m,...,K−2).

Its displayed blocks partition [K]. In particular the small middle
interval has exactly r letters, followed by K; there are m suffix
letters, namely m followed by K−m through K−2. Both boundary blocks
are increasing and hence overlap compatibly.

To make the identifications explicit, use zero-based occurrence t, 0<=t<j,
and positions td through td+K−1. Define P[t,a]=td+a for
0<=a<m−1 and H[t]=td+m−1, also for t=j.
Define M[t,b]=td+m+b, 0<=b<r, and Z[t]=td+m+r.
The suffix positions are exactly (t+1)d through (t+1)d+m−1,
so their names are P[t+1,0],...,P[t+1,m−2],H[t+1].
Since d>m, nonadjacent occurrence windows do not intersect. These
are all identifications; no middle or leaf is shared. Their union has

    (j+1)(m−1)+jr+(j+1)+j = m+jd = K+(j−1)d

positions and is exactly the source position interval.

Sorting one occurrence by its literal values gives exactly

    P[t,0]<...<P[t,m−2]<P[t+1,0]
      <M[t,0]<...<M[t,r−1]
      <P[t+1,1]<...<P[t+1,m−2]<H[t+1]<H[t]<Z[t].

Empty M is omitted. This confirms the candidate order (1), with
one-based names there. In particular m=3 still leaves P[t+1,1];
there is no missing boundary element. For r=0, K=2m+1, the
interval between P[t+1,0] and P[t+1,1] is empty and no argument
requires a middle vertex. The smallest pattern is 1267345 at m=3,K=7;
m=3,K=8 gives 12748356.

For completeness both closure inclusions hold symbolically. Form C
from P[0,*], then for t=0,...,j−1 append P[t+1,0], M[t,*],
P[t+1,1],...,P[t+1,m−2]. Every edge between consecutive elements
of C appears in one of the sorted occurrence chains, including the
joins from the last P of one block to the first P of the next.
The edge from the last C vertex to H[j] appears in the last occurrence.
Every H[t+1]<H[t] and H[t]<Z[t] also appears there. Thus every
comb-model edge is in the source closure. Conversely every consecutive
comparison in each sorted occurrence chain is either an edge of C,
an H-spine/leaf edge, or follows by going up C to H[j] and then up
the H spine. Thus every source edge is in the model closure.
This proves equality, acyclicity and the absence of hidden comparisons.
All vertices of C precede all H and Z vertices; deleting C preserves
the extension count exactly, with no multinomial factor.

After deleting C, the residual tree is H[j]<H[j−1]<...<H[0]
with H[t]<Z[t] for t<j. At j=1 this is a three-vertex chain,
so the count is 1, as also follows directly from a single pattern window.
For j>=2 the first two residual vertices must be H[j],H[j−1].
The remaining old comb, after its own forced minimum is removed, has
2j−2 vertices and e_(j−1) extensions. Z[j−1] is unconstrained
relative to these vertices. Inserting it in any of their 2j−1 gaps,
all after the two forced minima, is a bijection. Consequently
e_j=(2j−1)e_(j−1), proving (2j−1)!! for arbitrary admitted parameters.
Assigning ranks in linear-extension order gives a source permutation;
sorting a source permutation's positions by ranks gives the inverse.
There is no quotient or extra-occurrence exclusion.

## Different exact checker

`checker.py` imports no candidate code. It builds every strict pairwise
comparison in each literal window, computes reachability by graph search,
and compares that relation with the proposed model in both directions.
It also checks the position partition and global comparability of C.
144 cases cover m=3..8, r in {0,1,2,5}, and j in {1,2,3,5,8,12}.

For the independent counts it identifies universally comparable vertices
from the literal relation, whose ranks are forced by their predecessor
counts. It exhausts every permutation of the remaining vertices and
rejects against all literal comparisons. This uses neither ideal-state
recursion nor a hook formula nor the comb insertion count. Twenty cases
cover (m,r)=(3,0),(3,1),(4,0),(5,3), j=1..5; counts are
1,3,15,105,945 in each family. At most 9!=362880 residual permutations
are tried per case. `checker-results.json`, `checker.log`, and
`checker.guard.json` preserve the exact successful run. Guard exit 0,
sampled peak group RSS 16,965,632 bytes, wall 5.45 seconds. Finite checks
are diagnostics; the symbolic audit above supports the universal assertion.

## Substantive eligibility, at full strength

The strongest case for admission is real: the authors explicitly ask
for these representatives, and Proposition 5.24 is conditional on having
a tree pattern. A generic counting formula alone does not existentially
produce the pattern. The candidate supplies a new explicit witness family
and verifies the entire source quantifier range. Its shortness and use
of classical counting do not alone justify rejection. Nor does absence
of a new counting theorem decide whether a construction is substantive.

Nevertheless I recommend exclusion under this campaign's express ban
on routine source adaptations. The remaining realization is the elementary
unit-leaf version of the source's own core/branch model. Its backwards
H spine supplies the branching; every other overlap/interior position
is placed into an initial globally comparable chain. This is direct
design inside the source's objects, with no additional structural
classification or difficult compatibility mechanism. More concretely,
all (m,r) collapse to the same residual comb as the seed (3,0).
Increasing r by one only inserts j vertices into C. Increasing m by
one at fixed r only inserts j+1 vertices into C. The full parameter
range is thus achieved entirely by count-neutral chain padding.
The local occurrence order displayed above verifies these two padding
operations as well as their uniform overlap compatibility.

This is precisely the kind of neutral head/tail and globally comparable
element modification the source itself singles out. Section 7 item 7
explicitly says these elements do not affect extension counts;
the discussion following Proposition 5.37 supplies an actual Catalan
head/tail-padding example; the paragraph preceding Proposition 5.28
likewise separates globally comparable new letters from the counting
part. Proposition 5.24 then applies literally: 1 is in the prefix,
the undirected Hasse diagram is a tree, every genuine branch is a
unit leaf, and at attachment H[t] the vertices above it excluding its
leaf number 2t (zero-based t). Its factor is binomial(2t+1,1)=2t+1.
For the top attachment the factor 1 can equivalently be absorbed into
the terminal core. No new tree formula is being asserted.

This is not a claim of formal theorem subsumption of the existential
endpoint by Proposition 5.24 alone, and I found no old printed occurrence
of this exact word. It is a substantive-work judgment about the small
realization step remaining after that actual source body and its neutral
padding remarks. The source being open does not override the campaign's
routine-adaptation exclusion.

I read the current ledger and prior-campaign context, and the actual
acceptance decisions for outcomes 31 (arcsinh) and 32 (Gamma levels).
They expressly permit short classical proofs of full source questions;
the Gamma decision also says routine reductions need not use identical
objects to be excluded. Thus neither 'elementary' nor 'full open question'
is a sufficient criterion. Those decisions credit a source-specific
identity/normalization and strictness assembly. Here the entire
nontrivial extension structure is already the source's counted tree,
and both new parameters change only the neutral chain. I judge this
closer to the banned source-adaptation category. This is my independent
recommendation, not a deduction from the worker's self-exclusion or a
binding precedent for root. If root gives the compatible realization
itself greater substantive weight, the math audit supplies no obstacle
to a different eligibility decision.

## Bounded prior investigation and honest limits

I read the actual FPSAC 2023 precursor body, pp5–9, including Theorem 2's
recurrence proof, its prescribed-occurrence convention, and Propositions
1–4. It supplies general recurrence and related shifted-factorial examples,
not a located statement of this all-m/all-K representative family. No
claim that a classical hook theorem already states the new existential
endpoint is made; no unread classical body is used to subsume it.

At 2026-10-29T20:33:36Z I lawfully refreshed the arXiv abstract and
the distinct university-hosted precursor PDF; both were HTTP 200 and
byte-identical to the candidate copies. URLs, times and hashes are in
`current-primary-http.json`. A bounded two-query live search for
`"2610.29846" "representatives"` and
`"pattern packing" "double factorial" Blitvic Kammoun` produced
no usable primary proof body; broad aggregator hits were not relied on.
That ineffective search is explicitly not novelty evidence.

I used the saved lawful Omega HEAD 89cda9c274d1122b7676173296af3047c3b64cd1
(20:10:57Z) and OpenAI 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a evidence,
and inspected the saved 7-commit/3-path delta from 73a5033. Its three
paths concern Fiedler resistance and nonbinary borders, not this endpoint.
I read the nearby actual registry problem/library bodies and the claim,
count and result bodies of the saved Blueprint/Lean maximum refutation.
They negate item 4's maximum assertion via 9>8 at K=8,m=4,j=2;
this is separate from item 6 and does not settle items 5 or 8.
No external Lean was compiled. I did not repeat r105's recursive-tree
403 or r106's HEAD 403 requests, or seek alternate endpoints to bypass
them. The inherited 300-file capped comparison remains incomplete;
the old streaming term screen and dated tree/delta evidence are not a
worldwide semantic search. HEAD time is not each theorem's authorship
time. Hence novelty is HOLD, not FAIL for a located duplicate and not
PASS from absent search hits. No Lean/paper investment is recommended.

## Strongest falsifier and procedural record

The strongest mathematical falsifier is an admitted triple with either
a position identification outside the declared partition, a literal
window comparison absent from the comb closure, or a purported C vertex
incomparable to a later vertex. Any of these defeats the reduction and
must override matching small counts. Alternatively a residual constraint
on Z[j−1] invalidating one of the 2j−1 insertion gaps defeats the count.
The symbolic two-inclusion proof and independent full-pair checker
address precisely these tests. An exact previously published compatible
representative would change novelty from HOLD to a duplicate finding.
The eligibility judgment is falsifiable as a policy assessment by showing
a substantive realization obstruction beyond the source's unit-leaf tree
and neutral padding; merely invoking its explicit open-question wording
does not establish that additional work.

Two initial read-only shell calls ran before I applied the guard: a
pwd/rg inventory bounded by head, and a cat of the two AGENTS files and
guard. This was a deviation from the literal all-shell-helper rule and
is preserved here rather than represented as compliant. They made no
writes. Every subsequent Python/shell helper ran under the unchanged
assigned guard, with no cap increase. Native apply_patch wrote only this
lane. Some read outputs were display-truncated; no large aggregate
inventory was buffered. No helper/checker failure occurred. The supplied
guard samples at nominal 40ms, so sub-sample RSS excursions are not
certified absent. No children, git commands, shared writes, browser tabs,
posts, contacts, or uploads were used.

Handoff: full ordinary answer PASS; recommend routine-adaptation exclusion,
zero credit; novelty remains bounded/unestablished. Items 5 and 8 remain
unresolved. Root owns the final eligibility decision.
