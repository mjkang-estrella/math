# Sparse distance-constrained reliability: full ordinary candidate

One fresh precise source question was sustained. Pablo Romero, *Existence of
uniformly most reliable two-terminal graphs with distance constraints*,
arXiv:2610.36120v1, p10 immediately following Lemma27, explicitly leaves open
whether H_(n,m) is 3-UMRTTG for all n>=5, 5<=m<=2n-3. Its Lemma23 explicitly characterizes
the intended m-edge graph; printed Definition9 has an indexing defect
(detailed below). Definition1 imposes domination over EVERY graph in T_(n,m) and
EVERY rho in [0,1]. All graphs are finite simple undirected; isolated vertices
are allowed. No terminal-universality restriction is imposed on competitors.
This entire parameterized sparse-range question, rather than one instance,
is the target. The separate dense-range classification is not claimed solved.

Latest obtained primary: https://arxiv.org/pdf/2610.36120 and
https://arxiv.org/abs/2610.36120. The actual abstract history lists v1 only,
26 October2026 18:27:37UTC. PDF SHA256:
9c42ee867de8f1fc0b57e5e76b6f6b3b67b28c7f96303b2b3b18d2a02b0c27f3.
The source footnote identifies a preliminary extended abstract without proofs:
Romero, *Most reliable two-terminal graphs with distance constraints*, Procedia
Computer Science273(2025)185–192. That body was not obtained. The new primary
explicitly identifies a false deletion equality in its earlier induction.
No DOI was authenticated for either version; none is invented. Latest arXiv
status is not authentication of the published body or worldwide novelty.
Retrieval UTC, exact URLs, final URLs, lengths and hashes are in http.jsonl.

Read early: the primary's definitions and Sections2–3; complete Lemma20,
Lemma23 and Lemma27 proofs, and the immediately following open problem;
Section7 and bibliography. Sections4–5 surrounding constructions and pathset
identities were read in bounded excerpts. The materially closest complete
proofs are the primary's own endpoint proofs: Lemma23 uniquely forces H
near rho=1, and Lemma27 asserts endpoint optimality near rho=0. Neither is
the all-rho bridge. No independent audit of the entire17-page paper is claimed.
No inaccessible predecessor proof is presented as read.

## Universal route and full classical-adaptation objection

PROOF.md contains a complete ordinary candidate. First, coupled edge
replacements insert st and turn single terminal-neighbor vertices into double
neighbors. Irrelevant edges can then be deleted and retained as unused budget.
The remaining graph is st plus a two-terminal double star with arbitrary
interior graph F on the common neighbors.

Conditioning on no surviving two-edge paths assigns each common neighbor
states T,N,S with probabilities u,1-2u,u, u=p/(1+p). An interior edge has
failure weight rho if its endpoints are opposite and1 otherwise. This matrix
is TP2 in the order T<N<S. Finite association, fully proved by induction in
PROOF.md, makes S_x increasing negatively correlated with T_y decreasing.
Symmetry and a one-site conditional calculation bound each marginal by u,
so opposite states have probability at most2u² in EVERY weighted core.

Removing at most two interior edges loses conditional failure factor at most
4p u²<=p². A new independent two-edge terminal path contributes precisely
1-p² to failure. Thus two edge-budget units can always be converted to one
fresh common neighbor without reducing reliability. The sparse bound
m<=2n-3 guarantees that a fresh vertex is available at EVERY such step.
The algorithm ends at the specified m-edge H_(n,m), for both parities of m. Endpoints
p=0,1 are treated separately. This is an all-order argument, not extrapolation
from a census, an endpoint comparison, or an unproved independence assertion.

The full applicable classical bridge is therefore exposed: coupling, finite
TP2/FKG association, S/T symmetry, union bound and budget induction. FKG
is classical, and no claim is made to invent the correlation theorem. The
finite proof here avoids requiring an unread theorem body as a mathematical
dependency. Whether this adaptation is substantive enough for campaign
eligibility is a genuine root-review question; no exclusion is asserted from
shortness, and no automatic eligibility follows from the word “open”.
This source family is distinct from Romero–Petingi triangle maximization;
that r193 question was not reopened. No component or parity-instance credit.

## Adversarial scope checks and exact method countermodel

The proof explicitly checks both path orientations, strict positivity only for
0<p<1, arbitrary core graphs rather than trees, disconnected competitors,
every edge of the initial graph, fixed n, unused budget, the final even-m
edge, and both probability endpoints. The association induction proves the
monotone likelihood-ratio step rather than assuming independence after
conditioning. The correlation bound is used under mu_(F0), the graph AFTER
the removed edges are deleted. Using the original measure here would be an
unjustified substitution. The candidate does not rely on Lemma27's cut
classification or on the paper's other cited all-terminal results.

The published-source deletion induction cannot be reused literally:
for H_(8,10), deleting the edge from s to one endpoint of the interior edge
gives R(1/2)=413/512, while H_(8,9) gives431/512. These are exact
3-constrained probabilities. This is a method countermodel, not a refutation
of the sparse conjecture. The new replacement removes up to TWO interior
edges and adds an independent two-edge path; it does not identify these
unequal deleted graphs.

checks.py covers26,471 fixed-terminal labeled graphs of orders4–6 in its
5<=m<=2n-3 range, finding coefficientwise H domination. It includes45
independent state-integrator controls and110 rational closed-form H controls.
correlation-checks.py covers225 weighted core models,2,085 marginal/opposite
bounds, and1,353 one/two-edge replacements through four core vertices at
p=1/3,1/2,2/3. Exact replay is byte-identical. These finite checks support
implementation and arithmetic only; the ordinary proof is separate.

## Bounded broad reconnaissance, aliases and provenance

The inherited current math.CO and cs.DM listing bodies from r193 were inspected
and bound as source context, not new original history records. A second actual
primary was retrieved: Alexander Clow, *Cops and Robbers on Graphs without
Long or Short Holes*, arXiv2610.36290v1 (26October2026 21:14:08UTC).
Its introduction and concluding question/conjecture passages were inspected.
Its public theorems are not nominations. No second question was sustained,
no cop-number proof claimed, and no extra fresh slot counted. Other listing
abstracts remain reconnaissance, not read proof bodies or source clearance.

Before sustained work, refreshed r193's corrected2,564 actual-original-path
records/1,245 distinct bodies, preserving all aliases and r111–113 originals.
The bounded direct-original refresh gives2,572 paths/1,253 distinct bodies,
eight changed/new, zero missing. Changed r192/r193 handbacks and r194
dispositions were read. Every inherited original path is separately hashed
and copied even when bytes coincide. Generated frozen inventories were not
recursively promoted to new original records. Retained inherited provenance
aliases remain aliases, not independent investigations.

early-screen.json retains the broad Romero author hit in r193, which is a
different statement family. exact-alias-screen.json has no historical match
for the exact arXiv id, either full title, UMRTTG, or terminal-reliability
statement-family patterns. No DOI was available for an exact DOI screen.
Absence in this bounded index is not proof of historical or public novelty.

The inherited access/failure bytes were preserved and inspected by the safety
filter. Denied GitHub API/raw/codeload/diff/patch, ScienceDirect, Google
challenge routes and parked historical intervals were not requested. The
conservative filter also blocked successful inherited list/registry URLs
before any network request; those entries are local safety-filter failures,
not server denials. Hence no current complete registry tree/head was cleared.
An institutional author homepage returned404 once and was not retried.
No proxy, browser, TLS disabling, external messages, uploads or MathDB edits.
The missing2025 body and public-registry history leave novelty HOLD.

## Disposition

Retain ONE full ordinary candidate for independent SOURCE/MATH and complete
classical-adaptation/substantive review by root. Zero acceptance or credit.
No Lean or manuscript investment. Counts9additional/39total,next40 unchanged.
Scientific originals/copies and administrative snapshots are distinguished;
separate final-manifest verification follows final writes. The initial
unguarded inventory and failed basename-collision freeze remain documented.

## Final visual source qualification

A guarded page4 rendering, definition9-page4.png, confirms that printed
Definition9 runs i from3 through (m-1)/2 for odd m. That gives only
(m-5)/2 common neighbors and m-4 total edges, contradicting membership
in T_(n,m). This is an actual printed defect, not just pdftotext extraction.
Lemma23 explicitly requires floor((m-1)/2) two-edge paths, and its even
case adds the one common-neighbor edge; those are the graphs specified
and proved optimal here. Thus the candidate proves the full sparse
existence/optimization question with an explicit m-edge graph and resolves
the intended H reading supported by Lemma23; literal defective Definition9
is NOT silently identified with it. SOURCE status needs qualified review.
The indexing correction receives no credit and is not the mathematical
content of the candidate. No dense-range or corrected-parameter variant
is nominated.
