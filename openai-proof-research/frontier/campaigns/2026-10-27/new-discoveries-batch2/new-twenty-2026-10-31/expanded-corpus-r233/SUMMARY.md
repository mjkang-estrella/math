# expanded-corpus-r233

No eligible new solution survived. Proposed credit: **0**. The lane recommends
9 exclusions and parks 11 records. No Lean endpoint or acceptance is claimed,
and the campaign ledger and counts were not changed.

## Main findings

353712 is already proved by Garamvolgyi–Jackson–Jordan, arXiv:2509.03150v1
Theorem 1.6 (IMRN 2026 version Theorem 1.4). 353750, 354068 and
354473 are proved in their own cited sources. For 354035, source footnote 1
explicitly refutes the literal empty-U degree with an n-cycle and corrects
it from |E|-|V|-1 to |E|-|V|+1; Theorem 1.2 proves only the |U|>1 case.
No solution of the corrected empty-U case is claimed. 354810 was refuted by
[Muller](https://arxiv.org/abs/2304.08459), using the primitive action of
the triality group on 4064256 points. These are not new targets.

A targeted follow-up search found an August 2026 public proof of the exact
354092 maximality conjecture on
[ProbXiv](https://probxiv.com/problems/on-eigenfunctions-and-maximal-cliques-of-generalised-paley-graphs-of).
The initial title/citation search did not find it; it was found after the bounded
computations. Computation was stopped on that route. The public proof is
preserved, not silently treated as a fresh discovery or a Lean certificate.

354420 admits the short ordinary source-criterion bridge recorded in
EXCLUDED-ROUTES.md. It receives no credit under the user's routine-bridge
exclusion. 355215 has an obvious printed-obstruction blow-up route, likewise
ineligible. No exact base certification was pursued for that route.

The 355005 paraphrase omits the source's essential zircon hypothesis.
The corrected source question remains parked; a failure without that premise
would only be a wording correction. 354366 is proved in type A but the source
still leaves other types contingent on its Corollary 2.4.9 analogue.

## Exact bounded work

The Paley script uses F_q[a]/(a^2-delta) for prime q, binary exponentiation
to test m-th powers, and cyclic bitset intersections to find every possible
extra vertex adjacent to the constructed clique. It covers 2170 pairs with
503<=q<=6000, 3<=m<=(q+1)/3, m dividing (q+1)/2 and clique size<=40.
No extension was found. This does not cover prime powers, larger cliques,
or source cases where m does not divide (q+1)/2. The earlier pass has 301
pairs and is separately preserved. The source reports verification through
q=500. All three available source versions were fetched and the construction,
partial maximality and Example 5.9 were checked.

The great-circle script samples 24 arrangements with integer normals and no
triple concurrence. Cross products, angular comparisons and coloring checks
use integer arithmetic. The order list is 9,10,11,12,14,16,18,20, with three
samples at each. Twenty-three backtracking searches found a 3-coloring; one
18-circle sample hit 100000 nodes. The separate local-search pass found a
proper 3-coloring for it too. No uncolorable sample and no general coloring
theorem resulted. The recent 2026 antipodal-coloring counterexample is for a
stronger claim and explicitly has an ordinary 3-coloring.

The design script checks 164181 necessary integer tuples with 2<=k<=150,
k<r<=1000 and 1<=y<=floor(k/2), including the source intersection identity
and k*lambda divisibility by y. No tuple passes Proposition 18. The general
ordinary counting argument is stronger than this diagnostic scan.

Full output and CPU/wall/max-RSS receipts are in logs/. All numerical runs
used scripts/bounded.py: two CPUs, MALLOC_ARENA_MAX=2, 120 CPU seconds,
140 wall seconds, and a 6 GiB address-space cap. No Lean process was run.
To reproduce without overwriting existing logs, choose new run names, e.g.:

    python3 -I -B scripts/bounded.py replay-paley paley.py 6000
    python3 -I -B scripts/bounded.py replay-design design.py
    python3 -I -B scripts/bounded.py replay-circles circles.py
    python3 -I -B scripts/bounded.py replay-circle-local circle_local.py

## Evidence and limits

results.json contains exactly the 20 reserved ID-keyed dispositions, literal
statements, actual review depth, mathematical attempts, remaining obstacles,
raw/chunk/statement SHA-256 hashes, one-based raw line numbers and primary
HTTP receipts. inputs/<ID>.jsonl retains every exact raw line including newline.
The actual current arXiv version histories are in inputs/source-index.json;
all listed primary versions were downloaded. Fetching a version does not mean
its entire proof body was read. inputs/printed-example-inventory.json is a
mechanical label/line inventory, not full visual inspection of every figure.

Live Lean Pool head: 01db1d7049cf9668bda1e9e106875ee1278b43e6; its
recursive tree is complete. Live OpenAI/math head:
4eaee87548250b2682affda7d05d947c05554bae. Its root recursive tree is
truncated; the complete preprints subtree (13578 entries) and current CONTENTS
were separately retrieved. Only path/name and catalogue screening was done;
there is no full Lean proof-body or deleted-history clearance. Generic GitHub
web searches were noisy and are not evidence of absence. No candidate was
cleared on the strength of those negative searches.

Ancestor AGENTS/TASK exclusions and both ledgers were read. The exact-ID
history scan of SUMMARY/CANDIDATE/results reports returned no hits; it was
not a full-text search of every historical artifact. This reservation's absence
from routing indexes is not a novelty guarantee. No global openness or priority
claim is made for any parked target. Citing-work and recent-web searches are
bounded, and current MathDB solution/comment bodies were not directly fetched.

Crossref, Semantic Scholar, arXiv search API, ScienceDirect and DBLP were not
requested. Some search-engine result lists contained those domains; they were
not followed. All direct HTTP access retained TLS verification and immutable
timestamped receipts. Redirects were not automatically followed. No downloaded
code was executed and no archives were extracted. All writes stayed in this
lane; no child agents, git, external messages, publication or browser tabs.
