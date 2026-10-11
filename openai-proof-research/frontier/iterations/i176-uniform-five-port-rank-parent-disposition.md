# I176 parent disposition: uniform first-surgery saturation

**Technical result at its stated scope. No ninth nomination. Eight accepted,
two remaining.** The parent accepts U176's written proof for every even
$k\ge6$, not an extrapolation from its finite tests. The specified surgery
has $L_k=\ker B_k$, dimension $k+8$ and loss zero. This excludes a high-loss
construction in this family. It does not prove a uniform brace theorem,
universal exchange, (T), or Q164.

## Original proof review

The [original report](i176-uniform-five-port-rank.md), mathematical modules,
development runner, authentication, packaging and sealed verifier were read.
The source revision and catalogue entry 180, complete manuscript-family path
listing, and actual `cor:pfaffian-paths` statement were checked. All upstream
theorems at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` remain stipulated true.
U176 itself needs only its explicit constructions and rational linear algebra.
The inherited A175 uses the actual prescribed-path statement, with all its
hypotheses. No upstream truth audit was performed.

### Graph and uniform availability

The actual edges removed are $1\,2$ and $T_{k-2}T_{k-3}$, with the facial
square orientation specified in the report. The original large face starts
with $1,2$ and its seventh directed edge is the latter attachment edge;
the identification with `[0,0,6]` is uniform. The retained protected face
is a hexagon, not a $(3,3)$ octagon. Vertex and edge counts are
$2k+14$ and $3k+21$. Local counts are $2k+1$ and $3k-1$.
The local graph is connected: the upper break is replaced by the path
through $p,q$, every top vertex has its rung, and the bottom rail is a
cycle. The fixed exterior and cut edges connect the full graph.
The existing bipartite coloring extends over the oriented square.

The path-word argument was reviewed for all indices, not just sampled
parameters. Write $n=k-1$, $j=k-3$, both odd. The odd/even blocks in $W_j$
partition the first $j-1$ columns, followed by both vertices in column
$j$. The blocks in $V_j$ use all top indices $1,\ldots,j$ and exactly
bottom indices $2,\ldots,j$. Their joins are respectively top edges and
rungs. The displayed tails cover the remaining indices without overlap.
In the $6r,7r$ rows, the splits at $r,r+1$ partition each rail; the special
$6(n-1)$ row is separate and never crosses the missing top edge.
Every join in the remaining rows is a rung, a surviving rail edge, the
bottom wrap edge, or one of the three edges through $p,q$.
This verifies coverage, adjacency and absence of isolated cycles uniformly.

The endpoints give the eleven stated local pairings. The fourteen listed
exterior partners are actual spanning path packings on the fixed thirteen
vertices. Their pairings glue to one cycle. States 2 and 6 omit cut edge
2 but their partners use $1\,7$; every other state uses cut edge 2.
Thus the local directions have common *surviving* partners, and the
anchors are actual cycles, not freely translated representatives.
The fourteen partners are sufficient subfamilies, not a claim to list
every exterior packing.

### Independent minor derivation

Put $m=k/2$. On columns $h_1,\ldots,h_{j-1}$, the $d_r$ rows give $-I$,
with tail $(1,0,0)$ on $h_{n-1},z,g_0$.
The parent's parity calculation from the omitted edges gives:

| Row | Coefficients for $1\le i<j$ | Tail |
|---|---|---|
| $u$ | $-1$ at even $i$, zero otherwise | $(-1,0,1)$ |
| $v$ | $-1$ at odd $i$, zero otherwise | $(1,0,-1)$ |
| $w$ | $-1$ at odd $i\ne1$, zero otherwise | $(0,1,-1)$ |

There are $m-2$ odd and $m-2$ even indices in this interval.
Elimination therefore gives first tail coordinates
$-(m-2)-1=1-m$, $-(m-2)+1=3-m$, and $-(m-3)=3-m$.
The other two coordinates do not change. Expanding the second column
of the displayed Schur block gives determinant
$-\det\bigl[\begin{smallmatrix}1-m&1\\3-m&-1\end{smallmatrix}\bigr]
=4-2m$. The $-I$ block has even order $k-4$, so the full determinant is
also $4-k$, nonzero throughout the claimed range.

The parent rebuilt the fixed exterior paths, all full projected vectors,
and the nine-column minor independently. Its determinant is 1. The first
three directions are actual within-exterior differences, the remaining
six actual anchor differences. Since the local directions have zero
projection, projected independence proves independence modulo the local
kernel. This is the required intersection argument.

For a connected bipartite graph the unsigned incidence matrix has rank
one less than the vertex count. Consequently the local zero-projection
kernel has dimension $k-1$, the global kernel has dimension $k+8$, and
its projected image has dimension 9. The constructed directions attain
these upper bounds. Since survivor differences lie in the global kernel,
they fill it; the full Hamiltonian difference space lies between them
and the same kernel. This proves loss zero without complete uniform
cycle enumeration.

At $k=4$ the formula's determinant vanishes and its local basis assertion
does not apply. The separate finite check has local rank 1 and two extra
anchor-kernel directions. Neither that exception nor the observed
cycle-count pattern is promoted to another uniform theorem.

## Authentication and validation

The [parent validator](../experiments/i176-parent-validate.py) authenticated
the detached report, seal and verifier hashes, all **59 owned** and
**507 non-context external** entries, complete owned membership, and the
inventory/prevalidation/seal chain. Four separate context ledgers make
**511 external/context entries**. All bytes, controls and current context
hashes were unchanged across replay.

[Sealed parent replay](../experiments/i176-parent-verification.json):
**PASS in 2.02917855407577 seconds**, three byte-identical payloads,
eight blocked probes, empty stderr. The context policy now correctly
allows inherited ledger drift while freezing current bytes for the run.
All mathematical inputs remain strict. This does not retroactively repair
I175's historical-context requirement. Python audit hooks are not an OS
sandbox, and clean-clone reconstruction remains untested.

The [independent parent checker](../experiments/i176-parent-certificates.py)
executes no child implementation. It reuses only the committed parent
DFS/Fraction helper chain, with the immediate helper hash recorded in its
[receipt](../experiments/i176-parent-certificates.json). It independently
reconstructs the graph, exhausts each complete local/exterior state product,
compares the union to independently enumerated surviving Hamiltonian cycles,
and recomputes all ranks:

| $k$ | Survivors | Local rank | Image | Total | Extra anchor kernel |
|---|---:|---:|---:|---:|---:|
| 4 | 26 | 1 | 9 | 12 | 2 |
| 6 | 30 | 5 | 9 | 14 | 0 |
| 8 | 34 | 7 | 9 | 16 | 0 |
| 10 | 38 | 9 | 9 | 18 | 0 |
| 12 | 42 | 11 | 9 | 20 | 0 |

It also checks 96 expanded local words, their omitted-edge sets and
pairings, actual glued partners and anchors, all four local minors and
the fixed determinant-1 image minor. Only the stipulated five parameters
were computed; no larger census was run. The old mandatory seven-family,
matching and residual checks are covered by sealed replay rather than a
second parent rescan of the historical populations in this round.

## Preserved failures and limits

The child's ordering-dependent $71$ selector, schema-inspection error,
and mistaken identification of the C171 functional reference with its
pre-switch cycle remain sealed, including failed stages and empty captures.
The corrected switch reconstructs the pre-switch cycle from the prescribed
F and retains the distinct functional reference. F and generic T remain
different. The inherited I175 and I174 failures are not erased.

The parent's first checker incorrectly required the report's fourteen
sufficient exterior partners to exhaust the complete exterior families.
It failed at state 5, which has an additional partner. States 9 and 10
also have extra partners. The
[failed source](../experiments/i176-parent-certificates-attempt-01.py.disabled),
[empty stdout](../experiments/i176-parent-certificates-attempt-01-stdout.txt)
and [reproduced assertion stderr](../experiments/i176-parent-certificates-attempt-01-stderr.txt)
are retained. The corrected comparison checks the exact listed partners
and anchor order, while the separate exhaustive-family comparison remains
unchanged. This was a parent test-scope error, not a defect or repair of
U176. The corrected checker passes.

The child's literature receipt honestly distinguishes search snippets
from primary proof reads. No new parent literature search or priority
clearance is claimed. The result closes a technical family obstruction,
not a contribution gate toward the ten-result count.

## Next round and integration order

[I177's full brief](iteration177-adjacent-port-surgery-brief.md) assigns an
independent original-scope U176 audit and one previously untested P8
operation, `[0,0,10]`, deleting $1\,2$ and $13\,14$ near port 0.
The five-port decomposition must be rebuilt, not imported from U176.
Positive loss is required before any further attachment; a zero-loss
outcome must be recorded as another obstruction, not success.
No larger-prism sweep is authorized.

This disposition, brief and shared ledgers are finalized and preflight
checked before dispatch to avoid the I174 late-parent-document race.
The subsequent task archive records the actual provider and readback;
the integration receipt records the exact publication scope.
Only `openai-proof-research` is eligible for publication.
