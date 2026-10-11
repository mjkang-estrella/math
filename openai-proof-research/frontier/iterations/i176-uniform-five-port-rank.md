# I176: uniform saturation of the first five-port prism surgery

Research iteration, 2026-10-10. **Technical result, not a ninth nomination.
Eight substantial findings remain accepted; two remain.** All OpenAI
theorems at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` remain stipulated true.
No upstream truth audit or lowered contribution gate is used.

## 1. Result and exact quantifiers

**Theorem U176.** For every even integer $k\ge6$, perform exactly the
first canonical surgery described in Section 2 on the punctured-$P_k$
replacement of vertex 0 of $P_6$. Keep vertex 7 contracted and define
survivors to be Hamiltonian cycles using at least one of the protected
edges $6a_k$ and $1\,7$. In sorted undirected-edge coordinates over
$\mathbb Q$, their difference space satisfies
$$
L_k=\ker B_k,\qquad \dim L_k=k+8,\qquad \ell_k=0,
$$
where $B_k$ is the unsigned vertex-edge incidence matrix.
The actual within-state local packing differences span the entire
zero-exterior-projection kernel, of dimension $k-1$.
The projected actual exterior and anchor differences have dimension 9.

This pays the previously conditional $(k-1,9)$ criterion **for this first
surgery for every even $k\ge6$**. It is not finite-rank interpolation.
The proof gives closed path words, $k-1$ realized local differences with
a minor of determinant $4-k$, and nine realized projected differences
with a fixed minor of determinant 1. No strip induction is needed.

The exceptional $k=4$ graph also has loss zero, freshly checked, but its
within-state local rank is 1, not $k-1=3$. Two actual anchor-kernel
directions supply the deficit. It is not covered by the local basis
formula above.

This is a uniform **obstruction to obtaining high loss by this surgery**.
It is not a high-loss-brace theorem, a uniform brace theorem, or a
statement about every surgery or attachment.

## 2. Exact graph, orientation, and five ports

Write $n=k-1$, $j=k-3=n-2$ and
$$
T_i=a_i=12+i\ (1\le i\le n),\qquad
B_i=a_{k+i}=12+k+i\ (0\le i\le n).
$$
Thus the attachment is the prism with its top vertex $a_0$ removed.
Its three old ports are $1T_1,5T_n,6B_0$. The core keeps vertices
$1,\ldots,11$ and all edges of $P_6$ not incident to 0.

The initial oriented large face is
$$
[1,2,3,4,5,T_n,T_{n-1},T_j,T_{j-1},\ldots,T_1].
$$
Its edge at position 0 is $1\,2$ and its edge at position 6 is
$T_{n-1}T_j=a_{k-2}a_{k-3}$. It is lexicographically first:
its first vertex is 1 and next vertex 2; the other oriented faces
through 1 next visit 7 or $T_1$. Rotation to the minimum does not
reverse orientation. Consequently the same triple `[0,0,6]` denotes
these **actual edges** for all even $k\ge4$.

Delete them and insert new vertices
$$
s=12+2k,\quad t=13+2k,\quad p=14+2k,\quad q=15+2k
$$
with edges
$$
1s,\quad2t,\quad T_jp,\quad T_{n-1}q,\quad st,\quad sp,\quad tq,\quad pq.
$$
This is the square $s,t,q,p$ with the required facial, not crossed,
orientation. The large face splits into
$$
[1,s,p,T_j,T_{j-1},\ldots,T_1],\qquad
[2,3,4,5,T_n,T_{n-1},q,t].
$$
The reverse side of $1\,2$ acquires the segment $2,t,s,1$; the reverse
side of $T_jT_{n-1}$ acquires $T_j,p,q,T_{n-1}$.
Together with $[s,t,q,p]$ these replacements preserve opposite directed
edge occurrences and each vertex's cyclic link. They replace disks
by disks. This establishes the planar orientation uniformly, rather
than relying on face indices observed at a few parameters.

The protected face stays
$[1,T_1,B_1,B_0,6,7]$. The graph is simple, connected, cubic and
bipartite: the prism colorings match across the three old ports;
$1$ and $T_j$ have opposite colors, so $s,p$ have opposite colors, as
do $t,q$. The displayed replacement fits the existing coloring.
It has $2k+14$ vertices and $3k+21$ edges.

Put $X=\{T_1,\ldots,T_n,B_0,\ldots,B_n,p,q\}$ and
$Y=\{1,\ldots,11,s,t\}$. The five cut edges, in **fixed label order**, are
$$
0:1T_1,\quad1:5T_n,\quad2:6B_0,\quad3:sp,\quad4:tq.
$$
Their endpoints are distinct on both sides.
$X$ has $2k+1$ vertices and $3k-1$ internal edges.
$Y$ has 13 vertices and these 17 internal edges, in the coordinate
order used below:
$$
(17,1s,23,28,2t,34,39,45,4\,10,5\,11,
 67,6\,11,78,89,9\,10,10\,11,st).
\tag{2.1}
$$
Here, for example, $17$ means the edge $1\,7$, not vertex 17.

For clarity the local internal edges are
$T_iB_i$ for $1\le i\le n$;
$T_iT_{i+1}$ for $1\le i<n$, except $i=j$;
the bottom cycle $B_0B_1\cdots B_nB_0$;
and $T_jp,pq,qT_{n-1}$.

## 3. Actual state products and ambient bounds

A Hamiltonian cycle uses a nonempty even number of the five cut
edges, hence two or four. Its restriction to each side is a spanning
path packing with degree one at the used cut endpoints and two
elsewhere, and has no isolated cycle. Conversely two such packings
with the same used set $J$ glue to one Hamiltonian cycle precisely when
their endpoint pairings have connected union. For two endpoints this
is automatic; for four it means the pairings differ.

Survival is exactly
$$
2\in J\quad\text{or the exterior packing uses }1\,7.
\tag{3.1}
$$
It does not depend on the particular local packing within its state.
Thus any two listed local packings in the same state can be combined
with the **same specified actual exterior packing** to realize their
difference as a survivor difference. Exterior differences are likewise
realized holding a listed local packing fixed.

For complete actual state families and actual anchors $c_i$ this proves
$L=W_X+W_Y+\langle c_i-c_0\rangle$, as in I175. The proof here needs only
the explicit subfamilies below, not any assertion that every abstract
type is available or that every type has full affine span.

The connected bipartite local graph has incidence rank $2k$.
Consequently, for projection $\pi$ onto all exterior and cut coordinates,
$$
\dim(\ker B_k\cap\ker\pi)=(3k-1)-2k=k-1.
$$
The global connected bipartite graph has incidence rank $2k+13$, so
$$
\dim\ker B_k=k+8,\qquad \dim\pi(\ker B_k)=9.
\tag{3.2}
$$
These are upper bounds. Sections 4–6 construct actual survivors
attaining both, with no free translation of anchors.

## 4. Closed path words: availability for every parameter

For indices $a,b$, let $T[a:b]$ or $B[a:b]$ list consecutive vertices
from $a$ to $b$, increasing or decreasing as indicated. Concatenation
in the following table joins words without deleting repeated endpoints;
the displayed words have **no repeats**. A slash separates components.
Define, since $j$ is odd and $j\ge3$,
$$
W_j=(T_i,B_i,B_{i+1},T_{i+1})_{i=1,3,\ldots,j-2},T_j,B_j,
$$
$$
V_j=(T_i,T_{i+1},B_{i+1},B_{i+2})_{i=1,3,\ldots,j-2},T_j.
$$
These are explicit concatenations, not unspecified Hamiltonian paths.

| Template | Local spanning path word(s) |
|---|---|
| $0$ | $T[1:j],p,q,T[n-1:n],B[n:0]$ |
| $1a$ | $B_0,B_1,V_j,p,q,T_{n-1},B_{n-1},B_n,T_n$ |
| $1b$ | $T_n,T_{n-1},q,p,T[j:1],B[1:n],B_0$ |
| $2$ | $T_n,T_{n-1},B_{n-1},B_n,B_0,B_1,V_j,p,q$ |
| $3$ | $B_0,B_n,T_n,T_{n-1},B[n-1:1],T[1:j],p,q$ |
| $4a$ | $W_j,B_{n-1},B_n,B_0\ /\ T_n,T_{n-1},q,p$ |
| $4b$ | $T[1:j],B[j:0]\ /\ T_n,B_n,B_{n-1},T_{n-1},q,p$ |
| $5$ | $W_j,B_{n-1},T_{n-1},q,p\ /\ T_n,B_n,B_0$ |
| $6r$, $1\le r<j$ | $T[1:r],B[r:0],B[n:r+1],T[r+1:j],p\ /\ T_n,T_{n-1},q$ |
| $6(n-1)$ | $T[1:j],p\ /\ T_n,B_n,B[0:n-1],T_{n-1},q$ |
| $7Z$ | $W_j,B_{n-1},T_{n-1},T_n,B_n,B_0\ /\ p,q$ |
| $7r$, $1\le r<j$ | $T[1:r],B[r:0]\ /\ p,T[j:r+1],B[r+1:n],T_n,T_{n-1},q$ |
| $8$ | $T[1:j],p\ /\ B[0:n],T_n,T_{n-1},q$ |
| $9$ | $T_n,B_n,B_0\ /\ p,T[j:1],B[1:n-1],T_{n-1},q$ |
| $10a$ | $T_n,B_n,B_{n-1},T_{n-1},q\ /\ B_0,B_1,V_j,p$ |
| $10b$ | $T_n,T_{n-1},q\ /\ B_0,B[n:1],T[1:j],p$ |

**Uniform verification of this table.** In $W_j$, the blocks partition
columns $1,\ldots,j-1$ into odd/even pairs and the last pair of
vertices is column $j$. Thus it uses both rails through column $j$
exactly once, with adjacent blocks joined by the top edge from an
even column to the next odd column. In $V_j$, the top vertices are
$T_1,\ldots,T_j$ exactly once, and the bottom vertices are
$B_2,\ldots,B_j$ exactly once; adjacent blocks join by the rung at
the next odd column. Adding the explicitly displayed $B_0,B_1$ or
tail vertices covers precisely the omitted indices.

For the $6r,7r$ rows the top intervals partition $1,\ldots,j$ at
$r,r+1$, and the bottom intervals partition $0,\ldots,n$ at the same
place, in their displayed cyclic order. The other component covers
the two remaining top vertices and $q$. The special $6(n-1)$ row
is written separately, not inferred by crossing the missing top edge.
In every other row the monotone intervals and displayed tails have
disjoint index sets with exactly the stated union. Every consecutive
pair is an edge in Section 2; the only passage over the missing
$T_jT_{n-1}$ uses $p,q$ when that passage is needed. These observations
prove, for every allowed parameter, adjacency, coverage and absence
of repeated vertices or isolated cycles. They are an index-partition
proof, not a finite test. Reading the endpoints gives the next table.

The first number of each template names its state. Pairings below use
cut labels, not vertex labels:

| State | $J$ | Local pairing | Exterior pairing | Local anchor |
|---|---|---|---|---|
| 0 | 02 | 02 | 02 | 0 |
| 1 | 12 | 12 | 12 | 1a |
| 2 | 14 | 14 | 14 | 2 |
| 3 | 24 | 24 | 24 | 3 |
| 4 | 0123 | 02,13 | 03,12 | 4a |
| 5 | 0123 | 03,12 | 02,13 | 5 |
| 6 | 0134 | 03,14 | 01,34 | 61 |
| 7 | 0234 | 02,34 | 03,24 | 7Z |
| 8 | 0234 | 03,24 | 02,34 | 8 |
| 9 | 1234 | 12,34 | 14,23 | 9 |
| 10 | 1234 | 14,23 | 12,34 | 10a |

Here $61$ means $6r$ with $r=1$. This supplies actual local packings
in all eleven states for every even $k\ge6$.

### Fixed actual exterior partners

The following words each cover the same 13 exterior vertices exactly
once. Their endpoints give exactly the exterior pairings just listed.
The subscript 0 denotes the default partner and anchor choice.

| Exterior packing | Actual path(s) |
|---|---|
| $y_{0,0}$ | $1,s,t,2,3,4,5,11,10,9,8,7,6$ |
| $y_{1,0}$ | $5,11,10,4,3,9,8,2,t,s,1,7,6$ |
| $y_{1,1}$ | $5,4,3,2,t,s,1,7,8,9,10,11,6$ |
| $y_{2,0}$ | $5,4,3,2,8,9,10,11,6,7,1,s,t$ |
| $y_{3,0}$ | $6,11,5,4,10,9,3,2,8,7,1,s,t$ |
| $y_{4,0}$ | $1,7,8,2,t,s\ /\ 5,4,3,9,10,11,6$ |
| $y_{4,1}$ | $1,7,8,9,3,2,t,s\ /\ 5,4,10,11,6$ |
| $y_{4,2}$ | $1,7,8,9,10,4,3,2,t,s\ /\ 5,11,6$ |
| $y_{5,0}$ | $1,7,6\ /\ 5,11,10,4,3,9,8,2,t,s$ |
| $y_{6,0}$ | $1,7,6,11,10,9,8,2,3,4,5\ /\ s,t$ |
| $y_{7,0}$ | $1,s\ /\ 6,7,8,9,10,11,5,4,3,2,t$ |
| $y_{8,0}$ | $1,7,8,2,3,9,10,4,5,11,6\ /\ s,t$ |
| $y_{9,0}$ | $5,11,10,4,3,9,8,2,t\ /\ 6,7,1,s$ |
| $y_{10,0}$ | $5,4,3,9,10,11,6\ /\ s,1,7,8,2,t$ |

Every consecutive pair appears in (2.1). Every used cut-label set
agrees with its local state. The two four-endpoint pairings differ,
so gluing yields one cycle, not an isolated two-factor.
States 2 and 6 are the only listed states not using cut 2; both
their exterior words use $1\,7$. Thus every gluing survives.
This also checks survival for both packings in each local difference.

Let $c_i$ mean the **actual** union of its listed local anchor,
$y_{i,0}$ and the cut edges in $J_i$. These eleven anchors, including
all their edges and boundary data, are retained in
`uniform-attempt-02.json`. The words define them uniformly.

## 5. An explicit local basis and its nonzero minor

Let $\chi_A$ be a packing's incidence vector on the local internal
edges. Use the following $k-1$ differences:
$$
d_r=\chi_{6r}-\chi_{6(n-1)}\quad(1\le r<j),\qquad
u=\chi_{1a}-\chi_{1b},\quad
v=\chi_{4a}-\chi_{4b},\quad
w=\chi_{7Z}-\chi_{71}.
\tag{5.1}
$$
There are $j-1=k-4$ vectors $d_r$. Every difference has a common
compatible surviving partner, respectively
$y_{6,0},y_{1,0},y_{4,0},y_{7,0}$, from Section 4.
So every vector in (5.1) belongs to $L\cap\ker\pi$.

For a transparent coordinate calculation put
$$
h_i=T_iT_{i+1},\quad g_i=B_iB_{i+1}\ (0\le i<n),\quad
g_n=B_nB_0,\quad r_i=T_iB_i,\quad z=pq.
$$
The omitted internal edges of $6r$ are
$$
\{r_i:1\le i\le n,\ i\notin\{r,r+1\}\}\cup\{h_r,g_r,z\},
$$
for $r\in\{1,\ldots,j-1,n-1\}$.
This can also be read directly from its word.
For the other three differences their omitted sets are:

| Template | Omitted edges |
|---|---|
| 1a | $h_i$ for even $2\le i\le n-1$; $g_i$ for odd $1\le i\le j$; $g_n$ |
| 1b | $r_i$ for $2\le i\le n$; $g_0$ |
| 4a | $h_i$ for odd $1\le i<j$; $T_jp,r_{n-1},r_n,g_0$; $g_i$ for even $2\le i\le j-1$ |
| 4b | $r_i$ for $1\le i<j$; $T_jp,h_{n-1},g_n,g_j$ |
| 7Z | $h_i$ for odd $1\le i<j$; $T_jp,T_{n-1}q,g_0$; $g_i$ for even $2\le i\le n-1$ |
| 71 | $r_i$ for $3\le i\le n-1$; $h_1,g_1,g_n,z$ |

Take columns
$$
h_1,\ldots,h_{j-1},\quad h_{n-1},\quad z,\quad g_0.
\tag{5.2}
$$
The first $k-4$ rows have block $-I$ in the first columns and
last three entries $(1,0,0)$. Subtracting their appropriate multiples
from $u,v,w$ leaves, with $m=k/2$, the Schur block
$$
\begin{pmatrix}
1-m&0&1\\
3-m&0&-1\\
3-m&1&-1
\end{pmatrix}.
\tag{5.3}
$$
For example the first entry is just the sum of the top-edge
coefficients of the row, since each eliminated $d_r$ has coefficient
1 at $h_{n-1}$. Counting odd and even indices in the omitted-edge
table gives $1-m,3-m,3-m$ respectively; the $z,g_0$ entries are
displayed directly. This derives (5.3) for every $k$, without
interpolating any computed ranks.

The determinant of (5.3) is $4-2m=4-k$.
Since $k-4$ is even, the determinant of the whole minor is also
$4-k\ne0$. Hence (5.1) is an explicit independent local basis,
attaining the ambient dimension $k-1$.

### The base $k=6$ is explicit

Here $j=3,n=5$; $W_3=T_1B_1B_2T_2T_3B_3$ and
$V_3=T_1T_2B_2B_3T_3$.
The five rows are $d_1,d_2,u,v,w$ on
$h_1,h_2,h_4,z,g_0$, and their minor is
$$
\begin{pmatrix}
-1&0&1&0&0\\
0&-1&1&0&0\\
0&-1&-1&0&1\\
-1&0&1&0&-1\\
0&0&0&1&-1
\end{pmatrix},\qquad \det=-2.
$$
The path tables supply every base packing, with complete expanded
edge lists and partners in the retained certificate.

## 6. Nine independent actual projected directions

Use the 17 exterior coordinates (2.1), followed by the five cut
coordinates. Put $\bar c_i=\pi(c_i)$. Use, in order,
$$
y_{1,1}-y_{1,0},\quad y_{4,1}-y_{4,0},\quad
y_{4,2}-y_{4,0},
$$
$$
\bar c_1-\bar c_0,\quad\bar c_2-\bar c_0,\quad
\bar c_3-\bar c_0,\quad\bar c_4-\bar c_0,\quad
\bar c_5-\bar c_0,\quad\bar c_7-\bar c_0.
\tag{6.1}
$$
The exterior differences keep their respective listed local anchor
fixed; the other vectors are differences of the actual glued anchors.
No representative is freely moved or replaced by an abstract port vector.

On the exterior columns
$$
(1\,7,\ 1s,\ 2\,3,\ 2\,8,\ 3\,4,\ 4\,5,\ 5\,11,\ 6\,7,\ st),
$$
their minor is
$$
\begin{pmatrix}
0&0&1&-1&0&1&-1&-1&0\\
0&0&1&-1&-1&0&0&0&0\\
0&0&1&-1&0&-1&1&0&0\\
1&0&-1&1&0&-1&0&0&0\\
1&0&0&1&0&0&-1&0&0\\
1&0&0&1&-1&0&0&-1&0\\
1&-1&-1&1&0&0&-1&-1&0\\
1&-1&-1&1&0&-1&0&0&0\\
0&0&0&0&0&0&0&0&-1
\end{pmatrix},
\qquad \det=1.
$$
This fixed calculation is a finite exact certificate for the fixed
13-vertex exterior, valid for every $k$ because all required local
anchors have just been constructed uniformly. Cut coordinates,
although unnecessary for this minor, are retained in the full
22-coordinate projected vectors and all glued anchors.

By (3.2) the image rank is exactly 9. The local basis has zero
projection. Therefore any linear combination of lifts of the nine
directions lying in the local kernel has all nine coefficients zero.
This explicitly pays the kernel/image intersection cost. Together
the local and lifted image bases give $k+8$ independent survivor
differences. Since every cycle difference lies in $\ker B_k$, equality
follows. The full Hamiltonian difference space lies between $L_k$
and $\ker B_k$, so it too equals that space and $\ell_k=0$.
This proves Theorem U176.

## 7. Authentication, mandatory controls, and bounded validation

The full original I176 brief and `AGENTS.md` were read before work.
The immutable upstream contract, relevant catalogue entry, complete
manuscript-path listing for the result family and actual
`cor:pfaffian-paths` statement (local pinned manuscript lines 812–828)
were read. The inherited A175 uses that stipulated statement. U176
itself uses only the explicit graph constructions and rational algebra.

The supplied I175 detached report/seal/verifier hashes match:

| Object | SHA-256 |
|---|---|
| Report | `7df9e04e808e5f537eef1291b9f323ffd27dfb25c6edd4b76b34d8f23e198ff9` |
| Seal | `42636ad1d8a669c8bee23332d7059e0ba957c3467a343ea2b563fdf346905c31` |
| Verifier | `e09a4daaa655b9482cb3ac5686fce7e0555eb7d857b8d0ce77b063d184be101a` |

All **94 owned**, **399 non-context external**, and **four context**
entries are accounted for, including complete owned membership and
the successful-prevalidation/control chain. Four contexts make 403
external/context entries. Parent disposition, precheck, replay,
verification, certificate and integration receipts are bound.
The parent replay's **16.19692463602405 seconds**, five byte-identical
payloads, eight blocked probes and empty stderr are authenticated
history, not an I176 replay time.

**Context limitation retained.** I175's exact current-context assertion
predates integration. All four current ledgers differ from that
inventory. Its parent records historical recoverability at
`0cb1adce63798d0cc88db2a33bb3e4e91bb9228f`; no historical reconstruction
or ancestor execution was attempted here. No sealed evidence was edited,
no live ledger rolled back. I176 records those historical hashes but
requires only current context-byte stability during its own replay.
All non-context mathematical bindings remain strict.

Ancestor Python was hashed as opaque evidence only, never executed,
imported or copied as implementation. All code is fresh standard-library
Python run under `-I -B`. The first controls completed the required
indices in order:
`0,520,522,524,527,528,530,533,534,536,539,431`,
then C171, I172 G6/G10, and the first I175 P8 child with its complete
five-port certificate, **before** new-parameter work.

Fresh checks include complete seven-family comparisons on these
targeted controls; prescribed-degree enumeration versus independent
rooted Hamiltonian DFS; gcd-normalized integer rank versus reverse-pivot
exact Fraction rank; actual $b,\beta,c$, alternating arc vectors,
compatible-old families and residual-minus-anchor sets; and
$$
U=V_{\rm good}+R,\qquad
\ell-t=\delta_V+\epsilon-\delta_R.
$$
The bridge displacement lies in $L$, and $b,\beta$ give identical
bridge increments. $\rho(L)=\mathbb Q^2$ and both failed $V$ containments
at index 431 are reproduced. C171's actual pre-switch Hamiltonian
cycle is reconstructed from F and the prescribed square; the functional
gives **$F=1/14$ and distinct $T=-1/2$**, both two-component 2-factors.
All **1,032 C171** and **900 first-P8** retained matching extensions
are checked coordinatewise with complete disjoint-pair coverage.
This is a targeted audit, not a repeated historical population search.

The first-surgery finite checks are:

| $k$ | Product survivors | Local rank | Exterior within-state rank | Anchor increment | Image rank | Extra anchor kernel | Survivor rank |
|---|---:|---:|---:|---:|---:|---:|---:|
| 4 | 26 | 1 | 3 | 8 | 9 | 2 | 12 |
| 6 | 30 | 5 | 3 | 6 | 9 | 0 | 14 |
| 8 | 34 | 7 | 3 | 6 | 9 | 0 | 16 |
| 10 | 38 | 9 | 3 | 6 | 9 | 0 | 18 |
| 12 | 42 | 11 | 3 | 6 | 9 | 0 | 20 |

The existing $k=4,6,8$ cases were reconstructed. Only **$k=10,12$**
were newly checked, not a larger census. For these parameters, fresh
complete local/exterior packing enumeration agrees exactly with the
full survivor family. Closed words are independently checked against
their explicit omitted-edge formulas, degrees, vertex coverage,
endpoint pairings, common partners and surviving glued anchors.
The local minors are $-2,-4,-6,-8$; all four image minors are 1.
The count pattern is **not claimed as a uniform enumeration theorem**;
the uniform rank theorem rests on the formulas and proof above.

## 8. Retained failures and sealed replay protocol

Inherited I175 `rankUV` and mixed-coordinate implementation failures,
their failed source stages, empty JSON and errors, the rejected rotation,
and the I174 pre-seal document transition remain bound unchanged.
They are not mathematical counterexamples.

Three I176 development issues are retained:

1. An ordering-based selector chose $7Z$ itself as the alleged $71$
   at $k=8$, making their difference zero and leaving rank 6 instead
   of 7. The missing $pq$ direction, exact state/parameter, source,
   stdout and empty stderr are retained. The final formula defines
   $71$ by its actual edge set, independently of ordering.
2. A schema-inspection command requested `brace.witnesses` rather than
   `brace.extensions`; its source and original combined error/output
   capture are retained. This was not a mathematical diagnostic.
3. `mandatory-attempt-03` assumed C171's functional reference $C_0$
   was its pre-switch cycle. It is not. The empty payload, assertion
   stderr and source stages remain. The corrected check reconstructs
   the actual pre-switch cycle and keeps $C_0$ only as the functional
   reference. The prescribed F and generic T were never identified.

The authoritative package is
`frontier/experiments/i176_uniform_five_port_rank/`, with literature
receipt in `frontier/sources/i176_uniform_five_port_rank/`.
The complete inventory binds every source, input, output, failed stage,
empty capture and this report before final diagnostic replay.
Inventory, prevalidation and seal are the non-self-hashed controls;
the final read-only replay emits its receipt to stdout.

The verifier authenticates bytes into immutable memory before compiling
only exact owned implementation bytes. Historical source stages and all
ancestor executables remain opaque. Deterministic mandatory, finite,
and uniform-certificate payloads must be byte-identical to the retained
successful payloads. Eight probes must block write, mutation, network,
subprocess, unbound read, outside compilation, outside execution and
forged bytes under an owned filename. Before/after checks cover every
mathematical binding, control, complete owned membership and the current
four context ledgers. The order is inventory, successful prevalidation,
**one exclusive seal**, read-only replay. Never reseal.

Replay:

```text
python3 -I -B /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/experiments/i176_uniform_five_port_rank/verify176.py
```

Detached report/seal/verifier hashes, final counts and actual runtime
are returned separately to avoid self-reference. The Python audit guard
is not OS sandboxing; interpreter/standard-library behavior is a runtime
dependency. Clean-clone reconstruction was not tested.

## 9. Original scopes, contribution limits, and next action

I175's finite P8 scope stays exactly two of fourteen valid first triples:
order 26/loss 3 before surgery, then two order-30/rank-16/loss-zero
braces, 900 matchings each, with protected **(3,1) hexagons**, not
high-loss octagons. Twelve valid triples remain untested. No second
attachment or surgery was performed here.

The general five-port product/anchor formula is retained with its actual
states. M175 still requires complete exterior-controlled fibres and
the restricted full exterior family $H_T$:
$\ell_G=\ell(H_T,S_H)+\dim K_T-\dim K_I$ for actual within-type sums.
Its cube losses 4 to 6, incomplete-fibre dimensions 8/5, and nonbipartite
K4 proper-subset equal-kernel example remain only in their original
scopes. All three types are sufficient, not logically necessary.
A175 still requires its actual protected local geometry; the 720 finite
checks do not become a remote-interface theorem.

D168's bidirectional-transfer obstruction, M168's failure of typed
fullness, $\rho(L)=\mathbb Q^2$, failed $V\subseteq U$ and
$V\subseteq L+U$, isolated-cycle toggle failures and C171's $F\ne T$
remain binding. S172 remains remote-only; S174/M175 do not cover
cut-breaking surgery. U176 bypasses none of those objections.

The new theorem closes the unpaid uniform rank step only for the
specified first surgery. It rules out a high-loss result there, even
at untested large $k$. Literature queries and primary leads are recorded,
but returned snippets are not full proof reads, and no literature
priority or independent contribution-gate clearance is claimed.
**No acceptance increment.** High-loss braces, universal coefficient
exclusion, the lower bound, exchange, (T), and Q164 remain open.

**One bounded next action, not executed:** keep $k=8$ and test the
previously untested `[0,0,10]` operation, whose actual deleted edges are
$1\,2$ and $a_1a_2=13\,14$. Moving the attachment surgery adjacent
to port 0 changes the local path templates, so U176's particular
minor does not apply. Rebuild its actual five-port states and rank
decomposition, including anchor-kernel relations; retain it as a
candidate only if loss is positive before considering any attachment.
This is an escape from the **scope of the proved obstruction**, not
a prediction of high loss or an excuse for a larger-prism sweep.
