# I177: adjacent-port surgery is saturated by two anchor-kernel directions

2026-10-11. **Technical obstruction, not a ninth nomination. Eight accepted
findings remain eight; two remain.** All OpenAI results at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true.

## 1. Outcome and exact scope

The sole newly tested surgery is `[0,0,10]` on the **initial** I175
affected-P8 exterior, with vertex 7 still contracted. Its actual removed
edges are $1\,2$ and $13\,14$. The resulting order-30 graph is a brace:
all **900** disjoint edge pairs have explicit perfect-matching extensions.
It has **64** Hamiltonian cycles, **46** protected survivors, and
$$
d=16,\qquad \dim L=16,\qquad \ell=0.
$$
The protected interface remains the **(3,1) hexagon**
$[1,13,21,20,6,7]$, with protected deletions $20\,6$ and $1\,7$.
It is not a target octagon.

Its actual five-port decomposition has
$$
(\dim W_X,\dim W_Y,\text{anchor increment})=(5,3,8),\qquad
\dim\pi L=9.
$$
Two independent actual anchor relations add the missing local-kernel
directions. Thus lowering within-state local rank from 7 to 5 does
**not** preserve defect. All three old quotient directions are absorbed;
explicit transport and absorption coefficients appear in Section 6.

The graph is not even unmarked-isomorphic to either previously tested
P8 child: it has **10 four-cycles**, while each has 9. Complete marked
isomorphism checks also return none. No symmetry or U176 extension is
invoked to establish this outcome.

Only one new operation was executed. No larger parameter, other triple,
second attachment, or second surgery was tested. Three of the original
14 triples have now been tested across I175 and I177, leaving **11**
untested. This does not exclude those choices or all prism gadgets.

## 2. Source contract and byte authentication

The full finalized I177 assignment, AGENTS.md, original I176 assignment,
original I176 report and full written proof, and parent disposition were
read. The immutable source contract, catalogue family 180, complete
manuscript-family listing, and actual `thm:main`,
`cor:edge-avoidance`, and `cor:pfaffian-paths` statements were checked.
The last statement's finite/simple/cubic/3-connected/bipartite/Pfaffian
hypotheses remain intact. It supplies the inherited A175 path argument;
the present exact finite construction needs no stronger upstream claim.

The supplied I176 report, seal, and verifier SHA-256 anchors match:

| Object | SHA-256 |
|---|---|
| Report | `e5cf0be3222c1b60152659e968a1ce571832b243c40e3adceb3514b2d7324721` |
| Seal | `72560bdafd354f0e0e5cb405a032fa6eb72f2b4e6f92c6a1ec6c3736d3fdc22b` |
| Verifier | `ff1f84ec5853c22c7e37f5049ff80deda9a02578563cb7b14ed82c338cf22ec0` |

All **59 owned**, **507 strict external**, and **four context** entries
authenticate, with complete owned membership and the full
inventory/successful-prevalidation/seal chain. Contexts bring the
external/context total to **511**. The original parent disposition,
all available `i176-parent-*` sources/receipts/failures, the later final
integration receipt, and task archives are strict bindings in the I177
inventory. Ancestor Python is opaque hashed evidence, never imported,
executed, or copied as implementation.

The authenticated parent replay took **2.02917855407577 seconds**, with
three byte-identical payloads, eight blocked probes, empty stderr and
unchanged bindings. Its independent DFS/Fraction checker exhausted the
five retained products at $k=4,6,8,10,12$ and checked 96 words/minors/
anchors. The dispatch separately records a live-context preflight of
**1.9975806439761072 seconds**; the subsequently available final
integration receipt records another passing replay of
**1.9835700179683045 seconds**. These are distinct historical runs, not
I177 runtimes.

All four current context ledgers differ from I176's inventory. I177
records the historical drift but freezes their **current** bytes across
each replay. Only the four named ledgers are context exemptions.
I175's historical-context replay limitation is not retroactively fixed;
no ancestor bytes or live ledger were rolled back, and no historical
clean-clone reconstruction was tested.

## 3. Independent original-scope U176 verdicts

### 3.1 Graph, actual edges, orientation: PASS uniformly

For every even $k\ge6$, set $n=k-1$, $j=k-3$,
$T_i=12+i$, $B_i=12+k+i$. The original oriented large face starts
$$
[1,2,3,4,5,T_n,T_{n-1},T_j,\ldots,T_1].
$$
Its positions 0 and 6 are exactly $1\,2$ and $T_{n-1}T_j$.
It is first in the stated orientation-preserving lexicographic order:
the other faces at minimum vertex 1 next visit 7 or $T_1$, not 2.
The square replaces the two facial darts with the stated noncrossing
attachment, with $1s,2t,T_jp,T_{n-1}q,st,sp,tq,pq$.
The two split faces and reverse-side subdivisions preserve dart
opposition and cyclic links. The protected hexagon is untouched.

The counts are $2k+14$ vertices, $3k+21$ edges, $2k+1$ local vertices
and $3k-1$ local internal edges. Bottom-cycle connectivity, surviving
rungs, and the replacement path through $p,q$ establish local
connectivity; the fixed exterior joins through the five distinct ports.
The parity coloring extends over the square. These arguments depend on
indices, not finite interpolation.

### 3.2 Uniform path words and actual partners: PASS

The original closed words were independently expanded from their
formulas, not selected by witness order. In $W_j$, odd/even blocks
partition columns $1,\ldots,j-1$, then append column $j$. In $V_j$,
the same blocks use every top index $1,\ldots,j$ and bottom indices
$2,\ldots,j$ exactly once. Inter-block joins are respectively top
edges and rungs. The displayed tails use precisely the remaining
indices. For $6r,7r$, the split at $r,r+1$ partitions the rails;
the special $6(n-1)$ row does not cross the missing top edge.
Every other join is a rung, surviving rail edge, bottom wrap edge,
or replacement edge through $p,q$.

This proves adjacency, coverage, no repeats and no isolated cycles
for every allowed index. Endpoint reading gives the eleven actual
states. Each of the fourteen fixed exterior words uses all thirteen
exterior vertices once. The four-port pairings differ, so gluing
produces one cycle. Only states 2 and 6 omit cut 2; their exterior
partners use $1\,7$. The paired local witnesses share the same
compatible **surviving** exterior partner.

The fourteen partners are sufficient subfamilies, not exhaustive
families. The parent's failed equality assertion at state 5, and
the additional partners at states 9 and 10, do not change this proof.
The failed source, empty stdout, and reproduced assertion stderr
remain bound. I177 checks the actual listed partner prefix separately
from complete-product exhaustion.

### 3.3 Realized local rank and parity minor: PASS uniformly

Use the original differences
$d_r=\chi_{6r}-\chi_{6(n-1)}$ for $1\le r<j$,
$u=\chi_{1a}-\chi_{1b}$,
$v=\chi_{4a}-\chi_{4b}$,
$w=\chi_{7Z}-\chi_{71}$.
They have common surviving partners in states 6,1,4,7 respectively.
The omitted-edge sets were checked independently against the closed
words and the written formulas.

On $h_1,\ldots,h_{j-1},h_{n-1},z,g_0$, the $d_r$ block is $-I$
with tail $(1,0,0)$. Write $m=k/2$. There are $m-2$ odd and
$m-2$ even indices below $j$. The $u$ row has $-1$ at even
indices and tail $(-1,0,1)$; $v$ has $-1$ at odd indices and
tail $(1,0,-1)$; $w$ has $-1$ at odd indices other than 1 and
tail $(0,1,-1)$. Elimination gives
$$
\begin{pmatrix}1-m&0&1\\3-m&0&-1\\3-m&1&-1\end{pmatrix},
\qquad \det=4-2m=4-k.
$$
The $-I$ order $k-4$ is even, so this is also the entire minor's
determinant. It never vanishes in the claimed range. At $k=6$ the
five explicit rows on $h_1,h_2,h_4,z,g_0$ are
$$
\begin{pmatrix}
-1&0&1&0&0\\0&-1&1&0&0\\0&-1&-1&0&1\\
-1&0&1&0&-1\\0&0&0&1&-1
\end{pmatrix},\qquad\det=-2.
$$
This is an analytic parity proof for all even $k\ge6$, not an
inference from the observed determinants at four parameters.

### 3.4 Nine actual image directions and independence: PASS uniformly

The three specified exterior differences and six differences of
the specified **actual glued** anchors reproduce the fixed $9$ by $9$
minor with determinant 1. I177 rebuilds each full anchor from its
local word, actual exterior packing and cut set before projection.
An enumerator's first anchor need not equal the proof's chosen
anchor; neither may be freely translated.

The local connected bipartite incidence rank is $2k$, giving
zero-projection kernel dimension $(3k-1)-2k=k-1$. Globally the
incidence rank is $2k+13$, so the kernel dimension is $k+8$ and
its projected image has dimension 9. The local basis has zero
projection; independence of the nine images makes their lifts
independent modulo that kernel. The realized $k+8$ directions
attain the ambient bound. Thus the unchanged written U176 proves
$L=\ker B$, $\dim L=k+8$, $\ell=0$ for **every even $k\ge6$**,
without typed fullness.

### 3.5 Exceptional parameter and limits: PASS in separate finite scope

Fresh complete $k=4$ packing products give local rank 1, image rank 9,
and two additional anchor-kernel directions, for total rank 12 and
loss zero. The uniform local-basis formula does not apply there.
I177 reconstructs the required $k=6$ product and checks the retained
96 closed words, omitted sets, partners, anchors and minors at
$6,8,10,12$; it adds no parameter values. The parent's broader five-case
product exhaustion remains authenticated history, not a newly repeated
population census. Neither U176 nor this audit proves uniform brace
status or a uniform cycle-count formula.

## 4. Mandatory controls and independent methods

Before the new surgery, fresh diagnostics ran in the exact order
`0,520,522,524,527,528,530,533,534,536,539,431`,
then C171, I172 G6/G10, the first I175 P8 child and its five-port
certificate, and I176's $k=6$ local/image proof certificate.

Complete seven-family sets were independently regenerated, not
accepted from stored dimensions. Prescribed-degree edge enumeration
is checked against independent rooted vertex DFS for Hamiltonian
cycles and single paths. Ranks use primitive integer row elimination
and separate reverse-order exact Fraction elimination on the transpose.
The actual sorted-coordinate $b,\beta,c$, all residual-minus-anchor
vectors, and prior bridge displacements are checked, including
$$
U=V_{\rm good}+R,\quad
\ell-t=\delta_V+\epsilon-\delta_R,\quad
b-\beta\in L,\quad \rho(L)=\mathbb Q^2.
$$
Every retained seven-family control agrees exactly with its original
vectors and residual data. The ten high-loss indices give
$(\ell,t,\eta)=(7,6,1)$; 0 and 431 give $(1,0,1)$.
At 431 the retained separator annihilates $L+U$, evaluates to 10
on the actual bridge, and has absolute value 8 on the old direction.
Both $V\subset U$ and $V\subset L+U$ fail; every compatible-old
family is empty.

C171's pre-switch cycle is reconstructed from its actual $F$ and
the prescribed square, not identified with the distinct functional
reference. Exact values remain $F=1/14$ and $T=-1/2$, for distinct
two-component factors. All 1,032 C171 and 900 first-P8 matching
extensions are checked with complete disjoint-pair coverage.
G6/G10 retain losses 3/7. No entire ancestor census or ancestor
implementation was executed.

## 5. The single new graph and complete product certificate

The rebuilt initial graph agrees exactly with I175, including the
original oriented face
$$
[1,2,3,4,5,19,18,17,16,15,14,13].
$$
Positions 0 and 10 give directed edges $1\to2$ and $14\to13$.
With $(s,t,p,q)=(28,29,30,31)$, the replacement edges are
$$
1s,2t,13p,14q,st,sp,tq,pq.
$$
The split faces are $[1,28,30,13]$ and
$[2,3,4,5,19,18,17,16,15,14,31,29]$. Reverse-side subdivisions
and $[28,29,31,30]$ complete the sphere rotation.
The certificate checks every directed dart, every vertex link, Euler
characteristic two, cubic bipartiteness, and connectivity after every
two-vertex deletion.

Put $X=\{13,\ldots,27,30,31\}$ and
$Y=\{1,\ldots,11,28,29\}$. The five ports in fixed label order are
$$
0:1\,13,\quad1:5\,19,\quad2:6\,20,\quad3:28\,30,\quad4:29\,31.
$$
There are 23 local internal and 17 exterior internal edges.
Both sides have distinct cut endpoints. All ten two-port and five
four-port used sets are enumerated, including empty packing families.
Packings must span their side, have the exact endpoint degrees and
no isolated cycle. A product survives exactly when it uses port 2
or its exterior packing uses $1\,7$.

The complete nonempty surviving states are as follows. Counts refer
to the full actual families, not the fourteen U176 sufficient witnesses.

| State | Used ports | Local pairing | Exterior pairing | Local | Exterior |
|---|---|---|---|---:|---:|
| 0 | 02 | 02 | 02 | 1 | 1 |
| 1 | 12 | 12 | 12 | 2 | 2 |
| 2 | 14 | 14 | 14 | 1 | 1 |
| 3 | 24 | 24 | 24 | 1 | 1 |
| 4 | 0123 | 02,13 | 03,12 | 2 | 3 |
| 5 | 0123 | 03,12 | 02,13 | 5 | 2 |
| 6 | 0134 | 03,14 | 01,34 | 5 | 1 |
| 7 | 0234 | 02,34 | 03,24 | 1 | 1 |
| 8 | 0234 | 03,24 | 02,34 | 1 | 1 |
| 9 | 1234 | 12,34 | 14,23 | 5 | 2 |
| 10 | 1234 | 14,23 | 12,34 | 2 | 3 |

Their disjoint products contain exactly 46 survivors, equal to the
independently enumerated global family. Connectivity of the union
of endpoint pairings is checked for every product.

| Graph | Seven counts $00,10,01,11,P,Q,D$ | $d$ | $\dim L$ | $\ell,t,\eta$ | $\delta_V,\delta_R,\epsilon$ |
|---|---|---:|---:|---|---|
| Initial | 18,2,6,6,6,18,6 | 14 | 11 | 3,2,1 | 0,0,1 |
| Adjacent child | 18,2,6,38,36,18,36 | 16 | 16 | 0,0,0 | 0,0,0 |

For the child, $\dim L_0=14$, $\dim U=\dim(U+V)=10$.
The $(|\mathcal F_J|,|\mathcal R_J|)$ counts for $P,Q,D$ are
$(0,36),(18,0),(0,36)$. Exact bridge, balanced bridge, cross-class
offset, compatible families, all residual vectors and actual anchors
are retained, not only these dimensions.

Brace status is established by **900 actual extending matchings**,
with no failed pairs, not by 3-connectivity or absence of a visible cut.

## 6. Actual bases, anchor corrections, and absorption

All vectors below use the child's sorted 45-edge order stored in
`experiment-attempt-03.json`. Within each state, local/exterior
packings are in lexicographic incidence-vector order. Set
$c_i$ to its actual first glued product and $A_i=c_i-c_0$.

Choose $X_1$ from local packing 1 minus 0 in state 1, and
$X_2,\ldots,X_5$ from local packings 1,2,3,4 minus 0 in state 5.
Choose $Y_1$ from exterior packing 1 minus 0 in state 1, and
$Y_2,Y_3$ from exterior packings 1,2 minus 0 in state 4.
Every difference has a retained common surviving partner.
These have ranks 5 and 3 on disjoint supports.

The actual image basis consists of
$$
\pi Y_1,\pi Y_2,\pi Y_3,\pi A_1,\pi A_2,\pi A_3,
\pi A_4,\pi A_5,\pi A_7.
$$
Two actual relations have zero projection:
$$
K_1=A_6+A_1-A_2-A_5,\qquad
K_2=A_8+A_1-A_3-A_5.
$$
Their complete 45-coordinate vectors and the defining lift relations
are retained. Independent exact ranks give
$$
\dim\langle X_1,\ldots,X_5,K_1,K_2\rangle=7.
$$
Since that is the whole local ambient kernel, adding the nine
independent image lifts gives the explicit survivor-space basis
$$
\mathcal B=(X_1,\ldots,X_5,Y_1,Y_2,Y_3,
A_1,A_2,A_3,A_4,A_5,A_7,K_1,K_2).
$$
This pays the anchor quotient, the additional kernel, and the
kernel/image intersection separately.

An independent basis of **16 actual survivor-minus-common-anchor
vectors** is also retained in `child.survivor_basis`, together with
the common survivor. Its columns
`0,1,3,4,6,8,10,12,19,21,24,26,28,30,33,41`
have determinant **2**. Thus an actual-cycle certificate, independently
of the decomposition, attains the ambient bound
$45-(30-1)=16$. Therefore $L=\ker B$ and $d=\dim L=16$.

### Explicit convention for transporting the old defect

This is an ambient linear injection, **not** an assumed lift of every
old Hamiltonian cycle. For an old incidence-kernel vector $r$, write
$a=r_{12}$ and $b=r_{13,14}$. Keep every surviving old coordinate;
give the arms $1s,2t$ value $a$, arms $13p,14q$ value $b$,
and give $(st,pq,sp,tq)$ values $(-a,-b,0,0)$. Call this map
$\tau$. At each new vertex the sum is zero, and the old vertex sums
are unchanged. The arms recover the deleted coordinates, so $\tau$
is injective on the old ambient kernel.

The certificate selects actual old Hamiltonian differences $D_1,D_2,D_3$
by augmenting the old survivor basis in lexicographic cycle order.
Their classes form a basis of the old three-dimensional quotient.
Their complete old vectors and transported vectors are retained.
Writing $Z_i=\tau D_i$, the following exact coordinate relations hold:
$$
\begin{aligned}
Z_1={}&\tfrac{25}{6}X_1-\tfrac56(X_2+X_3+X_4+X_5)
-3Y_1+Y_2+Y_3\\
&+A_1+A_2-2A_3+4A_4-5A_5+A_7
+\tfrac56K_1-\tfrac56K_2,\\
Z_2={}&Z_1+Y_2,\qquad Z_3=Z_1+Y_3.
\end{aligned}
$$
Thus the old quotient basis has no surviving child quotient direction.
Two pairwise differences are paid directly by exterior variations;
the remaining displayed direction is absorbed by local, actual anchor,
and the two extra anchor-kernel directions. This does not assert an
unsupported natural map of quotient spaces under surgery.

## 7. Isomorphism, escape requirement, and one next action

The new graph has 10 four-cycles; each previous P8 child has 9.
This elementary unmarked invariant already forbids graph isomorphism.
Complete finite backtracking also tests isomorphisms preserving the
two protected edges individually, the X/Y partition, and all five port
labels; none exists. Hence this is not a disguised tested case, and
the new result is finite, not a symmetry application of U176.

**Concrete structural escape requirement.** In a prospective construction
with independently established $d=16$ and the same nine-dimensional
survivor image, loss at least two requires the entire survivor kernel
to have dimension at most five. Merely lowering $\dim W_X$ to five
is insufficient. Both independent anchor corrections above must cease
to contribute modulo $W_X$, and no other actual anchor relation or
within-state direction may replace them. More generally the required
deficit must occur in the total actual kernel plus image, not in a
local rank considered in isolation.

**One bounded next action, not executed:** analyze the compatibility
equations of these eleven five-port states with this fixed 13-vertex
exterior, to determine which complete local fibres would permit a
two-dimensional survivor annihilator after *all* actual anchor
relations are included. Require actual packings and complete
exterior-controlled products, and pay the full-cycle dimension
separately. This is a fixed-interface algebraic feasibility problem,
not another triple sweep or a second attachment to a zero-loss graph.
Only a realizable deficient state system would justify a later gadget
construction.

## 8. Failures, final replay contract, and contribution limits

The I177 development failures are retained in `failures.md` with
exact disabled source stages, empty stdout, stderr and receipts:
template spelling `6r1`; confusing the proof anchor with the first
enumerated anchor; and JSON serialization of exact Fraction basis
entries. They are checker/schema issues, not mathematical repairs.
The inherited I176, parent, I175 and I174 errors, rejected embeddings,
empty captures and pre-seal transition remain strict evidence.

Final code is fresh standard-library Python under `-I -B`.
All sources, inputs, outputs, attempts, failures, literature receipt
and this report enter a complete immutable-first inventory **before**
final diagnostics. Only inventory, successful prevalidation and seal
are non-self-hashed controls. Final replay compiles only exact
authenticated owned implementation bytes from immutable memory.
Historical stages and all ancestor Python remain opaque.

The final sequence is complete inventory, successful prevalidation,
one exclusive seal, then read-only replay. Eight live probes block
write, filesystem mutation, network, subprocess, unbound read, outside
compilation, outside execution, and forged bytes under an owned
filename. Three deterministic payloads (mandatory, audit, experiment)
must be byte-identical. Strict mathematical bytes, control bytes,
complete membership and current context bytes are checked before and
after. No resealing is permitted. The Python audit guard is not an OS
sandbox; clean-clone reproduction was not tested.

Replay:

```text
python3 -I -B /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/experiments/i177_adjacent_port_surgery/verify177.py
```

Exact report/seal/verifier hashes, inventory counts and measured final
runtime are returned detached, avoiding circular self-hashes.

The literature receipt records actual primary leads and clearly labels
returned snippets rather than full proof reads. No literature priority
or contribution-gate clearance is claimed.

D168 bounded bidirectional transfer and M168 typed fullness remain
false; $\rho(L)=\mathbb Q^2$ and the two failed V containments remain
binding; binary toggles can isolate cycles; C171's prescribed F is not
generic T. S172 is remote-only. S174/M175 require complete
exterior-controlled fibres and the restricted full exterior
$\mathcal H_T$; the exact formula remains
$\ell_G=\ell(\mathcal H_T,S_H)+\dim K_T-\dim K_I$.
Cut-breaking surgery is outside that transport statement.
A175 retains its exact local geometry, and its 720 checks stay finite.
I172 high-loss octagons remain non-braces; I173's 212 braces remain
loss zero. Universal coefficient exclusion, the nonvacuous lower
bound, exchange, (T), Q164 and a high-loss-brace construction are
**open**. No acceptance increment follows from this obstruction.
