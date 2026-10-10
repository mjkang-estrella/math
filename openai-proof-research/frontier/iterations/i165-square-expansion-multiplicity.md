# I165: square-expansion monotonicity is false

2026-10-10. Independent Factory/Astra research sub-agent report.
**Research, not acceptance. Eight accepted findings remain eight.**

## 1. Outcome

The universal all-step inequality

$$
\tag{M} P_{ux}+P_{vy}+D_{11}\ge N_{00}+2
$$

is **FALSE in the exact original class and admissible expansion contract**.
A fully encoded, independently counted example has

| Quantity | Value |
|---|---:|
| Old/new orders | 50 / 54 |
| Old/new Hamiltonian-cycle counts | 576 / 572 |
| $N_{00}$ | 138 |
| $P_{ux},P_{vy},D_{11}$, in the final encoding | 52, 38, 44 |
| Replacement sum | 134 |
| Expansion gain | −4 |

Both graphs are finite, simple, cubic, bipartite, planar and
3-vertex-connected. The removed edges share a certified face, have four
distinct terminals, and leave odd residual paths. Cycles are unoriented
edge sets. This is not a nonplanar, disconnected, or wrong-parity example.

More generally, the same finite base construction, spliced with the even
prism $L_m$, gives an explicit family, for every even $m\ge4$, with

$$
|V(G_m)|=2m+30,\quad
h(G_m)=62m-44,\quad h(G'_m)=54m+32.
$$

Consequently the gain is $76-8m$, negative for every even $m\ge10$
and unbounded below. The family formulas use an exact finite
computer-assisted base count and a proved splice bijection, not
extrapolation from several numerical examples.

**Q164 remains unproved and unrefuted:**
$h(G)\ge |V(G)|/2+2$ for every graph in the original class.
The example has far more cycles than that bound. Refuting (M) only
refutes the proposed all-step induction. It neither demotes all of Q164
to a routine consequence nor establishes its literature novelty.

Additional paid bridges:

* If either residual boundary path has length one, an explicit
  recoverable bijection proves (M).
* The Hamiltonian-cycle affine dimension satisfies an exact splice
  formula, developed in §6. It reduces the full affine-span route to
  cyclically 4-edge-connected pieces, without assuming local coverage
  gives linear independence.
* The counterexample's two graphs still have full affine dimensions
  26 and 28. Thus this particular obstruction does not obstruct that
  genuinely different global route.

## 2. Original-scope audit, without repairs to I164

### Premises, reading, and coverage

All OpenAI results **and lower proof operations** at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true.
No upstream truth audit, contradiction exploitation, or ex-falso
reasoning was performed.

I read the complete ORIGINAL I164 report, lines 1–571, its original task
summary, the project instructions, upstream pin, requested current ledger
openings, and the parent receipt. The task summary explicitly is not
the full original dispatch; I do not claim to have retrieved that dispatch.

I read family 180's actual `upstream-paper.tex`, lines 1–838, including
the statements and proof endings of `thm:partition`, the state/forest
operations, separating-triangle assembly, `cor:edge-avoidance`, and
`cor:pfaffian-paths`; its references, lines 1–151, were also read.
The actual operative stronger contract is: every three-edge path in a
finite simple cubic 3-vertex-connected Pfaffian bipartite graph extends
to a Hamiltonian cycle. Planar members qualify.

GSW's actual primary text, lines 288–1097, was read, including
Theorems 4.16 and 5.1, tight-cut contractions, splice/trisum operations,
and the precise square definition at 677–686. HMM is a scanned PDF:
I rendered and visually read printed pp. 280–284 and 294–296.
In particular, printed p. 281 shows reductions $R_0,R_4$ and p. 294
contains Theorem 4 and its complete proof. Empty extracted text was not
used as evidence. Theorem 4 says every member of order greater than
eight has a class-preserving $R_0$ or $R_4$ reduction; reversing them
generates the class from the cube. It does not assert counting
monotonicity or $N_{00}\le1$. GSW restates exactly this generation
contract. I did not recursively audit HMM's cited earlier lemmas.

`reading-ranges.json` records exact reading coverage. BKN's primary text
80–324 was read for its four/six-cycle baseline and the explicit
limitation on repeated switching. No exhaustive corpus/companion
semantic review is claimed.

### Verdict table

| Original assertion/interface | Independent verdict |
|---|---|
| Proposition P, even-prism exact count and graph-class membership | **PASS ORIGINAL**, no repair |
| Proposition E, square-expansion identity | **PASS ORIGINAL**, no repair |
| Three source-$P_4$ positivity statements | **PASS ORIGINAL**, no repair |
| Splice identity, cube doubling, restricted $N_{00}\le1$ induction | **PASS ORIGINAL**, no repair |
| Use of HMM/GSW for structural generation | **PASS in stated scope**; no counting conclusion supplied |
| Affine dimension and constant-weight criterion, I164 §4.4 | **PASS as a sufficient criterion**, not its unproved universal premise |
| Original signed-state Proposition S and bipyramid state enumeration | **NOT independently audited**; not used here |
| Original Q164 | **GAP**, unchanged |
| Original unpaid conjectural (M) | **REFUTED here**; not an originally proved theorem being repaired |

Reading the signed-state source is not a verdict on I164's new
Vandermonde/injectivity argument. No signed-state deduction is used
to prove the counterexample or the affine splice result.

### P: terminal cases and counting convention

In $L_m=C_m\square K_2$, $m\ge4$ even, the used rungs have endpoint set
$S$ on each rim. Omitted rim edges are perfect matchings of the induced
cyclic runs of $S$. If $S$ is proper and nonempty, every run is even
and its omission matching is unique on both rims. Removing $r$ common
rim edges gives $r$ ladder-boundary cycles, so connectedness forces
$r=1$. These are the $m$ cycles $H_i$. If $S=\varnothing$, there are
two components. If $S$ is all columns, the two equal omission matchings
give $m/2$ squares, while the two unequal choices give two spanning
cycles. This remains correct at $m=4$. Hence $h(L_m)=m+2$.
The original two-deletion connectivity argument proves 3-connectivity;
the standard nested-rim embedding and coloring by rim parity with
opposite colors across rungs prove the remaining class conditions.
No orientation or starting-point factors enter this count.

### E: complete arm classification

Use I164's names and cyclic boundary order
$u,v,\ldots,y,x,\ldots,u$. The bipartition has $u,y$ in one
class and $v,x$ in the other. Put $p,s$ opposite $u,y$, and
$q,r$ opposite $v,x$. The arms and all four square edges therefore
join opposite classes. The odd residual paths have endpoints
$(v,y)$ and $(x,u)$, precisely as required by GSW, not $(u,y)$.

A Hamiltonian cycle in the expanded graph crosses the four-arm cut
in two or four edges, never zero. With two arms it uses the unique
spanning square path between adjacent corners. The four allowed
terminal pairs give $N_{10},N_{01},P_{ux},P_{vy}$, each with fibre
size one. Opposite corners cannot be the endpoints of a spanning
path on four square vertices.

With all four arms, the exterior consists of two spanning disjoint
paths and no cycle component, because the whole object is connected.
For four cofacial terminals, $(u,y),(v,x)$ is the crossing pairing
in the disk outside the face and is impossible. Boundary arcs can be
pushed slightly into that disk, so use of other facial edges does
not invalidate this Jordan-curve argument. Of the two remaining
pairings, $(u,x),(v,y)$ recovers an old Hamiltonian cycle using $e,f$;
$(u,v),(x,y)$ recovers exactly two cycles with $e,f$ on different
components. Exactly one square perfect matching joins either exterior
pairing into one cycle. Restriction and insertion are inverse.
Thus

$$
h(G')=N_{10}+N_{01}+N_{11}+P_{ux}+P_{vy}+D_{11}
     =h(G)-N_{00}+P_{ux}+P_{vy}+D_{11}.
$$

The decisive diagnostic checks equality of the **complete sets** in
all six bijection fibres, not just this scalar identity.

For completeness, the expansion preserves 3-connectivity directly.
With no new vertex deleted, each surviving old edge $e,f$ can be
replaced by a route through the connected square after at most two
old deletions. With two new deletions, $G-e-f$ is connected by
3-edge-connectivity, and each remaining square vertex has its arm.
With one new and at most one old deletion, if the old deletion is a
terminal, the old remaining graph loses at most one additional edge
from a 2-connected graph. Otherwise a disconnection of
$G-a-e-f$ can only separate two shores of a two-edge cut in $G-a$,
each containing two terminals; the three surviving arms join both.
All cases stay connected. Simplicity and cubicity are immediate.
The face replacement gives a sphere embedding, and parity was checked
above. This also explains why the source path theorem applies to $G'$.

### Positivity and splice interfaces

For $P_{ux}$, prescribing $upqs$ forces $sr,rx$: otherwise $r$
cannot have degree two. For $P_{vy}$ prescribe $vqpr$.
For $D_{11}$ prescribe $uprx$; then $vq,qs,sy$ are forced.
The square matching pairs $(u,x),(v,y)$, so connectivity and
noncrossing force exterior pairing $(u,v),(x,y)$.
All prescribed paths have four distinct vertices, and none invokes
an impermissible simultaneous-pattern extension. Each family is
nonempty, but its size is not controlled by $N_{00}$.

At a vertex splice of two class members, the three port edges are
a cut. A spanning cycle crosses it exactly twice and restricts to
one spanning path in each piece. Closing the deleted vertex in each
piece and reversing this operation gives
$h(G_1\star G_2)=\sum_i a_i b_i$ with fibre size exactly one.
Choose a planar port bijection and flip one piece's bipartition if
necessary. The result remains simple, cubic, bipartite and planar.
To check 3-connectivity: with one deletion in each piece, both
vertex-deleted pieces remain connected and at least one of the
three disjoint port edges survives. With two deletions in one piece,
the other is connected; every component in the first has a surviving
port, since otherwise it would already be disconnected in its original
graph after those two deletions. Thus all components attach.

The source $P_4$ contract gives at least two cycles in each omitted-port
class. The cube's three counts are exactly two. Cube expansion therefore
doubles the count and adds six vertices. For $a_i,b_i\ge2$,
$a_i b_i\ge a_i+b_i$, establishing the original splice lower bound.
The restricted $N_{00}\le1$ induction follows from E and three
nonempty families. There is no original mathematical failure to
preserve separately in these audited claims.

**Coverage correction only:** I164 still twice says seven selected
minimum representatives for its 198 expansion tests. The parent receipt
correctly records six orders, 8,12,14,16,18,20; the order-24 graph was
used in discovery and affine-rank checks, not the expansion probe.
I did not change that report or run either historical failed diagnostic.
Their original failures remain failures.

## 3. An explicit injection where it actually works

Suppose the residual path from $x$ to $u$ is the single edge $xu$.
Every cycle in $N_{00}$ uses $xu$, since both $u$ and $x$ have degree
two in $K=G-\{e,f\}$. Deleting $xu$ is an injective map to $P_{ux}$,
with inverse adding $xu$. Conversely every spanning $u,x$-path in $K$
can be closed by $xu$; it cannot already use that edge because the
graph has more than two vertices. Thus

$$
P_{ux}=N_{00}.
$$

The other two families each contain at least one source-paid output,
and the three families are tagged and disjoint in the expansion.
This supplies the requested recoverable charging map **in this
restricted scope**, including two excess outputs. The other short side
is symmetric. On a four-face all three families equal $N_{00}$,
by cutting either surviving side or flipping the two opposite sides,
so the gain is $2N_{00}$.

The analogous toggle of a longer facial arc need not preserve
connectedness. In $L_8$, the unique lost cycle for step `(1,3,7)`
has both odd residual arcs alternating. Toggling either gives the
right degrees for one path plus some cycles, but actually gives
two components. `fallback-02.json` records the full cycle, both
arcs, both output edge sets and components. Thus even
alternation plus correct degrees is insufficient. The counterexample
below excludes any universal injection with two excess outputs,
regardless of how cleverly that local map is repaired.

## 4. Recoverable counterexample and amplification proof

### Exact finite base

Vertex labels and face-list operations are implemented independently in
`graphs.py`. No I164 script was imported or executed.

1. Start with $L_{12}$: top vertices $0,\ldots,11$, bottom
   $12,\ldots,23$, corresponding rungs.
2. Apply square steps `(0,8,10)` and `(0,2,8)` to the evolving oriented
   face lists. Face index and the two edge-start indices are zero-based.
   This gives a 32-vertex graph $A$.
3. The step `(8,1,5)` in $A$ removes
   $e=29\,28$ and $f=24\,25$, with terminal tuple $(29,28,24,25)$.
   Its face is `[20,29,28,21,9,25,24,8]`; residual lengths are
   three and three. Denote its expansion by $A'$.
4. At vertex 21, order the neighbors as $(9,22,28)$.
   Exact omitted-port counts are

$$
\mathbf a=(34,62,6),\qquad \mathbf a'=(36,54,34).
$$

They sum to 102 and 124. In particular the middle traversal class
**loses eight cycles**, despite the positive total gain 22.
The unchanged vertex 21 is not one of the four terminals.

These are finite computational assertions. The proof certificate
includes complete base edges, faces, bipartitions, rotations and
all vertex-deletion checks. Independent anchored vertex-path enumeration
and complementary-perfect-matching enumeration verify the needed
counts and the final entire cycle sets. No isomorphism-class minimality
of this base or the final counterexample is asserted.

### Prism weighting and exact gluing

At vertex $a_0$ of $L_m$, in the neighbor order
$(a_1,b_0,a_{m-1})$, omitted-port counts are $(2,m-2,2)$.
Indeed $m-2$ of the $H_i$ omit the rung, while each rim omission class
contains one $H_i$ and one of the two alternating all-rung cycles.

Delete vertex 21 of $A$ and vertex 0 of $L_m$ and match ports

$$
9\longleftrightarrow 1,\quad
22\longleftrightarrow m,\quad
28\longleftrightarrow m-1.
$$

Relabel the prism vertices disjointly. The splice is $G_m$.
Carry out the same square step at $e,f$, obtaining $G'_m$.
Splicing commutes with this expansion: the splice vertex is not a
terminal, all altered incidences are disjoint, and the common face
is extended by the prism boundary. In particular its residual parity
remains odd. The owned final embedding checks this explicitly at
$m=10$; the general construction inserts an even number of vertices
along the affected face.

By the splice bijection,

$$
\begin{aligned}
h(G_m)&=2(34)+(m-2)62+2(6)=62m-44,\\
h(G'_m)&=2(36)+(m-2)54+2(34)=54m+32.
\end{aligned}
$$

The order is $32+2m-2=2m+30$, and the expansion adds four.
This proves the announced infinite family conditional only on the
exhaustively verified finite base counts, not on Q164 or (M).

The base boundary families have omitted-port profiles:

| Family, base terminal convention | Ports $(9,22,28)$ | Spliced count |
|---|---|---|
| $N_{00}$ | $(5,16,0)$ | $16m-22$ |
| $P_{ux}$ | $(3,4,0)$ | $4m-2$ |
| $P_{vy}$ | $(1,1,21)$ | $m+42$ |
| $D_{11}$ | $(3,3,7)$ | $3m+14$ |

The same multiplication is valid for these families. A spanning path
whose endpoints are in the base crosses the splice cut exactly twice.
For a $D_{11}$ object, an attachment-only component would leave both
$e,f$ in the other component, violating their required separation;
therefore exactly one component crosses the cut, twice. Restricting,
closing, and gluing again are inverse, with no orientation factors.
`amplification-01.json` independently recomputes every finite profile.

At $m=10$ the final deterministic encoding reverses the terminal
convention to $(25,24,28,29)$, interchanging the two path counts.
Its face is

```
[9,25,24,8,20,29,28,41,40,39,38,37,36,35,34,33]
```

and step `(24,1,5)` leaves lengths 3 and 11. This is the precise
admissibility certificate for the displayed 50-to-54 example.
The six fibres have sizes
$(N_{10},N_{01},N_{11},P_{ux},P_{vy},D_{11})
=(200,92,146,52,38,44)$, summing to 572.
The lost 138 cycles plus the first three classes sum to 576.

## 5. Independent search scope and diagnostics

The first complete seeded run tests 176 steps on 60 construction-history
records: 12 seeds, five levels, starting from prisms of rim length
4,6,8 and mixing cube and square histories. It tests the largest
$N_{00}$ step and two sampled steps at each level, with duplicates
within one level removed. Its maximum $N_{00}$ is 53 and minimum
gain is two.

This overweights short-side steps. The second complete run deliberately
tests only steps with **both residual lengths at least three**.
It has 352 steps on 90 history records: 18 seeds, five levels,
starting from rim lengths 8,10,12, mixing histories as above.
It selects the three largest lost families and one sampled candidate,
removing duplicates within a level. Orders reach 40, maximum
$N_{00}$ is 96, and minimum gain is 12.
The search is labelled, history-biased, and not isomorphism-free or
exhaustive over any graph order. Repeated graphs across histories are
not counted as distinct isomorphism classes.

Every stored graph has full edges and oriented faces, a rotation system,
a bipartition, Euler characteristic two, and deletion checks for every
set of at most two vertices. A connected orientable combinatorial
surface with a single link at every vertex and Euler characteristic two
certifies a sphere embedding. Every expansion is built by splitting
its chosen face and substituting paths on the neighboring faces.

The two positive searches did **not** establish (M). Inspecting the
three omitted-port gains at unchanged vertices exposed negative
coordinates. `deficits-01.json` records those discoveries and the
smallest resulting prism-amplified order **within that search**.
It led to the independently reconstructed 50-vertex example.

For the decisive case:

* Anchored simple-path DFS with necessary residual degree and
  connectivity pruning enumerates the complete Hamiltonian edge sets.
* A separately implemented perfect-matching recursion enumerates
  complements and checks their connected components.
* The two entire cycle sets, not merely their cardinalities, agree.
* Direct endpoint-path DFS counts the two $K$-path families.
* Two-component matching complements count $D_{11}$.
* Restriction of the independently enumerated expanded cycles checks
  all six E fibres, with uniqueness and exact equality to these families.
* Exact rational Gaussian elimination computes affine ranks.
* Small prism checks compare unpruned and pruned enumerators and verify
  all recorded short-side deletion/addition bijections.

Two preparation runs timed out at 200 seconds. Their zero-byte outputs
and messages remain in `failures.json`: the larger targeted search is
incomplete, and the initial unpruned decisive run is incomplete.
Separate completed runs are not retroactive passes for those attempts.
The performance change used only necessary pruning, independently
checked against unpruned small cases and matching enumeration.

## 6. Different global route: exact affine gluing

Let $d(G)$ be the real affine dimension of Hamiltonian-cycle incidence
vectors. For connected bipartite cubic $G$ of order $n$, the unsigned
incidence matrix has rank $n-1$: its only row dependence has opposite
constant coefficients on the two color classes. Hence
$d(G)\le n/2+1$; equality implies Q164.
The equivalent constant-weight criterion says that every edge
weighting constant on Hamiltonian cycles is a vertex potential
$w_{uv}=\alpha_u+\alpha_v$. The constant itself is then
$2\sum_v\alpha_v$. This original linear-algebra criterion is correct.
Its universal hypothesis is not proved by $P_4$ coverage.

Here is a paid global gluing theorem, not an equivalent restatement
of (M):

**Affine splice formula.** If each of the three omitted-port classes
is nonempty in each piece, then

$$
\tag{AS} d(G_1\star G_2)=d(G_1)+d(G_2)-2.
$$

Proof. For piece $i$, partition its finite cycle-vector set into
three classes $S_{i1},S_{i2},S_{i3}$ and choose representatives $r_{ij}$.
Let $U_i$ be the span of all within-class differences, across all
three classes. Projection to the three incident coordinates vanishes
on $U_i$. The three class values are
$(0,1,1),(1,0,1),(1,1,0)$, whose differences have rank two.
Every cycle difference is a within-class difference plus differences
of representatives. Thus $\dim U_i=d(G_i)-2$ exactly.

In the spliced graph, cycles are all compatible pairs
$\bigcup_j S_{1j}\times S_{2j}$. Their differences include
$U_1\times0$ and $0\times U_2$, because one may hold a representative
in the other nonempty class fixed. Two differences between compatible
representative pairs add exactly two dimensions, as seen in their
port projections. They span all remaining differences.
Consequently the compatible-pair affine dimension is
$(d(G_1)-2)+(d(G_2)-2)+2$.

Finally, deleting the old incident coordinates and identifying the
three compatible port values with the new cut coordinates is an
injective affine identification on this space. The cut coordinates
recover both pieces' deleted incident coordinates, so no extra rank
is lost. This proves (AS). ∎

Since $n=n_1+n_2-2$, maximal dimensions
$n_i/2+1$ in the pieces give $n/2+1$ in the splice.
Under the stipulated source all three classes are nonempty.
The classical tight-cut contraction/decomposition interface in GSW
§4 therefore reduces the affine problem to cubic planar braces,
equivalently the cyclically 4-edge-connected members. Each contraction
is a smaller class member; recursively gluing recovers the graph.
This is a dimension reduction, not a claim that every brace has an
all-brace square construction. GSW expressly discusses cube expansions
whose tight cuts are later destroyed by a square expansion.

The weaker numerical Q164 also reduces to these pieces by the original
splice inequality: if both pieces satisfy Q164, their splice does,
with room to spare. Thus a minimum-order Q164 counterexample cannot
have a nontrivial tight cut. This reduction is fully paid; the
remaining brace theorem is not.

The present obstruction keeps its splice cut, because all four
expansion terminals lie on one shore. It therefore explains why
an all-step count inequality can fail without threatening either
global gluing theorem. Exact ranks are:

| Piece or graph | Order | Cycles | Affine dimension |
|---|---:|---:|---:|
| $A$ | 32 | 102 | 17 |
| $A'$ | 36 | 124 | 19 |
| $L_{10}$ | 20 | 12 | 11 |
| $G_{10}$ | 50 | 576 | 26 |
| $G'_{10}$ | 54 | 572 | 28 |

The lost-cycle injection is impossible, yet affine dimension increases
by two. This concretely separates the two approaches.

**Precise remaining global gap:** show that Hamiltonian-cycle
differences span the entire unsigned-incidence kernel on every
cubic planar brace, or prove the weaker sharp cycle count there by
another global exchange mechanism. No such exchange spanning theorem
was obtained. The source state existence/positivity and BKN's
one-switch operation do not pay it. AS is a proved decomposition
tool, not an unproved replacement lemma advertised as progress.

## 7. Literature and contribution assessment

Primary searches were made before enumeration and repeated after the
final candidate. Exact queries, primary reading ranges, noisy results,
unread leads, and the returned `403 Forbidden` handout are recorded in
`literature-search.md`. The actual HMM generation theorem, GSW's
square/splice operations, and BKN's constant multiplicity baseline
were read. No exact full-scope literature duplicate of Q164 was
certified. No absence claim follows from unsuccessful keyword searches.
No MathDB ranking, acceptance priority, or worldwide novelty is claimed.

The counterexample is an actual negative resolution of the specific
all-step research target. Its full proof reduces to a finite base
traversal table, the standard splice product, and explicit prism
counts. The short-side injection is a single-edge deletion/addition
bijection. AS is elementary affine fibre-product linear algebra with
all fibres paid. These **narrow results are technical/supporting**,
not a ninth substantial positive finding. This classification is not
transferred to the whole of Q164, for which no complete reduction
to established results was supplied.

**Next action:** retire universal (M). Focus on the affine annihilator
problem on cyclically 4-edge-connected pieces, first testing a
weight-detecting exchange construction and its complete span, rather
than repeating local $P_4$ existence or proposing another lost-cycle
injection on arbitrary spliced graphs. An adaptive reduction route
must choose and prove a good reduction, not demand every reduction
be good. This report does not establish that adaptive existence claim.

## 8. Evidence contract and reproduction

Report:
`frontier/iterations/i165-square-expansion-multiplicity.md`.
Owned diagnostics:
`frontier/experiments/i165_square_expansion_multiplicity/`.
Owned reading/provenance:
`frontier/sources/i165_square_expansion_multiplicity/`.

`external-bindings.json` binds original I164 payload bytes without
copying or executing the corpus. In particular the preserved hashes are:

* I164 report:
  `19142c6dd6ba3758006b6bd4390ce10408f3648e5f3d2ea72a07e22d01e565cd`
* I164 seal:
  `dbf9aff37eb3fbd30270ea3de0992a02fe185e46ed8236ac2a0c45bc4f9fe14d`

The I165 verifier first checks immutable bytes and exact owned inventory,
then executes only explicitly named owned diagnostic modules.
The single seal is exclusive-created only after successful read-only
prevalidation. The prevalidation receipt is bound by the inventory;
the inventory is bound by the seal. Report and verifier hashes are
recorded there and returned by replay, avoiding self-referential hashes.

```
python3 -I -B /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/experiments/i165_square_expansion_multiplicity/verify.py --replay
```

Replay is standard-library, bytecode-disabled and read-only. An audit
hook denies writes, subprocesses and network; it executes no ancestor
code. It re-enumerates the complete successful searches, the deficit
screen, decisive cycles/fibres, amplification profiles and affine
diagnostics. Timed-out runs are preserved as incomplete artifacts,
not deliberately repeated. HMM rendering and web searches are byte-bound
preparation records, not subprocess/network operations during replay.

Finite exhaustive checks certify the encoded examples and reductions.
They are not a universal proof of Q164, formal verification, human peer
review, or acceptance. No children, shared-ledger edits, staging,
commits, publication, or acceptance changes were made.
