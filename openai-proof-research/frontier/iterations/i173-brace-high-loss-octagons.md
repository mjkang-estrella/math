# I173: protected-octagon surgeries across the two cube cuts

Date: 2026-10-10. Research iteration, **not an acceptance increment**.
Eight accepted findings remain eight. OpenAI theorems at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true.

**Outcome:** I172 passes its assigned original-scope audit. The declared
cut-breaking surgery family gives **212 certified braces**, but **no
high-loss brace**: every one of the 236 first/second-stage records has
$\ell=0$. Both cuts are really removed, not relocated. The first surgery
already makes the protected survivors span the entire homogeneous degree
kernel. Explicit survivor bases and **1,500** exact transported-direction
coordinate certificates identify this finite loss-collapse mechanism.

The requested brace with $\ell\ge2$ remains **open**. The surgery mechanism,
not a universal brace bound, is refuted in the exact finite scope below.

## 1. Contract and independent audit

Read the full saved assignment
`iteration173-brace-high-loss-octagons-brief.md`, project `AGENTS.md`,
the immutable upstream contract, catalogue family 180, and the matching
manuscript paths in `sources/preprints-tree.json`. The actual local pinned
manuscript statement `cor:pfaffian-paths`, lines 812–828 of
`frontier/sources/i164_structural_graph_discovery/upstream-paper.tex`,
says every three-edge path in a finite simple cubic 3-connected bipartite
Pfaffian graph extends to a Hamiltonian cycle and includes the planar class.
No upstream truth audit is undertaken. No other agent was started.

### Authentication before mathematical use

All detached I172 anchors match:

| Object | SHA-256 |
|---|---|
| Report | `030e71d1fe49909ed5dc98eb2a3250045cc3f7d8068f701cf844e676473accbe` |
| Seal | `8abdc63ae868fbbda7778e422da34194d918be99e15fc29b784cc6468140c972` |
| Verifier | `c7a8c1af8d767573ce16fcafa28a18e28fb373f403536d6bd93c30893b9cbe28` |

The seal's inventory and successful-prevalidation bindings match, the
complete owned-file set has **31** entries, and all **167 non-context
external** bindings match. Four inherited context discrepancies are retained
in `frontier/sources/i173_brace_high_loss_octagons/authentication.json`.
Their current hashes differ from the parent's earlier context receipts;
none is a mathematical input. All other ancestor bytes are non-exempt.

The parent's **323.138513 s** replay, seven byte-identical payloads, eight
blocked probes, and its before/after binding checks are authenticated
validation history. They are **not** I173's runtime or an independently
re-executed ancestor diagnostic. Ancestor Python is opaque hashed evidence:
no ancestor program was executed, imported, or copied as implementation.

### Notation

All vector spaces are over $\mathbb Q$. A graph in $\mathcal B$ is finite,
simple, cubic, bipartite, planar, and 3-vertex-connected with a specified
sphere embedding. For a face in order $u,v,\ldots,y,x,\ldots$, delete
$e=uv,f=xy$ and insert four new vertices $p,q,r,s$, arms
$up,vq,xr,ys$, and square $pq,qs,sr,rp$.

In sorted old-edge coordinates let $N_{ij}$ be the Hamiltonian classes by
deleted-edge status, and put
$$
S=N_{10}\cup N_{01}\cup N_{11},\quad
L=\operatorname{diff}(S),\quad
L_0=\sum_{ij\ne00}\operatorname{diff}(N_{ij}),\quad
V=\operatorname{diff}(N_{00}),
$$
$$
U=\operatorname{diff}(P_{ux})+\operatorname{diff}(P_{vy})
  +\operatorname{diff}(D_{11}).
$$
The paths are spanning in $G-e-f$; $D_{11}$ consists of exactly two
spanning-cover components with endpoint pairs $u,v$ and $x,y$.
Isolated cycles are not allowed. For actual representatives
$A\in N_{10},B\in N_{01},C\in N_{11},N\in N_{00},C_0\in S$,
$$
b=P+Q+D+2e+2f-3C_0,\quad
\beta=P+Q+D+2e+2f-A-B-C,\quad c=N-A-B+C.
$$
Then $\ell=d(G)-\dim L$, $t=\dim(L+U)-\dim L$ and
$\eta=\dim(L+U+\mathbb Qb)-\dim(L+U)$.

For each odd boundary arc use its alternating edge sum $q_A$ or $q_B$.
For $J=P_{ux},P_{vy},D_{11}$ put $q_J=q_A,q_B,q_A+q_B$ respectively.
The compatible old family is
$F_J=\{N\in N_{00}:N-q_J\in J\}$, with membership testing both binary
coordinates and the actual connectivity/pairing. The residual family is
$\{P\in J:P+q_J\notin N_{00}\}$. Anchor at a translated compatible
member when available, otherwise at an actual member of $J$.
The resulting spaces satisfy $U=V_{\rm good}+R$ exactly, with
$$
\delta_V=\dim(L_0+V)-\dim(L_0+V_{\rm good}),\quad
\delta_R=\dim(L_0+V_{\rm good}+R)-\dim(L_0+V_{\rm good}),
$$
$$
\epsilon=\dim(L_0+V+\mathbb Qc)-\dim(L_0+V).
$$
Every computed row verifies $\ell-t=\delta_V+\epsilon-\delta_R$ and
the $\beta$ and $b$ versions of $\eta$ agree. No containment
$V\subset U$ or $V\subset L+U$ is assumed.

## 2. Mandatory tests, before the surgery search

The first mathematical run used the exact order
`0,520,522,524,527,528,530,533,534,536,539,431`, then C171's
`two_component_forbidden_weight` at `[1,1,3]`, then $G_6,G_{10}$.
Every subsequent development diagnostic first repeats these tests.

The ten high-loss census entries reproduce $(\ell,t,\eta)=(7,6,1)$;
0 and 431 reproduce $(1,0,1)$. All seven families, residual membership,
actual $q_J$, $\beta,c,b$, and two exact ranks are retained. Different
choices of the old bridge differ by $L+U$, explicitly checked rather than
equating ranks only.

C171 has 110 Hamiltonian cycles. The independent matching extension
algorithm supplies an actual perfect matching for each of **1,032**
disjoint edge pairs. It is a brace. Its stored functional annihilates
every freshly enumerated $L,V$ generator and satisfies
$$
w(N-C_0)=1,\qquad w(F-C_0)=1/14,\qquad w(T-C_0)=-1/2,\quad T\ne F.
$$
Both factors have exactly two components. $F$ is checked coordinatewise
to be the prescribed square switch. A generic two-component factor's
negative weight therefore cannot answer the prescribed-switch question.

At 431 the independent separator check gives $w(L+U)=0$, $w(b)=10$,
and $w(v_{\rm old})=8$. Both proposed containments fail by exact ranks.
Every compatible old family is empty; binary toggles may isolate cycles.
$G_6,G_{10}$ reproduce losses **3 and 7**, with complete path families
and residual offsets, not just cycle counts.

## 3. Separate original-scope I172 verdicts

### S172: PASS ORIGINAL

Suppose a splice vertex $z$ is outside a prescribed facial square.
The switched factor $F=N+s$ has the same incident coordinates at $z$
as $N$. For a signed affine Hamiltonian representation
$F=\sum_C\lambda_C C$, let $a_1,a_2,a_3$ be the coefficient totals
by omitted port. The cut coordinates give
$$
a_2+a_3=h_1,\qquad a_1+a_3=h_2,\qquad a_1+a_2=h_3,
$$
where $(h_1,h_2,h_3)$ is one of $(0,1,1),(1,0,1),(1,1,0)$.
The unique solution is total one on $N$'s omitted-port type, zero on
the other two. In particular the coefficients need not be nonnegative.

Choose one attachment Hamiltonian cycle of each type, using the actual
attachment cycle of the given lift for its type. Glue each $C$ to its
type's chosen attachment cycle. The signed sum agrees with $F$ on the
core, the given attachment cycle on internal attachment edges, and the
given lift on all three cut coordinates. Thus it is the *prescribed*
lifted factor, not merely an affine-equivalent or equally weighted factor.
The protected deletion statuses are unchanged, so the total on $N_{00}$
is exactly the original $q$. This proves the universal remote-splice
transport assertion under the stated nonempty-port hypotheses.

For every even prism $P_m$, the complete Hamiltonian list is
$C_0,\ldots,C_{m-1},X,Y$: $C_j$ uses all rails except $t_j,b_j$ and
the two adjacent rungs, while $X,Y$ use every rung and opposite alternating
rail matchings. A nonempty proper rung set forces paired horizontal
segments; more than one omitted rail pair separates components. If every
rung occurs, only the opposite alternating choices connect. This proves
exhaustion. Rail equations and the affine coefficient sum prove independence.
The coordinate identity
$$
(m-2)(r_0+r_1-t_0-b_0)
=(m-3)C_0-\sum_{j\ne0}C_j+X+Y
$$
has coefficient sum zero. For either deletion type its prescribed factor
has lost-class total $q=1/(m-2)$. Hence remote decorations retain that
core-dependent total, not a formula using the decorated order.
This excludes the bad coefficient only in the stipulated decorated family.

Independent finite audit: all **12** remote graphs are reconstructed from
core/attachment edges and the port matching. Every full lifted cycle set,
seven-class set, signed rational sum, cut coordinate, internal coordinate,
lost total, and each of the three port-total equations checks. This is
validation of the proof, not its infinite-quantifier justification.

### K172: PASS ORIGINAL

For every even $m\ge4$, replace prism vertices $0,m+1$ by punctured
cubes with offsets $A=2m,B=2m+8$ and cut edges
$$
1a_1,\ (m-1)a_4,\ ma_3;\qquad
1b_1,\ mb_4,\ (m+2)b_3 .
$$
The exact protected face is
$1,a_1,a_2,a_3,m,b_4,b_5,b_1$, with deletions
$a_3m,1b_1$. Its complementary arcs have length three each.
The construction has order $2m+12$. The chosen planar gluing reverses
the local port order on the two punctures, giving an oriented sphere
embedding. No new edge has both ends in the same piece, and three distinct
ports prevent loops/parallel edges. The color classes match across ports.

For 3-connectivity, if two removed vertices are in one punctured side,
every surviving component there has a port, since restoring the puncture
would reconnect the original graph after those deletions. The intact
opposite punctured graph joins the ports. If one deletion is on either
side, each punctured graph minus its extra vertex stays connected by
the original 3-connectivity, and at least one cut edge remains. This
also covers fewer deletions. It proves admissibility for all even $m$,
not only the checked orders.

A Hamiltonian cycle crosses a 3-cut exactly twice. Cutting and restoring
the deleted vertex gives the compatible two-cycle splice bijection.
Each cube has two cycles per port type, so every prism cycle has four
lifts. Its three independent within-port differences are exactly the
one-cube kernel. The prism survivors
$C_{m-1},C_0,C_1,X,Y$ meet every port type at each replaced vertex,
so each kernel direction already occurs between survivors. Each splice
raises both full and survivor dimension by three. Therefore
$$
d(G_m)=m+7,\quad \dim L=10,\quad \dim L_0=8,\quad \ell=m-3.
$$
Both nontrivial splice cuts persist in $G_m$; it is not a brace.

### R172: PASS ORIGINAL, explicitly four-to-one

The map on all seven classes is **onto with fibre four**, not one-to-one.
For $P_{ux}$ the first cube has one endpoint. Cut parity is odd; the
deleted cut edge leaves at most two possible crossing edges, so exactly
one is used. Taking the cut edge to terminal 1 would complete that whole
spanning path before visiting the rest of the graph. The other port is
forced. The second cube has no endpoint and uses its two available cut
edges. The $P_{vy}$ case is symmetric.

For $D_{11}$ each cube contains one endpoint. It again uses exactly one
cut edge, and the prescribed terminal pairing forbids the port leading
to the other path's endpoint. Thus both remaining ports are forced.
Restrictions inside the gadgets are spanning paths: an additional closed
component would violate the definition of the original path/cover.
Conversely either of the two appropriate seven-vertex cube paths at
each gadget lifts every projected object, giving exactly four lifts.
This pays for the path classes, not just the old cycles.

The subtle ambient-kernel step is legitimate here: the independently
proved dimension $d(G_m)=m+7$ equals the connected bipartite homogeneous
degree-kernel dimension $|E|-|V|+1$. Thus every within-path difference
belongs to the full cycle-difference space. The collapse kernel is the
six-dimensional attachment kernel already in $L$, and its deleted
coordinates vanish, so it lies in $L_0$. No universal or typed fullness
claim is used. The projected $U$ and $V$ both equal the prism lost-class
difference space of dimension $m-4$, disjoint from prism survivors.
The projected cross-class offset $c$ supplies its remaining independent
direction. Consequently $t=m-4$ and $\epsilon=1$.

At the first cube, the two lost-class paths between ports 1 and 4 are
`1-5-6-2-3-7-4` and `1-2-3-7-6-5-4`. The former boundary toggle isolates
the four-cycle `1-5-6-2-1`; the latter is nonbinary. At the second cube,
the two paths between 4 and 3 are `4-5-1-2-6-7-3` and
`4-7-6-5-1-2-3`. One toggle is nonbinary; the other isolates
`4-7-6-5-4`. Since the pieces are disjoint, the double toggle cannot
repair either isolated cycle. Every compatible old family is empty,
$V_{\rm good}=0$, and $R=U$.

Fix one lift of each $C_2,\ldots,C_{m-2}$ with fixed gadget paths.
Remove cut edge $1a_1$ and replace the first gadget path by
`3-7-6-2-1-5-4`. This is a genuine spanning $a_3$–1 path, with the
same replacement offset for every $j$. Its differences equal the old
fixed-lift differences exactly, recovering $m-4$ directions. It is
not the failed boundary toggle.

The projection reads restored cut coordinates exactly and kills internal
gadget coordinates; thus it preserves the $2e+2f$ and representative
offsets in $\beta,c,b$. The bridge projects modulo prism $L+V$ to
$(3+2\alpha)r=m r/(m-2)\ne0$. Its kernel is already in $L$, so
$\eta=1$. For **every even $m\ge4$**,
$$
(\ell,t,\eta)=(m-3,m-4,1),\qquad
(\delta_V,\delta_R,\epsilon)=(m-4,m-4,1).
$$

Finite audit: $m=4,6,8,10$, orders 20/24/28/32 and cycle counts
24/32/40/48. Complete independent sets agree in all **28 class
projections**, every fibre has four elements, and residual recoveries
are 0/2/4/6. Formula edge sets, sphere embeddings, exact octagons,
3-connectivity, and actual matching-extension failures are checked.
The twelve remote checks and all **29** two-cap constructions also pass.
The caps are regenerated by two fresh square expansions; their outcomes
are exactly **20** loss-zero and **nine** loss-one cases. They are
mathematical failures of that proposed transport, not diagnostic failures.

## 4. Declared surgery family

Start only with $m=6,8,10$ in that order. Retain the actual eight
protected perimeter edges and both seven-vertex cube sides.
For the first surgery enumerate all lexicographic triples
`(face index, first edge index, second edge index)` whose edges lie
internally on opposite sides of the first cube cut, avoid the protected
perimeter, and give a bipartite square expansion. For each first child,
enumerate every such triple across the second original cube side.
No isomorphism, labelled-edge-set, or history deduplication is used.
All original vertex labels persist; new labels start above the current
maximum. Face splitting and neighbor-face insertion are explicit in
`toolkit.expand`.

| Core $m$ | First surgeries | Two-surgery histories | Total records |
|---:|---:|---:|---:|
| 6 | 6 | 40 | 46 |
| 8 | 8 | 68 | 76 |
| 10 | 10 | 104 | 114 |
| Total | 24 | 212 | 236 |

The full triples were saved in `surgery_plan-attempt-01.json` before
executing the search. Every record retains graph edges and faces, all
seven complete classes, exact ranks, bridge/residual offsets, and actual
transport attempts on I172's fixed old cycles and residual paths.
For each original object we retain **every** local extension having the
same restriction to surviving pre-surgery edges, and continue with the
lexicographically least extension when available. No absent extension
is silently replaced. Distinct offsets, equality/failure of paired
differences, and recovered ranks modulo the *new* survivor space are
recorded. Loss of independence modulo that space is different from
loss of the old objects themselves.

Removing the original cut partitions is insufficient. Every candidate
has a complete nontrivial three-edge-cut enumeration, and every disjoint
edge pair is separately tested for a perfect-matching extension by
bipartite augmenting paths. Success includes an explicit matching;
failure retains the edge pair. Bracehood is asserted only when every
pair succeeds, never from the cut scan alone.

## 5. New finite result: survivor saturation destroys the intended loss

### Proposition Q173, finite computer-assisted obstruction

For exactly the **236 labelled surgery histories** in Section 4, every
protected octagonal interface has
$$
(\ell,t,\eta)=(0,0,0),\qquad
(\delta_V,\delta_R,\epsilon)=(0,0,0).
$$
The first-stage graphs are not braces. Every second-stage graph is a
brace certified by 2-extendibility. All retain the exact original octagon
and its $(3,3)$ complementary arcs. No graph-isomorphism census or
quantification over other $m$, different gadgets, surgery orders, deeper
histories, or arbitrary braces is asserted.

| $m$ | Stage | Records | Order | $d=\dim L$ | Cycle-count range | Remaining nontrivial 3-cuts | Braces |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 6 | 1 | 6 | 28 | 15 | 56–64 | 1 | 0 |
| 6 | 2 | 40 | 32 | 17 | 86–148 | 0 | 40 |
| 8 | 1 | 8 | 32 | 17 | 72–88 | 1 | 0 |
| 8 | 2 | 68 | 36 | 19 | 108–220 | 0 | 68 |
| 10 | 1 | 10 | 36 | 19 | 88–120 | 1 | 0 |
| 10 | 2 | 104 | 40 | 21 | 130–324 | 0 | 104 |

**Proof certificate independent of exhaustive-cycle upper bounds.**
For any connected bipartite graph, multiply rows of its unsigned vertex-edge
incidence matrix by the bipartition signs. This gives an oriented incidence
matrix, of rank $|V|-1$. Its homogeneous degree kernel therefore has
dimension $D=|E|-|V|+1$. All Hamiltonian-cycle differences, in particular
survivor differences, lie in that kernel:
$$
\dim L\le d(G)\le D.
$$
For each of the 236 graphs, `post_analysis-attempt-01.json` supplies a
surviving Hamiltonian anchor and **$D$** other surviving Hamiltonian
cycles whose differences are independent. Each is checked directly for
binary incidence, degree two, connected spanning support, and use of at
least one protected deletion edge. Both exact rank implementations return
$D$. Thus $D\le\dim L\le d(G)\le D$, proving **$\ell=0$**.
This certificate rules out any missing Hamiltonian cycles changing the
loss: no cycle-difference space can exceed the paid ambient upper bound.
It uses no general affine-fullness premise.

At the first stage $D=m+9$, whereas the original $G_m$ has $d=m+7$
and $\dim L=10$. In this finite family the surgery adds only two total
degree-kernel directions, but adds $m-1$ survivor directions. This
absorbs all $m-3$ old missing directions immediately. At the second
stage both dimensions simply increase by two again.

**Cut removal rather than cut relocation.**
The exhaustive cut certificates show that after every first surgery the
only nontrivial three-edge cut is exactly the original untouched second
cube partition. The first cut has no replacement elsewhere. After the
second surgery there are no nontrivial three-edge cuts anywhere.
Independently, every first-stage graph has exactly three failed disjoint
edge pairs, the three pairs of edges of its remaining tight cut, and
every other pair extends. The surviving seven-vertex punctured cube
has bipartition imbalance one with all ports in its majority class,
so every perfect matching crosses that cut exactly once. This also
explains those three failed pairs structurally.

There are **26,076** successful first-stage matching witnesses and
**72** failed pairs, all retained. Every one of the **302,844**
second-stage disjoint-edge pairs has an explicit perfect matching.
This last fact, with the independently checked admissibility and
connectivity, is the brace certificate. We do not infer it from the cut
scan.

**The old residual mechanism can persist as an equality but lose its
quotient meaning.** In every retained canonical paired transport, the
old-cycle differences still equal the residual-path differences exactly.
That is not sufficient: their rank modulo the new $L$ is **zero in every
record**. The certificate supplies rational coefficients expressing each
of **1,500** such old/path directions in the displayed survivor basis.
Every remainder vector is exactly zero. This is actual vector absorption,
not just an observed equality of dimensions.

All local extensions of the attempted fixed old/path objects are saved.
Some objects have no such extension. Six second-stage records have no
remaining complete canonical pair at all; the others have between one
and $m-3$. A count of one gives no difference direction and is not called
rank preservation. The lost extensions, changing pair counts, and all
failed high-loss transports remain in the payload rather than being
filtered out of the population.

This proves an exact **finite survivor-saturation obstruction** to this
particular two-cut C4 surgery strategy. It does **not** prove that every
such surgery for every even $m$ saturates, that every cut-breaking
operation loses high loss, or that all braces have octagonal loss at most
one. No infinite new brace family with a loss mechanism is claimed.

The lower bound and full exchange both hold in all these records, but
only in the now-trivial loss-zero regime. They provide no evidence that
settles the requested high-loss brace inequalities. No high-loss brace
was available on which to launch the conditional further attack.

## 6. Independent algorithms and boundaries

Only standard-library Python under `-I -B` is used.

- Hamiltonian cycles: rooted vertex DFS, independently cross-checked
  against connected complements of **every** perfect matching from a
  least-unmatched-vertex recursion. Whole incidence sets agree.
- Spanning paths and paired covers: prescribed-degree saturation and
  connectivity/pairing filtering, independently compared against endpoint
  DFS (with a complementary second path for the paired cover).
- Ranks: integer elimination with gcd normalization in ascending pivot
  order and an independent sparse `Fraction` implementation with descending
  pivots. Every returned rank must agree; cached ranks are double-checked
  exact answers, not modular estimates.
- Admissibility: simple cubic degrees, a bipartition, connectivity after
  every two-vertex deletion, every oriented edge occurring once in each
  direction among faces, a single cyclic link at every vertex, and
  Euler characteristic two. This certifies the supplied sphere embedding.
- Bracehood: an independent augmenting-path matching solver, fixing each
  disjoint edge pair and checking every supplied perfect matching directly.
  The cut enumeration is supplemental evidence, not its justification.

No tests assume typed degree-and-port fullness (M168). The ambient-fullness
argument is confined to the explicitly proved prism/cube splice family.
D168's bounded bidirectional dual-transfer obstruction is not bypassed.
Every interface checks $\rho(L)=\mathbb Q^2$ and
$\dim L=\dim L_0+2$, so a deleted-edge-only separator is not introduced.
Binary toggles always receive full component and endpoint-pairing tests.

The universal square coefficient exclusion stays open. S172 removes
already controlled remote decorations; it supplies no genuinely
brace-internal signed relation ruling out $[r]=2g,[s]=-3g$.
The specific positive $F$ and the different negative $T$ at C171 remain
distinct throughout. No arbitrary-factor positivity, convexity, or
unsupported transfer principle is used.

Literature searches and their exact queries are retained in
`frontier/sources/i173_brace_high_loss_octagons/literature.md`.
They found Gorsky–Steiner–Wiederrecht's matching-theoretic Barnette paper,
but returned only abstract/interface or PDF metadata excerpts, not a
readable full proof. Other results concerned facet-Hamiltonicity of
graph associahedra, a different question. No search snippet is used as a
theorem. No full literature novelty or priority claim is established.

## 7. Failures, evidence order, and validation

All unsuccessful mathematical proposals are retained: I172's 29 cap
transports, all 236 loss-zero I173 surgery records, missing local extensions,
and failed matching pairs. There is one I173 diagnostic implementation
failure: `audit_refinements` attempt 01 treated the index-431 separator
object as a vector instead of reading its `w` field. Its exact source
snapshots, empty output, and `ValueError` stderr remain. Attempt 02
corrects the data schema and passes. This is not a mathematical
counterexample or a failed theorem check. I172's different earlier
`owned`/`files` authentication-schema failure remains inherited evidence.

The initial surgery run completed in **799.425798 s**; this is development
runtime, not final sealed replay runtime. Post-analysis took **53.054870 s**.
A retained profile of one previously certified candidate motivated only
enumeration optimizations: bitset floods for cuts and elementary degree/
connectivity pruning of the independent DFS enumerators. A Hamiltonian
continuation must traverse a connected unused induced graph; an internal
unused vertex needs two available neighbours, an endpoint one. These
necessary conditions cannot remove a genuine continuation.
Mandatory and ancestor outputs remain byte-identical after optimization.
The complete surgery output is compared byte-for-byte during final
prevalidation and sealed replay. No declared scan was abandoned.

### Final immutable-first package

Authoritative executable sources, the final report, all mathematical
inputs, all deterministic payloads, every retained failed/source-stage
artifact, and the literature receipt are inventoried **before** final
diagnostics. Only `inventory.json`, `prevalidation.json`, and `seal.json`
are control-chain files rather than self-hashed members of the owned list.
No output is silently excluded because it is inconvenient.

The verifier reads and authenticates all owned and non-context external
bytes into immutable memory before compiling any diagnostic. It compares
the complete owned-file set, not just a subset of hashes. Ancestor Python
stays opaque. Compilation is permitted only for the exact authenticated
bytes of the two executable mathematical modules. All later filesystem
reads and writes are blocked while diagnostics run.

The eight guard probes are writes, filesystem mutation, network,
subprocess, unbound reads, outside compilation, outside execution, and
forged bytes under an owned-source filename. Every probe must be blocked.
The six deterministic replays are mandatory cases, ancestor audit,
declared surgery plan, all surgeries, audit refinements, and post-analysis.
All six must reproduce their bound payloads byte-for-byte.

Only the four named shared ledgers are context-only. Their actual hashes
and inherited mismatches are explicit; their current bytes must remain
unchanged during a replay. No graph, theorem statement, report, ancestor
mathematical payload, source, or output receives that exemption.
An outer full rehash checks all owned and mathematical external bytes
again after the read-only diagnostic. The verifier also checks its control
bytes again. Python and its standard library are runtime dependencies,
not vendored or OS-sandboxed components. Clean-clone reconstruction was
not tested.

The order is final inventory, **successful prevalidation**, **one**
exclusive-create seal, then read-only sealed replay. No report or source
edits and no resealing follow the seal. Detached report/seal/verifier
hashes, final replay runtime, binding counts, and probe outcomes are
returned outside this report, avoiding self-hash or report/seal cycles.
Run from any directory with the absolute path:

```text
python3 -I -B /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/experiments/i173_brace_high_loss_octagons/verify.py
```

## 8. Status and concrete next step

- **Proved/verified in original scope:** S172, K172, R172 and all assigned
  finite certificates, including every cap failure.
- **Proved in the declared finite scope:** both cuts can be removed and
  212 brace histories certified; all 236 survivor spaces saturate the
  homogeneous degree kernel; transported residual directions are absorbed.
- **Refuted in that finite scope:** these ordered cross-cut C4 surgeries
  preserve I172's high-loss mechanism.
- **Open:** a brace with a genuine $(3,3)$ octagon and $\ell\ge2$; universal
  octagonal lower bound and exchange; prescribed-square coefficient
  exclusion, (T), and Q164. The accepted count remains eight.

The next concrete test should change the attachment gadget, not merely
add another C4 to these already saturated records. Start from $P_6$ and
replace its two opposite square corners by **punctured $P_6$ prisms**
instead of punctured cubes. Use each gadget's lateral-square route
`1-7-6` between two ports, of length two, so the protected face can still
be an octagon after the two planar port identifications. The resulting
initial candidate has order **32**. First certify the embedding, original
loss, all seven classes, and port kernels anew. Then test only the first
lexicographic perimeter-avoiding cross-cut C4 operation and compute a
survivor basis before launching a larger scan. If it already spans the
degree kernel, reject that transport immediately. This is a specific
unperformed next experiment, not a claimed construction or theorem.
