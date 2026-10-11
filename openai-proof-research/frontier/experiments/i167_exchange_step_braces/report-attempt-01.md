# I167: audit and exchange-step attack for the brace affine-span route

**Date:** 2026-10-10. **Status:** research, not acceptance.
**Outcome:** one original I166 mathematical interface **FAILS as written**;
its corrected form is proved below. The face-toggle lemma, B18 obstruction,
small-census ranks, 240 splice instances and survival counts pass independent
checks. Neither the exchange inequality nor the brace theorem is proved or
refuted. Q164 remains unproved and unrefuted; literature status is not certified.

All OpenAI results **and lower proof operations** at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. No upstream
truth audit or ex-falso argument occurs. Eight accepted findings remain eight.
No children, shared edits, staging, commits, publication or acceptance changes.

## 1. Scope and immutable original

Write scope is this report and the two directories
`frontier/experiments/i167_exchange_step_braces/` and
`frontier/sources/i167_exchange_step_braces/`.

Original I166 report SHA-256:
`b85346fd77aca2a38bcbdb9e29d10fbb5c6b025e42fb16e7ff1777b61ef1b7ec`.
Original I166 seal SHA-256:
`8e080e006b78700ad4487adb569fabf236fd96f8fba615376d5260dd02a4c717`.
Both matched before work. Original I164/I165/I166 bytes are preserved.
I166 payloads are data only: **no ancestor code, including a verifier, was
executed**. In particular I167 does not reproduce I166's statement that it
both avoided ancestor execution and reran I165's sealed replay.

Let $\mathcal B$ denote finite simple undirected cubic, bipartite, planar,
3-vertex-connected graphs. Hamiltonian cycles are unoriented edge sets.
Write $d(G)=\dim\operatorname{aff}\{\chi_C:C\text{ Hamiltonian in }G\}$.
For connected bipartite $G$, the unsigned incidence matrix has rank $n-1$.
Thus $d(G)\le m-n+1=n/2+1$, and equality is equivalent to every edge
weight constant on Hamiltonian cycles being a vertex potential.

## 2. Independent audit verdicts

| Original I166 interface | I167 verdict and scope |
|---|---|
| Face-toggle lemma | **PASS ORIGINAL**, full proof; §2.1 |
| B18 three-way certificate and smallest order | **PASS ORIGINAL**, independently rebuilt closure DAG, order obstruction and all 12 contractions; §2.2 |
| Survival counts, 136/142, deficit up to 5, maximum lost share 1/2 | **PASS ORIGINAL**, independent enumeration and exact ranks |
| Section 5 aggregated constant-weight equations | **FAIL ORIGINAL as written**, even for a vertex potential on an expanded cube; §3.1 |
| Section 5 path/two-path *within-class constancy* | **PASS as necessary conditions**, but those conditions alone omit cross-class offsets; corrected complete system in §3.2 |
| OEIS A007083 terms through order 20 | **PASS**, with validation claim narrowed: aggregate agreement is an anchor, not by itself a proof of program correctness or completeness |
| (AS) 240-instance checks | **PASS**, exact same pair/port order, all 240 reconstructed independently, both cycle enumerators agree |
| Exact-rank methodology | **PASS** for the stated rational-difference method and incidence upper bound; independent fraction-free elimination, plus a second Fraction implementation on all 15 census graphs |
| Entire 452-record campaign | **Metadata consistency PASS; partial independent numerical replay**, not a new 452-record dual-enumerator replay |
| HMM two R0 applications per square | **PASS with order >8**, exactly as HMM Theorem 4 states; original blanket wording including the cube needs a scope correction |
| GSW 5.2 brace closure; Figure 4 caution | **PASS source reading**; full Lemma 5.2 proof read; neither claims brace-only C4 generation |
| Single-cycle switch-spanning equivalence | **Sufficiency PASS; converse GAP**, not established in I166; §6.2 |

The audit failure concerns **new I166 content**, not any stipulated source.
The original report and verdict are not silently repaired. The correction
below is a separate I167 result.

### 2.1 Face-toggle proof

Remove the alternating facial edges of a Hamiltonian cycle. What remains
is a collection of disjoint paths pairing the $2k$ facial vertices, with
all other vertices internal to those paths. Every path lies in the disk
on the other side of the facial boundary on the sphere. This gives a
noncrossing matching of the boundary vertices.

For precision in the adjacent-pair step, select a pair and one of its
boundary arcs minimizing the number of intervening endpoints. If this
number is positive, noncrossing forces all the intervening endpoints to
pair inside the arc, furnishing a pair with fewer intervening endpoints.
Thus some pair is adjacent. If its boundary edge lies in the matching
used by the original Hamiltonian cycle, that edge and the exterior path
already form a proper cycle component, impossible. If it lies in the
other boundary matching, it forms a proper component after toggling.
The remaining $2k-2\ge2$ facial vertices ensure properness in both cases.
This checks the disk argument, adjacent-pair existence and both cases.

Own sweep: all 161 faces of the 15 census graphs alternate on at least one
Hamiltonian cycle; none admits a Hamiltonian toggle. I did not rerun the
full 5795-face walk sweep. The proved lemma, not that sample, supplies
the universal obstruction.

### 2.2 Census, B18 and the generation claim

From the recorded census face lists, I167 independently checks simplicity,
oppositely paired darts, one rotation link per vertex, Euler characteristic
two, bipartition and connectivity after every deletion of one or two
vertices. A fresh DFS-rooted rotation encoding distinguishes all 15
graphs. Small graph isomorphism backtracking supplies a separate check
where contractions and cube splices are used.

Counts at orders $8,10,12,14,16,18,20$ are
$1,0,1,1,2,2,8$. OEIS A007083 has offset 2 and counts graphs on $2n$
vertices, so these are precisely its terms at indices 4 through 10.
I167 rebuilds all expansions whose child has order at most 20:
**176 face/vertex-labelled DAG edges**, under square and cube expansions.
Every output is in the census and every census graph is reachable.
Together with HMM generation, closure plus these distinct class certificates
pays completeness through order 20. Numerical agreement with OEIS alone
would not pay that argument or validate unrelated large-graph code.

Brace status is checked from the complete perfect-matching set by
2-extendability and independently by deleting all triples of edges and
looking for a nontrivial cut. There are ten census braces. Brace-only
square reachability misses exactly B18:

- The fresh DAG gives the same missing brace.
- A C4 predecessor has order 14; the unique order-14 member is a non-brace.
  A cube expansion cannot end at a brace, because its nontrivial tight
  cut is present immediately after the expansion.
- B18 has six facial squares. Of their twelve R0 applications,
  **six are class-valid and six invalid**. Every valid result is
  independently isomorphic to the order-14 non-brace, with an explicit
  nontrivial 3-cut recorded. No valid result is a brace.

All other non-base braces in this census have a brace-only square path
from the cube. Hence order 18 is minimal. This is not inferred merely
from a chosen first-discovery history.

HMM's statement is checked on **nine non-base braces, 63 squares,
126 applications**. Each square has a class-valid application.
I166's code also excludes the cube; some prose fails to say so.
The cube is the base case, not a counterexample to HMM's actual theorem.
I166 computes a full DAG in memory, but its saved graph payload does not
contain that DAG; I167 rebuilt it rather than treating it as saved data.

### 2.3 Rank and large-sample limits

Own exact diagnostics reproduce every census $(h,d)$ and all 240 splice
rows, with Hamiltonian cycles obtained both by vertex-path search and by
connected complements of perfect matchings. Fraction-free integer row
operations compute rank over $\mathbb Q$; primitive row division is by
the exact gcd. A separate Fraction Gaussian elimination agrees on all
15 census graphs. Early stopping is used only at the proved incidence
upper bound, never as a numerical rank tolerance.

All 452 record summaries have full reported rank and exhaustion flags;
there are 443 distinct recorded canonical strings. These checks do not
re-enumerate 452 graphs. Additionally, one deterministic graph at each of
orders $24,28,\ldots,64$ is independently enumerated by perfect-matching
complements and ranked, reproducing:

| n | 24 | 28 | 32 | 36 | 40 | 44 | 48 | 52 | 56 | 60 | 64 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| h | 42 | 64 | 94 | 132 | 238 | 376 | 670 | 1528 | 2404 | 3464 | 5648 |
| d | 13 | 15 | 17 | 19 | 21 | 23 | 25 | 27 | 29 | 31 | 33 |

The last four are reconstructed as adjacency lists from literal canonical
tuples, not by executing walk code; their embedding and history are not
independently reconstructed. The second I166 batch stores canonical
adjacency and history, not the claimed full face list for every walk graph.
No full campaign revalidation or new prism-only tightness classification
is claimed by I167.

## 3. The original constant-weight system fails; a complete correction

### 3.1 Explicit original FAIL

Use the cube with facial square $(0,1,3,2)$ and expand its edges $01,23$.
Use GSW labels $(u,v,x,y)=(0,1,2,3)$, new vertices
$(p,q,r,s)=(8,9,10,11)$, arms $up,vq,xr,ys$, and square
$pq,qs,sr,rp$. Define the vertex potential $\alpha_p=1$ and all other
potentials zero, so $w(ab)=\alpha_a+\alpha_b$.

Every child Hamiltonian cycle has weight **2**. The square-matching
difference
$\delta=w(pr)+w(qs)-w(pq)-w(rs)$ is **0**. But the two length-three
path sums are

$$
\widehat w(uv)=w(up)+w(pq)+w(qv)=2,\qquad
\widehat w(xy)=w(xr)+w(rs)+w(sy)=0.
$$

All other parent weights are zero. Both $N_{10}$ and $N_{01}$ are nonempty
(one cycle each), and their aggregated weights are respectively **2 and 0**.
There is no common $\gamma$ as asserted by I166 §5. This is a necessary-
condition failure on an actual vertex potential, not a subtle failure of
induction. The full labelled witness is in `diagnostic-attempt-01.json`.

### 3.2 Correct complete six-class system

Fix an admissible expansion with cyclic terminal order
$u,v,\ldots,y,x,\ldots,u$ and $K=G-\{uv,xy\}$. Put

$$
a=w(pq),\ b=w(rs),\ c=w(pr),\ d=w(qs),\quad
S=a+b+c+d,\quad \delta=c+d-a-b,
$$

and $t_u=w(up),t_v=w(vq),t_x=w(xr),t_y=w(ys)$.
Define the **normalized**, not length-three-aggregated, parent weight

$$
W|_K=w|_K,\qquad W(uv)=t_u+t_v-a,\qquad W(xy)=t_x+t_y-b.
$$

**Proposition CW167.** For any real child edge weighting $w$, it is constant
with value $\lambda$ on all child Hamiltonian cycles if and only if the
following equations hold for every object in the indicated class, where
$\gamma=\lambda-S$:

$$
\begin{array}{rll}
 W(C)&=\gamma,&C\in N_{10}\cup N_{01},\\
 W(C)&=\gamma+\delta,&C\in N_{11},\\
 w(P)&=\gamma-t_u-t_x+c,&P\in P_{ux},\\
 w(P)&=\gamma-t_v-t_y+d,&P\in P_{vy},\\
 w(D)&=\gamma+a+b-(t_u+t_v+t_x+t_y),&D\in D_{11}.
\end{array} \tag{CW167}
$$

Here $D_{11}$ consists of spanning two-path covers with terminal pairing
$(u,v),(x,y)$, without cycle components. Empty classes contribute no
equations. There is deliberately no equation for $N_{00}$.

**Proof.** With two arms, the square portion must be its unique spanning
path between adjacent corners. For $N_{10}$ the added weight is
$t_u+t_v+b+c+d$, giving $W(C)+S$; for $N_{01}$ it is
$t_x+t_y+a+c+d$, again $W(C)+S$.
For $N_{11}$ the added square matching is $pq,rs$, giving
$W(C)+2(a+b)$.
For $P_{ux}$ the square path omits $pr$, adding
$t_u+t_x+S-c$; for $P_{vy}$ it omits $qs$, adding
$t_v+t_y+S-d$. For $D_{11}$ the square matching is $pr,qs$,
adding $t_u+t_v+t_x+t_y+c+d$.
The four-arm exterior cannot use the crossing pairing $(u,y),(v,x)$
in a planar disk. The other two pairings are exactly $N_{11}$ and
$D_{11}$, with one connecting square matching each. These six disjoint
fibres exhaust all child Hamiltonian cycles. Subtracting their added
weights proves necessity and sufficiency. ∎

This checks **complete sets**, not just counts, on all 636 tested
expansions, and tests their coefficient formulas with independent signed
weights. In particular the corrected $N_{11}$ sign is **plus** for the
specified $\delta$. The exact cross-class offsets in the last three
equations are essential; independent within-class constancy is weaker.
The original is not relabelled PASS after this correction.

## 4. Exchange attack: proved obstructions and exact finite results

### 4.1 The transported hull has exactly the survival rank

For a parent cycle write $E=\chi_C(uv)$ and $F=\chi_C(xy)$.
For $E+F\ge1$ its unique child lift has unchanged coordinates on $K$,
arm coordinates $(E,E,F,F)$, and square coordinates

$$
(\chi(pq),\chi(rs),\chi(pr),\chi(qs))=(F,E,2-E-F,2-E-F).
$$

This is a single affine map on the whole surviving class, not separate
unrelated maps. It is injective on that affine hull: recover the $K$
coordinates unchanged and $E,F$ from the arms. Therefore the affine
dimension of the **transported child cycles equals** $d_{\rm surv}$.
Consequently the new path classes must supply at least

$$
d(G)+2-d_{\rm surv}=2+\bigl(d(G)-d_{\rm surv}\bigr)
$$

new directions to prove the exchange step. “Two extra dimensions” is
insufficient accounting whenever transport loses old directions.
I166's survival conclusion is thus justified, but its quantitative
interpretation needs the lost directions added back.

### 4.2 A universal fixed-terminal path-rank obstruction

**Proposition P167.** For every admissible expansion of $G\in\mathcal B$,
put $\beta(K)=|E(K)|-|V(G)|+1=n/2-1$ and let
$\epsilon=1$ if $vy\in E(K)$, otherwise $0$. Then

$$
\dim\operatorname{aff}P_{ux}
\ \le\ \beta(K)-2+\epsilon
\ <\ \beta(K). \tag{P167}
$$

The symmetric assertion holds for $P_{vy}$, with $ux$ in place of $vy$.
The stipulated P4 result guarantees these path families are nonempty.

**Proof.** In $K$, vertices $v,y$ have degree two and are not endpoints
of a spanning $u,x$ path. Every such path uses both edges incident with
each of $v,y$. Every difference of two path vectors is therefore zero
on their incident edges and lies in the degree-matrix kernel of
$K-\{v,y\}=G-\{v,y\}$. The latter is connected by 3-connectivity and
is bipartite. Deleting $v,y$ removes $4-\epsilon$ edges and two vertices.
Its cycle-kernel dimension is
$\beta(K)-2+\epsilon$. This proves both inequalities. ∎

Thus constancy on $P_{ux}$ **cannot**, in this full scope, force
$w|_K$ to be a vertex potential. The space annihilating path differences
is strictly larger than the $(n-1)$-dimensional potential space.
This is a full-scope reduction, not a sample-based claim.

Even allowing arbitrary weights on the forced incident edges does not
make the naive path-fullness assertion true. In the expanded-cube witness,
$P_{ux},P_{vy},D_{11}$ are all singletons. The first path is
$(0,4,5,1,3,7,6,2)$. It has affine dimension zero, whereas
$\beta(K)=3$ and the forced-edge-reduced upper bound is 2.
A unit weight on edge $04$ has nonzero alternating sum on
$0,2,6,4,0$ in $G-\{1,3\}$, yet is constant on the singleton path.
It is neither a potential nor a potential plus weights supported only
on the edges incident with $1,3$. P4 existence alone cannot manufacture
the proposed weight-controlling family. No source theorem is contradicted.

### 4.3 New finite exchange campaign

For **all 636 face-labelled admissible C4 expansions from all 15 census
graphs of order at most 20**, the child is certified in $\mathcal B$,
both Hamiltonian-cycle enumerators agree, and exact ranks give
$d(H)=d(G)+2$. Children have order at most 24; these are 636 steps,
**not 636 distinct graphs**.

- On the original 142 steps: exactly 136 survival failures, maximum
  deficit 5, maximum $N_{00}$ proportion $1/2$, as in I166.
- On all 636 steps: 498 survival failures, maximum deficit 7.
  The path classes must add as many as **nine**, not merely two, directions.
- No single $P_{ux}$ class is full in $\ker A_K$: **0/636**, as P167 proves.
- The span of the within-class differences of **all three** new families
  fills $\ker A_K$ in only **8/636** steps. Even their combination cannot
  replace the exact cross-class equations in general.
- The required extra-rank distribution is
  $2:138,\ 3:441,\ 5:34,\ 7:13,\ 9:10$.

These checks find no exchange counterexample. They do not prove exchange,
and failure of the tested proof methods refutes neither (T) nor Q164.
CW167 is a corrected interface, **not a solved exchange lemma**.

## 5. McCuaig generation: actual contract and affine mismatch

The original 2001 Wiley article returned **HTTP 403 Forbidden**.
Its original proof and stronger splitter theorem remain unread.
I obtained and read full statements in two later primary papers:
Fabres et al., *Minimal Braces*, Theorems 1.8 and 3.4, and
Carvalho–Lucchesi–Murty, *On the Number of Perfect Matchings in a
Bipartite Graph*, Theorems 2.5 and 2.6. Owned PDFs, extracts and retrieval
receipts are in the sources directory.

The contract: a simple brace outside the exceptional prisms, Möbius
ladders and biwheels (with small $K_2,C_4$ conventions as appropriate)
has a **strictly thin edge** $e$: deleting it and bicontracting degree-two
vertices yields a smaller simple brace. Repeating gives a brace-generation
sequence. The inverse operations have index 0, 1 or 2:
edge addition; one vertex bi-split plus one edge; two opposite-color
vertex bi-splits plus one edge. A bi-split partitions a noncubic vertex's
incident edges into two blocks of size at least two and inserts a
degree-two middle vertex.

Planarity is preserved in the reducing direction, since deletion and
contraction are minor operations. Thus planar braces admit such a
**planar** reducing sequence under this theorem. The sequence need not
be **cubic**. Starting from a cubic graph, every edge has index 2.
A strictly thin reduction changes

$$
(n,m)\longmapsto(n-4,m-5),
$$

and produces two degree-four vertices, all remaining vertices degree
three. (There is no triangle, so the two contraction triples are disjoint;
strict thinness rules out parallel edges in the result.) The cycle-space
dimension drops by one, not by the two dimensions in a C4 expansion.
The stipulated P4 theorem and I165's cubic splice theorem do not directly
apply to those noncubic intermediate braces.

**Explicit typed interface.** Delete $uv$ and bicontract
$\{a,u,b\}$ and $\{c,v,d\}$, where $a,b$ are the other neighbors of $u$
and $c,d$ those of $v$. At each resulting degree-four vertex retain the
two pairs of ports inherited from its two outer vertices.
Hamiltonian cycles of the cubic graph **avoiding $uv$** correspond
bijectively to Hamiltonian cycles of the retract that use one port from
each pair at both degree-four vertices. Proof: an avoiding cycle uses
$a-u-b$ and $c-v-d$; contracting these disjoint subpaths preserves one
cycle. The one-from-each-pair condition is exactly what permits the
inverse subdivision, which is unique. This map is affine and injective
on the incidence affine hull after adding back the fixed path edges.
Unrestricted retract Hamiltonian cycles are not interchangeable with
these typed cycles.

Own witness: a 16-vertex brace, deleted edge $02$, has a 12-vertex simple
brace retract with degree sequence $3^{10}4^2$. It has **14**
Hamiltonian cycles but only **8** satisfy the typed port rule, exactly
the eight original cycles avoiding $02$. The full graph, retract and
counts are in `support-attempt-01.json`. Thus blindly transporting
all retract cycles would already be false at this size.

This makes McCuaig a possible **typed-state** induction, not a free
replacement for HMM+(AS). The needed affine theorem for noncubic braces
with port constraints is unpaid. I did not claim it or assume all planar
braces Hamiltonian.

**Fallback induction design, without a generation gap.** Use strong
induction on all of $\mathcal B$. Non-braces are handled by their smaller
tight-cut factors and (AS). For a non-base brace, HMM gives a C4
predecessor: a cube expansion cannot be its last step. If that predecessor
is a brace, use its inductive fullness; if it is a non-brace, use (AS) on
its tight-cut factors. In both cases the remaining obligation is CW167
forcing child potentials. The predecessor need not have a brace-only
history; B18 is explicitly covered. This is a correct architecture,
not a proof of the unpaid step.

## 6. A distinct supporting angle: dual-tree transfers

### 6.1 A full-scope antichain obstruction

For a Hamiltonian cycle of a plane cubic 3-connected graph, the faces
on its two sides each induce a tree in the dual. One proof uses the
noncrossing remaining chords in each disk: their weak dual is a tree.
Equivalently, this is the usual dual tree-partition correspondence.
Fix a dual root and denote the shore not containing it by $S_C$.

**Proposition A167.** The sets $S_C$ for distinct Hamiltonian cycles
form an antichain. More generally, in any 3-edge-connected graph,
nonempty proper sets inducing trees on both shores form an antichain
after fixing which shore avoids a root.

**Proof.** Suppose $S\subsetneq T$ are two such shores. Pick a connected
component $R$ of the induced graph on $T\setminus S$. In the induced tree
on $T$, this component has exactly one edge to the nonempty tree on $S$:
at least one for connectivity, at most one to avoid a cycle.
In the induced tree on $V\setminus S$, it similarly has exactly one
edge to the nonempty tree on $V\setminus T$. It has no edges to another
component of $T\setminus S$. Hence $\delta(R)$ has size two,
contradicting 3-edge-connectivity. ∎

The dual of the plane graph in question is 3-edge-connected, so the
general lemma applies. I167 verifies the full dual tree correspondence
and pairwise non-inclusion for all cycles of all 15 census graphs.

This rules out **any nonempty one-direction transfer of faces**, not only
a single-face toggle, as a Hamiltonian-preserving move. A dual ear/leaf
exchange proof must move faces in both directions. This is a genuinely
different obstruction to a concrete induction mechanism, not a new name
for (T). It gives no growing lower bound by itself.

### 6.2 What switch spanning actually establishes

A signed vector of a **single** alternating cycle whose toggle takes one
Hamiltonian cycle to another is an HC difference. Therefore if these
vectors span $\ker A_G$, then $d(G)=n/2+1$.
The reverse implication needs an additional argument: the symmetric
difference of two Hamiltonian cycles may have several alternating
components, and toggling one component need not remain Hamiltonian.
Decomposing the difference into its components does not by itself put
each component in the single-HC-switch span.

I166 gives no bridge across this issue. I167 finds no counterexample to
the stronger switch statement: its rank is full on all 15 census graphs.
Nevertheless it is **not used as an established equivalence**. If
“switch” means an entire multi-component HC difference, equivalence is
immediate but loses the claimed single-cycle content. No universal
single-switch connectivity or spanning theorem was proved here.

The stipulated signed-state cancellation machinery was also read in its
actual source range. Its nonzero Taylor coefficient pays existence of
a forest state, not a number of affinely independent HC witnesses.
No new multiplicity claim is extracted from that nonvanishing statement.

## 7. Precise unresolved target and contribution assessment

The live target remains

$$
(T)\qquad d(B)=|V(B)|/2+1
\quad\text{for every cubic planar brace }B.
$$

Under the stipulated nonempty-port hypotheses, (AS) plus tight-cut
decomposition makes this equivalent to full dimension on all of
$\mathcal B$. The all-class C4 exchange inequality plus HMM and (AS)
would prove that assertion; conversely all-class fullness implies the
exchange inequality. As before, $h(G)\ge d(G)+1$ would then prove Q164,
sharply on the even prisms.

**No proof or counterexample of these universal assertions is delivered.**
The exchange obligation is now the *corrected complete* CW167 system,
including all three cross-class offsets, not I166's false aggregation.

**Contribution: technical research only, no ninth nomination.**
Concrete full-scope reductions supporting this classification:

1. CW167 is the six established boundary fibres with their edge weights
   added exactly; the original failure is a single vertex-potential test.
2. P167 is a forced-edge observation followed by the connected bipartite
   incidence-rank formula on $G-\{v,y\}$.
3. The transported-rank identity is an explicitly invertible affine map.
4. The McCuaig port interface is contraction/subdivision of two fixed
   subpaths, with its scope witnessed exactly.
5. A167 reduces entirely to the two forbidden boundary edges of a
   component between nested tree partitions.
6. The finite campaign is independently checkable evidence, not a
   universal theorem or a novelty certificate.

These are useful corrections and method exclusions. None closes the
global rank gap or produces the requested genuinely substantial finding.
Searches were made early and repeated for affine hulls, path hulls,
brace generation, switch spanning and dual antichains. No exact relevant
primary result was located; blocked original McCuaig retrieval is
distinguished from absence. No unverified MathDB metadata is used.

**Next action.** Work in the quotient by vertex potentials with CW167's
cross-class equations intact. The target is to recover the
$d(G)-d_{\rm surv}$ lost directions **and** two new ones using path classes
jointly; single-family affine fullness and within-family-only arguments
are excluded. Seek a two-direction dual exchange or a typed
degree-four-retract theorem, but require an explicit rank-producing
construction rather than another equivalent unpaid condition.
First test any candidate on the cube's three singleton new classes and
the recorded steps requiring nine new directions.

## 8. Evidence, replay and honest limits

All diagnostics are owned standard-library Python, run with `-I -B`.
The authoritative files are:

- `kernel.py`: independent graph, enumeration and integer-rank toolkit;
- `diagnostics.py` → `diagnostic-attempt-01.json`;
- `support.py` → `support-attempt-01.json`;
- `reduction_audit.py` → `reduction-01.json`;
- `verify.py`: immutable-first, read-only replay;
- `owned-files.json`, `prevalidation.json`, `seal.py`, `seal.json`.

Replay binds this report, every owned payload/source/code byte and every
non-context external byte **before** running only the listed owned
diagnostics. It forbids writes, network and subprocesses, and rejects
ancestor code execution. The exact inventory excludes only the three
control files `owned-files.json`, `prevalidation.json`, `seal.json`;
the seal binds the inventory and prevalidation receipts. The seal writer
requires successful read-only prevalidation and uses exclusive creation.
There is exactly one seal creation; no resealing after errors.

**Preserved earlier failure:** an initial blanket recheck of the 70
external bindings failed because the parent concurrently updated the two
shared progress ledgers. `context-drift-01.json` retains old/new hashes
and the failure. The original binding file is unchanged. The explicit
`replay-policy.json` excludes only those two mutable context ledgers from
mathematical replay, not a single old result, report, source or payload.
Their later openings still say eight accepted and research active.
No diagnostic mathematical failure is hidden by this policy.

Successful prevalidation and the one seal must be checked in their
receipts; final hashes are returned separately so this report is not edited
after sealing. The final replay checks deterministic equality of all three
payloads. It is a reproducibility check, not an independent proof jury.

Limits: 452 records receive metadata checks, not full re-enumeration;
large independent checks cover eleven deterministic records with one
enumerator; dual enumerators cover the 15 census graphs, 636 steps and
240 splices. Census completeness stops at order 20. The 636 steps can
repeat isomorphic graphs. Original McCuaig proof retrieval is blocked.
Novelty is not certified. All universal positive targets remain open.
