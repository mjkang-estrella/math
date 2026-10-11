# I184: the alternating cycle exists; connected reconnection remains open

2026-10-11. **Z184 UNRESOLVED. E183 UNRESOLVED.**
All OpenAI results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`
are stipulated true. Eight accepted findings remain eight; two remain.

This is a written proof attempt, not a computational package. Section 3
proves the first of the two obligations in the brief by a direct cut
argument. It does not prove the connected-complement obligation.
The elementary lemma is not nominated as a ninth finding or as new to
the literature. Independent correctness and contribution review remain
necessary before any substantial candidate can be accepted.

## 1. Exact target, with all hypotheses retained

Let $X$ be any finite connected simple bipartite locally cubic disk.
Its five distinct degree-two ports are $b_0,\ldots,b_4$, in boundary
order $(0,2,1,4,3)$, with colors $(1,1,1,0,1)$ in label order.
All other vertices of $X$ have degree three. Glue cut edges $e_i$
from $b_i$ to the respective exterior vertices $(1,5,6,28,29)$.
The exterior $Y$ has vertex set $\{1,\ldots,11,28,29\}$ and exactly
the internal edges

```
1-7,1-28,2-3,2-8,2-29,3-4,3-9,4-5,4-10,5-11,
6-7,6-11,7-8,8-9,9-10,10-11,28-29.
```

Require the glued graph $G$ to be simple, planar, bipartite and a
brace. In particular, every two disjoint edges of $G$ extend to a
perfect matching. All eleven survivor local fibres are complete and
nonempty:

```
02;02  12;12  14;14  24;24  0123;02,13  0123;03,12
0134;03,14  0234;02,34  0234;03,24  1234;12,34  1234;14,23.
```

Keep the complete lost fibre $P=(01;01)$ and the lost type
$D=(0134;01,34)$. A packing spans its side, has degree one precisely
at the used ports, degree two elsewhere, and has no isolated cycle.
Fibre and compatible exterior-product completeness mean completeness,
not a list of representatives.

The internal, port-disjoint two-square patch consists of the two
quadrilateral faces with shared edge $xy$ and simple boundary
$C=(x,a,b,y,d,c,x)$. Put

$$
A=\{xa,by,dc\},\qquad B=\{ab,yd,cx\}.
$$

For every $p$ in complete $P$ with $p\cap E(C)=A$, assume
$q=p\triangle E(C)$ is also in complete $P$. Write
$G'=G-V(C)$ and let $\mathcal H(q)$ be the complete set of Hamiltonian
completions of this particular $q$ in the exact $G$.

Z184 asks, for every such $(X,p,q,C)$, whether

$$
\exists H_0\in\mathcal H(q)\ \exists Z\subseteq G':
\quad Z\text{ is a simple }M_0\text{-alternating cycle},\
e_2\in E(Z),\
H_0\triangle E(Z)\text{ is connected},
\qquad M_0=E(G)\setminus E(H_0).
$$

The completion quantifier is existential. We do not replace it by a
universal completion quantifier. E183 asks instead for some perfect
matching containing $A$ whose complement is Hamiltonian and has a
survivor local type, without the single-cycle or cut-2 prescription.

## 2. Paid local facts and the starting matching

Here are the local deductions from the I183 final analytic review,
with their short cut arguments made explicit where used below.

Color $x,b,d$ black and $a,y,c$ white. Vertices $x,y$ are already
cubic within the patch. An additional internal patch edge could only
be $ad$ or $bc$. Both together would close a six-vertex component,
contrary to connectedness and the disjoint exterior.

If only $ad$ existed, the patch shore would have exactly the two
outgoing edges $bb',cc'$. The disjoint edges $bb',cd$ would extend
to a perfect matching. That matching would cross the even six-vertex
shore exactly once, impossible since

$$
|S|=2|M\cap E(S)|+|M\cap\delta(S)|.
$$

If only $bc$ existed, use $aa',cd$ instead. Thus the four continuation
edges $aa',bb',cc',dd'$ all leave $V(C)$.

Their terminals are distinct. Bipartition permits only $a'=c'$ or
$b'=d'$. If $a'=c'=t$, the shore $V(C)\cup\{t\}$ has four black
vertices and three white vertices; every white vertex has all its
neighbors in the shore. Every perfect matching therefore crosses its
three-edge cut exactly once. Two cut edges with different outside
endpoints would be disjoint, violating two-extendability. If all
outside endpoints coincide, their common cubic endpoint closes an
eight-vertex component, again impossible. Reverse colors to exclude
$b'=d'$. This uses the seven-vertex shore, not the unsuccessful
smaller Hall-set argument.

Consequently, in $G'$ the only degree-two vertices are $a',b',c',d'$.
The black ones are $a',c'$ and the white ones are $b',d'$.
Every other vertex of $G'$ has degree three. These are continuation
terminals, not the five boundary ports; primes distinguish the notation.

Deleting $A$ bijects perfect matchings of $G$ containing $A$ with
perfect matchings of $G'$. Indeed $A$ covers every removed vertex, so
no other matching edge can touch the patch. Conversely adjoining $A$
to any perfect matching of $G'$ covers all vertices of $G$.

At $x,y$ the packing $p$ must use $xy$, and at $a,b,c,d$ it must use
the four continuation edges. The same statements hold for $q$,
which uses $B$ instead of $A$. Completeness gives
$\mathcal H(q)\ne\varnothing$. Every $H_0\in\mathcal H(q)$ therefore
has complementary perfect matching $M_0$ containing $A$. Its
restriction $M'=M_0\setminus A$ is a perfect matching of $G'$.
Since $q$ has used set $\{0,1\}$, $e_2\notin E(H_0)$ and
$e_2\in M'$. The port-disjoint patch ensures $e_2\in E(G')$.

## 3. First obligation: a cycle through the matching edge exists

### Lemma, no edge is forced in all residual perfect matchings

Under the exact patch and brace hypotheses above, for **every**
perfect matching $M'$ of $G'$ and every edge $e\in M'$, there is
a simple $M'$-alternating cycle in $G'$ containing $e$.

This conclusion does not assume that $G'$ is a brace, two-extendable,
or even that every nonmatching edge of $G'$ belongs to a perfect
matching. None of those stronger assertions is being made.

### Proof

Write $e=uv$ with $u$ black and $v$ white. In $G'-e$, orient every
nonmatching edge from black to white and every remaining matching
edge from white to black.

If there is a directed path from $u$ to $v$, choose one with no
repeated vertex. It starts and ends with a nonmatching edge and
alternates between nonmatching and matching edges. Adjoining $e$
gives the required simple alternating cycle. Simplicity of $G'$
precludes a second edge $uv$, so this is not a spurious two-edge
cycle.

Suppose, to the contrary, that $v$ is not reachable. Let $S$ be the
reachable black vertices and $T$ the reachable white vertices.
Then $u\in S$, $v\notin T$, and $M'$ gives a bijection

$$
T\longleftrightarrow S\setminus\{u\}.
$$

In fact every reachable white vertex has its matching successor
reachable, and every reachable black vertex other than the starting
vertex is reached along its unique incoming matching edge. Thus
$|S|-|T|=1$.

Every nonmatching neighbor of a vertex of $S$ lies in $T$. For
$s\in S\setminus\{u\}$ its matching neighbor also lies in $T$;
the sole exception is $uv$. Hence in $G'$ exactly one edge goes
from a black vertex in $S$ to a white vertex outside $T$, namely $e$.
Let $h\geq0$ count edges from a white vertex in $T$ to a black vertex
outside $S$. Define the terminal deficits

$$
r=|S\cap\{a',c'\}|,\qquad s=|T\cap\{b',d'\}|.
$$

Counting black degrees minus white degrees inside $S\cup T$ cancels
every internal edge and gives

$$
1-h=(3|S|-r)-(3|T|-s)=3-r+s.
$$

Therefore $r-s=2+h$. Because $r\leq2$ and $s,h\geq0$, necessarily

$$
r=2,\qquad s=0,\qquad h=0.
$$

Put $W=S\cup T$. It follows that

$$
\delta_{G'}(W)=\{e\},\qquad
\delta_G(W)=\{e,aa',cc'\}.
$$

All three edges leave a black vertex of $W$. In particular every
white vertex of $W$ has every neighbor inside $W$, and $W$ has one
more black than white vertex. Every perfect matching of $G$ must
therefore use **exactly one** edge of $\delta_G(W)$: all white
vertices must be matched internally, leaving exactly one black
vertex to match outside.

But $aa'$ and $cc'$ are disjoint edges, since the continuation
terminals are distinct. Brace two-extendability gives a perfect
matching containing both, a contradiction. The directed path must
exist, proving the lemma. $\square$

### Consequences and limits

Applied to $e_2\in M_0\setminus A$, this proves the first obligation
for **every** $H_0\in\mathcal H(q)$, hence also for some completion.
The stronger completion quantifier is proved here only for existence
of an alternating cycle, not for its connected-complement property.

Equivalently, no edge belongs to every perfect matching of $G'$.
For one direction, toggle the cycle just proved. For the converse,
if another perfect matching omits $e$, its symmetric difference
with $M'$ has degree zero or two at every vertex; its component
through $e$ is a simple alternating cycle. This equivalence uses
no matching-polytope or matching-structure theorem.

The proof pays the descent issue explicitly. It does not infer
three-edge-frozen extendability from two-extendability. It uses
two-extendability once, on the two continuation edges across the
specific shore forced by failure of reachability. The exact fixed
exterior and complete fibres remain hypotheses of Z184; this local
lemma happens not to require their additional strength.

## 4. Second obligation: exact segment reconnection

Fix $H_0\in\mathcal H(q)$ and a cycle $Z$ supplied by Section 3.
Set

$$
R=E(Z)\cap E(H_0),\qquad T_Z=E(Z)\cap M_0.
$$

Alternation gives $|R|=|T_Z|=k\geq2$, and both $R$ and $T_Z$
are matchings on the vertices of $Z$. The new complement is

$$
H_Z=(H_0-R)\cup T_Z
    =H_0\triangle E(Z).
$$

It is a spanning degree-two subgraph. This degree assertion does
not yet assert that it has one component.

Delete the edges $R$ from $H_0$ while retaining all vertices. The
remaining subgraph has exactly $k$ path components. Regard each
path as having two labelled endpoint incidences. For a general
version with adjacent deleted edges, an isolated vertex is a
length-zero path with two incidences at that vertex and is retained.
In the present simple alternating-cycle setting $R$ is a matching,
so such singleton paths do not actually arise.

Contract each path component to one vertex, and retain each edge
of $T_Z$ as a separately identified edge between the associated
incidences. Call the resulting multigraph $K_Z$. Loops count twice
toward degree, and parallel edges are not identified or removed.
Each contracted path supplies two endpoint incidences and each is
incident with exactly one edge of $T_Z$. Thus $K_Z$ is 2-regular.

Contraction of the disjoint connected paths preserves components;
expanding each contracted path is the inverse operation for
component connectivity. Hence

$$
\#\operatorname{comp}(H_Z)=\#\operatorname{comp}(K_Z).
$$

In particular $H_Z$ is Hamiltonian if and only if $K_Z$ is connected.
A one-vertex component with a loop and a two-vertex component with
two parallel edges must be counted as components, not erased as
degenerate artifacts.

There is also an endpoint-only formulation. Let $S_H$ pair the two
endpoint incidences of each retained path. Then
$S_H\cup T_Z$, with multiplicities and edge identities retained,
has exactly the same number of components as $H_Z$. The connected
cycle $Z$, however, certifies connectedness of **$R\cup T_Z$**,
not of **$S_H\cup T_Z$**. Those are different pairings.

## 5. The precise failed implication in this proof attempt

The failed step is:

> From a simple alternating cycle, even one chosen shortest through
> $e_2$, pass from connectedness of the removed-edge pairing
> $R\cup T_Z$ to connectedness of the retained-path pairing
> $S_H\cup T_Z$.

That inference is false as a pairing inference. It is not another
name for the universal Z184 existence statement. It specifies exactly
which additional information the reachability proof fails to control.

For clarity, the following is an **abstract incidence calculation**,
not a new graph, an admissible $X$, or a counterexample to Z184.
Take four endpoint incidences $1,2,3,4$ in their order on $H_0$ and
the pairings

$$
R=\{12,34\},\qquad S_H=\{23,41\},\qquad T_Z=\{23,41\}.
$$

The copies in $S_H$ represent retained paths, whereas the copies in
$T_Z$ represent added edges; equality of endpoint pairs does not
identify these objects. The union $R\cup T_Z$ is one four-cycle.
But $S_H\cup T_Z$ has two components, each with parallel copies.
After path contraction $K_Z$ has two separate loops. Thus the
shortest possible simple alternating-cycle length alone does not
exclude the disconnection pattern. This does not assert that such
a shortest cycle, or all such cycles, occurs in an instance of Z184.

Section 3 rules out the absence of alternating paths by constructing
a forbidden color-imbalanced shore. The reachability sets and their
degree counts contain no ordering of endpoint incidences along
$H_0$. They therefore do not rule out the pattern just displayed.
To finish this route one needs a further argument using the exact
embedding, $p,q$, complete fibres or exterior choices that selects a
cycle whose retained-path pairing is connected. No such argument is
proved here.

Two further attempted repairs also stop short:

* Minimizing the number of components after toggling does not show
  that another available alternating toggle reduces that number.
  An additional toggle can alter the reference completion or produce
  a symmetric difference with several cycles rather than the one
  simple cycle required by Z184.
* Choosing a Hamiltonian survivor from a complete fibre and comparing
  its complementary matching with $M_0$ does not ensure that it
  contains $A$. Even if that extra restriction were supplied, the
  difference of two perfect matchings can have several alternating
  components. Connectivity after all toggles does not establish
  connectivity after just the component through $e_2$.

The abstract incidence obstruction is not promoted to an actual
counterexample: it has not been realized with the exact $Y$, brace,
eleven complete nonempty survivor fibres, and this prescribed
$p,q,C$. Nor has it excluded every $q$-completion. Z184 remains
unresolved, not false.

## 6. Exact implication for E183

If a pair $(H_0,Z)$ satisfying the remaining connectedness condition
exists, then

$$
M_Z=M_0\triangle E(Z)
$$

is a perfect matching. Because $Z$ avoids $V(C)$, it contains no
edge of $A$ and no edge incident with the patch, so $A\subset M_Z$.
Its complement is exactly $H_Z$. Connectedness and spanning
degree two make $H_Z$ Hamiltonian. Since $e_2\in M_0\cap E(Z)$,
the new complement uses $e_2$.

In the exact five-port setting, a Hamiltonian complement using cut
2 has a survivor local type: the two lost types $P$ and $D$ omit
that label. Read that local type from the full lifted complement,
not merely from a pairing of the four patch continuation incidences.
Thus **Z184 implies E183 instance by instance and universally**.

Section 3 alone gives an $A$-containing matching whose complement
uses $e_2$ and is a spanning 2-factor; it does **not** give a
Hamiltonian complement or a cycle-free local packing.

No converse or strict separation between Z184 and E183 is proved.
Failure of Z184 would not alone refute E183. Several toggles, or a
survivor not using cut 2 (including state 6), could still establish
E183 without this prescription.

## 7. Dependencies, validation and status

The exact setting and the local continuation facts are those of the
I184 brief, I183 final analytic review, finalized parent disposition,
and resumed analytic attempt Sections 1--6. The lemma in Section 3
and the reconnection proof in Section 4 are direct arguments above,
not applications of an unread external matching theorem.

Actual pinned statements `thm:main`, `cor:edge-avoidance`, and
`cor:pfaffian-paths` were read in the retained manuscript source.
They give Hamiltonicity, avoidance of one edge, and containment of
one three-edge path under their respective hypotheses. None is
used as a simultaneous frozen-matching/connectivity/survival theorem.
No claim that a contracted auxiliary graph is simple or a brace is
made.

Internal written checks covered both orientations of the bipartition,
the matching bijection in the reachability proof, all terminal-deficit
possibilities via the displayed inequality, the exactly-one-crossing
count, the disjointness needed for two-extendability, and preservation
of components under contraction/expansion. These are not independent
external review or a formal proof-assistant verification.

The required report/seal/verifier hashes matched before proof work;
the brief and parent disposition were also hashed and recorded then.
No graph generation, attachment changes, numerical tests, sweeps,
matching-population scans, historical replay, or Python implementation
was undertaken.

The parent reports completion of all 23 I183 stages, 562 owned files,
1,153 strict bindings, eight live blocked probes and the authentic-source
positive control, with replay about 8.76 seconds. Its independent
twelve facial controls and 626 retained matching cases remain finite
evidence: three patches, six directed instances, five controlled
matchings per instance. None is a universal proof here. The original
provider failure and incomplete unsealed checkpoint remain historical.

**Final disposition:** the first matching-cycle obligation is proved
in this written attempt; the connected-reconnection selection is not.
Z184 and E183/E182/E181/H180/L179, exchange/(T)/Q164 remain unresolved.
D168/M168 shortcuts, failed containments and isolated-toggle failures
are not revived. No acceptance, novelty clearance or lowered
contribution gate is claimed.
