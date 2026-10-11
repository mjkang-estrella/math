# I185: eligible ear splices and the unproved component reduction

2026-10-11. **Original Z184 UNRESOLVED; E183 UNRESOLVED.**
Eight accepted findings remain eight, with two remaining.
All OpenAI results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`
are stipulated true.

This is an unsealed, proof-only record. The elementary splice and
component-count identities below are internally checked deductions,
not an independently accepted result or a ninth finding. No graph
computation or new graph construction was undertaken.

## 1. Exact target and quantifiers

Let $X$ be any finite connected simple bipartite locally cubic disk
with five distinct degree-two ports $b_0,\ldots,b_4$, boundary order
$(0,2,1,4,3)$, and colors $(1,1,1,0,1)$ by label. All other vertices
are cubic. Join the ports by cut edges $e_i$ to the respective vertices
$(1,5,6,28,29)$ of the **fixed** exterior $Y$. Its vertex set is
$\{1,\ldots,11,28,29\}$ and its internal edges are exactly

```
1-7,1-28,2-3,2-8,2-29,3-4,3-9,4-5,4-10,5-11,
6-7,6-11,7-8,8-9,9-10,10-11,28-29.
```

Require the glued graph $G$ to be simple, planar, bipartite and a brace.
The eleven complete nonempty survivor fibres have types

```
02;02  12;12  14;14  24;24  0123;02,13  0123;03,12
0134;03,14  0234;02,34  0234;03,24  1234;12,34  1234;14,23.
```

Retain the complete lost fibre $P=(01;01)$ and lost type
$D=(0134;01,34)$. Packings span their side, have degree one exactly
at used ports, degree two elsewhere, and no isolated cycles.
Fibres and compatible exterior products are complete, not lists of
representatives.

The internal port-disjoint two-square patch has simple boundary
$C=(x,a,b,y,d,c,x)$ and shared chord $xy$, with

$$
A=\{xa,by,dc\},\qquad B=\{ab,yd,cx\}.
$$

For every $p\in P$ using exactly $A$ on $C$, require
$q=p\triangle E(C)\in P$. Write $\mathcal H(q)$ for **all**
Hamiltonian completions of this $q$ in this exact $G$, and
$G'=G-V(C)$. The target remains

$$
\forall (X,p,q,C)\text{ as above},\quad
\exists H_0\in\mathcal H(q)\ \exists Z\subseteq G':
\quad
\begin{cases}
Z\text{ is a simple }M_0\text{-alternating cycle},\\
e_2\in E(Z),\\
H_0\triangle E(Z)\text{ is connected},
\end{cases}
\quad M_0=E(G)\setminus E(H_0).
$$

It does not ask for every completion to work. E183 asks for some
$A$-containing perfect matching whose complement is Hamiltonian of a
survivor local type, without prescribing a single-cycle difference
or cut 2.

### Paid starting facts

The full I184 argument and finalized parent disposition are accepted
at their stated strength:

* The four continuations leave the patch and have distinct terminals
  $a',b',c',d'$. These are the only degree-two vertices of $G'$.
* Removing $A$ bijects perfect matchings containing $A$ with perfect
  matchings of $G'$. Every $H_0\in\mathcal H(q)$ has complementary
  matching containing $A$, and $e_2\in M_0\cap E(G')$.
* $\mathcal H(q)$ is nonempty. For every perfect matching $M'$ of
  $G'$ and every $e\in M'$, there is a simple $M'$-alternating cycle
  through $e$ in $G'$.

The last fact follows from I184's reachable-set identity
$r-s=2+h$, the forced values $(r,s,h)=(2,0,0)$, and the
one-crossing shore with cut $\{e,aa',cc'\}$ contradicting extension
of the disjoint pair $aa',cc'$. It does not assert that $G'$ is
two-extendable or that every nonmatching edge is usable.

Thus the set of pairs $(H_0,Z)$ satisfying everything except final
connectedness is finite and nonempty. Choose a pair minimizing,
lexicographically,

$$
\bigl(c(H_0,Z),\,|E(Z)|\bigr),\qquad
c(H_0,Z)=\#\operatorname{comp}(H_0\triangle E(Z)),
$$

**over all completions and all their qualifying cycles**. In the
rest of the argument keep this $H_0$ fixed. Put
$F=H_0\triangle E(Z)$. If $c=1$, Z184 is paid for this instance.
The attempted improvement concerns $c>1$.

## 2. Exact ear eligibility

Use $M=M_0\cap E(G')$ when speaking of alternation in $G'$.
An ear here is a simple path $Q\subseteq G'$ with distinct endpoints
$u,v\in V(Z)$, internal vertices outside $V(Z)$, and no edge of $Z$.
The last condition explicitly excludes treating an existing cycle
edge as a length-one ear. A genuine length-one chord is allowed.

### Lemma 1: the endpoint edges and the replaced arc are forced

Suppose $Q$ is $M$-alternating. Both endpoint edges of $Q$ are outside
$M$, hence are edges of $H_0$. Its length is odd and its endpoints
have opposite bipartition colors. There is exactly one $u$--$v$ arc
$I$ of $Z$ whose first and last edges are outside $M$. The other arc
$J$ starts and ends in $M$. The only alternating splice using $Q$
and one arc of $Z$ is

$$
\widehat Z=J\cup Q.
$$

It is a simple $M$-alternating cycle. It contains $e_2$ exactly when
$e_2\in E(J)$, equivalently $e_2\notin E(I)$.

**Proof.** At each vertex of $Z$, the unique matching edge already
lies on $Z$. An edge of an ear leaving $Z$ cannot be that edge.
Since $G$ is cubic and $H_0$ is its complementary 2-factor, the ear
uses the remaining $H_0$ edge at each endpoint. Alternation therefore
starts and ends outside $M$, so $|E(Q)|$ is odd. Bipartiteness gives
opposite endpoint colors.

Orient matching edges white-to-black and nonmatching edges
black-to-white. The alternating cycle becomes a directed cycle.
After naming $u$ black and $v$ white, the ear is directed from $u$
to $v$. The directed $u$--$v$ arc of $Z$ is $I$ and has nonmatching
first and last edges. The return arc $J$ has matching first and
last edges. Joining $J$ to $Q$ alternates at both endpoints;
joining $I$ to $Q$ fails alternation at both. Internal disjointness
gives a simple cycle. Simplicity of $G$ rules out a two-edge cycle
made from parallel length-one paths.

The ear shares no edge with $Z$, so in particular it does not
contain the already-present $e_2$. Retaining $e_2$ is exactly the
condition that it lies on $J$. This proves all assertions. $\square$

An endpoint cannot be one of $a',b',c',d'$: a degree-two vertex of
$G'$ on $Z$ has both its available edges on $Z$. An internal ear
vertex may be a continuation terminal. The conditions do not grant
an ear at every pair of opposite-color vertices, and an ear may
exist but remove the arc containing $e_2$.

Write the odd lengths as

$$
|E(I)|=2r+1,\quad |E(J)|=2s+1,\quad |E(Q)|=2t+1,
\qquad r,s,t\geq0.
$$

Then $I$ has $r+1$ nonmatching and $r$ matching edges, $J$ has $s$
nonmatching and $s+1$ matching edges, and $Q$ has $t+1$ nonmatching
and $t$ matching edges. These counts include length-one possibilities.
The splice changes cycle length by $2(t-r)$.

All later splices are restricted to $e_2\in J$. They leave $H_0$
and its local packing $q$ unchanged, avoid $V(C)$, and keep exactly
one simple alternating cycle. They do not use a sequence of net
disjoint cycles or a changed reference completion.

## 3. The exact complement update

For a path $K\in\{I,J,Q\}$ write

$$
R_K=E(K)\cap E(H_0),\qquad T_K=E(K)\cap M_0.
$$

Then

$$
\begin{aligned}
E(F)&=(E(H_0)\setminus(R_I\cup R_J))\cup T_I\cup T_J,\\
E(\widehat F)&=(E(H_0)\setminus(R_J\cup R_Q))\cup T_J\cup T_Q,
\qquad \widehat F=H_0\triangle E(\widehat Z).
\end{aligned}
$$

The relevant difference cycle is $W=I\cup Q$, **not** $\widehat Z$.
It is a simple cycle, and

$$
L=E(F)\cap E(W)=T_I\cup R_Q,\qquad
N=E(W)\setminus E(F)=R_I\cup T_Q.
$$

The two sets $L,N$ alternate around $W$ and each is a matching
covering $V(W)$. In particular

$$
|L|=|N|=k=r+t+1,\qquad
E(\widehat F)=(E(F)\setminus L)\cup N.
$$

To check the endpoints, $I$ begins and ends with edges absent from
$F$, while $Q$ begins and ends with edges present in $F$. Internal
vertices alternate by construction. This is also an alternating
switch for the complementary matching of $F$. It preserves degree
two, but that alone gives no component reduction. Because $W$ is
simple in a simple bipartite graph, $k\geq2$.

### Lemma 2: the exact gain criterion

Let $a$ be the number of components of $F$ meeting $L$. Deleting
$L$ breaks those $a$ cycles into exactly $k$ retained paths.
Let $S$ be the pairing of their $2k$ endpoint incidences, retaining
all path and edge identities. Let

$$
b=\#\operatorname{comp}(S\cup N).
$$

Here $L$ and $N$ are regarded as pairings on the same incidences.
Then

$$
\#\operatorname{comp}(S\cup L)=a,\qquad
c(H_0,\widehat Z)=c(H_0,Z)-a+b.                 \tag{1}
$$

Thus the splice improves the component minimum **if and only if**
$b<a$.

**Proof.** Every component of the 2-factor $F$ is a cycle. A touched
cycle from which $j\geq1$ edges are deleted becomes $j$ paths.
The edges of $L$ are a matching, so these paths are non-singleton.
Summing over touched cycles gives $k$ paths. Every vertex of $W$
is incident with exactly one deleted edge and hence is an endpoint
of one of these paths.

Restore $L$: the resulting endpoint multigraph $S\cup L$ expands
back into exactly the $a$ original touched cycles. Restore $N$
instead: it expands into exactly $b$ new cycles. No edge of $N$
can reach an untouched component, since all its endpoints lie in
$V(W)$. The other $c-a$ cycles survive unchanged. This proves
(1), by contraction and expansion rather than a degree-only
argument. Parallel pairing edges remain distinct. After path
contraction, loops count as components and are not discarded.
$\square$

The criterion uses the retained paths of $F-L$. This is an exact
update of the original Hamiltonian retained-path criterion, not a
replacement of it by the connectedness of $W$. To exhibit the
relationship directly, use the common spanning forest

$$
\mathcal P=H_0-(R_I\cup R_J\cup R_Q).
$$

These deleted edges are distinct. Since at least one edge of $H_0$
is deleted, $\mathcal P$ has only path components. Keep every
component, including singleton vertices: at $u,v$ both $H_0$ edges
have been deleted, so these are indeed singleton paths here.
There are no other vertices with two deleted $H_0$ edges, because
$Q$ is internally disjoint from $Z$ and the individual removed
sets are matchings.

Contract the paths of $\mathcal P$. The old and new reconnection
multigraphs add, respectively,

$$
\mathcal B_{\rm old}=T_I\cup T_J\cup R_Q,\qquad
\mathcal B_{\rm new}=R_I\cup T_J\cup T_Q.        \tag{2}
$$

Each gives degree two at the contracted path vertices, and their
component counts are $c(H_0,Z)$ and $c(H_0,\widehat Z)$.
Equation (2) follows by restoring the displayed edges to the common
forest before contraction, so it does not assume a spurious equality
of the two retained-path pairings. On each singleton $u$ or $v$,
use two distinct endpoint incidences, pairing them as a zero-length
path. One incidence can be assigned to the common $T_J$ edge in
both reconnections and the other to the restored $R_Q$ or $R_I$
edge. There is no need to identify these incidences by the original
deleted-edge names. This also shows why erasing singleton paths
would give an incorrect common-refinement calculation.

The pairings $S_H(Z)$ from $H_0-(R_I\cup R_J)$ and
$S_H(\widehat Z)$ from $H_0-(R_J\cup R_Q)$ are generally different.
Equations (1) and (2) account for that difference explicitly.

### Useful sufficient condition, not an existence theorem

If every edge of $L$ lies in a different component of $F$, then
$a=k$. Each retained path joins the two incidences of its own
deleted edge, so $S$ has the same endpoint pairs as $L$, but with
different edge identities. Because $L\cup N=W$ is one cycle,
$S\cup N$ is connected. Hence $b=1$ and the gain is $k-1>0$.

For example, conditionally on an actual eligible ear with
$|I|=1$, $|Q|=3$, the switch removes two edges of $F$. If these
are in distinct components, it merges the components and lowers
$c$ by one. This is a conditional proof, not an assertion that the
required short ear occurs in the exact instance.

Conversely, if $a=1$, no strict improvement is possible because
$b\geq1$. If $a\geq2$ but a component is cut more than once, it
can fragment. Merely touching several components does not determine
the sign of (1).

## 4. A precise failure of the proposed endpoint-joining shortcut

The following is a **formal six-incidence calculation only**.
It constructs neither a graph nor an admissible $X$, and is not
a counterexample to Z184 or to the exact-hypothesis ear mechanism.
Its purpose is to test the implication

> An eligible ear whose endpoints lie in different components of
> $F$ must strictly lower the complement component count.

Label the incidences on the difference cycle $W$ cyclically
$1,2,3,4,5,6$ and put

$$
\begin{aligned}
L&=\{12,34,56\},\\
N&=\{23,45,61\},\\
S&=\{12,36,45\}.
\end{aligned}                                                   \tag{3}
$$

Copies with equal endpoint labels in different sets are distinct:
$S$ denotes retained paths, not edges of $W$. Split $W$ into
$Q=(1,2,3,4)$ and $I=(1,6,5,4)$. With the memberships of Section 3,
$Q$ has edge types $R_Q,T_Q,R_Q$, and $I$ has edge types
$R_I,T_I,R_I$. Thus they have exactly the endpoint types and odd
lengths required for an ear replacement. A retained arc $J$ and
$e_2$ have not been supplied; this is a local calculation conditional
on eligibility, not a realization of those additional objects.

The old pairing $S\cup L$ has two components:

* incidences $\{1,2\}$, with the two distinct $12$ copies;
* incidences $\{3,4,5,6\}$, in the order
  $3\mathrel{L}4\mathrel{S}5\mathrel{L}6\mathrel{S}3$.

In particular the prospective ear endpoints $1,4$ lie in different
old components. The new pairing $S\cup N$ also has two components:

* incidences $\{1,2,3,6\}$, in the order
  $1\mathrel{S}2\mathrel{N}3\mathrel{S}6\mathrel{N}1$;
* incidences $\{4,5\}$, with the distinct $45$ copies.

Thus $a=b=2$. The switch attaches part of one old component to
the other, but leaves a separated piece. Also $|I|=|Q|=3$, so it
does not lower the secondary length objective. The obstruction
is **joining accompanied by fragmentation**, not lack of degree
preservation or of a single difference cycle.

This formal pattern is not ruled out by the two elementary local
tests of bipartition and noncrossing: give odd and even labels
opposite colors; every displayed pair joins opposite colors.
In a disk with boundary order $1,\ldots,6$, the pairs of $S$ can
be drawn disjointly, with $36$ enclosing $45$ and $12$ separate.
This observation only concerns these endpoint arcs. It does not
establish their simultaneous realization with a Hamiltonian $H_0$,
the rest of $Z$, the fixed exterior, the frozen patch, the brace
condition, or complete fibres.

Consequently, “different endpoint components plus alternation plus
local noncrossing implies a strict gain” is not a valid inference
from that data alone. An exact-instance theorem might still exclude
(3) or force a different ear. No such exclusion or selection has
been proved here.

## 5. Attempt to force a joining ear from the exact hypotheses

### 5.1 What the minimum really says

For the globally selected pair, every actual eligible ear must obey

$$
b>a\quad\hbox{or}\quad
\bigl(b=a\text{ and }|Q|\geq|I|\bigr).            \tag{4}
$$

Otherwise (1) lowers the primary objective, or equality in (1)
and $|Q|<|I|$ lowers the secondary objective. Formula (4) is only
a restriction on available ears. It is not a proof that $c=1$.
Pattern (3) explains concretely why a component-touching ear can
be consistent with both parts of this lexicographic minimum.

The missing sufficient assertion is now specific: when the minimum
has $c>1$, the exact brace/embedding/fibre/exterior hypotheses must
force a directed ear from a black vertex $u$ of $Z$ to a white
vertex $v$ of $Z$, neither an endpoint terminal, whose forced
removed arc $I$ avoids $e_2$, and for which the pairing of the
retained paths of $F-(T_I\cup R_Q)$ gives

$$
\#\operatorname{comp}\bigl(S\cup(R_I\cup T_Q)\bigr)
<
\#\operatorname{comp}\bigl(S\cup(T_I\cup R_Q)\bigr).                \tag{5}
$$

Neither the supply of alternating cycles nor “ear endpoints in
different components” proves (5). A plateau could also be used
only after proving an actual finite escape/improvement rule;
the length tie-breaker does not supply one for equal lengths.

### 5.2 Why the I184 reachability shore does not pay (5)

In the matching orientation, ordinary ears are directed excursions
off the directed cycle $Z$. They must leave at black vertices,
return at white vertices, and use a return arc avoiding deletion
of $e_2$. Reachability alone does not impose the pairing inequality.

The paid matching-cycle lemma does not itself provide an ear:
for a matching edge on $Z$, its witnessing cycle may just be $Z$;
for other matching edges, the supplied cycles are not asserted
to meet $Z$. Nor can an arbitrary departure edge be declared
usable, since usability of every nonmatching edge was not proved.

I184 assumed absence of **every** directed path from the exposed
black endpoint of one deleted matching edge to its white mate.
That yielded a genuine vertex reachability set, a matching
bijection leaving exactly one unmatched black vertex, and exactly
one possible black-to-outside edge. Only then did its deficit
equation force the forbidden three-edge shore.

Failure of (5) is not failure of ordinary directed reachability.
There can be paths, ears, and cycle exchanges, but all relevant
reconnections may satisfy $b\geq a$, or delete $e_2$. A search
restricted to “joining” states would need to remember the cut
segments and their endpoint pairing, not just the terminal vertex.
Projecting such a failed search to black and white vertex sets
does not show that every nonmatching neighbor is reachable:
traversing an edge can change the component/ordering data used
to reject a state. In particular it does not supply the sole-exit
condition or the equation $|S|-|T|=1$ used in I184.

No matching shore with an exactly-one-crossing condition is derived
from (4). Thus two-extendability cannot yet be applied to a
contradictory pair of continuation edges. The earlier proof
remains valid; its hypothesis of failed unfiltered reachability
has simply not been established at this new step.

### 5.3 Embedding

An ear with internal vertices outside $Z$ lies in one of the two
sides of the Jordan curve $Z$. This gives a planar theta
configuration $I,J,Q$ and validates using either simple boundary
$I\cup Q$ or $J\cup Q$. It does not change which arc is alternating
with $Q$, nor ensure that the retained arc contains $e_2$.

On the difference boundary $W$, retained $F-L$ paths are constrained
by the embedding. However, the formal pairing (3) is already
noncrossing on one side of that boundary and still has zero gain.
Therefore merely appealing to noncrossing retained paths cannot
replace the count in (5). The full embedding with $H_0,Z,C$ may
impose more, but an argument extracting such a restriction is
missing. No embedded exact-instance counterexample is asserted.

### 5.4 What the fixed exterior actually supplies

There is no substitution for $Y$. Since $q$ has type $P$, every
$H_0$ uses cuts 0 and 1 and omits cuts 2, 3 and 4. Its restriction
to $Y$ is a spanning path from vertex 1 to vertex 5.

Some internal exterior edges are forced directly, without a
matching scan: vertices 6, 28 and 29 use both their internal edges
in $H_0$. Hence $H_0$ contains

$$
6\!-\!7,\quad6\!-\!11,\quad1\!-\!28,\quad28\!-\!29,\quad2\!-\!29.
$$

At vertex 1, cut 0 and $1\!-\!28$ exhaust its Hamiltonian degree,
so $1\!-\!7\in M_0$. At vertex 7 this forces $7\!-\!8\in H_0$.
At vertex 6 the matching edge is $e_2$ itself. Thus a cycle through
$e_2$ chooses one of $6\!-\!7,6\!-\!11$, and an ear departing
there, if possible in its directed orientation, must use the
other. These facts fix local edge types, not the order in which
the retained paths return through the arbitrary disk $X$.

No proof extends these forced exterior edges into an ear satisfying
(5). Choosing a different exterior completion is allowed by the
global minimum and can alter retained-path pairings, but it still
leaves the local packing $q$ of type $P$. Exterior-only rerouting
does not itself give survival.

### 5.5 Complete fibres and brace extension

The eleven nonempty complete survivor fibres supply actual survivor
packings and all their compatible exterior products, not a
restriction on representatives. They do not, without an additional
argument, place $A$ in a survivor's complementary matching. Even
if such a survivor were supplied, its matching difference from
$M_0$ may have several alternating cycle components; their
combined connectivity says nothing by itself about the gain of
one eligible ear for the fixed $H_0$.

Brace two-extendability concerns extending two disjoint edges
to a perfect matching. It does not control the pairing $S$ after cutting multiple
edges of a prescribed 2-factor. No reduction converts the failure
of (5) into a violation of that property. Pinned Hamiltonicity,
one-edge avoidance and prescribed-three-edge-path statements are
also not simultaneous frozen-matching/ear/reconnection theorems.
No unread external ear theorem is invoked.

These are limitations of the attempted deductions, not proofs that
the full hypotheses cannot force an improvement.

## 6. Original verdict and implications

The round determines exact endpoint/parity/splice conditions and
proves the change in retained-path pairing by (1) and (2). It
does not force an eligible joining ear at the full hypotheses,
and it does not derive a forbidden matching shore when none is
available. The precise unpaid implication is from the exact
hypotheses and $c>1$ at the global minimum to an ear satisfying
(5); the tempting weaker endpoint-joining inference fails by (3).

If that implication were proved, the ear would contradict the
minimum with the **same** $H_0$, proving Z184. This is a sufficient
route, not an equivalent formulation or an available improvement
theorem. No impossibility of this route at exact instances is
established here.

If Z184 holds, $M_0\triangle E(Z)$ is a perfect matching retaining
$A$, since $Z$ avoids the patch. Its connected spanning degree-two
complement is Hamiltonian and uses $e_2$. Both lost types $P,D$
omit cut 2, so the complement has a survivor type. Thus Z184
implies E183. Neither the converse nor strict separation is proved.
Failure of an ear rule, or even failure of Z184, would not alone
refute E183.

**Z184 and E183/E182/E181/H180/L179, exchange/(T)/Q164 remain open.**
There is no exact-hypothesis counterexample, no ninth finding,
and no lowered contribution gate.

## 7. Validation and evidence boundary

Before the proof work, all five I184 output hashes matched the
detached anchors in the I185 brief; the brief and finalized parent
disposition were also hashed and recorded. Focused contract and
source hashes are in `input-authentication.json`.

Internal written checks covered endpoint matching saturation,
both arc endpoint types, the length-one exclusions, continuation
terminal exclusion, the identities for $L,N$, contraction and
expansion in (1), singleton incidences in (2), and both explicitly
traced pairings in (3). These are written deductions, not numerical
tests or independently reviewed theorems.

The parent's inherited 23-stage sealed I183 replay, about 8.89
seconds with eight probes and the authentic-source positive
control, is reported rather than rerun. The twelve facial controls
and 626 matching controls remain finite evidence. No historical
replay, graph generation, graph tests, attachment change, sweep,
matching scan, research code, new seal framework, copied snapshot,
agent, shared-ledger edit, staging, commit or publication was used.

Actual pinned theorem statements were read, not audited for truth.
No full upstream proof reread, external ear-decomposition literature
survey, formal proof-assistant check, independent correctness review
or literature-priority clearance was performed. Any substantial
candidate requires subsequent independent correctness and
contribution gates.
