# I186: all three theta regions, and the limit of their balance equations

2026-10-11. **Z184 UNRESOLVED; E183 UNRESOLVED. PARK THE LOCAL-EAR
MECHANISM.** Eight accepted, two remaining. This is an unsealed proof
record, not an accepted contribution.

All five I185 anchors were authenticated before the new proof work.
The I186 brief and finalized I185 parent disposition were also hashed
before that work. All OpenAI results at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true.

## 1. Exact hypotheses and quantifiers, unchanged

Let $X$ be an arbitrary finite connected simple bipartite locally cubic
disk, with five distinct degree-two ports $b_0,\ldots,b_4$, boundary
order $(0,2,1,4,3)$ and colors $(1,1,1,0,1)$ in label order. All other
vertices are cubic. Join these ports by cut edges $e_i$ to, respectively,
$(1,5,6,28,29)$ of the fixed exterior $Y$. Its vertex set is
$\{1,\ldots,11,28,29\}$ and its internal edges are exactly

```
1-7,1-28,2-3,2-8,2-29,3-4,3-9,4-5,4-10,5-11,
6-7,6-11,7-8,8-9,9-10,10-11,28-29.
```

Require the glued $G$ to be simple, planar, bipartite and a brace.
The eleven complete nonempty survivor fibres have types

```
02;02  12;12  14;14  24;24  0123;02,13  0123;03,12
0134;03,14  0234;02,34  0234;03,24  1234;12,34  1234;14,23.
```

Retain the complete lost fibre $P=(01;01)$ and lost type
$D=(0134;01,34)$. Packings span their side, have degree one precisely
at used ports, degree two elsewhere, and no isolated cycles.
Fibres and compatible exterior products are complete, not
representative lists.

The internal port-disjoint two-square patch has simple boundary
$C=(x,a,b,y,d,c,x)$, chord $xy$, and

$$
A=\{xa,by,dc\},\qquad B=\{ab,yd,cx\}.
$$

For every $p\in P$ using exactly $A$ on $C$, require
$q=p\triangle E(C)\in P$. Put $G'=G-V(C)$ and let $\mathcal H(q)$
be all Hamiltonian completions of this $q$ in this exact $G$.

The original Z184 assertion is

$$
\forall(X,p,q,C)\text{ satisfying these hypotheses},\
\exists H_0\in\mathcal H(q)\ \exists Z\subseteq G':
\quad
\begin{cases}
Z\text{ is a simple }M_0\text{-alternating cycle},\\
e_2\in E(Z),\\
H_0\triangle E(Z)\text{ is connected},
\end{cases}
\qquad M_0=E(G)\setminus E(H_0).
$$

The completion quantifier is **some**, not every. E183 instead asks for
some $A$-containing perfect matching with a Hamiltonian complement of
survivor local type; it does not prescribe cut 2 or a single difference
cycle from a $P$-completion.

### Paid facts, used only at their reviewed strength

The four continuations $aa',bb',cc',dd'$ leave $C$ and have distinct
terminals. They are the four degree-two vertices of $G'$. Every
$H_0\in\mathcal H(q)$ exists in a nonempty completion family, contains
$B$, $xy$ and the four continuations, and its complementary matching
contains $A$ and $e_2$. Removing $A$ identifies these matchings with
perfect matchings of $G'$.

I184 proves that every edge of every residual perfect matching lies
on a simple alternating cycle in $G'$. Its reachability argument uses
$r-s=2+h$, forcing $(r,s,h)=(2,0,0)$, and a forbidden three-edge,
one-crossing shore. It does not prove residual two-extendability.
I185's original technical claims pass finalized parent review without
repair.

Consequently choose $(H_0,Z)$ minimizing
$(c(H_0,Z),|E(Z)|)$ over **all completions and all qualifying cycles**,
where $c(H_0,Z)=\#\operatorname{comp}(H_0\triangle E(Z))$.
Keep this selected $H_0$ fixed during an ear splice.

For an actual proper alternating ear $Q$ with endpoints $u,v$ on $Z$,
its endpoint edges are nonmatching, its length is odd, and the endpoints
have opposite colors. The only removable arc $I$ of $Z$ has nonmatching
endpoint edges. The retained arc $J$ has matching endpoint edges; an
eligible splice requires $e_2\in J$. Thus $\Theta=I\cup J\cup Q$ is an
embedded theta, wholly in $G'$, while all degree counts below are in $G$.

Write $R_K=E(K)\cap E(H_0)$ and $T_K=E(K)\cap M_0$. For
$F=H_0\triangle E(I\cup J)$ the splice removes
$L=T_I\cup R_Q$ and adds $N=R_I\cup T_Q$. If $S$ is the retained-path
pairing of $F-L$, then

$$
c(H_0,J\cup Q)=c(H_0,I\cup J)-a+b,\quad
a=\#\operatorname{comp}(S\cup L),\quad
b=\#\operatorname{comp}(S\cup N).                 \tag{1}
$$

All edges and endpoint incidences keep their identities. Parallel
pairing edges, loops after contraction and the singleton paths in the
common refinement of $H_0$ are not discarded.

## 2. The three-region matching-closure lemma

Work on the sphere, so the unbounded planar region needs no exception.
The three open disks complementary to the embedded theta are
$\rho_{IJ},\rho_{JQ},\rho_{IQ}$, with boundaries the indicated pairs
of paths. Let $U_\rho$ be the vertices strictly inside $\rho$, not its
boundary vertices.

**Claim.** $M_0$ matches every vertex of $U_\rho$ to another vertex of
$U_\rho$. More strongly, every connected component of $G[U_\rho]$
has a perfect matching given by restriction of $M_0$.

**Proof.** At $u,v$, the $J$ edge is the unique matching edge; the
$I,Q$ edges are Hamiltonian edges. At every other theta vertex,
the two theta edges alternate and exactly one is in $M_0$.
Thus every theta vertex is already matched on the theta.

An edge with one endpoint strictly inside $\rho$ cannot reach a
different open region without crossing the theta. A matching edge
cannot end on its boundary either, since a boundary vertex already
has its matching edge. Hence an interior vertex's mate lies in
$U_\rho$. That edge is also an edge of $G[U_\rho]$, so it cannot join
two different connected components of that induced subgraph. This
proves both assertions. $\square$

**Scope correction.** The assertion is closure of the *strict interior*
under $M_0$, not closure of the interior together with the whole
boundary. On $\partial\rho_{IQ}$ the matching edges at $u,v$ run along
$J$, not along that boundary. No matching-closed shore of the I184
kind follows by indiscriminately including boundary vertices.

At an internal theta vertex there is exactly one edge outside the
theta, and it belongs to $H_0$. Its incident half-edge, called a
boundary stub, is assigned to the unique adjacent region into which
the edge runs. At $u,v$ all three edges are already on the theta,
so there are no such stubs. A stub need not run to an interior
vertex: an edge may join two theta vertices through a region.

## 3. Exact black/white balance, including chords and pieces

Use black/white color names independently of the port label convention.
For a fixed region let $n_{\mathrm B},n_{\mathrm W}$ count its
strict-interior vertices, and $m_\rho$ count all edges with both
endpoints there. Let $t_{\mathrm B},t_{\mathrm W}$ count edges from
the theta to the interior, classified by their **theta-end** color.
They are all Hamiltonian edges. Cubic degree counts give

$$
3n_{\mathrm B}=m_\rho+t_{\mathrm W},\qquad
3n_{\mathrm W}=m_\rho+t_{\mathrm B}.              \tag{2}
$$

Matching closure gives $n_{\mathrm B}=n_{\mathrm W}$, so
$t_{\mathrm B}=t_{\mathrm W}$. The very same equations hold for each
connected component of $G[U_\rho]$, using only its incident edges to
the theta. Disconnected interiors cannot exchange a color imbalance.

Let $h_\rho$ be the number of edges joining two boundary vertices
whose edge interiors lie in $\rho$, excluding theta edges themselves.
Each is an $H_0$ edge, has opposite-colored ends, and uses two stubs.
If $\sigma_{\mathrm B},\sigma_{\mathrm W}$ count **all** boundary
stubs assigned to $\rho$, including these chords, then

$$
\sigma_{\mathrm B}=t_{\mathrm B}+h_\rho,\qquad
\sigma_{\mathrm W}=t_{\mathrm W}+h_\rho,\qquad
\boxed{\sigma_{\mathrm B}=\sigma_{\mathrm W}}.    \tag{3}
$$

No chord is confused with a theta edge having the same endpoint
labels in a contracted picture. No nonempty interior is presumed
connected. Empty interiors and chord-only regions obey (2)--(3)
with the appropriate zero counts.

In particular, a region cannot have just one boundary stub or have
two same-colored boundary stubs and no others. If it has no stubs,
it has no interior vertices: matching edges cannot leave, there are
no other edges to the theta, and an interior component would be a
component of the connected $G$ disjoint from the theta.

These are necessary conditions for an actual hypothetical admissible
instance, proved without using brace extendability or complete fibres.
They are not a characterization of realizable regions.

## 4. The single Hamiltonian cycle, not arbitrary noncrossing arcs

Restrict the edges of $H_0$ to those whose interiors lie off the theta,
keeping their theta endpoints. In each region they form vertex-disjoint
paths between its assigned stubs. These paths cover every strict-interior
vertex in that region. Boundary-to-boundary chords are length-one paths.

There cannot be an additional cycle entirely inside a region: it
would be a component of $H_0$, while $H_0$ also visits the theta.
Interior vertices have Hamiltonian degree two and boundary stubs have
degree one in this restriction, so these are all its components.
Let $K_\rho$ denote the resulting path pairing and let
$K=\bigcup_\rho K_\rho$, keeping each path as a distinct object.

A path in $K_\rho$ is made of $H_0$ edges, **not alternating edges**.
Its endpoint colors need not be opposite. In fact (3) says

$$
\#\{K_\rho\text{ paths with two black ends}\}
=
\#\{K_\rho\text{ paths with two white ends}\}.     \tag{4}
$$

It does not say both sides of (4) vanish. An even-length path with
two white ends has one more black than white *internal* vertex;
a path with two black ends has the reverse difference. Their
imbalances may cancel within the same region, whose matching may
join vertices lying on different Hamiltonian paths.

After replacing each off-theta path by an identity-preserving
pairing edge, the exact single-cycle condition is that

$$
K\cup R_I\cup R_J\cup R_Q                         \tag{5}
$$

is one circuit through all theta vertices, with its expansions
covering all off-theta vertices and with no discarded interior
cycles. This is stronger than separate noncrossing of $K_\rho$.
Each internal theta vertex has one $K$ incidence and one displayed
$R$ incidence. At $u,v$, the two displayed $R$ incidences meet each
other. Equivalently, in the common refinement
$H_0-(R_I\cup R_J\cup R_Q)$, $u,v$ are singleton paths, each with
two distinct endpoint incidences. Keeping them yields (5); deleting
them from the incidence accounting would not.

Similarly,

$$
F=K\cup T_I\cup T_J\cup R_Q,\qquad
\widehat F=K\cup R_I\cup T_J\cup T_Q               \tag{6}
$$

after expansion. In particular $F-L=K\cup T_J$ on its touched
paths, together with any untouched circuits. Paths in $S$ can travel
along $J$ and concatenate paths from different theta regions. They
are not in general single region-interior Hamiltonian paths.

Equations (3)--(6) are the full region bookkeeping used below.
The Hamiltonian connectedness in (5) is imposed explicitly, not
inferred from degrees or noncrossing.

## 5. Where the patch and all four continuations go

The connected patch, including its chord, is disjoint from the theta,
so all six vertices lie in one open region, say $\rho_*$. Its three
$M_0$ edges are precisely $A$; no matching edge leaves those six
vertices. Name $x$ black. Then $y,a,c$ are white and $x,b,d$ are
black, so the patch contains three vertices of each color.

Its Hamiltonian edges are $B\cup\{xy\}$, with the four continuations.
Thus the two patch pieces of $H_0$ are exactly

$$
a'-a-b-b',\qquad c'-c-x-y-d-d'.                  \tag{7}
$$

The four continuation terminals have colors
$a',c'$ black and $b',d'$ white. A terminal may lie in the strict
interior of $\rho_*$ or on its theta boundary. In the latter case
the continuation is exactly that vertex's non-theta Hamiltonian
stub, directed into $\rho_*$. It cannot be $u$ or $v$, whose three
edges are already occupied by the theta. A terminal cannot lie in
a different open theta region.

All of (7) therefore belongs to the covering paths used in
$K_{\rho_*}$. The two displayed pieces need not belong to distinct
such paths; no new local pairing of the four continuations is
assumed. The matching pairs $A$ contribute zero net color imbalance
to (2), but the continuations cannot be dropped from its boundary
or interior edge counts. In particular $\rho_*$ cannot be a
zero-stub region.

### Explicit residual correction if one uses $G'$

Although the proof uses $G$, here is the correction that prevents
a false cubic count after patch deletion. In $G'$ only
$a',b',c',d'$ have degree deficit one, with two black and two white
deficits in total. For one region's residual strict-interior vertices
let $d_{\mathrm B},d_{\mathrm W}$ count deficits there, and
$t'_{\mathrm B},t'_{\mathrm W}$ count its surviving theta-to-interior
edges by theta-end color. Its residual matching still gives
$n'_{\mathrm B}=n'_{\mathrm W}$. Instead of (2) one has

$$
3n'_{\mathrm B}-d_{\mathrm B}=m'_\rho+t'_{\mathrm W},
\qquad
3n'_{\mathrm W}-d_{\mathrm W}=m'_\rho+t'_{\mathrm B},
$$

and hence, including surviving boundary chords,

$$
\sigma'_{\mathrm B}-\sigma'_{\mathrm W}
=t'_{\mathrm B}-t'_{\mathrm W}
=d_{\mathrm B}-d_{\mathrm W}.                   \tag{8}
$$

If $d^\partial_{\mathrm B},d^\partial_{\mathrm W}$ count terminal
deficits *on* this theta boundary whose removed continuation went
into this region, then
$\sigma'_{\mathrm B}=\sigma_{\mathrm B}-d^\partial_{\mathrm B}$
and likewise for white. All four deficits are assigned to $\rho_*$
as interior or boundary deficits, so

$$
d_{\mathrm B}-d_{\mathrm W}
=-(d^\partial_{\mathrm B}-d^\partial_{\mathrm W}).
$$

This agrees with (3) and (8). Other regions have neither kind of
deficit. Formula (8) also holds separately for each residual
interior component; deleting the patch may split an old component.

The Hamiltonian restriction in $G'$ is not a 2-factor. Globally
$H_0-V(C)$ consists of two paths with endpoints $a',b',c',d'$,
without cycles. Their endpoint pairing together with the patch
pairing $\{a'b',c'd'\}$ in (7) is one circuit, so the outside pairing
is one of the two cross pairings, not that patch pairing itself.
These outside paths may traverse the theta and several regions.
Counting them as closed regional arcs would erase the four deficits
and the Hamiltonian condition. No such erasure is used here.

## 6. Revisit the formal six-label pattern in the full theta

The numerals in this section are **formal theta labels**, not the
vertices with the same numerals in the fixed exterior $Y$.
Retain the I185 pattern

$$
L=\{12,34,56\},\quad N=\{23,45,61\},\quad
S=\{12,36,45\},\quad
Q=(1,2,3,4),\quad I=(1,6,5,4).                  \tag{9}
$$

Odd labels are black and even labels white. Thus
$T_I=\{65\}$, $T_Q=\{23\}$,
$R_I=\{16,54\}$ and $R_Q=\{12,34\}$.
The retained arc $J$ is a matching-ended odd path from 1 to 4.

We ask what the necessary full-theta equations and the Hamiltonian
circuit condition say about (9). The following are symbolic
incidence deductions, not graph construction or a realization claim.

### 6.1 A concrete exclusion: $|J|=1$ or $3$ cannot realize (9)

If $|J|=1$, its matching edge joins 1 directly to 4 in $F-L$.
There is no other edge at either of these two endpoints in $F-L$,
so $S$ must contain $14$, contrary to (9).

If $J=(1,s,t,4)$ has length three, its types are matching,
Hamiltonian, matching; $s$ is white and $t$ black. Its only
$T_J$ edges are $1s$ and $t4$. The pairing of $F-L=K\cup T_J$
in (9) then forces

$$
K=\{s2,\ t5,\ 36\}.                              \tag{10}
$$

For example, after traversing $1s$, a $K$ path to $t$ would
immediately terminate at 4, not 2; a path to another vertex of
$I\cup Q$ would terminate there. Thus $s2$ is forced, and
similarly $t5$ is forced. The remaining pair is $36$.

A $K$ path cannot touch another theta vertex internally, so its
endpoints must lie on the boundary of its single region.
The pair $s2$ must lie in $\rho_{JQ}$, $t5$ in $\rho_{IJ}$,
and $36$ in $\rho_{IQ}$. Region $\rho_{JQ}$ has exactly the two
white stubs $s,2$ and no black stub. Region $\rho_{IJ}$ has
exactly the two black stubs $t,5$ and no white stub. Both
contradict (3).

Extra interior pieces or boundary chords cannot repair this:
all available stubs at these theta vertices are already assigned,
and chords or additional paths would need further stubs.
The contradiction takes place in the cubic $G$, so a patch hidden
in a region cannot supply an uncounted deficit.

This excludes these two short retained arcs for the specified pattern,
not the pattern for arbitrary $J$ and not all zero-gain patterns.

### 6.2 Length five: the full incidence constraints do not exclude it

Let the *symbolic* retained path be

$$
J=(1,s,t,w,z,4),\quad
T_J=\{1s,tw,z4\},\quad R_J=\{st,wz\}.
$$

Its internal colors are $s,w$ white and $t,z$ black. Consider the
following possible **regional path-pairing data**, without asserting
that any region with these data exists in an admissible $G$:

$$
K_{JQ}=\{2s,3t\},\qquad
K_{IJ}=\{6w,5z\},\qquad K_{IQ}=\varnothing.       \tag{11}
$$

Each symbol denotes a prospective off-theta $H_0$ path, not a new
edge of an actual graph. In particular these four pairs have
same-colored ends and cannot be boundary chords. They would have
positive even lengths and interior vertices.

Here is the complete incidence-level check.

* In $\rho_{JQ}$ the stubs are $2,s$ white and $3,t$ black.
  In $\rho_{IJ}$ they are $6,w$ white and $5,z$ black.
  Each region satisfies (3) and (4). Each white-white path's
  internal color surplus is canceled by its black-black partner.
  This does not assume that each Hamiltonian path is matched
  internally; matching closure was for a whole region component.
* On $\partial\rho_{JQ}$ the order is
  $(1,2,3,4,z,w,t,s)$. Pairs $2s$ and $3t$ are nested and
  noncrossing. On $\partial\rho_{IJ}$ the order is
  $(1,6,5,4,z,w,t,s)$, where $6w$ and $5z$ are also nested
  and noncrossing. The two sets occupy different open regions,
  so they are simultaneous, not just an $S$ drawing on one
  side of $I\cup Q$.
* The exact Hamiltonian incidence circuit (5) is

  $$
  1\mathrel{R_Q}2\mathrel K s\mathrel{R_J}t
  \mathrel K3\mathrel{R_Q}4\mathrel{R_I}5
  \mathrel K z\mathrel{R_J}w\mathrel K6
  \mathrel{R_I}1.                                \tag{12}
  $$

  This visits every theta vertex once. If the four $K$ paths
  covered all off-theta vertices without extra cycles, their
  expansion would be **one** Hamiltonian cycle. This is the
  explicit simultaneous single-cycle check, not an assertion
  from noncrossing alone.
* In $F-L=K\cup T_J$ the three paths are

  $$
  1\mathrel{T_J}s\mathrel K2,\qquad
  3\mathrel Kt\mathrel{T_J}w\mathrel K6,\qquad
  4\mathrel{T_J}z\mathrel K5.
  $$

  They give exactly $S=\{12,36,45\}$. In particular the middle
  retained path passes from one theta region to the other
  along the matching edge $tw$ on $J$.
* Restoring $L$ yields the circuits on $\{1,2\}$ and
  $\{3,4,5,6\}$; restoring $N$ yields the circuits on
  $\{1,2,3,6\}$ and $\{4,5\}$. The pairing edges with repeated
  endpoint labels retain distinct identities. Thus $a=b=2$,
  with 1 and 4 in different old components, exactly as in I185.
  The two replaced paths still have $|I|=|Q|=3$.

Componentwise balance imposes one further necessary condition on
any realization of (11). The two covering paths in each nonempty
region must lie in the **same** connected strict-interior component:
either same-colored path alone has an internal color imbalance,
and there are no other covering paths there to cancel it. There
can be no additional interior component without another covering
path. More precisely, on the internal vertices of its white-white
path, the number of matching edges leaving at black vertices minus
the number leaving at white vertices must be one. Such matching
edges would have to run to the other path in that region; internal
matching edges of the one path cancel in this count. The black-black
path has the opposite equation. This is a necessary matching
coupling, not an exhibited matching or a proof of its existence.

No interior matching, interior graph, patch placement, exterior
attachment, brace verification, complete fibres, or cut-2 edge
identification is supplied by (11). In particular (12) checks the
Hamiltonian *incidence requirement* conditional on covering paths;
it is not a Hamiltonian cycle constructed in a graph. Balances do
not prove existence of the interior perfect matching or the
componentwise matching closure in a realization.

If an actual instance realized (11), $\rho_{IQ}$ would be empty
by the zero-stub conclusion in Section 3, and its patch would
have to lie in $\rho_{IJ}$ or $\rho_{JQ}$. In that region the two
paths in (7), their four continuations and the matching $A$ must
all be accommodated by the covering paths and remaining matching.
Nothing in (11) supplies that accommodation. Likewise designating
one of the three $T_J$ positions as a prospective $e_2$ does not
identify the true port/exterior cut edge.

**Precise verdict on the formal pattern.** It has no length-one or
length-three $J$ completion in an actual cubic instance. With a
length-five $J$, it has compatible three-region color counts,
simultaneous noncrossing Hamiltonian path pairings, and a single
Hamiltonian incidence circuit. Thus these specific necessary
tests do not exclude it. Its completion to an actual exact-hypothesis
instance, and its occurrence at a global minimum, remain unproved.
No graph construction, existence theorem or counterexample is
claimed.

## 7. What is still missing at a global minimum with $c>1$

The balance theorem records **color totals of boundary stubs** and
matching closure of strict interiors. The single-cycle condition
also records how the $R$ edges join the regional $K$ paths.
Neither argument supplies a selection theorem for actual alternating
ears, controls every possible retained-path order after splicing,
or relates that order to the global choice among completions.

At the global minimum, every eligible actual ear still must have
$b>a$, or $b=a$ and $|Q|\geq|I|$. The symbolic calculation in
Section 6.2 is compatible with equality in both parts of this
necessary minimum condition. It does not prove that such a
global minimum with $c>1$ exists: other ears or a different
completion could do better.

The short-$J$ exclusion is real additional information but gives no
bound forcing $|J|\leq3$, no exclusion of longer zero-gain patterns,
and no reason that every non-Hamiltonian toggle has an eligible
improving ear. Longer $J$ paths can contribute additional stubs
of both colors to the two relevant regions. A blanket rule that
all regional Hamiltonian paths join opposite colors would remove
this possibility, but that rule is false as a deduction from
matching closure: matching pairs may run between different paths.

The exact exterior has not been replaced. For a $P$-completion
it still carries a spanning path from its vertex 1 to its vertex 5,
using cuts 0 and 1 and omitting 2, 3 and 4. Its forced edges
listed in I185 constrain local edge types, not the order in which
$K$ paths in the arbitrary disk return. The eleven complete
nonempty survivor fibres still do not by themselves supply an
$A$-containing survivor matching, nor a single-ear comparison
with this fixed $H_0$. Two-extendability in $G$ supplies matching
extensions, not their Hamiltonian retained-path order.

No failed component-filtered search in this analysis gives the
matching-closed, sole-exit vertex shore needed for I184. Region
closure is a different assertion: it has balanced interiors
and potentially many Hamiltonian boundary stubs, not the
one-crossing structure from that reachability contradiction.

The missing global information is a proved relation between:

1. the actual interior matching and Hamiltonian path orders across
   all three regions (including the frozen patch);
2. which ears the exact brace and port/exterior structure really
   make available, and which retain the actual $e_2$;
3. how the complete-fibre and completion choices constrain those
   orders simultaneously, rather than only their color totals.

No theorem establishing that relation is proved. This is a description
of information absent from this approach, **not a new proposed target
that merely renames $b<a$**.

### Stopping decision

**PARK THE LOCAL-EAR MECHANISM.** The bounded pass yields matching
closure, precise necessary balances, and a limited short-arc
exclusion, but no usable universal structural exclusion or
improvement bridge. The length-five incidence calculation prevents
promoting that short exclusion into a closure of the route.
Do not commission another renamed single-ear inequality from this
record. No subsequent broader program step is started here.

This recommendation does not say the mechanism is mathematically
impossible. It does not refute or resolve Z184 or E183.

## 8. Original-target verdicts, dependencies and validation

**Z184 remains UNRESOLVED. E183 remains UNRESOLVED.** Z184 still
implies E183: $M_0\triangle E(Z)$ is a perfect matching retaining
$A$ because $Z$ avoids the patch. Its connected complement is
Hamiltonian and uses $e_2$; both lost types omit cut 2. Neither
the converse nor strict separation has been proved.
E182/E181/H180/L179, universal exchange, (T) and Q164 also remain
open. The accepted count stays eight, with two remaining.

The new region deductions use only matching saturation, cubic
bipartite degree counts, planar separation and the stipulated
Hamiltonian completion, together with the reviewed I184/I185
local setup. The actual pinned statements `thm:main`,
`cor:edge-avoidance` and `cor:pfaffian-paths` were read to delimit
available prescriptions, not upgraded to an ear theorem.
No unread external theorem is invoked.

Internal written checks covered each region, each disconnected
interior component, chord incidences, the signs in (8), patch
colors and both Hamiltonian pieces, the exact circuits (12) and
the three retained paths, and the difference between an incidence
pattern and an admissible instance. These are not independent
correctness review or formal proof-assistant verification.

Only the five authorized files are outputs. Authentication and
document syntax/link/consistency checks are not graph experiments.
There was no graph generation, construction, test, attachment
change, numerical experiment, sweep, matching scan, research
implementation, historical replay, snapshot copy, seal framework,
agent, ancestor/shared-ledger edit, staging, commit or publication.

The finalized parent's inherited 23-stage I183 replay passed in
about 8.70 seconds, with eight probes and source positive control;
this is reported, not rerun. The twelve facial and 626 matching
controls remain finite evidence. Reading limits and failed routes
are retained in the companion files. No literature-priority
clearance is claimed. Any substantial candidate requires separate
independent correctness and contribution gates.
