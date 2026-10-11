# I187: frozen matching survival through the actual paired-state sum

2026-10-11. **Original E183: UNRESOLVED.** One proof-only attempt.
Eight accepted, two remaining. No substantial finding is nominated.
All OpenAI results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`
are stipulated true, not audited.

The five I186 anchors matched before new proof work. The I187 brief,
finalized I186 disposition and retained manuscript were hashed then.
This is an unsealed written record. The single-ear mechanism remains
PARKED; none of the arguments below is an ear or bounded-transfer argument.

## 1. Exact target and quantifiers

Let $X$ be any finite connected simple bipartite locally cubic disk with
five distinct degree-two ports $b_0,\ldots,b_4$, boundary order
$(0,2,1,4,3)$, and colors $(1,1,1,0,1)$ in label order. All other
vertices are cubic. The cut edges $e_i$ join the ports respectively to
$(1,5,6,28,29)$ in the fixed exterior $Y$. Its vertices are
$\{1,\ldots,11,28,29\}$, and its internal edges are exactly

```
1-7,1-28,2-3,2-8,2-29,3-4,3-9,4-5,4-10,5-11,
6-7,6-11,7-8,8-9,9-10,10-11,28-29.
```

Require the glued $G$ to be simple, planar, bipartite and a brace.
Retain the eleven complete nonempty survivor local fibres

```
02;02  12;12  14;14  24;24  0123;02,13  0123;03,12
0134;03,14  0234;02,34  0234;03,24  1234;12,34  1234;14,23.
```

The complete lost types are $P=(01;01)$ and $D=(0134;01,34)$.
Packings span their side, have degree one precisely at used ports,
degree two elsewhere, and no isolated cycles. All fibres and compatible
exterior products are complete, not representative lists.

The internal port-disjoint patch has simple boundary
$C=(x,a,b,y,d,c,x)$, chord $xy$, and

$$
A=\{xa,by,dc\},\qquad B=\{ab,yd,cx\}.
$$

For every admissible $p\in P$ using exactly $A$ on $C$, with
$q=p\triangle E(C)\in P$, E183 asks for some perfect matching
$M\supseteq A$ such that $H=G-M$ is Hamiltonian and its full local
type is one of the eleven survivors. There is no prescribed cut 2,
completion, difference cycle, or sequence of Hamiltonian-preserving moves.

The paid I183 reductions give four distinct continuation terminals
outside $C$, a bijection between $A$-containing matchings and matchings
of $G-V(C)$, and a lost Hamiltonian completion of $q$ whose matching
contains $A$. They do not supply survival or a paired-state preimage.
The full lifted complement, including its patch routes, determines type.

## 2. Paying the graph and dual hypotheses without an external theorem

Use the brace's two-extendability in precisely the sense used by the
reviewed I183 argument: every two disjoint edges extend to a perfect
matching. Connectivity and existence of a perfect matching also hold.
The graph here has more than four vertices because of its disjoint
thirteen-vertex exterior. Cubicity follows from the stated degrees and
attachments. Simplicity, bipartiteness and planarity are hypotheses.

Here is a direct small-cut argument; no theorem saying merely
"braces are sufficiently connected" is substituted for it.

For a nonempty proper vertex shore $U$, let $n_{\rm B},n_{\rm W}$
be its two color counts, and let $\alpha,\beta$ count cut edges whose
end in $U$ is black or white. Cubic degree counting gives

$$
3(n_{\rm B}-n_{\rm W})=\alpha-\beta.                 \tag{1}
$$

* A one-edge cut is impossible: its right side would be $1$ or $-1$.
* In a two-edge cut, (1) forces $\alpha=\beta=1$ and equal color
  counts in $U$. Write the cut edges as $uv$ and $wz$, where $u$
  is black in $U$, $w$ white in $U$, and $v,z$ are outside.
  The other two neighbors of $w$ are inside $U$ and are distinct.
  At least one, say $h$, is not $u$. Thus $uv$ and $wh$ are
  disjoint. Two-extendability supplies a matching containing them.
  It uses $uv$ and cannot use $wz$. But a matching of an equal-color
  shore must have equal black-end and white-end crossing counts.
  This is a contradiction.
* In a three-edge cut, (1) forces all three shore ends to have the
  same color, with shore color surplus one. Every perfect matching
  crosses this cut exactly once: all minority-color vertices are
  matched internally and exactly one majority-color vertex remains.
  Thus two cut edges cannot be disjoint. Three pairwise intersecting
  edges in a simple bipartite graph share a vertex: otherwise three
  of their endpoints form a triangle. Cubicity then implies that one
  shore is a singleton. Indeed, if the common vertex is in $U$, any
  other vertex of $U$ has no path to its complement or to that vertex
  through $G[U]$, contradicting connectivity; the other case is the
  same with shores interchanged.

Consequently there is no cut of size one or two and no nontrivial
three-edge cut.

This also pays 3-vertex-connectivity directly. A cut vertex would leave
at least two components, one incident with at most one of its three
edges, giving a forbidden small edge cut. If deleting two vertices
$u,v$ disconnected $G$, every remaining component would have at least
three incident cut edges. When $uv$ is an edge there are only four
available incidences, impossible. When it is not, there are six,
so there must be exactly two components with three each. Both cuts
are nontrivial unless that component is a singleton. A singleton,
however, cannot have three neighbors in the two-element set $\{u,v\}$
in a simple graph. This is again impossible.

Fix the given sphere embedding. As in the read source proof at
lines 760--782, the absence of one- and two-edge cuts excludes dual
loops and parallel dual edges: such dual curves separate a primal
shore with one or two crossing edges. Thus $T=G^*$ is simple and
connected. Its facial walks have length three by cubicity and hence
are actual triangles. Euler gives $|V(T)|=2+|V(G)|/2\ge4$.
The primal bipartition colors its faces black and white with opposite
colors across each edge.

**There is no separating triangle in $T$.** Such a triangle would
give a three-edge primal cut. Each of its disks contains a dual
vertex strictly inside. A triangulated disk with triangular boundary
and $I\ge1$ interior vertices has $2I+1\ge3$ triangular faces, by
Euler and side counting. Thus each primal shore has at least three
vertices (one for each such dual face). The cut would be nontrivial,
contradicting the proved small-cut statement.

This pays the hypothesis of `prop:pairs`; separating-triangle assembly
is not needed for these exact instances. The assembly proof at source
lines 720--758 was nevertheless read: it preserves one facial
same-label edge, not an arbitrary list of matching edges or a five-port
path type. If the brace hypothesis were dropped, one could not assert
that the present prescription survives that assembly.

**No claim that either patch square is facial is used.** Each dual
triangle used below is the face corresponding to a *primal vertex*.
All conclusions here hold without identifying the primal four-cycles
as faces.

## 3. Source objects and the exact recovery map

Color $x,b,d$ black and $a,y,c$ white. Let $t_v$ denote the triangular
face of $T$ corresponding to a primal vertex $v$. Choose the outer
black triangle $t_0=t_x$ and prescribed root edge $f_0=(xa)^*$.
The white root face across $f_0$ is $t_a$.

Use $\mathcal B$ for the black faces other than $t_0$ and $N$ for
the nonroot vertices of $T$. This avoids the source's collisions
with the patch $A$ and disk $X$. States are incidence bijections
$r,s:\mathcal B\longrightarrow N$, with $r(t)\ne s(t)$ in a pair.
If there are $k$ black faces, $|\mathcal B|=|N|=k-1$.

For a second state $s$, the source's $Q_s$ consists of the edge
**opposite** $s(t)$ in each $t\in\mathcal B$. If $s$ has a partner
and $Q_s$ is a forest, `lem:root-components` puts exactly one of the
three roots in each component.

The source's all-black-center spoke graph is denoted $\mathcal H$.
Delete the spokes $(t,s(t))$. Its remainder is $Q_s$ subdivided at
the black centers, joined at its three roots to the center of $t_0$.
It is a spanning tree. The duals of the deleted spokes form a tree
$W_s$ on the white faces, by `lem:duality`. Write $\tau_t$ for the
edge of $W_s$ corresponding to the deleted spoke at $t$.

Root $W_s$ at $t_a$. Assign each edge $\tau_t$ to its endpoint farther
from $t_a$. Select the side of $t$ incident with $s(t)$ and bordering
that assigned white face. Add $f_0$. Call this selected set $K_s$,
not $P$. Source `lem:P-forest` proves that $K_s$ is a forest;
there is exactly one selected edge at every black and white face.
Its two components are the two induced trees. Hence

$$
M_s=\{e\in E(G):e^*\in K_s\},\qquad H_s=G-M_s          \tag{2}
$$

are an actual perfect matching and an actual Hamiltonian complement.
They are not formal incidence data.

### 3.1 A useful strict distinction: $Q_s$ and $K_s$ are disjoint

For each nonroot black face, $Q_s$ selects the side opposite $s(t)$,
whereas $K_s$ selects a side incident with $s(t)$. These are different.
Different black faces cannot supply the same edge because every
dual edge has a unique black incident face. The only selected edge
of $t_0$ is $f_0$, and $Q_s$ supplies no edge there. Therefore

$$
Q_s\cap K_s=\varnothing.                            \tag{3}
$$

In particular, forcing a nonroot frozen edge *into* $Q_s$ would force
it *out of* the recovered matching. This is a concrete failure of
identifying the opposite-edge forest with the selected-edge forest,
not a counterexample to E183.

### 3.2 Exact frozen-edge conditions on the white-face tree

Let $f$ be a side of $t\in\mathcal B$, and let $w_f$ be the white
face across it. For a partnered forest state, the recovery rule gives

$$
f\in K_s
\iff
\left[
s(t)\in V(f)\ \text{and }\
t_a\notin \operatorname{comp}_{w_f}(W_s-\tau_t)
\right].                                           \tag{4}
$$

The component in (4) is considered only when the incidence condition
holds, so that $w_f$ is an endpoint of $\tau_t$. In a rooted tree,
that endpoint is assigned its edge exactly when it lies on the side
away from the root. This proves both directions of (4).

Equivalently, $\tau_t$ must be the parent edge of $w_f$ in $W_s$.
With our root prescription, the three frozen matching edges require

$$
\begin{aligned}
(xa)^*&=f_0\in K_s &&\text{automatically},\\
s(t_b)&\in V((by)^*),\quad
\tau_{t_b}\text{ is the parent edge of }t_y,\\
s(t_d)&\in V((dc)^*),\quad
\tau_{t_d}\text{ is the parent edge of }t_c.          \tag{5}
\end{aligned}
$$

These are two additional incidence-and-root-component conditions,
not two further consequences of choosing $f_0$.
All state choices remain nonroots and satisfy the full state bijection.
In primal language, each $\tau_t$ joins two white neighbors of the
black vertex corresponding to $t$; its child endpoint is that black
vertex's matching neighbor. Thus (5) is exactly the matching
prescription, rather than a proxy based on $Q_s$.

### 3.3 Full lifted type, not just cut membership

For $H_s$ in (2), retain every vertex and edge identity of the original
$X$ and $Y$. Define its used cut set to be

$$
U_s=\{i:e_i^*\notin K_s\}.
$$

Trace the actual components of $H_s\cap E(X)$ to obtain the pairing
$\pi_s$ of their port endpoints. The restriction covers $X$ and has
no isolated cycle: an isolated cycle would be a component of the
Hamiltonian $H_s$, which also visits the disjoint exterior.
Thus $\theta_s=(U_s;\pi_s)$ is the full lifted local path type.
Survival means that this exact type belongs to the eleven-element
list in Section 1.

In particular, types with cut set $0134$ distinguish the survivor
pairing $03,14$ from the lost pairing $01,34$. Cut-edge indicators
alone do not test survival. Nor does the four-continuation pairing
after removing $C$: its paths must first be lifted through the patch
and then traced to the five ports. No condition $2\in U_s$ is imposed.

## 4. State-image and preimage limits, with an exact conditional test

For a partnered forest state, the partner is unique. Its orientation
of $Q_s$ has outdegree one at every nonroot and zero at each root.
In a finite rooted tree it must point toward the root; the tail of
the edge owned by each black face recovers $r(t)$. This is the same
rooted-tree argument actually read in I164 Section 5.

The selected forest $K_s-\{f_0\}$ also has one root in each component.
Orienting it toward its roots recovers $s(t)$ as the tail of the
selected edge owned by $t$. Hence the fixed-root recovery is injective.
This does not assert that every Hamiltonian complement has a preimage.

The following elementary test makes the missing converse precise.
Let $H$ be *any* Hamiltonian cycle of this $G$ avoiding $xa$, and put
$K=\{e^*:e\notin H\}$. Then:

1. $K$ is a forest with two components. A simple dual cycle in $K$
   would separate primal vertices on both sides but cross no edge
   of the connected spanning $H$, impossible. The edge count
   $|K|=k$, $|V(T)|=k+2$ gives two components. The Jordan curve
   $H$ labels dual vertices by side; an edge is in $K$ exactly
   when its ends have the same label. Thus the third root is in
   the other component from the endpoints of $f_0$.
2. Removing $f_0$ gives three tree components with distinct roots.
   Orient them toward those roots. Each nonroot is the tail of one
   edge, and each black triangle except $t_0$ owns one edge.
   These tails define a genuine state $s_H$.
3. Form the deleted-spoke graph for $s_H$. The cycle $H$ lies in the
   fixed-root source image **if and only if** $Q_{s_H}$ is a forest
   with one root in each component. Equivalently, the duals of its
   deleted spokes form a tree on the white faces.

Here is the sufficiency in item 3, not just necessity. A rooted
$Q_{s_H}$ can be oriented toward its roots to give a bijective partner
$r$, disjoint from $s_H$ because its edge is opposite $s_H(t)$.
The remaining spoke graph, obtained by subdivision and the root star,
is a tree; its complementary dual $W_{s_H}$ is a tree. Every edge of
$K-\{f_0\}$ is incident with its assigned $s_H(t)$, so it assigns
$\tau_t$ to an incident white face. Since $G-H$ is a matching and
$xa$ is its root edge, these assignments use every white face except
$t_a$ exactly once and never $t_a$. On a tree this endpoint assignment
is uniquely the orientation away from $t_a$. Thus source recovery
returns exactly $K$, and hence $H$.
Necessity follows from `lem:root-components` and source recovery.
The equivalence with a white-face tree follows from plane-tree duality
in both directions: complementing a dual spanning tree gives a primal
spanning tree, and the remaining spoke graph is exactly the subdivided
$Q_{s_H}$ plus the root star.

For a known lost completion $H_0$ of $q$, items 1--2 do apply because
$A\subseteq G-H_0$. Item 3 is **not paid** by Hamiltonicity alone or
by the existence of the two lost packings. This attempt proves no
rooted-forest test for that $s_{H_0}$. Even a paid lost preimage would
still have type $P$, not a survivor.

The I164 $c_{\min}+1$ argument is a count of unfiltered partnered
forest states using Vandermonde rank and the same injection. It gives
neither this preimage test for a specified cycle nor an intersection
with (5) and the survivor predicate. Its Section 5 also records the
fixed-root image-size limitation on even bipyramids. No such graph is
substituted for the exact exterior or used as an E183 counterexample.

## 5. Fixed-second-state marking really does preserve cancellation

Use the source incidence weights $a(t,v)$ and
$\omega(s)=\sum_t a(t,s(t))$. Write

$$
J(r,s)=\frac13\sum_t\delta(r(t),s(t)),\qquad
Z_g(z)=\sum_{(r,s)\ {\rm pair}}g(s)i^{J(r,s)}
             e^{z\omega(s)}.                       \tag{6}
$$

The parameter is $z$, to avoid confusing it with patch vertex $x$.
Let $g$ be any scalar function of the second state alone.
For cyclic $Q_s$, `lem:cancel` fixes a cycle using $s$ alone,
reverses it by changing $r$ to $\widetilde r$, and changes $J$ by
$\pm2$. Both $g(s)$ and $\omega(s)$ are unchanged. Consequently

$$
Z_g(z)=\sum_{s\in\mathcal F}g(s)\alpha_s e^{z\omega(s)},
\qquad \alpha_s=i^{J(r_s,s)}\ne0,                  \tag{7}
$$

where $\mathcal F$ is the set of partnered forest second states.
Uniqueness of $r_s$ was paid in Section 4.

For an arbitrary partner-dependent multiplier $h(r,s)$ the paired
terms instead have sum

$$
i^{J(r,s)}e^{z\omega(s)}
       \bigl(h(r,s)-h(\widetilde r,s)\bigr).          \tag{8}
$$

Thus such a multiplier needs an invariance proof on the cancellation
involution. No claim that a restriction on $r$ automatically cancels
is valid.

For the intended restriction, prescribe on $\mathcal F$

$$
g(s)=\mathbf1_{\{A^*\subseteq K_s\}}
      \mathbf1_{\{\theta_s\text{ is a survivor}\}}. \tag{9}
$$

Extend it in any fixed second-state-only way to the other states
(zero is one possible choice); values on states without partners
are irrelevant. All such extensions give the same sum by (7).
If this sum is nonzero, (7) supplies a state satisfying
(5) and the full type condition; (2) gives the required actual
matching and Hamiltonian complement. This is a sufficient source-image
route to E183, not an equivalence with all of E183.

Equations (7) and (9) alone merely mark desired recovered solutions.
They do not prove there is one. The issue is whether the source's
independent nonvanishing proof can be retained. The next sections
compute that issue, rather than declare this coefficient nonzero.

## 6. Actual restricted orientation-group contribution

Fix an undirected source group $D$ with cycles indexed $1,\ldots,c$.
Let $\varepsilon_j=+1$ mean counterclockwise and $-1$ clockwise.
Its $2^c$ pairs have heads $s_\varepsilon$ and tails $r_\varepsilon$.
Every choice is a pair by the source regrouping at lines 525--533.
Changing an orientation changes the second state on that cycle.

Put

$$
L_j^\pm=L_\pm(C_j),\quad
m_j=(L_j^++L_j^-)/2,\quad
d_j=(L_j^+-L_j^-)/2>0.
$$

The strict positivity is exactly `lem:circulation` and the read
simple spoke-detour argument, not an assumed property of arbitrary
edge weights. By `lem:disk`, the phase per cycle is $-i\varepsilon_j$.
Consequently the actual contribution to (6) is

$$
\boxed{
G_D^g(z)=(-i)^c e^{z\sum_jm_j}
 \sum_{\varepsilon\in\{\pm1\}^c}
 g(s_\varepsilon)\Bigl(\prod_j\varepsilon_j\Bigr)
       e^{z\sum_j\varepsilon_jd_j}.
}                                                   \tag{10}
$$

For additional precision expand the Boolean-cube function, with no
assumption that it is constant, as

$$
g(s_\varepsilon)=\sum_{S\subseteq[c]}\widehat g_D(S)
                      \prod_{j\in S}\varepsilon_j,\qquad
\widehat g_D(S)=2^{-c}\sum_\varepsilon
                 g(s_\varepsilon)\prod_{j\in S}\varepsilon_j .
$$

Factoring the finite sum one coordinate at a time gives

$$
G_D^g(z)=(-i)^c2^c e^{z\sum_jm_j}
\sum_{S\subseteq[c]}\widehat g_D(S)
 \prod_{j\in S}\cosh(zd_j)\prod_{j\notin S}\sinh(zd_j). \tag{11}
$$

Here the sum is multiplied by the prefactor on the first line.
This is a finite algebraic identity, not a state enumeration.
For $g\equiv1$, only $S=\varnothing$ occurs and (11) is exactly
`eq:group-product`, with leading term
$(-i)^cz^c\prod_j(L_j^+-L_j^-)$.

For a nonconstant filter, nonempty $S$ can contribute in degree
$c-|S|$, and its coefficient $\widehat g_D(S)$ need not be positive.
For instance, in a one-cycle group the filter retaining only the
counterclockwise orientation gives

$$
G_D^g(z)=-i e^{zL_1^+},
$$

whereas retaining only the clockwise orientation gives
$i e^{zL_1^-}$. Both have order zero, unlike the unfiltered group's
simple zero and leading coefficient $-i(L_1^+-L_1^-)$.
This proves a precise failed implication: the unfiltered product
formula and its order cannot be inferred for a restricted population.
These algebraic filters are not asserted to occur as the full E183
filter in an admissible disk; they are not graph counterexamples.

If $g(s_\varepsilon)$ were a nonnegative constant $\gamma_D$ on
every group, then the source proof would work on the groups with
$\gamma_D>0$, provided at least one existed. It would use their
minimum $c(D)$ and the common leading phase there. Neither the
required constancy nor a positive retained group is established by
the frozen prescription and complete survivor fibres. In particular,
the recovery of $W_s$ changes with $s$; orientation reversal is not
merely a change of arrows on one fixed white-face tree.

## 7. A non-tautological necessary mark and its exact group formula

Before imposing recovery or type, consider the readily defined mark
on *all* second states

$$
\eta(s)=
\mathbf1_{\{s(t_b)\in V((by)^*)\}}\,
\mathbf1_{\{s(t_d)\in V((dc)^*)\}}.                 \tag{12}
$$

It is necessary for the two nonroot frozen edges by (4), but says
nothing about the root-component sides or survivor type.
It is a genuine incidence mark, not a definition using the desired
solution count. It preserves fixed-$s$ cancellation.

For a fixed $D$, let $d_t$ be its chosen undirected side at $t$.
At a marked face with desired edge $f$, the head is one endpoint
of $d_t$. If $d_t=f$, both orientation choices pass the incidence
mark. If $d_t\ne f$, those two sides of a triangle share exactly one
endpoint, so exactly one orientation of that cycle passes.

Thus (12) fixes signs on at most two cycles of $D$. If the two
requirements fix opposite signs on the same cycle, its entire
contribution is zero. Otherwise let $F_D$ be the cycles whose signs
are fixed, with required signs $\sigma_j$, and $U_D$ the others.
Set $\zeta_+=-i$, $\zeta_-=i$. Direct summation gives

$$
\boxed{
G_D^\eta(z)=
\prod_{j\in F_D}\zeta_{\sigma_j}e^{zL_j^{\sigma_j}}
\prod_{j\in U_D}\left(-i e^{zL_j^+}+i e^{zL_j^-}\right).
}                                                   \tag{13}
$$

The two displayed products are multiplied. If $q_D=|U_D|$,
$f_+$ and $f_-$ count fixed positive and negative signs, its first
nonzero coefficient is in degree $q_D$, and is

$$
(-i)^{q_D+f_+}i^{f_-}
       \prod_{j\in U_D}(L_j^+-L_j^-).               \tag{14}
$$

The formula includes $U_D=\varnothing$, when its order is zero
and the empty product is one.

This gives a precise restriction on transplanting the original proof.
Even the necessary local mark can replace source difference factors
by single exponentials and lower the order from $c(D)$ to
$c(D)-|F_D|$. At a common order $q_D$, (14) still contains the
fixed-orientation phases. The source argument aligning phases of
groups with minimum *total* cycle number no longer proves their
sum positive. No occurrence of opposing phases in an exact E183
instance is asserted here, and no impossibility theorem is claimed.
A further theorem would have to control these phases or find another
nonvanishing argument under the actual graph hypotheses.

Even a proof that $Z_\eta\ne0$ would only recover a partnered forest
state passing the endpoint conditions. It would still have to satisfy
both parent-edge conditions in (5) and the full lifted type test.
One cannot silently replace these global tests by the local mark.

## 8. The bounded attempt stops at a concrete gap

The attempted bridge was: freeze $xa$ by the root prescription, mark
the other two edges and the full survivor type as a second-state
condition, retain fixed-$s$ cancellation, and regroup by orientations
to prove nonvanishing. Its first half is valid, through (7). Its
nonvanishing step is not proved.

The remaining claim is specifically a positive restricted population
in the actual fixed-root state image, together with noncancellation
in (10), or another sufficient positivity certificate for it. The
available source positivity is only $d_j>0$, not a statement about
the Fourier coefficients in (11) or the fixed phases in (14).
The exact exterior, complete fibres and the two lost packings have
not been related to those coefficients or the white-tree parent tests.
This is not an invitation to replace those hypotheses by a ladder
census, to discard survivor types omitting cut 2, or to revive ears.

The following attempted shortcuts therefore fail at definite steps:

* $A^*\subseteq Q_s$ prescribes the wrong edges, by (3).
* Choosing $f_0$ freezes only $xa$; (5) remains.
* A known lost Hamiltonian completion supplies a state $s_H$, but
  not the rooted-forest preimage test in Section 4.
* Nonempty survivor fibres and a nonempty $A$-containing lost family
  do not prove their required intersection in the source image.
* The original sum is nonzero, but (10)--(14) do not inherit its
  product and common-phase argument under the restriction.
* Defining (9), setting it to zero on cyclic states, and declaring
  its sum nonzero just restates existence within the source image.
  No such declaration is made.

**Original E183 is UNRESOLVED.** There is neither a universal
survivor proof nor a fully hypothesized counterexample. The image
test and restricted-group calculations are scoped technical deductions,
not a ninth accepted finding or a new-to-literature claim.
No next task is commissioned.

Z184 remains unresolved. Its known sufficiency for E183 is unchanged;
neither a converse nor strict separation is proved. There is no new
implication for exchange, (T), Q164, or E182/E181/H180/L179.

## 9. Dependencies and validation limits

The source statements and operations used are `lem:duality`,
`prop:pairs`, `lem:disk`, `prop:forest-state`, `lem:cancel`,
`lem:circulation`, `eq:group-product`, `eq:leading-coefficient`,
`lem:root-components`, `lem:P-forest`, and the explicit recovery.
The full retained main TeX text, lines 1--838, was read. The included
figure and bibliography were not opened; this is not a claim to have
read all compiled supporting material. I164 Section 5, lines 386--474,
was read for the count/injection boundary, not recursively audited.
No external theorem beyond the stipulated source is imported.

Internal written checks cover small cuts, vertex connectivity,
the dual separation argument, black-face edge ownership, (3)--(5),
the conditional preimage test, cancellation phases, the finite
factorization (10)--(11), and the necessary-mark formula (13)--(14).
They are not independent review or proof-assistant verification.

Only the five assigned proof-record files are written. No research
code, graph/state/matching scans or tests, experiments, historical
replays/rebuilds, source copies, snapshots/seals, agents, ancestor or
shared-ledger edits, staging, commits or publication are used.
Document checks and SHA-256 authentication are not mathematical
experiments. The parent's inherited 23-stage checks and finite controls
are reported elsewhere as inherited, not rerun.
