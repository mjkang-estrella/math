# A realized two-coordinate trade, its normal form, and its obstruction

Myeongjin Kang; no affiliation. 2026-10-16.
Original prose CC BY 4.0; original code MIT. Third-party rights retained privately.

This is supporting work for unchanged full LR, not a solution or a universal
obstruction. All assertions below are independently proved. In particular,
this is neither a refinement of the balanced source nor the excluded
one-fresh-coordinate construction.

## 1. Model and the operation attempted

Let F be a finite field of order q and D its q+1 affine directions. An old
vertex [d,L] labels each affine line L of direction d. Fresh vertices in
different parts are disjoint and are distinct from all old vertices.
Ordinary edges e_x use [d,x+d] in every part. A two-coordinate exception
at p, with distinct omitted directions a,b and fresh labels z_a,z_b, is

    f(p;a,b;z_a,z_b) = {z_a,z_b} union {[d,p+d]: d notin {a,b}}.

Thus the retained OLD labels are a pencil, but there are TWO fresh
coordinates. The six-edge gadget below is a nonpencil partition trade:
its new triple blocks are not old line blocks, and it changes pair agreements.
The theorem is about this precise ambient model, not arbitrary exceptions.

Choose four distinct directions d_0,d_1,d_2,d_3, fresh labels z_i in these
parts, and six centers p_ij indexed by 0<=i<j<=3. Write f_ij for the
exception at p_ij using z_i,z_j. A useful elementary agreement rule is:
for two DIFFERENT centers, their old pencils agree only in their joining
direction, and retain that agreement if and only if neither edge omits it.
Fresh agreements are counted separately. This proves pair conditions
directly; it does not select colors without transitivity.

The intended mechanism was to increase all four affected part sizes by
one without leaving an unused old label: a fresh vertex with degree three
replaces several old agreements, while other exceptions recover the old
line labels that ordinary edges can no longer use.

Call the six centers **locally saturated** if, for every i and every j!=i,
the d_i-line through p_ij contains a center p_kl with i notin {k,l}.
This means every old line omitted by this gadget is recovered somewhere
within its six exceptions. Suppose the centers are distinct and the six
edges are linear and intersecting. The next calculation classifies this
locally saturated attempt, rather than assuming its incidence equations
are realizable.

## 2. Saturation forces characteristic two and an F_4 normal form

At the fresh label z_v, consider the three centers p_vu for u!=v. If an
old d_u-line omitted at p_vu is recovered by another gadget center, that
other edge must share z_v. Indeed, its joining direction is d_u, omitted
by f_vu, so it has no old agreement with f_vu. The other edge cannot use
z_u because it is using the old d_u label. Thus it is f_vw for some w,
and p_vu p_vw has direction d_u.

Draw an arrow u->w when this occurs, on the three neighbors of v. A pair
can support at most one arrow: d_u and d_w are distinct. Saturation says
every vertex has an outgoing arrow. There are only three unordered pairs,
so all three arrows occur and form a directed 3-cycle. In particular,
the three centers are noncollinear. This holds at every v.

Rename neighbors so that the cycle at 0 is 1->2->3->1. An invertible
linear change of affine coordinates sends d_0,d_1,d_2 to infinity,0,1.
Write d_3=t, with t!=0,1. Translate p_01 to (0,0). The three directions
at the cycle at 0, followed by a common nonzero scaling, give

    p_01=(0,0),  p_02=(1-t,0),  p_03=(1,t).

Here the scaling is legitimate because p_03 lies on the nonvertical
d_3-line through p_01 and differs from p_01.

At vertex 1 use neighbor order (0,2,3), and at vertex 2 order (0,1,3).
Call each cycle forward or reverse in its indicated order. If both cycles
are forward, p_12 would have x=0 and x=1-t. If 1 is forward and 2 reverse,
then p_12=(0,0); if both are reverse, the same equality follows. These
are impossible. Thus 1 is reverse, 2 is forward, and

    p_12=(1-t,1-t).

The cycle at vertex 1 also forces p_13 onto x=0. At vertex 3, using
neighbor order (0,1,2), a forward cycle would instead force x=1. Hence
3 is reverse, and p_13=(0,t). The conditions at 2 and 3 give

    p_23=(1,t^2).

The three remaining pair directions give, respectively,

    t^2-3t+1=0,   t^2+t-1=0,   t^2-t-1=0.

For clarity: the first comes from p_12 p_13 having slope t; the second
from p_12 p_23 being horizontal; the third from p_13 p_23 having slope 1.
Subtracting the last two gives 2t=0. Since t!=0, the characteristic is
two. All three equations then reduce to t^2+t+1=0. Consequently F contains
F_4, and t has multiplicative order three. Conversely the displayed
coordinates do realize all required directions, as the next section proves.
This calculation works with ANY chosen gadget vertex renamed 0. That
observation will permit the extension proof to normalize an arbitrary z_v.

## 3. Complete realization, including all pairs and ordinary edges

Let q=4^n, t^2+t+1=0, and put a=t^2=1+t. In coordinates the six centers are

    01:(0,0)  02:(a,0)  03:(1,t)
    12:(a,a)  13:(0,t)  23:(1,a).

The four omitted directions are d_0=infinity, d_1=0, d_2=1, d_3=t.
Here is the COMPLETE joining-direction list, grouped by the shared fresh
label (the two digits denote the center):

    at 0: 01-02:0       02-03:1       03-01:t
    at 1: 01-12:1       12-13:t       13-01:infinity
    at 2: 02-12:infinity 12-23:0      23-02:t
    at 3: 03-13:0       13-23:1       23-03:infinity
    opposite: 01-23:t^2, 02-13:t^2, 03-12:t^2.

These identities follow by subtracting the coordinate pairs and using
t^2=t+1 and t^3=1. They list all 15 unordered pairs. For adjacent K_4
edges, the joining direction belongs to their union of omitted directions,
so there is no old agreement and precisely their one shared fresh label.
For opposite K_4 edges, neither fresh label is shared, while direction t^2
is omitted by neither edge and supplies precisely one old agreement.
Thus every pair has EXACTLY ONE agreement.

Let U be the union of all d_i-lines through p_ij, i in {i,j}; equivalently,
the union of the twelve omitted lines. Choose ANY ordinary set X outside U.
An x in X differs from each p_ij and its joining direction to p_ij is
neither d_i nor d_j. Thus e_x meets f_ij in precisely one old vertex.
Two ordinary edges meet precisely in their joining-direction vertex.
The combined hypergraph is therefore an actual finite linear intersecting
(q+1)-partite hypergraph, including when X is empty. Distinct centers give
distinct edges; ordinary and exceptional edges differ in fresh coordinates.

For q>12, taking X=A minus U makes every other line in an affected
direction nonempty: such a line meets at most twelve lines of U and
coincides with none of them. Each affected part has q-3 ordinary-used old
labels, three further old labels used by exceptions, and one fresh label:
exactly q+1 nonisolated vertices. This verifies the hoped-for local part
enlargement; it is explicitly NOT a cover lower bound.

The three omitted lines in part 0 are x=0,a,1. Their only old-label users
among gadget edges are, respectively, 13,12,23. In part 1 the analogous
horizontal lines have intercepts 0,t,a and old users 02,03,23. Direct
substitution gives the same pattern in parts 2 and 3: three distinct lines,
each containing one incident and one nonincident center. Hence each gadget
edge has TWO old labels, in the other two affected parts, of degree one
in this initial hypergraph. The next proof shows these cannot be repaired
even by reusing gadget fresh labels in further two-coordinate exceptions.

## 4. No new two-coordinate edge can reuse a gadget fresh label

Assume q>=5 and that a linear intersecting extension in the stated model
contains the gadget. Any new exception has a center different from all six
gadget centers: at equal centers, the sets of omitted directions have union
of size at most four, leaving at least (q+1)-4=q-3>=2 common old vertices.
That violates linearity. An ordinary edge at a gadget center likewise
shares q-1 old vertices with its gadget exception.

A new exception cannot use two gadget fresh labels, since it would share
both with the corresponding existing f_ij. Suppose it uses exactly one,
say z_v. Normalize with v=0 by the preceding normal-form argument, and
let h!=infinity be its other omitted direction. Its other fresh label is
not any z_i, even if its part is one of the four old affected parts.
Write its center as (x,y).

Against the three NONincident gadget edges 12,13,23, no fresh agreement
is possible. Therefore their joining directions to (x,y) must avoid all
omitted directions, in particular infinity. Their x coordinates are a,0,1,
so x is none of a,0,1.

Against the three incident edges 01,02,03 the new edge already shares
z_0. Their joining directions must belong to the union of omitted
directions, to prevent an additional old agreement. The vertical option
has just been excluded. If h denotes its finite slope, these requirements
are exactly

    y=0       OR y=h x;
    y=x+a     OR y=h(x+a);
    y=t x     OR y=h(x+1)+t.

Call the second alternative in each row the h-alternative. Two first
alternatives would intersect only at one of 01,02,03, excluded by their
x coordinates. Hence at least two h-alternatives hold. Two parallel
h-lines through two different centers can agree only when h is their
joining direction. The three possibilities exhaust the cases:

* h=0: the first two h-lines have y=0. The last row then forces x=0,
  or 0=t, both impossible.
* h=1: the last two h-lines have y=x+a. The first row forces x=a,
  or a=0, both impossible.
* h=t: the first and last h-lines have y=t x. The middle row forces
  x=1, or 1=0, both impossible.

For the third case, (t+1)x=a implies x=1 because t+1=a. This proves
that no additional two-coordinate exception can use ANY gadget fresh
label. The argument allows arbitrary new directions and labels; it is
not a finite-field scan or an assumption that translates are independent.

## 5. A global (r-1)-cover in every such extension

Take one of the old labels v shown in section 3 to have a unique gadget
user. Its line L also contains a gadget center p_ij whose exception omits
that direction d. An additional ordinary edge using v would have its
center on L. It could not meet f_ij: at a different center its unique
possible old agreement is d, which f_ij omits, and it has no fresh label;
the equal-center case was already excluded.

An additional two-coordinate exception using v has its center on L too.
It shares no gadget fresh labels by section 4, so the same joining-direction
argument makes it disjoint from f_ij. Again equal centers are impossible.
Thus v remains degree one in the ENTIRE extension, regardless of the
ordinary subset or the number, centers, directions, and fresh-label choices
of additional two-coordinate exceptions.

Let e be its unique gadget edge. The set e minus {v}, of size q=r-1,
covers every edge: every edge other than e meets e, and cannot meet it at
the degree-one vertex v. It also meets e itself. This is a proved GLOBAL
cover, not a check of only same-part covers or edge-minus-one candidates.
It disproves this attempted LR mechanism for every q=4^n>=16 and every
allowed extension. A batch containing even one such gadget still fails.

## Limits, repair burden, and diagnostic

The successful part is a genuinely realized pair-changing trade with two
fresh coordinates, not a prescribed incidence equation alone. Its twelve
new triple-block pair incidences replace old line pair incidences. The
failed part is global covering: the private old labels are rigid under
the permitted extension operation. A repair must change the gadget itself,
use exceptions with at least three fresh coordinates, change old labels
away from a single pencil, or perform another global trade. None of these
remaining possibilities is ruled out here, and no repair was obtained.
In particular this is NOT a theorem about every two-coordinate gadget,
much less every linear intersecting hypergraph.

The inspected/authenticated diagnostic `diagnostics/check_k4.py` merely
checks the displayed F_4 coordinates, all 15 joins and twelve singleton
old labels. Its result is `diagnostics/k4-result.json`. The classification,
all-field extension obstruction and global cover proof above are symbolic
proofs, not consequences of this finite diagnostic. No broad search or
historical/third-party mathematical program was run. No worldwide novelty
or substantial-result nomination is asserted.
