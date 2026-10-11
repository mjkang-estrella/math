# I183 continuation: corrected strategy and terminal hypotheses

2026-10-11. Written deductions, not a universal CPTP-survival verdict.
The mandatory computational replay is incomplete. No new graph, attachment,
parameter sweep or enlarged instance population is used here.

## 1. Exact hypotheses and quantifiers

For every finite connected simple bipartite disk graph X with five distinct
degree-two boundary vertices b_0,...,b_4, all other vertices cubic, keep the
oriented boundary order (0,2,1,4,3) and colors (1,1,1,0,1). Glue its five cut
edges to the fixed thirteen-vertex exterior Y in H180. Require the glued
graph G to be simple, planar, bipartite and a brace. Here the brace
consequence used below is that every two disjoint edges extend to a
perfect matching. No stronger matching prescription is assumed.

In label order the exterior endpoints are (1,5,6,28,29). The exact exterior
vertex set is {1,...,11,28,29}, and its internal edges are

```
(1,7),(1,28),(2,3),(2,8),(2,29),(3,4),(3,9),(4,5),(4,10),
(5,11),(6,7),(6,11),(7,8),(8,9),(9,10),(10,11),(28,29).
```

The eleven complete, nonempty, acyclic spanning survivor local types are

```
0: 02;02       1: 12;12       2: 14;14       3: 24;24
4: 0123;02,13  5: 0123;03,12  6: 0134;03,14
7: 0234;02,34  8: 0234;03,24  9: 1234;12,34
10:1234;14,23
```

Complete lost types are P=(01;01) and D=(0134;01,34). A packing has
degree one exactly at the indicated ports, degree two elsewhere, and no
isolated cycle. Completeness includes the compatible exterior products,
not just displayed representatives.

The I181 patch consists of two internal quadrilateral faces sharing one
edge xy, their union a disk with simple port-disjoint boundary
C=(x,a,b,y,d,c,x). Set A={xa,by,dc}, B={ab,yd,cx}. Fix any p in the
complete P fibre with p intersect E(C)=A and q=p symmetric-difference
E(C) also in P. E183 asks for an A-containing perfect matching whose
Hamiltonian complement restricts to a survivor type. This is the same
quantified problem, not an assertion only about the retained ladder.

## 2. Fixed-local exterior rerouting cannot achieve survival

For any fixed spanning local packing r, its degree-one vertices determine
the used cut labels J(r), and its path components determine its local
pairing pi(r). Changing only edges inside Y does not change either datum.
At each port, cubic degree and the fixed internal degree also force
whether its cut edge is in the complementary Hamiltonian cycle. Thus
allowing cut-edge choices as well as exterior choices while holding r
fixed still cannot change J(r).

In particular, all Hamiltonian completions with local restriction q have
local type P. A different exterior partner may fail to be Hamiltonian,
or may be another Hamiltonian completion of the same lost type; it
cannot supply a survivor *local* type. This is an invariant argument,
not a finite search of exterior partners.

The proposed exterior-only strategy in I182's last paragraph is therefore
not equivalent to unrestricted E183. E183 allows a change to the local
packing, including edges outside the six-vertex patch but inside X.
Only the forced patch prescription must stay fixed. Disproving the
restricted fixed-local strategy does not refute E183.

## 3. Continuations leave V(C) and their terminals are distinct

These proofs use simplicity, bipartition, cubicity, the two-square patch,
connectedness and brace two-extendability. Distinctness is not inferred
from the six retained instances.

Color x,b,d black and a,y,c white. Vertices x,y are saturated by the
two boundary edges and xy. At each of a,b,c,d there is exactly one
unused incident edge beyond the patch's seven edges.

### 3.1 These four edges leave the six-vertex boundary

An additional edge with both ends in V(C) can only be ad or bc: other
nonadjacent possibilities have equal colors, an endpoint x or y is
already saturated, and existing edges cannot be duplicated.

Suppose ad exists. If bc also exists, all six vertices are saturated;
they form a connected component, contradicting connectedness of G and
the nonempty exterior Y. If bc does not exist, the third edges bb' and
cc' leave V(C). (They cannot end at x or y or at the now saturated a,d.)
They form the entire edge cut of this six-vertex set.

The two edges bb' and cd are disjoint. Two-extendability requires a
perfect matching containing them. It uses bb', cannot use cc' because
c is matched to d, and thus has exactly one matching edge across this
cut. For any perfect matching M and vertex set S,

    |S| = 2 |M intersect E(S)| + |M intersect delta(S)|.

This is impossible for |S|=6 and one crossing edge. So ad is impossible.
The case bc is identical with aa' and cd: the only cut edges are aa',
dd', and cd forbids dd'. Thus all four third edges leave V(C).

This preliminary step matters: a third edge leaving the two-face disk
must not silently be assumed to have its other endpoint outside V(C).

### 3.2 Either possible identification contradicts two-extendability

Write these edges as aa',bb',cc',dd'. Since a,c are white, a',c'
are black; since b,d are black, b',d' are white. Therefore the only
possible identifications are a'=c' or b'=d', independently.

Suppose a'=c'=t, so t is black. Let S=V(C) union {t}.
Its black vertices are {x,b,d,t}, its white vertices {a,y,c}.
All three white vertices have their full degree inside S:
a has neighbors x,b,t; y has neighbors x,b,d; c has neighbors x,d,t.
Thus the entire cut of S consists of the third edges at b,d,t.
Their other endpoints are outside S. For t's third edge, this also
uses simplicity (a,c are already neighbors) and saturation of y.

Every perfect matching crosses this cut exactly once: all three white
vertices must be matched internally, using three of the four black
vertices, and the fourth black vertex must be matched outside S.
If two of the three cut edges have distinct outside endpoints, they
are disjoint, so two-extendability would extend both to a perfect
matching. That would give at least two crossings, a contradiction.
If no such pair exists, all three cut edges meet one outside vertex w.
Cubicity then saturates w with these edges; S union {w} is a closed
eight-vertex component of G. This contradicts connectedness since G
contains all thirteen vertices of Y as well as the six patch vertices.
Hence a'=c' is impossible.

For b'=d'=t interchange the two color classes: S has white vertices
{a,y,c,t}, black vertices {x,b,d}, and its three cut edges leave
a,c,t. The identical one-crossing/two-extendability argument excludes
this case. All four continuation terminals are therefore distinct.

A smaller attempted Hall argument on {x,t} would not work:
it can have four neighbors. The successful obstruction uses the
seven-vertex shore and its fully internal minority color class.
No distinct-terminal theorem was assumed in proving this result.

## 4. Incidence-level reduction, including singleton paths

Section 3 pays distinctness in the exact E183 setting. The following
slightly more general lemma also explains what the original quotient
remark requires if brace assumptions are dropped. It is not evidence
that repeated terminals occur under the E183 hypotheses.

Give the four continuation incidences names alpha,beta,gamma,delta
corresponding to a,b,c,d. They are distinct *incidences*, even if
their endpoints in G' coincide. Write t(i) for their endpoints and
m(v)=number of incidences attached to v. Bipartition and cubicity imply
m(v)<=2 here; in any setting where a perfect matching of G' exists,
degree nonnegativity gives the same bound.

Deleting A bijects the A-containing perfect matchings of G with
perfect matchings M' of G'=G-V(C). This needs no distinct-terminal
assumption: A saturates every removed vertex, so no matching edge
crosses to G'. Conversely adjoining A to a perfect matching of G'
saturates every vertex exactly once.

Put H'=G'-M'. Its degrees are

    deg_G'(v)=3-m(v),       deg_H'(v)=2-m(v).

Attach one labelled stub at each continuation incidence to H'. Every
old vertex now has degree two in this stubbed graph; only the four
labelled ends have degree one. Each component is either a closed
cycle without stubs or an interval with exactly two stub ends. A
vertex with m(v)=2 is an isolated vertex of H', and connects its two
stubs: this is a legitimate length-zero path, not a discarded
isolated component. There are exactly two interval components, hence
a perfect matching R of the four incidence labels.

The forced patch complement S=B+xy+{aa',bb',cc',dd'} connects
alpha to beta and gamma to delta. Its incidence matching is

    L={{alpha,beta},{gamma,delta}}.

G-M is obtained by adjoining these two forced routes to H'. It is
one Hamiltonian cycle exactly when H' has no stub-free closed cycle
and the labelled multigraph R union L is connected. On four labels
this says

    R={{alpha,gamma},{beta,delta}}
       or R={{alpha,delta},{beta,gamma}},

not R=L. When R=L, retaining the two parallel copies gives two
closed components, not a simple matching. No parallel edges are
suppressed. The singleton intervals above are kept throughout.
This proves the corrected reduction in all allowed repeated-incidence
cases, without assuming a distinct-terminal theorem.

There is also a useful restriction using the already paid nonemptiness.
If both a'=c' and b'=d', H' has two singleton intervals. Every other
vertex has degree two, so the remaining nonempty vertex set contains
a closed component. It is nonempty because G contains all thirteen
exterior vertices and the six patch vertices, whereas only two vertices
can carry these repetitions. This contradicts the Hamiltonian completion
of q. Thus both identifications cannot hold simultaneously even under
these weaker assumptions. Section 3 excludes either one under the
full brace hypotheses.
If exactly a'=c' holds, every complement H' contains the singleton
alpha--gamma interval, and its other interval joins beta to delta.
The incidence pairing is automatically cross; the topological condition
is precisely that there be no additional cycle. The case b'=d' is
symmetric. No existence of a surviving local packing follows from this.

Equivalently insert two distinguished edges in G',
e_ab=a'b', e_cd=c'd', keeping their identities even if other edges
have the same endpoints. A spanning connected degree-two submultigraph
containing both distinguished edges lifts to the required Hamiltonian
cycle, and deletion of them gives the incidence intervals above.
If a more general quotient identifies the endpoints of a distinguished
edge, it is retained as a loop of degree two. Under the present
bipartition those individual loops cannot occur, but parallel edges
can arise under the allowed identifications. The auxiliary graph is
not asserted simple or a brace, so the pinned simple-graph theorem
cannot automatically be applied to it.

The local type of the lifted complement is determined by H' together
with the known forced routes S and the fixed cut labels. It should
not be confused with R itself, which is a pairing of continuation
incidences, not the five-port pairing.

## 5. Nonempty topology remains paid, survival does not

Complete fibre membership of q supplies a compatible exterior partner
and hence a Hamiltonian completion H0. Its complement M0 contains A,
because H0 uses B, the chord, and all four continuations. Thus M0-A
is a member of the nonempty cross-paired population in the corrected
incidence sense. Its local packing is q and is still lost.

The stipulated main theorem gives Hamiltonicity under its stated
simple/cubic/planar/bipartite/3-connected hypotheses; edge avoidance
gives a Hamiltonian cycle avoiding one specified edge; P4 gives a
Hamiltonian cycle containing one three-edge path in a simple cubic
3-connected Pfaffian bipartite graph. None, without an additional
reduction, simultaneously preserves A and forces a survivor local
type. Two-extendability is a matching statement, not a complement
pairing statement. Elevenfold fibre nonemptiness does not prescribe
their restriction on C.

No universal proof or valid counterexample has been obtained. E183,
E182, E181, H180 and L179 remain unresolved.

## 6. A concrete sufficient condition, not a renamed equivalent predicate

Here is a bounded possible route which genuinely permits local change.
Let e_2 be the cut edge with label 2. Every completion H0 of q omits
e_2, so e_2 belongs to M0. Seek a simple M0-alternating cycle Z
entirely in G', containing e_2, for which

    H_Z = H0 symmetric-difference E(Z)

is connected. Alternation makes M_Z=M0 symmetric-difference E(Z)
a perfect matching. Since Z avoids V(C), M_Z contains A. Its
complement is H_Z, and H_Z uses e_2. A connected spanning degree-two
graph is Hamiltonian, and using cut label 2 excludes both lost types.
Thus this sufficient condition proves E183 for the given instance.

Connectivity is explicitly checkable without a generic connectivity
assumption: delete Z intersect E(H0) from H0, retaining singleton
segments, and add Z intersect M0. Contracting the old segments while
keeping endpoint incidences gives a multigraph; require it to be one
cycle, counting loops and parallel edges. The contraction preserves
components, so this criterion is equivalent to connectivity of H_Z.

Existence of Z is **unpaid**. It is stronger than E183: E183 may need
several alternating cycles at once, or only a survivor of state 6,
which need not use cut 2. Failure of this single-cycle condition would
not refute E183. Also Z cannot be exterior-only: it contains a cut
edge, and by cut parity must enter X. This avoids the fixed-local
invariance mistake.

One bounded next action: for the given q-completion class, determine
whether brace structure and the complete eleven fibres force such an
M0-alternating cycle through e_2, avoiding V(C), with connected segment
reconnection. Prove that implication or identify the precise failing
step. Do not turn failure of this sufficient route into a refutation,
and do not add graphs or sweep matching populations.

## 7. Scope and novelty

The fixed-local invariance, distinct-terminal justification and
incidence-level reduction are elementary corrections/clarifications,
not a substantial new-to-literature theorem. The continuation and
distinctness arguments are direct cut consequences of two-extendability.
They do not lower the contribution gate. Eight accepted findings
remain eight.

The I182 finite certificate remains inherited: 626 matching checks,
three patches, six directed instances, five controlled matchings per
instance. None is a universal survival proof, and none is called a
freshly completed I183 reduction replay at this checkpoint.
