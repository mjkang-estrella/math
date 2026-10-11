# I168: cross-class rank splitting and two further exchange obstructions

Date: 2026-10-10. Status: technical research; no acceptance nomination.

**Outcome.** All six requested I167 mathematical audit items pass. A new exact
cross-class rank identity isolates two guaranteed local directions and a
single balanced bridge that can recover at most one additional lost parent
direction. An infinite even-prism family rules out every fixed bound on the
number of dual faces transferred in each direction as a universal
rank-spanning method. The order-16 typed retract refutes affine fullness
even relative to its degree **and port** equations. Neither the C4 exchange
inequality, (T), nor Q164 is proved or refuted.

All theorems and proof operations in the pinned OpenAI repository at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. No upstream
truth audit, contradiction extraction, or ex-falso reasoning occurs.
Only the assigned report, experiment directory, and source directory were
written. No child agents, staging, commits, publication, or shared-ledger edits.

## 1. Immutable inputs and independent audit

Before trusting I167, these supplied hashes were checked and matched:

- Report: `3e23c1ff8e272880e70ac5e5919bd4dc78de21f0e0f9bb400a561497909c4509`.
- Seal: `11719b2338411a9b23a5def9d65fae7ba0daa9e6293d9368d0792c24099ed1cc`.

`initial-hash-check.json` records this. I167's inventory hash was checked
against that seal; its diagnostic and support payload hashes were then
checked against that inventory. The graph-data and source hashes match
I167's external bindings. This is dependency authentication, not execution
of I167's verifier. No ancestor code was imported, executed, or used as an
implementation source. All enumerators and rank routines below are freshly
written standard-library Python.

Write-relative experiment directory:
`frontier/experiments/i168_cross_class_exchange/`.
Source/receipt directory: `frontier/sources/i168_cross_class_exchange/`.
Ancestor JSON is read only as data. The 15 graphs come from I166's `bfs`
payload; the 636 precise labelled steps and ten nine-direction steps come
from I167's `diagnostic-attempt-01.json`. Census completeness beyond that
specified input set is not re-proved here.

Let B be the finite simple undirected cubic bipartite planar
3-vertex-connected graphs. Hamiltonian cycles mean unoriented edge sets.
All vector spaces and ranks are over the rationals or reals, which agree
for the integer matrices used here. For connected bipartite G, its unsigned
incidence matrix A has rank n−1, so its degree kernel has dimension
β(G)=m−n+1. A vertex potential is an edge weight α(u)+α(v).
The dual of this kernel is precisely edge weights modulo vertex potentials.

### 1.1 CW167 — PASS ORIGINAL

Use I167's terminal order u,v,…,y,x around the expanded face. Replace
uv and xy by arms up,vq,xr,ys and square pq,qs,sr,rp, and put
K=G−{uv,xy}. Write a=w(pq), b=w(rs), c=w(pr), d=w(qs),
S=a+b+c+d, δ=c+d−a−b, and t_u=w(up), etc. Set
W|K=w|K, W(uv)=t_u+t_v−a, W(xy)=t_x+t_y−b.

There are exactly six disjoint child-cycle fibres. N10, N01, N11 are
parent cycles using respectively only uv, only xy, or both. Pux and Pvy
are spanning paths in K with their specified endpoints. D11 comprises
spanning two-path covers with pairing (u,v),(x,y), without cycle components.
Their child weights are respectively

- W(C)+S, W(C)+S, W(C)+2(a+b);
- w(P)+t_u+t_x+S−c, w(P)+t_v+t_y+S−d;
- w(D)+t_u+t_v+t_x+t_y+c+d.

Proof of exhaustion: two arms require a spanning square path, whose endpoints
are adjacent; the four possible adjacent pairs give N10, N01, Pux, Pvy.
With four arms the square is a perfect matching and the exterior is two
paths. The crossing exterior pairing (u,y),(v,x) cannot occur in the disk
complementary to the chosen face. For each noncrossing pairing, exactly
one square matching makes one cycle. These give N11 and D11. Zero arms
cannot make a spanning cycle of the entire graph.

Setting each displayed weight equal to λ and γ=λ−S yields exactly CW167:
W(N10)=W(N01)=γ; W(N11)=γ+δ;
w(Pux)=γ−t_u−t_x+c; w(Pvy)=γ−t_v−t_y+d;
w(D11)=γ+a+b−t_u−t_v−t_x−t_y.
Necessity and sufficiency follow per object, not merely from counts;
empty fibres impose no equations. There is no N00 equation.

Independent validation checks complete set equality between these lifted
fibres and child cycles on all 636 steps. It checks every edge-coordinate
unit weight and six new deterministic signed weightings per step. Thus
coefficient identities, cross-class offsets, and the N11 sign are all tested.

### 1.2 Original-I166-failure witness — PASS ORIGINAL

For the first cube expansion, labels are
(u,v,x,y,p,q,r,s)=(0,1,2,3,8,9,10,11). Put α_p=1 and all other
vertex potentials zero. Every child Hamiltonian cycle has weight 2,
δ=0, while the original length-three aggregated weights on N10 and N01
are 2 and 0. Both classes are singletons. The original common-γ assertion
therefore fails exactly as I167 reported. I166's original equation remains
**FAIL ORIGINAL**; it has not been silently repaired or relabelled.

### 1.3 P167 — PASS ORIGINAL

In K the vertices v,y have degree two and are internal in every ux path.
Path differences vanish on their incident edges and belong to the degree
kernel of K−{v,y}=G−{v,y}. This graph is connected by 3-connectivity.
If ε indicates vy∈E(K), its edge count is |E(K)|−4+ε. Its kernel dimension
is consequently β(K)−2+ε<β(K). Hence

    dim aff Pux ≤ β(K)−2+ε < β(K).

Interchange the terminal pairs for Pvy. The annihilator of these differences
strictly exceeds the vertex-potential space on K, so single-class path
constancy cannot force potentials. This is a universal conclusion, not an
inference from finite rank failures. Nonemptiness follows from the stipulated
P4 theorem on H, as made explicit in §2.2. All 636 bounds are checked.

### 1.4 Transported-hull identity — PASS ORIGINAL

For a surviving parent cycle let E=χ(uv), F=χ(xy). Its lift leaves K
unchanged, has arms (E,E,F,F), and square coordinates
(pq,rs,pr,qs)=(F,E,2−E−F,2−E−F).
This is one affine map T on the entire surviving hull. Reading K and the
up,xr coordinates is a left inverse. Thus transport has dimension exactly
d_surv, and the missing rank is 2+(d(G)−d_surv). Complete coordinate and
rank checks reproduce this on 636 steps, including the ten steps requiring
nine new directions.

### 1.5 A167 and the dual-tree correspondence — PASS ORIGINAL

For nested nonempty proper rooted shores S⊊T that induce trees on both
sides, any component R of T−S has exactly one edge to S in the tree T,
and exactly one to V−T in the tree V−S. It has no edges to another
component of T−S. This gives a two-edge cut, impossible in a
3-edge-connected graph. Thus such shores form an antichain.

For a plane cubic 3-connected graph, each side of a Hamiltonian cycle is
a disk subdivided by noncrossing chords; its face-adjacency graph is a
tree. Conversely, a two-induced-tree dual partition leaves exactly one
monochromatic edge in each dual triangular face. Its primal crossing edges
have degree two at every vertex and are connected: disconnectedness would
supply a cycle in the complementary dual forest. Thus they are a Hamiltonian
cycle. The dual is 3-edge-connected because a smaller bond would correspond
to a primal loop or two-edge cycle, excluded by simplicity.

The fresh checker enumerates **all** rooted dual subsets of each of the
15 census graphs, tests both induced-tree conditions, and checks exact
bijection with independently enumerated Hamiltonian cycles. It checks all
pairwise non-inclusions and the dual cut lower bound.

### 1.6 McCuaig typed-port interface and witness — PASS ORIGINAL

The local assertion assumes two disjoint bicontraction triples and a simple
retract with distinct retained edges; these conditions hold for a strictly
thin cubic reduction. A cycle avoiding uv contains the fixed paths a-u-b
and c-v-d. Contracting them gives one spanning cycle selecting one port
from each outer vertex's port pair at both merged vertices. Conversely,
that port rule uniquely permits subdivision into these two paths. Retained
edge coordinates and fixed path coordinates give an affine bijection.
This assertion does not transport arbitrary untyped retract cycles.

For I167's actual labelled order-16 witness, deleting 02 gives the stated
12-vertex retract with 19 edges and degrees 3^10 4^2. Fresh enumeration finds
14 unrestricted cycles, exactly 8 typed cycles, and exactly 8 original
cycles avoiding 02, with exact set correspondence and affine dimension 5.
Complete perfect-matching checks independently certify 2-extendability of
both parent and retract. No external brace-generation theorem is required
for this local audit; the claim of a whole McCuaig induction remains unpaid.

### 1.7 Audit execution and preserved failure

The independent audit finished **before** the new exchange campaign.
All 636 steps satisfy d(H)=d(G)+2. Required-extra-rank counts are again
2:138, 3:441, 5:34, 7:13, 9:10.

The first audit run failed at step 12 because I rotated each face to its
smallest label before applying inherited position-labelled steps. This
changed which edges step [0,0,2] selected: the observed N00 count was 3
instead of the recorded 1. The original failing code, empty output,
traceback and exact labelled detail are retained as `audit-attempt-01*`.
The fix uses the unaltered face arrays. `audit-attempt-02.json` then passed
all 636 exact comparisons. This was a genuine failed implementation
attempt, not a mathematical failure attributed to I167.

## 2. Route (i): an exact joint cross-class rank theorem

### 2.1 Definitions and quantifiers

**Proposition R168 (proved).** For every admissible C4 expansion G→H in B,
assume the stipulated P4 result (used only for fibre nonemptiness).
Choose any surviving parent cycle C0 and any representatives
P0∈Pux, Q0∈Pvy, D0∈D11. Let L be the span of differences of surviving
parent cycles. Let U be the sum of the within-class difference spaces of
Pux, Pvy, D11, embedded in R^{E(G)} by putting zero on uv,xy. Define

    b = χ(P0)+χ(Q0)+χ(D0)+2·1_uv+2·1_xy−3χ(C0),
    M = L+U+span{b}.

Then M⊆ker A_G and

    d(H) = 2 + dim M.                                      (R168)

In particular, writing ℓ=d(G)−d_surv, t=dim(L+U)−dim L, and
η=dim M−dim(L+U)∈{0,1},

    d(H)−d_surv = 2+t+η,
    d(H)≥d(G)+2  ⇔  t+η≥ℓ.                                (E168)

All choices of representatives give the same M. These are exact identities;
the right-hand inequality has **not** been proved universally.

### 2.2 Proof, including the two guaranteed directions

Use uppercase letters U_a,V_a,X_a,Y_a for the four arm coordinates, and
A_s,B_s,C_s,D_s for pq,rs,pr,qs. On the affine space satisfying the child
vertex degree equations, define the linear local projection

    π(z)=(U_a−V_a, A_s−X_a).

The images of the three transported classes are (0,0), while the images
of Pux,Pvy,D11 are respectively

    (1,0),  (−1,1),  (0,−1).

Thus the last three images span two dimensions and their unique linear
relation has coefficients (1,1,1).

For completeness these classes are nonempty without assuming a new rank
theorem. Apply the stipulated P4 corollary to the child paths u-p-q-s,
v-q-p-r, and u-p-r-x. The degree-two condition in a Hamiltonian cycle
forces respectively the Pux, Pvy, and D11 local patterns. For example,
u-p-r-x excludes pq and rs, forcing v-q-s-y as the other square segment.
A parent Hamiltonian cycle containing uv exists by that same stipulated
corollary on G, supplying C0.

On the degree-two affine space, π=0 means U_a=V_a and A_s=X_a.
The square degree equations then force Y_a=X_a, B_s=U_a and
C_s=D_s=2−U_a−X_a. Hence the π-zero affine subspace is exactly
T({z:A_Gz=2}), where T is the affine transport map from §1.4.
Its linear part T0 identifies ker A_G with the π-kernel of the child
degree-difference space.

Generate the child HC-difference space using transported differences,
within-fibre differences, and the three differences between the chosen
new lifts and T(C0). The first two sets lie in ker π and pull back to
L and U. The last three project to the three displayed vectors.
Consequently their only extra π-zero combination, modulo L and U,
is their sum. Its K-coordinates are χ(P0)+χ(Q0)+χ(D0)−3χ(C0)|K,
and its up,xr coordinates are 2−3χ(C0)(uv), 2−3χ(C0)(xy).
Its pullback is exactly b. Therefore the π-kernel of the child
HC-difference space is T0(M), while its π-image has dimension two.
Rank-nullity proves R168 and E168.

Each vector in L or U has zero vertex degrees. The three representative
path covers have total degree four at every terminal and six at every
other vertex; adding twice each deleted edge brings the terminal total
to six as well. Subtracting 3χ(C0) gives zero degrees, proving b∈ker A_G.
Changing a representative changes b by an element of U; changing C0
changes it by an element of L. Thus M is choice-independent.

This formulation retains CW167's cross-class equations. In the dual weight
space it says that all constraints are the annihilation of L, U, b,
together with the two local directions. Vertex potentials annihilate
these parent vectors automatically. More precisely,

    β(H)−d(H) = β(G)−dim M.

These are deficiencies modulo vertex potentials. No within-family-only
replacement has occurred.

### 2.3 Consequences and finite validation

**Proved consequences.** Survival-full expansions satisfy exchange
immediately. In general at least ℓ−1 lost directions must come from U
modulo L, because the balanced bridge contributes at most one. If
ℓ>0 and t=ℓ−1, the remaining obligation is precisely b∉L+U.
For an affine-full parent, exchange is equivalent to M=ker A_G.
For arbitrary parents, containing the parent HC-difference space in M is
a sufficient stronger condition, not claimed necessary or proved universal.

The first tests were the expanded cube and the ten steps with required
rank nine, extracted without altering I167's data. Their zero-based
indices are 520,522,524,527,528,530,533,534,536,539.
The cube has (ℓ,t,η)=(1,0,1). Each nine-direction step has
(ℓ,t,η)=(7,6,1), so its actual new rank is 2+6+1=9.
This explains why the cube's three singleton classes still matter:
their cross-class sum supplies the lost direction despite zero within-class
rank. A second, Fraction-based elimination independently confirms the
three ranks on all eleven mandatory cases.

The complete 636-step distribution of (ℓ,t,η) is

    (0,0,0):138; (1,0,1):385; (1,1,0):56;
    (3,2,1):34; (5,4,1):13; (7,6,1):10.

Every step satisfies R168 exactly and recovers all parent HC differences.
These are finite evidence for E168, not a proof of its remaining inequality.
A naive attempt to recover an N00 cycle as a convex average of one object
from each new class is impossible: the balanced parent barycenter has
uv=xy=2/3, whereas an N00 cycle has both coordinates zero. Linear span
recovery can still hold, as it does in the sample. This rejected convex
shortcut is recorded in the attack and is not used in the proof.

## 3. Route (ii): bounded bidirectional dual exchanges fail universally

### 3.1 Mandatory finite tests

With the recorded face 0 as root, exchanges moving exactly one face each
way have rank 5 in the expanded cube, whose full HC rank is 7. Their
exchange graph has three components. On each of the ten nine-direction
children they have rank 10 instead of 13 and four components. They fail
in 14 of the 15 original census graphs as well. These are exact finite
counterexamples to that restricted rank-spanning proposal, not to arbitrary
bidirectional exchange or C4 exchange.

### 3.2 An infinite obstruction with a complete proof

**Proposition D168 (proved).** For every integer b≥1 and every integer
k≥b+2, let G=C_{2k} □ K2 in its standard prism embedding and root the
dual at one cap face. The span of HC differences whose rooted dual shores
S,T satisfy

    |S−T|≤b and |T−S|≤b

has dimension exactly 2k−1, whereas d(G)=2k+1. The corresponding exchange
graph consists of one clique on 2k cycles and two isolated cycles.
Thus no universal bound on both transfer sizes can yield all HC
directions, even for affine-full even prisms.

Proof. Put L=2k. The dual is the bipyramid with nonadjacent cap vertices
A,B and an L-cycle Z={z_0,…,z_{L−1}}, each joined to both caps. Fix A as
root. Its rooted two-tree shores are exactly

    Z−{z_j}                  (j=0,…,L−1),
    {B}∪{z_j:j even},    {B}∪{z_j:j odd}.                    (D-list)

To prove exhaustion, first suppose B∈S and put I=S∩Z. Acyclicity of
G*[S] forces I independent, since adjacent elements with B make a
triangle. Likewise Z−I must be independent in the other shore with A.
Thus I is one of the two alternating classes. Both shores are stars.
If B∉S, the complementary shore contains both caps and J=Z−S.
Connectivity requires J nonempty. Its induced edge count is
2|J|+|E(Z[J])|, and its vertex count is |J|+2. The tree equation is
|J|+|E(Z[J])|=1, forcing J to be a singleton. Then S is a path.
This proves D-list, and the dual correspondence gives precisely L+2 HCs.

The L ordinary HCs C_j use every top and bottom horizontal edge except
the jth in each layer, together with the two incident rungs. The two
remaining cycles X,Y use all rungs and complementary alternating
horizontal edges in the two layers. These L+2 vectors are affinely
independent. Indeed let Σ a_jχ(C_j)+xχ(X)+yχ(Y)=0 with
Σ a_j+x+y=0, and put s=Σ a_j. Subtracting the top and bottom coordinate
equations gives x=y. Each horizontal coordinate then gives a_j=s+x.
The affine equation gives s=−2x, so a_j=−x and s=−Lx. Since L≥4,
x=0; all coefficients vanish. Hence d(G)=L+1.

Any two ordinary shores differ by one vertex each way. An alternating
shore and an ordinary shore differ by (1,k−1) or (2,k), up to order;
the two alternating shores differ by (k,k). For b<k−1 only ordinary
pairs are permitted. Their vectors are an affinely independent subset
of size L, so their difference span has dimension L−1. The two other
cycles are isolated, proving all assertions. The prism is simple, cubic,
bipartite and planar; it is 3-connected since deleting at most two vertices
either leaves an intact layer connecting the surviving paths of the other,
or leaves one connected path in each layer and an intact rung between them.
No stipulated existence result is required for this proof.

Fresh DFS and complementary-perfect-matching enumeration independently
check D-list and all ranks for L=4,6,…,16 (orders 8–32), with a second
rational rank computation. This validates rather than replaces the proof.
The obstruction permits transfers with one small shore change and an
unbounded other change; such moves are **not** ruled out. Nor does it rule
out using non-Hamiltonian intermediate states or nonlocal algebraic combinations.
The chosen cap root is an explicit hypothesis, sufficient to refute a
root-uniform bounded-transfer assertion.

## 4. Route (iii): even typed-equation fullness fails

**Proposition M168 (proved by an exact finite counterexample).** There is
a simple planar brace retract of a cubic planar brace, with the two
inherited degree-four port partitions, whose typed Hamiltonian cycles do
not affinely fill the solution space of the degree and port equations.

Use I167's independently audited order-16 witness and deletion 02.
The retract edge list is

    (0,2),(0,5),(0,9),(0,15),(1,3),(1,5),(1,9),(2,7),(2,11),(2,14),
    (3,7),(3,11),(5,13),(7,12),(9,11),(12,13),(12,14),(13,15),(14,15).

The two port partitions are
{(0,5),(0,15)}|{(0,2),(0,9)} at 0 and
{(2,7),(2,14)}|{(0,2),(2,11)} at 2.
The 12 degree equations have rank 11. Appending one port equation at each
merged vertex increases rank to 13. Therefore the degree-and-port affine
space has dimension 19−13=6. The 8 typed cycles have dimension only 5;
the 14 unrestricted retract cycles have dimension 8.

An explicit extra constant weight is

    w(0,2)=1, w(0,5)=−1, w(1,3)=1, w(1,5)=−2,
    w(2,7)=−1, w(12,13)=1, all other w(e)=0.

All eight typed cycles have weight −1. Yet the vector z supported on
(0,2),(0,9),(2,11),(9,11) with respective values +1,−1,−1,+1 has zero vertex
degrees and zero port sums, while w·z=1. Thus w is not a linear combination
of degree and port constraints. This certifies the extra affine equation
without relying solely on a rank routine. The complete eight-cycle list,
weight, perturbation and rational row-reduction checks are retained in
`support-attempt-02.json`.

The witness's parent and retract are independently checked to be braces
by enumerating all perfect matchings and extending every disjoint edge
pair. Planarity of the retract follows from the explicit minor operation
on the certified plane parent. This refutes a natural proposed typed
fullness theorem; it does not refute the typed-port bijection or establish
that no more elaborate typed-state induction can succeed. Such an induction
must include further states/equations and pay their rank contributions.

## 5. Evidence, replay and limits

Authoritative code: `toolkit.py`, `audit.py`, `attack.py`, `support.py`.
Authoritative deterministic payloads: `audit-attempt-02.json`,
`attack-attempt-01.json`, `support-attempt-02.json`.
The earlier successful support payload and its original source version are
also retained; support version 2 adds explicit brace checks. All failed
attempt bytes and logs are retained. There were no search timeouts or
unrecorded mathematical test failures. The rejected convex-average,
one-face-each and typed-fullness proposals remain described exactly above.

`verify.py` first binds the final report, every owned source/code/payload
byte and all non-context external dependencies. It then installs a read-only
audit hook rejecting file writes, file mutations, network, subprocesses,
and compilation/execution outside the approved owned code and standard
library. It runs fresh diagnostics and requires byte-for-byte deterministic
payload equality. Guard probes test forbidden operations before diagnostics.
All diagnostics and replay run with `python3 -I -B`, using no third-party
packages and no network. Integer elimination is crosschecked by a separately
written Fraction elimination on the mandatory cases, typed witness and prisms.

The manifest excludes only its own bytes and the prevalidation/seal control
files; the seal binds the manifest and successful prevalidation receipt.
The seal is created once with exclusive creation after successful
`--prevalidate`; no resealing is allowed. Final runtime and three requested
hashes are returned separately so that the report need not be changed after
sealing. Runtime receipts and any replay-time context drift are emitted in
verifier JSON. Context-ledger drift seen before sealing is retained in
`context-drift-01.json`.

The shared `frontier/TEN-FINDINGS.md` and `frontier/iterations/README.md`
are bound in `external-bindings.json` but explicitly excluded as context-only
in `replay-policy.json`, since the parent edits them concurrently. No
mathematical dependency is exempted. Owned bytes remain immutable.

Literature search responses, queries, local-source receipts and limitations
are retained. Primary abstract pages concerning thin edges and induced-tree
reconfiguration were inspected; no usable cross-class rank theorem was
obtained. Search does not certify novelty. The actual pinned P4 corollary
was read, not inferred only from the catalogue. The catalogue shows one
family-180 manuscript. No other upstream theorem, I165 splice theorem,
or global generation theorem is needed to prove R168, D168 or the finite
M168 obstruction. The assumed implications from the wider program remain
context, not independently re-proved here.

Finite limits: 636 are labelled expansion steps, not distinct children.
The parent census has order at most 20 and children at most 24. No new
completeness claim for graph generation is made. The prism enumeration
stops at order 32, but D168 has a full proof for every stated k,b. An exact
finite witness suffices to refute typed fullness, whereas passing 636
exchange inequalities cannot establish the universal exchange theorem.
These elementary reductions and exclusions are not certified new-to-literature
results or a substantial-finding nomination.

## 6. Final claim status and recommended next action

**Proved:** all six I167 audit statements in their original mathematical
scope; R168 and E168 with their explicit quantifiers; the guaranteed two
local directions and at-most-one balanced bridge; D168's infinite
bounded-bidirectional-transfer obstruction; M168's finite refutation of
typed degree-and-port affine fullness. The original I166 aggregation,
the bounded dual-transfer spanning proposal, and the simple typed-fullness
proposal are refuted, with witnesses retained.

**Finite evidence only:** exchange and exact parent-direction recovery on
636 steps; the (ℓ,t,η) distribution; the census dual-move ranks; numerical
checks supporting the prism theorem and typed witness. These checks do
not turn the universal positive targets into theorems.

**Open:** for every admissible G→H, the inequality

    dim(L+U+span{b}) ≥ d(G),

or equivalently t+η≥d(G)−d_surv. In particular neither t≥ℓ−1 nor the
needed bridge independence in its equality case is proved in general.
C4 exchange, (T), and Q164 remain unproved and unrefuted here. No certified
counterexample to any of those three positive targets was found.

**Recommended next action:** construct lost N00 parent differences inside
L+U+span{b}, or prove its dimension bound directly, allowing nonlocal
bidirectional face transfers or additional typed states. Keep b and its
cross-class offsets explicit. First demand t=6 and η=1 on the ten recorded
nine-direction steps and η=1 on the expanded cube; any general method
requiring bounded transfers on both shores or typed-equation fullness
must be replaced in view of D168 and M168.
