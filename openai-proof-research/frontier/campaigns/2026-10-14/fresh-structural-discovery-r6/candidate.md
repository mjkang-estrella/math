# Hamiltonian affine span in Barnette graphs: unresolved round 6

Myeongjin Kang; no affiliation. 2026-10-16. Original prose CC BY 4.0;
original code MIT. Third-party reading copies retain their own rights.

**Disposition: UNRESOLVED.** The recorded full theorem H is neither proved
nor refuted. No substantial result is nominated, no campaign count is
changed, and no Lean or manuscript work is requested. The all-graph target
was not replaced by the prism or splice statements below. These are
technical supporting results, with complete proofs, and a precise remaining
step. Finite computations are the author's own checks, not independent
review and not a proof of the full theorem.

## 1. Original target and exact scope

A *Barnette graph* is a finite simple undirected cubic bipartite planar
3-vertex-connected graph. Write n=|V|, m=|E|=3n/2, let B be its unsigned
vertex-edge incidence matrix, and let H(G) be the set of 0-1 incidence
vectors of all its Hamiltonian cycles. The full target, recorded in
`original-scope.md` before the mathematical attempts, is

> **H.** For every Barnette graph G,
>
>     aff_R H(G) = A(G) := {x in R^E : Bx = 2 1}.

This concerns the entire set of cycles, every graph size, and all real
edge weightings. It asks for real affine span, not binary cycle-space span,
convex-hull equality, or a polynomial algorithm. For a connected bipartite
graph, rank_R B=n-1: a left-kernel vector satisfies a_u+a_v=0 on every
edge, and connectivity propagates one value on one color class and its
negative on the other. Thus dim A(G)=m-n+1=n/2+1. H would imply at least
n/2+2 different Hamiltonian cycles. This implication is part of the same
target and would not be a second campaign result.

An equivalent formulation is:

> If w in R^E has sum_(e in C) w_e independent of the Hamiltonian cycle C,
> then there are vertex potentials a_v with w_uv=a_u+a_v on every edge.

Indeed, H(G) is nonempty by the stipulated source. The annihilator of the
direction space of A(G) is row(B). Equality of the two affine spaces is
equivalent to equality of their annihilators; every row(B) weighting has
cycle cost 2 sum_v a_v. This is standard finite-dimensional linear algebra,
not the proposed discovery.

The bounded screen rejected exponential counting *before* target selection:
even prisms have only linearly many Hamiltonian cycles. The primary
Gibbons working note already treats the linear lower bound as a research
target. Accordingly, H was selected as a real gap requiring new work, not
as a routine consequence of Hamiltonicity. The screen found no exact
primary statement of H, but it is not a worldwide novelty certificate.

## 2. Strongest source interfaces actually read

The pinned input is OpenAI's *Paired states and Hamiltonian cycles in cubic
bipartite planar graphs*, at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The entire TeX body and bibliography
were read. The source proves:

* `thm:main`: Hamiltonicity for every Barnette graph.
* `thm:partition`: a partition of every properly black/white face-colored
  simple sphere triangulation into two induced trees, with any prescribed
  same-class edge on a specified facial triangle.
* `cor:edge-avoidance`: any single edge can be avoided.
* `cor:pfaffian-paths`: every three-edge path in every finite simple cubic
  3-connected bipartite Pfaffian graph is contained in a Hamiltonian cycle.

These are stronger premises than bare existence. The last corollary already
uses Gorsky--Steiner--Wiederrecht (GSW), Theorem 4.16; prescribed-path
Hamiltonicity itself is not new here. GSW Observations 4.10--4.11 also supply all six square traces; the finite
witness below respects this local consequence as well. The full source-tree search finds
one preprint directory for this family; it contains one mathematical TeX
body, rather than a separate counting or affine-span companion.

At proof-operation level the source supplies a finite weighted sum over
pairs of incidence states. For a fixed second state with a cyclic opposite
edge set, an involution reverses signs and cancels. Regrouping instead by
union cycles and choosing positive spoke circulations yields a nonzero
lowest coefficient. This proves existence of a forest state. Rooting a
dual tree recovers a perfect matching whose complementary dual is a
Hamiltonian cycle. None of these operations provides an affine basis of
cycle incidence vectors. Differentiating the partition function in an
incidence weight only counts weighted forest states; it does not identify
all edge-cost annihilators after the white-tree reconstruction. I did not
find a rank-preserving map from that derivative information to H(G).
This is an unpaid attempted route, not a theorem ruling out such a map.

GSW, arXiv:2202.11641v3, Section 4, gives the tight-cut splice mechanism and
the prescribed-path equivalences. Its Section 5, definition before Theorem
5.1 and that theorem, gives generation of all Barnette graphs from the cube
by cube expansions and C4 expansions. Their stated interface, including the
cofacial and odd-path restrictions, was read rather than inferred from an
abstract. Original HMM reduction diagrams were also inspected; the precise
extent and distinction between that inspection and GSW's generation
statement are in `source-contracts.md`.

Björklund--Kaski--Nederlof (BKN), arXiv:2308.01574v2, Section 3.4, proves
four cycles through an edge and at least six cycles in a Hamiltonian cubic
bipartite Pfaffian graph. The earlier ICALP version omits these proofs; the
full-version proofs were therefore retrieved and read. Their good-coloring
and matching switch mechanism in Sections 2--3 was examined at its used
interfaces. The resulting constant bound does not pay the growing affine
rank in H. No claim is made that their algorithms cannot be used in a new
rank argument.

## 3. A full proof for even prisms (technical support only)

Let P_m=C_m square K_2, with even m>=4. Name its top, bottom and rung edges
A_i=u_i u_(i+1), D_i=v_i v_(i+1), R_i=u_i v_i (indices modulo m).
There are the following m+2 Hamiltonian cycles:

* L_i uses every top and bottom edge except A_i,D_i, and the two rungs
  R_i,R_(i+1). Its two long ring paths join into one spanning cycle.
* Z_0 uses all rungs, the even A_i and odd D_i. Z_1 uses all rungs and the
  complementary ring edges. Each travels successively through the columns
  in cyclic order, so each is one spanning cycle.

**Proposition 1.** These m+2 vectors are affinely independent and span
A(P_m). Consequently H holds on all even prisms.

*Proof.* Give the three edge types weights a_i,b_i,r_i. Suppose all the
listed cycle costs equal K. Put S=sum_i(a_i+b_i), R=sum_i r_i. Summing the
costs of the L_i gives

    m K = (m-1) S + 2R.

Adding the two zigzag costs gives 2K=S+2R. Subtraction, with m>2, gives
S=2R and K=S. Each L_i equality now gives

    a_i+b_i = r_i+r_(i+1).                              (3.1)

Equality of the zigzag costs gives sum_i (-1)^i(a_i-b_i)=0. By (3.1) the
alternating sum of b is the negative of the alternating sum of a. Hence
sum_i(-1)^i a_i=0. The cyclic equations p_i+p_(i+1)=a_i are soluble:
choose p_0 arbitrarily and recurse p_(i+1)=a_i-p_i; for even m the terminal
condition is exactly the alternating-sum condition. Set q_i=r_i-p_i.
Then (3.1) gives q_i+q_(i+1)=b_i. Thus the weighting is the sum of its
endpoint potentials p on the top and q on the bottom.

The annihilator characterization from Section 1 now proves that the listed
vectors affinely span A(P_m), of dimension m+1. They number m+2, so they
are affinely independent. Every other Hamiltonian vector also lies in
A(P_m), proving the final assertion. ∎

The listed cycles and the exact prism count are classical elementary
material; the fresh Gibbons primary note supplies a complete count proof.
The proposition's real linear-algebra conclusion is proved here and is
not claimed substantial or new to the literature. No exact count theorem
is needed for its proof. The checker separately exhausts perfect matchings
and validates the counts for m=4,6,...,20.

## 4. Splice closure, with the entire affine statement retained

For two disjoint connected simple cubic bipartite graphs G_1,G_2, choose
vertices v_1,v_2 and a bijection between their three incident edges,
labelled 1,2,3. Delete v_1,v_2 and replace each matched pair of incident
edges by one edge joining their other endpoints. Call the result G.
Assume each G_i-v_i is connected. The color classes can be reversed in
one piece to make G bipartite. For planar pieces, matching the boundary
orders gives a planar splice; for three attachment points every bijection
is a rotation or reflection of an order.

**Lemma 2 (finite affine gluing).** Let S_i be finite sets partitioned into three nonempty
classes S_(i,1),S_(i,2),S_(i,3). Suppose an affine map pi_i on aff(S_i)
sends S_(i,s) to the s-th standard basis vector of R^3. Then

    aff { (x,y): x in S_(1,s), y in S_(2,s), some s }
      = { (x,y) in aff(S_1) x aff(S_2): pi_1(x)=pi_2(y) }.       (4.1)

*Proof.* Inclusion from left to right is immediate. For the reverse,
consider any affine functional F(x,y)=f_1(x)+f_2(y) vanishing on the left.
Fixing one variable in each nonempty class shows that f_i is constant on
that class; write the constants a_(i,s). They obey a_(1,s)+a_(2,s)=0.
The affine function g_i(z)=sum_s a_(i,s) z_s agrees with f_i on S_i after
composition with pi_i, hence on aff(S_i). On the right of (4.1), F is
therefore sum_s(a_(1,s)+a_(2,s)) z_s=0. Equality follows because a proper
affine subspace of a finite-dimensional affine space has a separating
affine functional. ∎

**Proposition 3 (splice closure).** Suppose H(G_i) affinely spans A(G_i)
for i=1,2, and for each s each G_i has a Hamiltonian cycle omitting its
s-th edge at v_i. Then H(G) affinely spans A(G).

*Proof.* A Hamiltonian cycle of G uses a positive even number of the three
joining edges, hence exactly two. It restricts to a spanning path in each
piece. Adding back v_i turns these paths into Hamiltonian cycles of G_i
with the same omitted edge s. Conversely any such pair splices to one
Hamiltonian cycle. This is exactly the ordinary splice correspondence,
with all compatible pairs retained.

On A(G_i) set pi_i(x)_s=1-x_(v_i,s). Since the three star coordinates sum
to 2, the three pi coordinates sum to 1; on a Hamiltonian vector pi is
its omitted-edge basis vector. Lemma 2 shows that the affine hull of all
compatible pairs is the fiber product of A(G_1),A(G_2) over pi.

That fiber product is affinely isomorphic to A(G). The map retains the
internal coordinates and uses the common star coordinates on the joining
edges. Its inverse is obtained by duplicating each joining coordinate at
the two removed stars. The only potentially additional equations are the
degree equations at v_i. They follow already from the equations in G:
in G_i the color classes have equal size by cubicity; after removal of
v_i, the piece has one fewer vertex of its color and all three boundary
vertices have the opposite color. Subtracting the degree sum on one color
from the sum on the other cancels all internal edges, and gives sum of the
three joining coordinates equal to 2. This argument is valid for arbitrary
real coordinates, without positivity. Thus the inverse satisfies both
removed-vertex equations, completing the affine identification. ∎

For Barnette graphs, all the omitted-edge classes are nonempty by the
pinned `cor:edge-avoidance`. The cube satisfies Proposition 1. Thus cube
expansions preserve H. Arbitrarily iterated planar splices of even prisms
also satisfy H, with no size bound. This is a supporting family theorem,
not a narrowed campaign nomination. The substantive global issue is the
other generator, C4 expansion. The glue is elementary affine bookkeeping
on top of the GSW/HMM splice, and is not assessed as a nonroutine advance.

## 5. The C4 step and a rigorous loss in the direct lifting route

Use GSW's exact C4 expansion notation. Choose cofacial edges uv,xy with
u,y in one color class, v,x in the other, all distinct, such that deleting
these edges from their facial cycle leaves two odd paths. Replace them
by the chains u-u'-v'-v and x-x'-y'-y, and add u'x',v'y'. The four new
vertices induce the square u'v'y'x'. Call the expanded graph G^+.

An original Hamiltonian cycle using uv or xy has a unique lift with the
following traces. If it uses both, lift through the two chains; if it
uses only uv, replace uv by the long square path

    u-u'-x'-y'-v'-v;

if it uses only xy, use the other long square path. All these are spanning
lifts with the old exterior edges unchanged. If the cycle uses neither,
its exterior already forms a closed spanning cycle on the old vertices;
keeping those exterior edges leaves each old vertex degree two and
precludes attachment of the four new vertices. It therefore has no such
lift. These facts follow directly from degree two and connectedness.
They are the classical local trace issue, not a new obstruction to H.

**Proposition 4 (arbitrarily large rank loss for this route).** In P_m,
choose the two rungs at columns 0 and 1, which meet the cofacial odd-path
conditions. Exactly five original Hamiltonian cycles have spanning lifts
of the above kind. Their lifts have affine dimension at most four,
whereas dim A(P_m^+)=m+3. Thus inheriting only these cycle lifts cannot
prove H for this expansion, with a deficit growing in m.

*Proof.* The exact prism count says every Hamiltonian cycle is one of the
m+2 cycles listed in Section 3. A short independent verification of the
needed classification is as follows. Let R_H be its rung set; it is
nonempty and even. If R_H is proper, any gap of length at least two
between consecutive chosen rungs forces the entire top and bottom path
across that gap into the cycle. At each chosen rung, both adjacent gaps
cannot have length at least two, since each rung endpoint can use just
one ring edge. If there is at least one such long gap, each of its two
chosen boundary rungs has its one ring edge already fixed toward that
gap; the two ring paths and the boundary rungs consequently form a closed
component. Hamiltonicity forces that component to be the whole graph,
so there are exactly two chosen rungs and the other gap is one edge:
the cycle is L_i. This argument also covers runs of consecutive chosen
rungs: any long gap would already close a component before those runs
could be attached. If all rungs are chosen, the ring edges must be
perfect matchings in the two m-cycles. Each cycle has precisely two
perfect matchings; choosing the same one makes disjoint four-cycles,
while complementary ones give Z_0,Z_1. This proves the classification.

The cycles using R_0 or R_1 are L_(m-1),L_0,L_1,Z_0,Z_1, five distinct
cycles even when m=4. Any five vectors have affine dimension at most four.
The expanded graph has 2m+4 vertices and is connected and bipartite, so
its degree affine space has dimension m+3. ∎

The general direct-lifting deficit is not a counterexample. For example,
the exact check at m=10 finds 26 Hamiltonian cycles after expansion and
full affine dimension 13; most needed directions arise outside the five
inherited lifts. No exact formula for all expanded sizes is claimed.
A successful induction needs information on exterior spanning path
covers or some other source of these directions. Neither Proposition 3
nor the original affine rank of P_m supplies that information.

## 6. Prescribed P4 witnesses can still have deficient affine rank

Here is a finite, exact limitation of using only the source's local
existence conclusions. It is not a counterexample graph to H.

Take G to be the splice of two cubes at vertex 0 with the three neighbors
matched in sorted order, using the deterministic relabelling in
`explore.py:join`. It is a 14-vertex Barnette graph. The matching cut has
three edges; simplicity, cubicity and bipartiteness are immediate. For 3-connectivity, delete at most two vertices. If at most one lies in
each fragment, both fragments remain connected, since the original pieces
are 3-connected; at least one of the three joining edges survives. If two
lie in one fragment, the other remains connected. Every component of the
damaged fragment has a surviving attachment: otherwise it would be a
component separated from the restored root in the original graph with
just those two vertices deleted. All its components therefore join the
intact fragment. The checker also checks every deletion set directly. Planarity follows by
placing the two cube-minus-vertex disks on opposite sides of their
three matched attachment points.

`local-witness.json` fixes the sorted list of its 21 edges, eight chosen
Hamiltonian vectors by the deterministic exhaustive ordering, and an
integer weighting w. Those eight cycles contain every three-edge path
of G, and they also avoid every single edge. They also realize all six permitted traces on every one of its six
squares, and each edge occurs in at least four of the eight witnesses.
Their affine rank over Q is exactly 6, while dim A(G)=8. The supplied weighting gives all eight
cost -2, but costs -1 and -3 also occur on other Hamiltonian cycles.
Thus w is not a vertex-potential weighting. All assertions are verified
by exact exhaustive enumeration, including a second Hamiltonian DFS,
and rational elimination in `checks.py`.

For review without trusting the ordering convention, the report also
stores the complete eight edge-index supports in `local-witness.json`.
Checking the 84 three-edge paths against these supports and reducing
their seven difference rows is a finite certificate. The exact nonzero
minor and all cost values are generated directly by rational elimination;
no floating-point tolerance or optimizer status enters.

This proves only that a *family of witnesses* satisfying every stated
P4 existence request need not span A(G). The actual complete family
H(G) does span it here, by Proposition 3 and by enumeration. Applying the
pinned theorem to further gadget graphs could conceivably force more;
that broader route is not refuted by this finite witness.

## 7. Exact unpaid step, full scope preserved

The following step would complete H via GSW Theorem 5.1 and Proposition 3:

> **U_C4.** For every Barnette graph G and every C4 expansion G^+ allowed
> by the exact cofacial odd-path definition, if aff H(G)=A(G), then
> aff H(G^+)=A(G^+).

This is unpaid. No proof or counterexample is supplied. Under the quoted
generation theorem and the proved cube base and cube-expansion closure,
U_C4 is equivalent to the full global target: one direction follows by
induction along a construction, and H itself implies the conditional
statement immediately. Consequently U_C4 is an exact remaining target,
not a reduction to a weaker subcase or an extra assumption in a claimed
full proof.

The work in Sections 3--6 was the actual proof attempt: annihilator
analysis closes the complete prism family; a fiber-product argument
closes all splices; a traced induction is then blocked by the unbounded
loss of the directly inherited cycles. The pinned weighted-cancellation
route was also examined, without a rank extraction. The finite P4 witness
rules out concluding the desired rank merely from a list of local
existence witnesses. No mechanism overcoming U_C4 was found.

## 8. Contribution, validation and provenance

No result here meets the requested full-scope substantial-theorem gate.
Proposition 1 is elementary cyclic linear algebra; Lemma 2 and Proposition
3 are standard affine gluing applied to the known splice; Proposition 4
is a classical trace problem with an explicit rank consequence. The
14-vertex witness is diagnostic finite evidence, not a frontier theorem.
None is promoted by renaming it, its quantifiers, or its consequences.

`checks.py` verifies the prism bases, the splice correspondence, the local
P4 certificate and cost obstruction, the lifting loss, and graph
hypotheses on the 160 seeded generated examples. It compares perfect-
matching enumeration with direct Hamiltonian DFS at the certificate
interfaces and includes deliberate wrong-rank, disconnected-factor,
wrong-cost and corrupted-witness controls. All ranks use exact fractions;
there is no numerical solver. The generated examples are probes with
possible isomorphic duplicates, not an isomorphism census or an exhaustive
all-size check. `exploration-receipt.txt` preserves the initial probe run;
it is separately replayed. No sampled check proves H.

`verify.py` first authenticates the caller-pinned seal, both manifest
files, every inventory entry and every pinned Git blob. Only then does
it execute the authenticated finite programs, without network or writes,
and compare stdout with the immutable receipts. It never regenerates
receipts or inventories. `mutation_tests.py` tests rejection on disposable
copies inside this owned directory. The external seal hash is the trust
anchor; hashes alone are not a signature or independent review.

All new files are within `fresh-structural-discovery-r6/`. Third-party
copies and rendered reading pages are private inputs, excluded from
releasable original files. No nested agent, shared edit, staging, commit,
external communication, upload or submission was performed. Earlier
vetoes remain in force; this report neither revisits those mathematical
lanes nor changes acceptance decisions.
