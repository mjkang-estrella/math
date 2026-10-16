# Hamiltonian affine span: focused second attempt, unresolved

Myeongjin Kang; no affiliation. 2026-10-16.
Original prose CC BY 4.0; original code MIT. Third-party reading copies retain
upstream rights and remain private.

**Disposition: UNRESOLVED.** No proof or counterexample to the full real
statement H was obtained. No result is nominated, counted, or independently
certified. The new material is an exact C4 rank decomposition and rigorous
obstructions to two attempted exchange identities. Neither is presented as
a solution, a smaller substitute target, or a substantial-theorem nomination.

## 1. Original full target and what was authenticated

For every finite simple undirected cubic bipartite planar
3-vertex-connected graph G, with unsigned vertex-edge incidence matrix B,

> H: aff_R {1_C : C is any Hamiltonian cycle of G}
>    = A(G) := {x in R^E : Bx=2*1}.

All graph sizes, all real weights and the complete Hamiltonian family are
retained. If n=|V|, then |E|=3n/2 and dim A(G)=n/2+1. Indeed the left kernel
of B consists exactly of vectors constant on one color class and the
negative constant on the other: along every edge a_u+a_v=0, and connectivity
propagates these values. Thus rank B=n-1. A(G) is nonempty (the all-2/3 vector
satisfies its equations). The pinned Hamiltonicity theorem makes the
Hamiltonian family nonempty too.

Equivalently, if a real edge weight w has constant sum on every Hamiltonian
cycle, H says w_uv=a_u+a_v for some real vertex potentials. This follows
by taking annihilators of the Hamiltonian difference space and ker B.
Every vertex-potential weighting has cycle cost 2 sum_v a_v.

The r6 seal authenticated to the parent-supplied SHA256
8cd0210428791a68f2e0a10b9447217996fb3a45967cc3b4203bca51ba647921.
All 40 input entries, 17 output entries and exact 61-file tree matched.
All five pinned OpenAI Git blobs were independently recomputed and matched
to the complete preprint tree. No r6 code was executed. The known conditional
write in generate_probe.py was therefore never reached; the frozen tree
was independently hashed before and after this round's final verification.
See source-contracts.md for exact reading extents, paths and primary URLs.

## 2. Exact allowed expansion and all six trace families

Let G have n vertices and let e=uv, f=xy be a GSW C4-expansion input:
u,y in one bipartition class, v,x in the other; all four endpoints distinct
on one facial cycle; deleting e,f from that cycle leaves two odd paths.
The expanded graph G+ adds u',v',x',y', deletes e,f, and adds

    uu', vv', xx', yy', u'v', x'y', u'x', v'y'.

This is precisely the definition preceding GSW Theorem 5.1. Its stated
closure keeps the required graph class. Put F=G-{e,f}; the old vertices
are retained. Write the new square cyclically as

    q0=u', q1=v', q2=y', q3=x',
    r_i=q_i q_(i+1), s_i=a_i q_i,
    (a0,a1,a2,a3)=(u,v,y,x),

with indices modulo four. F is connected: a simple cubic 3-vertex-connected
graph has no cut of at most two edges. To see this, each side of such a cut
has at least three vertices (a singleton has boundary three and two vertices
have boundary at least four); deleting its at most two boundary endpoints
on one side disconnects a nonempty remnant from the other side, a contradiction.
Thus deleting e,f cannot disconnect G.

Every Hamiltonian cycle in G+ has one of the following gadget traces:

- L_i, i=0,1,2,3: the three ring edges other than r_i, and spokes s_i,s_(i+1).
- P: ring edges r1,r3 and all four spokes.
- Q: ring edges r0,r2 and all four spokes.

For completeness, let t be the number of used spokes. Degree two at the
four square vertices gives 8=2*(number of ring edges)+t. The possible
values of t are 0,2,4. Zero would isolate the entire square as a closed
cycle, impossible because old vertices exist. With two spokes the three
ring edges form a spanning path; with four they form a perfect matching.
This exhausts all traces.

All six occur, from the exact pinned P4 corollary. The three-edge path in
the square omitting r_i forces L_i. To force the matching trace containing
r_i, prescribe the three-edge path a_i-q_i-q_(i+1)-a_(i+1). The adjacent
ring edges at its two square endpoints are excluded, forcing the opposite
ring edge and the other two spokes. This gives both P and Q. No printed
path-length typo in GSW Observation 4.11 is used.

Removing the gadget from such a cycle leaves a spanning path in F with
endpoints a_i,a_(i+1) in type L_i. In type P it leaves two spanning paths
pairing (a0,a1),(a2,a3); in type Q it leaves two paths pairing
(a0,a3),(a1,a2). There are no extra cycle components, because the original
cycle was connected. The third pairing of four boundary points crosses
and is impossible in the disk exterior of the square. The pairing must be
the one different from the internal matching, to obtain a single cycle.
Conversely every such spanning path cover completes to the corresponding
Hamiltonian cycle. Hence these are complete path-cover families, not
arbitrarily selected local witnesses.

## 3. The exact C4 rank decomposition

Let gamma_i be the eight gadget incidence coordinates (four ring, then
four spokes) in trace i. Explicitly, gamma_i for L_i has ring coordinates
1 except at i and spoke coordinates 1 exactly at i,i+1; gamma_P has ring
(0,1,0,1) and all spokes; gamma_Q has ring (1,0,1,0) and all spokes.

**Lemma 1.** Their affine rank is four, and their sole affine relation,
up to scalar, is

    gamma_0+gamma_2-gamma_1-gamma_3-gamma_P+gamma_Q=0.       (3.1)

*Proof.* The spoke vectors of L0,L1,L2,L3 form a parallelogram of affine
rank two, all with sum two. The all-spoke vector has sum four and adds a
third direction. The difference gamma_P-gamma_Q is nonzero on the ring
and zero on the spokes, adding a fourth direction. All eight-coordinate
vectors satisfy the four independent degree equations at the new vertices;
independence follows since each equation has its own spoke coordinate.
Their affine rank is therefore at most four. Direct coordinate addition
gives (3.1), whose coefficient sum is zero. With six points and affine
rank four, the space of affine relations has dimension one. ∎

For each trace i, let S_i be its complete set of exterior edge vectors on
F, and choose any representative z_i in S_i. Define

    W = sum_i span_R {z-z_i : z in S_i},
    d = z_0+z_2-z_1-z_3-z_P+z_Q.                         (3.2)

Changing representatives changes d only by a vector in W.

**Lemma 2 (exact rank formula).**

    dim aff_R HC(G+) = 4 + dim_R(W+R d).                 (3.3)

Moreover W+R d is a subspace of ker B_F, of dimension at most n/2-1.
Consequently H on this expanded graph is equivalent to

    W+R d = ker B_F.                                    (3.4)

*Proof.* Let D be the Hamiltonian difference space and project it onto
the gadget coordinates. Since all six trace families are nonempty, the
image has dimension four by Lemma 1. Within-trace differences lie in the
kernel and have exterior coordinates generating W.

Consider any vector in the projection kernel. Express it as a linear
combination of full Hamiltonian vectors with coefficient sum zero. Group
coefficients by trace, writing their six sums as b_i. Subtract the
within-trace differences to replace every cycle of type i by its chosen
representative (z_i,gamma_i). The remaining coefficients satisfy
sum b_i=0 and sum b_i gamma_i=0. Lemma 1 says b is a scalar multiple of
(1,-1,1,-1,-1,1). Thus the remaining exterior vector is a multiple of d.
Conversely d, with zero gadget coordinates, is that linear combination
of actual Hamiltonian vectors and belongs to D. This identifies the
projection kernel exactly with W+R d, proving (3.3).

Every full Hamiltonian difference satisfies degree zero. If its gadget
coordinates vanish, its old-vertex equations say B_F z=0, proving the
inclusion. F is connected and bipartite, so rank B_F=n-1 by Section 1.
Since |E(F)|=3n/2-2, dim ker B_F=n/2-1. The expanded graph has n+4 vertices
and degree affine dimension n/2+3=4+(n/2-1). Equality of dimensions inside
A(G+) now proves the final equivalence. ∎

This pays the local gadget rank exactly. It does not pay (3.4). In
particular, source-guaranteed nonempty families pay four dimensions;
the remaining n/2-1 directions require their full exterior variation.
Even W=ker B_F is too strong as a universal replacement: the expanded
cube diagnostic below has dim W=2, dim ker B_F=3, and d adds the missing
direction. Conversely full H forces codim(W in ker B_F) at most one.
No argument proving that necessary bound for every exterior was obtained.

The inherited cycles from G occupy only types L0,L2,Q. Cycles avoiding
both e and f do not lift with their old exterior fixed. Original H alone
therefore does not directly identify W or d. The adjacent-rung prism
deficit in the authenticated r6 report remains valid and unpaid.

## 4. An integer exchange route is impossible for structural reasons

An original Hamiltonian cycle C avoiding e,f is a Hamiltonian cycle of
F. In G+ its union with the new square is a disconnected spanning
2-factor D0 with two components. On gadget coordinates,

    1_square = gamma_0+gamma_2-gamma_P
             = gamma_1+gamma_3-gamma_Q.                 (4.1)

One attempted way to recover missing cycles was to choose actual
Hamiltonian cycles of those types so that the same identity holds on
exterior coordinates, for example

    1_D0 = 1_HL0 + 1_HL2 - 1_HP.                        (4.2)

The following proves that this route cannot work, independently of
finite probing.

**Lemma 3 (Pfaffian parity obstruction).** In a bipartite Pfaffian graph
on N vertices, the incidence vector of a spanning 2-factor with an even
number of components is not an integer affine combination of Hamiltonian
cycle vectors. Any rational affine certificate for it has an even common
denominator.

*Proof.* Fix a Pfaffian orientation. Put epsilon_e=1 when e is directed
from the second bipartition class to the first, and zero otherwise.
For a conformal cycle of length 2k, take an alternating traversal. If b
is the number of its edges oriented from the second class to the first,
the number aligned with the traversal has parity k+b: among its k steps
from the first class to the second, a backward orientation subtracts one,
and among the other k steps it adds one. The Pfaffian condition makes
that aligned number odd. Therefore

    sum_(e in cycle) epsilon_e = k-1  (mod 2).

Each component of a spanning 2-factor is conformal, since the remaining
even cycle components have perfect matchings. Summing gives

    epsilon . 1_D = N/2-c(D)  (mod 2),                 (4.3)

where c(D) is its component count. All Hamiltonian vectors have parity
N/2-1. Integer affine coefficients summing to one preserve that parity,
whereas even c(D) gives the opposite value. For rational coefficients
with odd common denominator a, multiply the proposed identity by a.
Their integer coefficient sum is a, and reducing modulo two produces
the same contradiction. ∎

Planar graphs are Pfaffian by GSW Theorem 4.6, so the lemma applies here.
In particular (4.2) is impossible. This is an integral exchange
obstruction, not a real linear functional constant on all Hamiltonian
cycles. It neither refutes H nor changes its coefficient field.

## 5. The first half-integral repair also fails, exactly

The gadget identity suggested a six-trace repair

    D0=(H_L0+H_L1+H_L2+H_L3-H_P-H_Q)/2.                 (5.1)

It already fails for an allowed expansion of the cube, and in fact that
D0 has no half-integral affine representation at all.

Start with the usual cube P4 with vertices 0,1,2,3 on one ring and
4,5,6,7 on the other. Expand rungs 0-4 and 1-5 on the facial square
0,1,5,4; the retained facial paths 0-1 and 5-4 each have length one.
The ordered edge list of the result is

    0:01  1:03  2:0,11  3:12  4:18  5:23  6:26  7:37  8:45
    9:47  10:4,10  11:56  12:59  13:67  14:89  15:8,11
    16:9,10  17:10,11.

Commas disambiguate two-digit vertices. This graph is the six-prism:
its corresponding cyclic rings are

    (1,2,6,5,9,8), (0,3,7,4,10,11).

Thus its complete Hamiltonian family consists of eight cycles, by the
prism classification proved in Section 6. In trace order L0,L1,L2,L3,P,
then the three Q cycles, their edge-index supports are

    H0 = 0 1 4 5 6 8 9 12 13 15 16 17
    H1 = 0 1 3 6 7 9 10 11 12 14 15 17
    H2 = 0 2 3 5 7 8 10 11 13 14 15 16
    H3 = 1 2 3 4 6 7 8 9 11 14 16 17
    HP = 1 2 3 4 6 7 9 10 11 12 15 16
    Q0 = 1 2 3 4 6 7 8 10 12 13 14 17
    Q1 = 1 2 3 4 5 9 10 11 12 13 14 17
    Q2 = 0 2 4 5 6 7 9 10 11 12 14 17.

The two-component factor D0 has support

    0 1 3 6 7 8 9 11 14 15 16 17.

The augmented incidence matrix with a leading all-one column has an
8-by-8 minor of determinant -4, at augmented column indices
0,1,2,4,6,9,10,15 (column j+1 corresponds to edge j). Hence the eight
vectors are affinely independent. Direct coordinate addition gives

    D0=(H0+3H1+H2+3H3-HP-Q0-Q1-Q2)/4.                  (5.2)

The coefficient sum is one. Uniqueness follows from independence, so
no alternative half-integral certificate exists. This includes every
possible choice in (5.1), which would have coefficients in (1/2)Z.
The graph satisfies H: eight independent cycle vectors span its
seven-dimensional degree affine space. This is expressly not a
counterexample to the real target. It rejects an attempted bridge to H.

The immutable square-diagnostic.json stores all graph, trace, support,
minor and coefficient data. The checker independently matches two
complete enumerations: perfect-matching complements and Hamiltonian
DFS. It also verifies the prism isomorphism, the exact minor and (5.2).

## 6. Why denominators cannot be repaired by a fixed universal bound

Here is a supporting calculation over a family already paid in r6, not
a replacement goal. In the even prism P_m, let A_i,D_i be the two ring
edges at column gap i and R_i the rungs. The complete Hamiltonian family
has cycles L_i using both rings except A_i,D_i and rungs R_i,R_(i+1),
and two zigzags Z0,Z1 using all rungs and complementary alternating
ring matchings.

To check completeness, the chosen rungs in any Hamiltonian cycle are
nonempty and even in number. If not all rungs are chosen, there is a gap
of at least two steps between consecutive chosen columns. The top and
bottom paths across it are forced, as are its two boundary rungs. They
already form a closed component. Hamiltonicity forces it to contain every
column, so the other gap is one step and there are exactly two rungs:
this is L_i. If all rungs are chosen, each ring contributes one of its
two alternating perfect matchings. Equal choices give disjoint squares;
complementary choices give Z0,Z1. This also verifies that the listed
cycles themselves are Hamiltonian.

They form an affine basis. Here is the weight proof, included to avoid
silently assuming the r6 supporting lemma. Let a_i,b_i,r_i be edge costs
and let all listed cycle costs equal K. Set S=sum(a_i+b_i), R=sum r_i.
Summing the L_i costs and the two zigzag costs gives

    mK=(m-1)S+2R,  2K=S+2R.

Since m>2, subtraction yields S=2R and K=S. Individual L_i equations
then give a_i+b_i=r_i+r_(i+1). Equality of zigzag costs says the alternating
sum of a_i-b_i is zero. The alternating sum of a_i+b_i is also zero by
the preceding equations, so the alternating sum of a_i is zero. Therefore
p_i+p_(i+1)=a_i has a cyclic solution for even m, by recursion
p_(i+1)=a_i-p_i. Put q_i=r_i-p_i; then q_i+q_(i+1)=b_i. These are vertex
potentials, proving affine span by Section 1. There are m+2 listed cycles
and dimension m+1, so they are independent.

Let D_ring be the disconnected factor of the two rings. Coordinatewise,

    D_ring=(sum_i L_i-Z0-Z1)/(m-2).                     (6.1)

Each ring edge has numerator (m-1)-1=m-2, and every rung has numerator
2-2=0. Coefficients sum to one, and the affine basis makes them unique.
In particular their common denominator must be divisible by m-2. As
even m grows, no fixed denominator represents every such integral degree
two vector by affine combinations of the complete Hamiltonian family.
This does not exclude real rank proofs or iterated local rational
identities, whose denominators could grow under composition.

## 7. Routes examined and exact remaining work

**Alternate reduction.** Removing the new square and joining a0-a3,
a1-a2 yields the other natural reduction. It is not always a simple
3-connected graph: adjacent-rung prism inputs create parallel edges to
the retained ring edges. Thus induction on all smaller graphs in H's
class cannot be applied to this reduction without a separate argument.
No theorem about a larger class is substituted for H.

**BKN good-half-color fibers.** Its Lemmas 14–15 identify all anchored
Hamiltonian cycles extending a fixed half-coloring with projections of
perfect matchings of its auxiliary F_lambda. Lemma 16 supplies a switch.
These operations were read at the exact construction/proof interface.
They ensure extra Hamiltonian cycles inside a fiber, but the source does
not state that the union of fiber difference spaces gives ker B in the
original graph. I did not find a way to use them to prove (3.4). Applying
ordinary matching span to an auxiliary fiber without comparing all
fibers would leave precisely that unpaid transfer.

**Condensation/exchange.** The three-cycle reconstruction of a disconnected
square factor is universally impossible by Lemma 3. The most immediate
half-integral replacement is false already on the cube expansion, by
(5.2). General real identities remain possible; these obstructions do
not refute all source-gadget arguments.

**Source local witnesses.** All six traces and all prescribed P4 paths are
valid source consequences. The prior 14-vertex rank-deficient selected
witness family is not a graph counterexample, and is not treated as one.
This round uses complete families in its formula, so it does not repeat
the invalid inference from the existence of selected witnesses to rank.

The precise unpaid assertion in the focused route is (3.4) for EVERY
allowed GSW expansion, under the hypothesis H(G), or an argument that
proves the same identity throughout a construction from the cube. No
bound on the size of G is allowed. The existing cube base and splice/cube
closure, combined with GSW Theorem 5.1, would then prove H. This round
has not supplied that implication, nor an alternative global proof,
nor any Barnette graph violating (3.4). H and U_C4 remain unresolved.

## 8. Verification, contribution and rights

checks.py uses exact rational elimination, an exact finite GF(2) solve
for all 64 conformal-cycle equations of the diagnostic graph, independent
Hamiltonian DFS, and all 20 of its spanning 2-factors. It verifies the
four-dimensional gadget rank, the formula's concrete kernel ranks 2 and
3, the eight-vector basis and quarter certificate, both failed exchanges,
and prism bases/denominator identities for m=4,6,...,16. Wrong-sign,
wrong-coefficient and disconnected-factor negative controls are included.
Its stdout is frozen in checks-receipt.txt.

exchange_probe.py verifies the rank formula and full rank in 36 constructed
expansions (five prism instances, 31 seeded expansions, possible duplicates),
up to 28 vertices. It also checks degree, bipartition, every deletion of
at most two vertices, and the retained facial incidence data. Those probes
support only finite diagnostics. They are neither an isomorphism census
nor a proof of the all-graph kernel identity. A full exact new graph
counterexample was not found. No floating-point optimization was used.

The rank formula is elementary affine-fiber bookkeeping. The parity
obstruction follows directly from the standard Pfaffian orientation
condition. The prism calculation uses an elementary established family.
These are technical progress, not substantial frontier results. No
independent proof or contribution PASS is claimed. The bounded literature
screen found no exact duplicate of H but is not a novelty certificate.
No Lean or manuscript packaging was attempted.

inputs-manifest.json and outputs-manifest.json bind SHA256 and byte size
of every retained file. seal.json binds both manifests; seal.sha256 is its
detached trust anchor. verify.py authenticates the caller-supplied anchor,
manifests, exact inventory, source pins and frozen r6 chain BEFORE executing
any local checker. It then replays only this round's two read-only programs
with bytecode disabled, compares immutable receipts, and independently
hashes both trees afterward, including on checker failure. It regenerates
no receipt, fixture, inventory or source. Hashes supply integrity under a
trusted external anchor, not a signature or independent mathematical review.

All writes were within this assigned directory. No nested agent, shared
edit, staging, commit, publication, external message, upload, or campaign
count change occurred. Parent integrates. Original prose is CC BY 4.0,
original code MIT, author Myeongjin Kang, no affiliation. Third-party inputs
remain private and are not relicensed.
