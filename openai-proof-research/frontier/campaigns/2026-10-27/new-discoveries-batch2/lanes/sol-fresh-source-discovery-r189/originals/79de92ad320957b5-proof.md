# Author proof — fresh-structural-discovery-r135

Provenance: Factory Droid / claude-opus-5-5 / high, 2026-10-20. Scope: exactly the frozen statement
`packet/public/frozen-statement.md` (SHA-256 1000a115e013b3bc28247fdc03f33b8d4ae3ee8ee2a41ce4da55c79e1081a99d),
frozen before proof drafting. The pinned source (openai/math commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, preprint
`preprints/The-crossing-number-of-complete-bipartite-graphs-September-23-2026`) is stipulated true
and is not audited; its theorem is quoted only for the closing identification with the ordinary
crossing number. Everything else below is proved here.

## 0. Statement, notation, and the role of each section

Conventions and the quantities `d_r`, `chi(e,f)`, *even-adjacent*, `oc(D)` are as in the frozen
statement. We prove:

**Theorem.** For all positive integers m, n:
(1) every even-adjacent drawing D of K_{m,n} satisfies oc(D) >= d_m d_n;
(2) there is a drawing of K_{m,n} with no adjacent crossings, every pair of edges crossing at most
    once, and exactly d_m d_n crossing pairs.

Section plan. Section 1 normalizes a drawing without changing any crossing parity. Section 2 proves
the parity chord lemma. Section 3 defines the parity intersection matrix J_2 and proves the cycle
pairing z^T J_2 y = 0 over GF(2). Section 4 derives the additive block relation. Sections 5 and 6
prove the subspace intersection bound and the rank-sum corollary over infinite fields of
characteristic 2. Section 7 builds the rank detector in characteristic 2. Section 8 assembles the
lower bound for odd n. Section 9 extends to even n by vertex deletion. Section 10 gives the axis
drawing. Section 11 derives the corollaries and states limitations. Section 12 lists the mechanical
sanity checks (performed by `sanity.py`).

Global notation. K_{m,n} has first class {a_1..a_m} and second class {b_1..b_n}; edge a_i b_p is
written ip and is oriented from a_i to b_p (the orientation is used only to define a consistent
one-sided shift in Section 3; all matrix entries are orientation-free). GF(2) is the two-element
field; F is an arbitrary fixed infinite field of characteristic 2 (for instance the rational
function field GF(2)(t)); ranks, determinants, and dimensions in Sections 5–8 are over F unless
stated otherwise. For n = 2s+1 we put d = s^2 = d_n.

## 1. Parity-preserving normalization

**Lemma 1 (normalization).** Let D be a drawing of a finite graph G (frozen-statement conventions).
Then there is a drawing D' of G with the same vertex positions such that every edge is polygonal,
each edge is straight in some neighborhood of every vertex and of every crossing point, and
chi'(e, f) = chi(e, f) for every pair of edges e, f. In particular D' is even-adjacent if D is.

*Proof.* A proper crossing of two edges is a transverse double point: some open disk around it meets
the two edges in two properly embedded arcs crossing once. Crossings are finitely many and vertices
are finitely many, so we may choose pairwise disjoint closed disks around all vertices and all
crossings such that each vertex disk meets the drawing only in radially ordered proper arcs from the
center to the boundary (shrink the disk until this holds, using that edges are simple arcs meeting
the vertex only at the endpoint), each crossing disk meets the drawing in exactly the two crossing
arcs, and no arc re-enters a disk after leaving it (shrinking again).

In each crossing disk, replace the two arcs by the two straight chords joining their boundary
points. The chords cross exactly once, transversely; the replacement disk is disjoint from all other
edge pieces, so no other crossing parity is affected.

In each vertex disk, the incident edges appear as disjoint arcs from the center to distinct boundary
points. Replace each by the straight radial segment to the same boundary point. Straight radial
segments from one center meet only at the center, so no crossings are created or destroyed inside
the disk.

Outside all disks, each edge is a compact arc disjoint from all vertices, and any two edges are
either disjoint or meet in finitely many crossing disks only. For two edges e, f whose outside-disk
pieces are disjoint, compactness gives a positive minimum distance between those pieces. Approximate
each outside piece by a polygonal arc with the same endpoints, inscribed in a tube of radius smaller
than half the least such positive distance over all edge pairs, and smaller than the distance from
every outside piece to every vertex and to the interior of any disk boundary approach. Choose the
polygonal vertices generically (avoid finitely many forbidden coincidences) so that no three
polygonal pieces meet and no two share a segment. Crossings of the approximations with other pieces
can then occur only inside crossing disks, where the pieces were left unchanged. Hence every pair
of edges keeps its crossing number exactly, in particular its parity. Finally, within each crossing
disk and vertex disk the edges are already straight; the polygonal pieces join the disk boundary
points, giving straight neighborhoods of every vertex and crossing as required. ∎

*Remark.* We do not remove adjacent crossings (an even-adjacent drawing may have adjacent edges
crossing twice); only parities matter below.

## 2. The parity chord lemma

Fix an oriented circle and a gap (a boundary point used as cut). For distinct boundary points u, w
write t(u, w) = 1 if u precedes w in counterclockwise order starting just after the gap, and
t(u, w) = 0 otherwise.

**Lemma 2 (chord parity).** Let C, E be simple arcs properly embedded in a closed disk, with four
distinct boundary endpoints, meeting transversely in their interiors. Write the endpoints of C as
u_1, u_2 and those of E as w_1, w_2. Then

    |C ∩ E| ≡ t(u_1, w_1) + t(u_1, w_2) + t(u_2, w_1) + t(u_2, w_2)   (mod 2),

and the right-hand side is independent of the gap (among gaps distinct from the endpoints).

*Proof.* C separates the disk into two regions, and the endpoints of E alternate with those of C on
the boundary circle if and only if w_1, w_2 lie in different regions. Traversing E, each transverse
crossing of C changes the region, so |C ∩ E| is odd exactly in the alternating case. For the
right-hand side: moving the gap past one endpoint u_i changes both terms t(u_i, w_j) (j = 1, 2), a
change of 2 ≡ 0 (mod 2); likewise for moving past a w_j; so the sum is gap-independent. Now place
the gap just before u_1 in the counterclockwise order, so t(u_1, ·) = 0 and the sum is
t(u_2, w_1) + t(u_2, w_2). This equals 1 exactly when exactly one of w_1, w_2 precedes u_2, i.e.
exactly when the endpoints alternate (checking the two alternating orders u_1 w_1 u_2 w_2 and
u_1 w_2 u_2 w_1 against the two non-alternating orders u_1 u_2 w_1 w_2 and u_1 w_1 w_2 u_2 gives
values 1, 1, 0, 0 respectively). ∎

## 3. The parity intersection matrix and the cycle pairing

Let D be a normalized (Lemma 1) drawing of K_{m,n}; we do **not** assume D even-adjacent in this
section. At each vertex v, choose a gap between consecutive incident spokes and define t̃_v(e, f)
for distinct edges e, f incident with v as in Section 2 (t̃_v(e, f) = 1 if the spoke of e precedes
the spoke of f counterclockwise from the gap).

Define a matrix J_2 indexed by the edge set E of K_{m,n}, with entries in GF(2): for distinct edges
e, f,

    J_2(e, f) = chi(e, f) + sum over common endpoints v of e and f of t̃_v(e, f),

where chi(e, f) is the crossing parity of e and f. (In K_{m,n} two distinct edges have at most one
common endpoint, so the sum has at most one term; the formula is written so that the proof below
needs no such restriction.) The diagonal entries J_2(e, e) are defined during the proof below; their
values are irrelevant in later sections, because Section 7's map Phi annihilates diagonal matrices
and Section 4 only ever evaluates off-diagonal block entries.

**Lemma 3 (cycle pairing).** Let z, y in GF(2)^E be the indicator vectors of two simple cycles of
K_{m,n}. Then z^T J_2 y = 0.

*Proof.* *Step 1: two closed walks.* Choose pairwise disjoint small round disks at the vertices,
meeting the drawing only in its straight spokes, with every crossing outside all disks. Build a
closed polygonal walk gamma from z: keep the edge tracks of edges of z outside the vertex disks,
and inside each disk used by z (a simple cycle uses exactly two distinct spokes at each of its
vertices) join the two boundary points by a chord inside the disk. Build a closed polygonal walk eta
from y by shifting the edge tracks of edges of y a small distance to the left of the fixed edge
orientation a_i -> b_p, as follows. Place further pairwise disjoint small disks at all crossings and
at all polygonal bends, each meeting only the straight pieces incident with its center. Outside all
disks, shift each straight stretch parallel to itself to the left. In a crossing disk, continue
along the shifted straight line: it avoids its own original line and meets the other original line
once, transversely. In a bend disk, the incoming boundary point moves clockwise and the outgoing one
counterclockwise (for the left shift), so both displaced points lie in the boundary sector on the
left of the oriented bend, and can be joined by a polygonal arc inside that sector, avoiding the
original bent arc. In a vertex disk, join the two shifted boundary points by a chord. All truncated
straight stretches are compact and pairwise disjoint, so for a sufficiently small shift no new
intersections are introduced, the shifted tracks avoid their unshifted originals, the boundary order
of shifted versus unshifted points at every spoke is stable, and gamma, eta meet transversely (make
the chords generic two-segment polygonal arcs to avoid collinear overlaps). Note eta may
self-intersect; this is harmless.

*Step 2: the total intersection is even.* Two closed polygonal walks in the plane meeting
transversely intersect in an even number of points: cone each oriented segment [u, w] of gamma from
a point o chosen outside the finitely many lines that would make a cone triangle degenerate, pass
through a corner of eta, or meet eta non-transversely; each cone-triangle boundary meets the closed
walk eta in an even number of points (entrances pair with exits); summing over the triangles, the
cone-segment intersections cancel in pairs, leaving |gamma ∩ eta| ≡ 0 (mod 2). Self-intersections
of either walk are irrelevant to this count.

*Step 3: exterior contributions.* Outside the vertex disks, gamma uses unshifted tracks of edges of
z and eta uses shifted tracks of edges of y. If e is in z, f is in y, and e ≠ f, then near each
crossing of e and f the unshifted e-track meets the shifted f-track exactly once, and there are no
other e/f meetings; so the contribution of the pair (e, f) is chi(e, f). If an edge s lies in both
cycles, its unshifted and shifted tracks are disjoint, contributing 0. If e is in z but f is not in
y (or vice versa), the pair contributes 0. Hence the exterior total is

    sum over distinct e, f of z_e y_f chi(e, f)   (mod 2).

*Step 4: vertex-disk contributions.* Consider a vertex disk used by both cycles, with z using
spokes e_1, e_2 and y using spokes f_1, f_2 (each pair distinct). Inside the disk, gamma is a chord
with endpoints P_1, P_2 on spokes e_1, e_2 and eta is a chord with endpoints Q_1, Q_2 on the shifted
spokes f_1', f_2'; all four boundary points are distinct. By Lemma 2 the chords cross with parity

    sum_{i,j} t(P_i, Q_j).

For e_i ≠ f_j the shifted endpoint on f_j' is so close to the spoke of f_j that
t(P_i, Q_j) = t̃_v(e_i, f_j). For a shared spoke e_i = f_j = s, the value t(P_i, Q_j) is a fixed bit
delta_{v,s} in GF(2), determined by the spoke, the vertex, and the (fixed, one-sided) shift
convention; in particular it does not depend on z or y. Since a simple cycle uses each spoke at v at
most once, the disk contributes

    sum over distinct e, f at v of z_e y_f t̃_v(e, f)  +  sum over spokes s at v of z_s y_s delta_{v,s}.

*Step 5: assembly.* Define J_2(s, s) = sum over endpoints v of s of delta_{v,s}. Adding Steps 3 and
4 over all vertex disks and using Step 2 gives

    0 = sum over distinct e, f of z_e y_f J_2(e, f) + sum over s of z_s y_s J_2(s, s)
      = z^T J_2 y.   ∎

*Remark (what replaced the classical averaging).* The real-signed version of this argument shifts
the second cycle both left and right and averages, which makes the shared-spoke terms cancel and
produces half-integer vertex terms. Division by 2 is unavailable over GF(2); the single-sided shift
plus the exact diagonal bookkeeping in Step 4 is the replacement, and the diode-type diagonal
entries are later annihilated by Phi, so their precise values never matter.

## 4. The additive block relation

Let L be the GF(2)-space of n x n matrices H with H(p, q) = r_p + c_q for some vectors r, c.
Write J_2^{ik} for the n x n block J_2^{ik}(p, q) = J_2(ip, kq).

**Lemma 4 (additive block relation).** For all 1 <= i, k <= m,
    J_2^{ik} + J_2^{i1} + J_2^{1k} + J_2^{11} ∈ L.

*Proof.* Write H for the left-hand side. We claim all rectangular differences of H vanish:
    H(p, q) + H(p, q') + H(p', q) + H(p', q') = 0.
If i = 1 or k = 1 then H = 0 identically (over GF(2), J_2^{1k} + J_2^{11} + J_2^{1k} + J_2^{11} = 0,
and similarly for i = 1). If p = p' or q = q' the displayed sum is 0 trivially. Otherwise i ≠ 1,
k ≠ 1, p ≠ p', q ≠ q', and the four-tuples a_i b_p a_1 b_{p'} a_i and a_k b_q a_1 b_{q'} a_k are
simple 4-cycles. Let z, y in GF(2)^E be their indicator vectors. Expanding Lemma 3,

    0 = z^T J_2 y = sum over e in z, f in y of J_2(e, f).

Each of the sixteen summands J_2(e, f) is an entry of one of the four blocks J_2^{ik}, J_2^{i1},
J_2^{1k}, J_2^{11} (the a-endpoint of an edge of z is a_i or a_1; that of an edge of y is a_k or
a_1), and collecting terms shows the sum equals exactly
H(p, q) + H(p, q') + H(p', q) + H(p', q'): for instance the terms J_2(ip, kq), J_2(ip, 1q),
J_2(1p, kq), J_2(1p, 1q) are the (p, q) entries of the four blocks, and the primed variants give
the other three corners. This assembly is term-by-term valid also when the two cycles share edges
or vertices (e.g. p = q puts the shared edge 1p into both cycles, contributing the diagonal entry
J_2(1p, 1p), which is simultaneously the (p, p) corner term of the expansion); Lemma 3 covers all
these cases.

Now fix p_0 = q_0 = 1. Vanishing rectangles give, for all p, q (the cases p = 1 or q = 1 being
immediate),

    H(p, q) = H(p, q_0) + H(p_0, q) + H(p_0, q_0),

so H(p, q) = r_p + c_q with r_p = H(p, q_0) + H(p_0, q_0) and c_q = H(p_0, q). ∎

## 5. The subspace intersection bound in characteristic 2

**Lemma 5 (subspace intersection bound).** Let W be a vector space of dimension N over the
infinite characteristic-2 field F, and let U_1, ..., U_m, V_1, ..., V_m be subspaces of W, m >= 1.
If U_i ∩ V_i = {0} for every i, then

    sum_{i,j=1}^m dim(U_i ∩ V_j) <= floor(m^2/4) * N.

*Proof.* The proof is a characteristic-free interpolation argument; we write it in full because the
classical presentation assumes the reals, and we must confirm that no step uses the characteristic.
Choose distinct t_1, ..., t_m in F (possible because F is infinite). For a subspace Z of W and an
integer h >= 0 put

    P_h(Z) = { P in Z[xi] : deg P <= h, P(t_i) in U_i for all i },   P_{-1}(Z) = {0},

write E_h(Z; t) = { P(t) : P in P_h(Z) }, and put k_h(Z) = dim P_h(Z) − dim P_{h-1}(Z),
k_{-1}(Z) = 0.

*Evaluation away from the nodes.* For t not among the nodes, the kernel of the evaluation
P_h(Z) -> Z, P -> P(t), is exactly (xi − t) P_{h-1}(Z): division by xi − t preserves the coefficient
space Z and, since t_i − t ≠ 0, preserves the constraint P(t_i) in U_i; the reverse inclusion is
multiplication. (Polynomial division with remainder by a monic linear factor works over any field.)
Hence

    dim E_h(Z; t) = k_h(Z)   for t outside the nodes.    (5.1)

Evaluation at all m nodes maps P_{m-1}(Z) isomorphically onto the direct sum of U_i ∩ Z: the map
sending (z_1, ..., z_m) to sum_i L_i(xi) z_i with L_i(xi) = prod_{k ≠ i} (xi − t_k)/(t_i − t_k) is
the inverse (Lagrange interpolation uses only field operations and distinct nodes), and uniqueness
holds because a scalar polynomial of degree at most m−1 with m distinct roots over a field is zero
(a polynomial ring over a field is a domain). Therefore

    sum_{h=0}^{m-1} k_h(Z) = dim P_{m-1}(Z) = sum_{i=1}^m dim(U_i ∩ Z).    (5.2)

*Polynomial minors of controlled degree.* Fix t_* outside the nodes. The spaces E_h(W; t_*) are
nested (multiplication by 1 includes P_{h-1} in P_h), so

    l_h = k_h(W) − k_{h-1}(W) >= 0   (0 <= h <= m−1).

At stage h choose l_h polynomials in P_h(W) whose values at t_* extend the previously chosen values
to a basis of E_h(W; t_*). In fixed coordinates of W let M_h(xi) be the matrix of all polynomial
columns chosen through stage h. It has r_h = k_h(W) columns, independent at t_*, so some r_h-row
square minor Delta_h(xi) satisfies Delta_h(t_*) ≠ 0. The column introduced at stage e has degree at
most e, so determinant expansion gives

    deg Delta_h <= sum_{e=0}^h e l_e.    (5.3)

(If r_h = 0, take the empty determinant Delta_h = 1.)

*Rank loss at the nodes.* For each j,
    dim E_h(W; t_j) <= k_h(W) − k_h(V_j).    (5.4)
Indeed, let pi_j : W -> W/V_j. At every non-node t, the kernel of pi_j on E_h(W; t) contains
E_h(V_j; t), so by (5.1), dim pi_j(E_h(W; t)) <= k_h(W) − k_h(V_j). To pass to t_j, take a fixed
basis of P_h(W), evaluate at the variable xi, and project columns by pi_j: a polynomial matrix whose
entries have degree at most h. Every minor of order larger than the displayed bound vanishes at
every non-node; being a polynomial of degree at most h times its order, hence finite-degree, and
vanishing on an infinite set (F is infinite), it is the zero polynomial. (This is the only use of
infinitude; the reals may be replaced by any infinite field, any characteristic.) So the rank bound
holds at t_j as well. But E_h(W; t_j) is contained in U_j, and pi_j is injective on U_j since
U_j ∩ V_j = {0}. Hence (5.4).

The chosen columns of M_h(t_j) lie in E_h(W; t_j), and restriction to the rows of a minor cannot
increase rank, so the square submatrix defining Delta_h has rank deficiency at least k_h(V_j) at
t_j. A square polynomial matrix with deficiency at least q at t_j has determinant divisible by
(xi − t_j)^q: extend q independent kernel vectors at t_j to a constant invertible column change
(possible over any field), observe the corresponding q transformed columns vanish at t_j, and each
contributes a factor xi − t_j, while the column change rescales the determinant by a nonzero
constant. Applying this at the distinct nodes separately,

    prod_{j=1}^m (xi − t_j)^{k_h(V_j)}   divides   Delta_h(xi).

(For r_h = 0 all k_h(V_j) vanish by (5.1) and the assertion is empty.) Since Delta_h is not the
zero polynomial, (5.3) yields

    sum_{j=1}^m k_h(V_j) <= sum_{e=0}^h e l_e.    (5.5)

*Summing the degree bounds.* Sum (5.5) over h = 0, ..., m−1 and apply (5.2) with Z = V_j:

    sum_{i,j} dim(U_i ∩ V_j)
        <= sum_{h=0}^{m-1} sum_{e=0}^h e l_e
         = sum_{e=0}^{m-1} e (m − e) l_e
        <= floor(m^2/4) sum_e l_e
        <= floor(m^2/4) N,

using sum_e l_e = k_{m-1}(W) = dim E_{m-1}(W; t_*) <= N. (The inequality e(m−e) <= floor(m^2/4)
for 0 <= e <= m is integer arithmetic.) ∎

## 6. The rank-sum corollary

**Corollary 6 (rank sum for differences).** Let X_1, ..., X_m, Y_1, ..., Y_m be d x d matrices over
F. If X_i − Y_i is invertible for every i (over F; subtraction is addition in characteristic 2),
then

    sum over ordered pairs i ≠ j of rank(X_i − Y_j)  >=  2 d_m d.

*Proof.* In W = F^d ⊕ F^d (dimension N = 2d) let U_i = { (v, X_i v) } and V_j = { (v, Y_j v) }.
Then v -> (v, X_i v) identifies ker(X_i − Y_j) with U_i ∩ V_j, so
dim(U_i ∩ V_j) = d − rank(X_i − Y_j), and U_i ∩ V_i = {0} by invertibility. Lemma 5 gives

    sum_{i,j} rank(X_i − Y_j)  >=  (m^2 − 2 floor(m^2/4)) d.

The m diagonal terms each equal d. Removing them leaves the claim, since

    m^2 − m − 2 floor(m^2/4) = 2 d_m

(for m = 2r both sides are 2r(r−1); for m = 2r+1 both sides are 2r^2). ∎

## 7. The rank detector in characteristic 2

Throughout this section n = 2s+1 with s >= 1 and d = s^2.

**Lemma 7 (two-triangle interpolation).** Let x_1, ..., x_{2s+1} be pairwise distinct elements of
F, and set

    Q_s = { (p, q) : 1 <= q < p <= s+1 }  ∪  { (p, q) : s+1 < p < q <= 2s+1 }.

Then the s^2 vectors  h_{pq} = ( x_p^a x_q^b )_{0 <= a, b < s},  (p, q) in Q_s,  form a basis of
F^{s^2}.

*Proof.* |Q_s| = s(s+1)/2 + s(s−1)/2 = s^2 equals the dimension of the space of polynomials P(u, v)
of degree at most s−1 in each variable, so it suffices that such a P vanishing at all points
(x_p, x_q), (p, q) in Q_s, is zero. Induct on s. For s = 1, P is constant and vanishes at
(x_2, x_1). Let s > 1. P(x_{s+1}, v) has degree at most s−1 in v and s distinct roots
x_1, ..., x_s, so it is identically zero (a univariate polynomial over a field with more roots than
its degree is zero). Hence P(u, v) = (u − x_{s+1}) P_1(u, v) with deg_u P_1 <= s−2, deg_v P_1 <= s−1
(monic division over any field). For p = 2, ..., s the points (x_p, x_1) give P_1(x_p, x_1) = 0
since x_p ≠ x_{s+1}; so P_1(u, x_1), of degree at most s−2 with s−1 distinct roots, vanishes
identically, and P(u, v) = (u − x_{s+1})(v − x_1) R(u, v) with both degrees of R at most s−2. At
every remaining point of Q_s the two factors are nonzero and F is a field, so R vanishes at
{ 2 <= q < p <= s } ∪ { s+2 <= p < q <= 2s+1 }. Put

    (y_1, ..., y_{2s-1}) = (x_{s+2}, ..., x_{2s+1}, x_2, ..., x_s),   S(u, v) = R(v, u).

The lower triangle q < p <= s for the y-tuple is the remaining upper triangle for the x-tuple after
swapping coordinates, and the upper triangle s < p < q <= 2s−1 for the y-tuple is the remaining
lower triangle; so S vanishes on the pattern Q_{s-1} for the y-tuple. By induction S = 0, hence
R = 0 and P = 0. No step uses the characteristic. ∎

**Lemma 8 (rank detector).** Fix pairwise distinct x_1, ..., x_n in F (n = 2s+1, d = s^2). Define

    Pi(t) = prod_{p=1}^n (t − x_p),   h_{pq} = (x_p^a x_q^b)_{0 <= a,b < s} in F^d,
    B_{pq} = ((x_p + x_q) / (Pi'(x_p) Pi'(x_q))) * h_{pq} h_{pq}^T,   Phi(H) = sum_{p,q} H(p,q) B_{pq},

for n x n matrices H over GF(2) (entries read in F). Then:

(i) Phi annihilates every additive matrix H(p, q) = r_p + c_q and every diagonal matrix;
(ii) rank B_{pq} = 1 for p ≠ q, and B_{pp} = 0; consequently
    rank Phi(H) <= |{ (p, q) : p ≠ q, H(p, q) ≠ 0 }|;
(iii) for every strict linear order ≺ on {1, ..., n}, Phi(T_≺) is invertible, where
    T_≺(p, q) = 1 if p ≺ q and 0 otherwise.

*Proof.* Pi'(x_p) = prod_{k ≠ p} (x_p − x_k) ≠ 0 (formal derivative of a product of distinct linear
factors; valid in any characteristic), and x_p + x_q = x_p − x_q ≠ 0 for p ≠ q in characteristic 2,
while B_{pp} = 0 since x_p + x_p = 0. This proves (ii), and the support bound follows by rank
subadditivity.

For (i) we use the barycentric identity: for any univariate polynomial A over F with
deg A <= n − 2,
    sum_{p=1}^n A(x_p) / Pi'(x_p) = 0.    (7.1)
Indeed A(t) = sum_p A(x_p) Pi(t) / ((t − x_p) Pi'(x_p)), since both sides have degree at most n−1
and agree at the n distinct nodes; comparing coefficients of t^{n−1} (the left side has none, as
deg A <= n−2) gives (7.1). The entry of B_{pq} indexed by (a, b), (a', b') is
(x_p + x_q) x_p^{a+a'} x_q^{b+b'} / (Pi'(x_p) Pi'(x_q)); for fixed p its sum over q vanishes by
(7.1) applied to A(u) = (x_p + u) u^{b+b'}, whose degree is at most 1 + 2(s−1) = 2s − 1 = n − 2.
Symmetrically the sum over p vanishes for fixed q. Hence
sum_q B_{pq} = 0 for all p and sum_p B_{pq} = 0 for all q, and for H(p, q) = r_p + c_q,

    Phi(H) = sum_p r_p (sum_q B_{pq}) + sum_q c_q (sum_p B_{pq}) = 0.

For (iii), first take the natural order, so T = T_≺ has T(p, q) = 1 iff p < q (strict upper
triangle). Let A be the matrix with A(p, q) = 1 iff p <= s+1 (an additive matrix: r_p = [p <= s+1],
c = 0), and put H'' = T + A. The off-diagonal entries of H'' are: for p <= s+1, H''(p, q) = 1 +
[p < q], which is 1 exactly when q < p; for p > s+1, H''(p, q) = [p < q], which is 1 exactly when
s+1 < p < q. Hence the off-diagonal support of H'' is exactly Q_s, with value 1 throughout.
Since Phi annihilates A and all diagonal entries,

    Phi(T) = Phi(H'') = sum_{(p,q) in Q_s} B_{pq} = A_Q D A_Q^T,

where A_Q is the d x d matrix with columns h_{pq} for (p, q) in Q_s (invertible by Lemma 7) and
D = diag( (x_p + x_q)/(Pi'(x_p) Pi'(x_q)) )_{(p,q) in Q_s} has nonzero diagonal entries. So Phi(T)
is invertible. For an arbitrary order with pi(1) ≺ ... ≺ pi(n), relabel the indices and use the
tuple (x_{pi(1)}, ..., x_{pi(n)}) in the argument just given: the relabeled evaluation vector at
position (r, q) is h_{pi(r), pi(q)}, so the sum defining Phi(T_≺) is merely reindexed, Pi is
unchanged, the relabeled nodes are distinct, and Lemma 7 applies again. Hence every order has
invertible image. ∎

*Remark.* Over the reals the detector is applied to the half-sign matrix of the spoke order
(entries ±1/2), which has no mod-2 image; the GF(2)-native object is the 0/1 order matrix T_≺, and
the additive row flip T -> H'' (turning one triangle off and the complementary one on) replaces the
real-signed rearrangement.

## 8. Assembly: the lower bound for odd n

Let n = 2s+1 >= 3 and put d = s^2 = d_n. If m <= 2 then d_m = 0 and the claim oc(D) >= d_m d_n = 0
is vacuous; assume m >= 3. Let D be an even-adjacent drawing of K_{m,n}. By Lemma 1 we may take D
normalized: polygonal, straight near every vertex and crossing, with all crossing parities
unchanged; in particular D is still even-adjacent.

Choose a gap at every vertex, build the matrix J_2 of Section 3, and with the map Phi of Lemma 8
(for any fixed choice of distinct nodes x_1, ..., x_n in F) set

    R_{ik} = Phi(J_2^{ik})  in F^{d x d},   X_i = R_{i1},   Y_k = R_{11} + R_{1k}.

*Difference form.* By Lemma 4 and Lemma 8(i),
    R_{ik} + R_{i1} + R_{1k} + R_{11} = 0,
i.e. R_{ik} = X_i + Y_k for all i, k (addition is subtraction in characteristic 2).

*Diagonal blocks.* For p ≠ q the edges ip, iq share only a_i, so
    J_2^{ii}(p, q) = chi(ip, iq) + t̃_{a_i}(ip, iq) = t̃_{a_i}(ip, iq),
because chi(ip, iq) = 0 by the even-adjacent hypothesis. Thus J_2^{ii} = T_i + Delta_i with T_i the
order matrix of the linear spoke order at a_i and Delta_i diagonal, and Lemma 8(i), (iii) give

    R_{ii} = Phi(J_2^{ii}) = Phi(T_i)   is invertible.

In particular X_i + Y_i = R_{i1} + R_{11} + R_{1i} = R_{ii} (the block relation with k = i) is
invertible for every i.

*Off-diagonal rank bounds.* For i ≠ k and p ≠ q the edges ip, kq have no common endpoint, so
J_2^{ik}(p, q) = chi(ip, kq). Lemma 8(ii) gives

    rank R_{ik} <= |{ (p, q) : p ≠ q, chi(ip, kq) = 1 }| =: oc_{ik}.

*Rank sum.* Corollary 6 applies:

    2 d_m d  <=  sum_{i ≠ k} rank R_{ik}  <=  sum_{i ≠ k} oc_{ik}  =  2 oc(D).

The last equality holds because every oddly crossing pair {e, f} of D is independent (adjacent pairs
cross evenly by hypothesis), hence has the form {ip, kq} with i ≠ k and p ≠ q, and is counted
exactly twice in the ordered sum, once in oc_{ik} and once in oc_{ki}; conversely every summand
counts such pairs. Dividing by 2,

    oc(D) >= d_m d = d_m d_n.   ∎

## 9. The even case by vertex deletion

Let n >= 4 be even (n = 2 is vacuous since d_2 = 0) and let D be an even-adjacent drawing of
K_{m,n}. For each r in {1, ..., n} the subdrawing D − b_r is an even-adjacent drawing of K_{m,n−1}
(the hypothesis is hereditary), and n−1 is odd and >= 3, so Section 8 gives

    oc(D − b_r) >= d_m d_{n-1}.

Every oddly crossing pair of D is independent, hence has the form {ip, kq} with p ≠ q, and survives
in D − b_r exactly when r is neither p nor q: exactly n−2 of the n subdrawings. Therefore

    (n − 2) oc(D) = sum_r oc(D − b_r) >= n d_m d_{n-1} = (n − 2) d_m d_n,

where the last identity is integer arithmetic: for n = 2t, d_n = t(t−1) and d_{n−1} = (t−1)^2, and
n d_{n-1} = 2t (t−1)^2 = (2t − 2) t (t−1) = (n−2) d_n. Dividing by n−2 gives oc(D) >= d_m d_n. ∎

Together with the vacuous cases min(m, n) <= 2 and n = 1 (d_1 = 0), Sections 8 and 9 prove part (1)
of the Theorem for all positive integers m, n.

## 10. The upper bound: the balanced-axis drawing

Place the first-class vertices on the vertical axis, ceil(m/2) of them at distinct positive and
floor(m/2) at distinct negative intercepts, and the second-class vertices on the horizontal axis in
the same balanced way, all intercepts nonzero; join every pair by a straight segment. Choose the
intercepts generically so that no three segments are concurrent in their interiors: concurrence of
three segments requires six distinct endpoints (segments sharing an endpoint do not cross elsewhere),
is a proper polynomial condition on the intercepts (fixing two segments and varying one intercept of
the third avoids the intersection point), and there are finitely many triples, so a product of
nonzero defining polynomials cannot vanish on the open set of permitted intercept choices.

An edge interior lies in one open quadrant. In a quadrant whose bounding rays carry u first-class
and v second-class vertices, each choice of two vertices on each ray spans a convex quadrilateral,
and exactly one of the two diagonal pairings crosses; since both pairings are present as edges,
each such 4-tuple contributes exactly one crossing, giving C(u, 2) C(v, 2) crossings in the
quadrant. Summing over the four quadrants factorizes:

    ( C(ceil(m/2),2) + C(floor(m/2),2) ) ( C(ceil(n/2),2) + C(floor(n/2),2) ) = d_m d_n,

using d_r = C(floor(r/2),2) + C(ceil(r/2),2) (for r = 2t both sides equal t(t−1); for r = 2t+1 both
equal t^2). Two edges sharing an endpoint lie on distinct lines through that endpoint and have no
other meeting, so adjacent edges do not cross; two independent straight segments cross at most once.
Hence the drawing satisfies the strengthened conditions of part (2) with exactly d_m d_n crossing
pairs, all of them crossing exactly once (so oddly). ∎

*Remark.* This is the classical balanced-axis construction (Woodall's presentation, recorded in the
pinned preprint's Section sec:formula); it is included for completeness and to record the parity and
adjacency properties the corollaries need.

## 11. Consequences and limitations

*Corollaries (as frozen).* For all positive integers m, n, with the definitions of the frozen
statement:
    ocrpm(K_{m,n}) = ocr+(K_{m,n}) = pcr+(K_{m,n}) = d_m d_n.
Indeed, part (1) applies to even-adjacent drawings, giving the lower bounds for ocrpm and (a
fortiori, since forbidding adjacent crossings restricts the class) for ocr+; in a drawing with no
adjacent crossings every oddly crossing pair is a crossing pair, so part (1) also lower-bounds
pcr+; and the Section 10 drawing lies in the smallest class and has exactly d_m d_n crossing pairs,
each crossing exactly once, giving all three upper bounds. Quoting the pinned Theorem thm:main
(cr(K_{m,n}) = d_m d_n, stipulated true), these three variants coincide with the ordinary crossing
number on K_{m,n}.

*Limitations (as frozen).*
- The unrestricted odd crossing number ocr, independent odd crossing number iocr, and pair crossing
  number pcr of K_{m,n} are not determined here: the even-adjacent hypothesis is what forces the
  diagonal blocks J_2^{ii} to be pure order matrices, and the present method says nothing about
  drawings with oddly crossing adjacent edges. Whether the restriction can be removed is a separate
  question (for general graphs, adjacent-crossing restrictions can change odd-crossing quantities;
  see reading-limits.md).
- No general comparison ocrpm(G) >= c * cr(G) could substitute for the direct argument: the best
  general relation between ordinary and (independent) odd crossing numbers is quadratic
  (cr(G) <= 2 iocr(G)^2, per Schaefer's survey DS21), which yields only oc(D) >= Omega((d_m d_n)^{1/2})
  for K_{m,n} — far from d_m d_n. The exact equality genuinely requires the machinery rebuilt above.
- The signed (real) version of the machinery does not itself imply the parity statement: a pair of
  edges crossing twice with equal signs has nonzero signed intersection but even parity, so the
  real rank bound counts more than the odd-crossing pairs. The characteristic-2 rebuild (Sections
  3–7) is therefore necessary, not cosmetic.

## 12. Sanity checks (mechanical, performed by sanity.py)

(artifact checks, not a mathematical gate)
(a) d_r = floor(r/2) floor((r−1)/2) = C(floor(r/2),2) + C(ceil(r/2),2) for all r <= 400;
(b) n d_{n−1} = (n−2) d_n for all even n <= 400;
(c) m^2 − m − 2 floor(m^2/4) = 2 d_m for all m <= 400;
(d) exact rational-arithmetic simulation of the Section 10 drawing for 2 <= m, n <= 7: crossing
    count equals d_m d_n, no adjacent pair crosses, no pair crosses more than once, no three edges
    concur internally;
(e) the chord parity formula of Lemma 2 verified against explicit alternation for all 24 cyclic
    orders of four points;
(f) the Lemma 8 detector over GF(2^4) = GF(16) for s = 1 and s = 2 (n = 3, 5; d = 1, 4) with
    pseudorandom distinct nodes: B_{pq} has rank 1 for p ≠ q and is zero for p = q; Phi annihilates
    pseudorandom additive and diagonal matrices; Phi(T_≺) is invertible for all 6 orders when
    s = 1 and for 40 pseudorandom orders when s = 2; the support bound rank Phi(H) <= |support|
    checked on pseudorandom H;
(g) Corollary 6 checked on pseudorandom families X_i, Y_k over GF(2) with invertible diagonal
    differences, for (m, d) in {3,4,5,6} x {1,2,3}: the ordered rank sum is >= 2 d_m d in all
    trials;
(h) the barycentric identity (7.1) checked on pseudorandom polynomials over GF(16).
