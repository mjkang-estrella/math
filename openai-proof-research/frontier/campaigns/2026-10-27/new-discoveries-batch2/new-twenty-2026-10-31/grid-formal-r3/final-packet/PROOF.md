# MathDB 343536: equitable partitions of rectangular grid graphs (full proof, all m, n)

Status: ordinary proof from expanded-corpus-r131, independently reviewed in grid-review-r1.
This lane supplies a PARTIAL conditional Lean formalization, not a completed certificate.
Root decides acceptance; no credit is requested for this round.

## 1. Source and exact statement

Source: J. M. Neuberger, N. Sieben, J. W. Swift, "Invariant synchrony subspaces of sets of
matrices", arXiv:1908.05797 (v1 15 Aug 2019, v2 18 Feb 2020; the conjecture is the same in both
versions: v1 text line 299, v2 text line 293). Definition 5.1 (equitable partition), Example 5.5,
Conjecture 5.6:

> Conjecture 5.6. The equitable partitions of P_m □ P_n are the orbit partitions of natural
> actions of the subgroups of the automorphism group of the graph. The lattice of equitable
> partitions is isomorphic to the lattice of subgroups exactly when there is a vertex with
> trivial stabilizer subgroup. This happens unless 2 ≤ m = n ≤ 3.

Evidence in the source: "We have computed the equitable partitions up to m = n = 20, along with
some larger graphs." The authors suggest that an eigenvector algorithm "can possibly be applied
symbolically for all m and n to prove this conjecture". No proof is given. The 2024 follow-up by
the same authors (arXiv:2411.10904 v1/v2) does not mention grid graphs (text grep in
`sources/2411.10904v2.txt`).

Definition 5.1: a partition A of the vertex set is equitable if d_B(i) = d_B(j) for all i, j in
the same cell A in A and all cells B in A, where d_B(i) = |N(i) ∩ B|.

## 2. Notation

Fix integers m, n ≥ 1. V = [m] × [n]; (i, j) and (i', j') are adjacent iff |i − i'| + |j − j'| = 1.
This is G = P_m □ P_n. Define the permutations of V

* ρ_r(i, j) = (m + 1 − i, j), ρ_c(i, j) = (i, n + 1 − j), and, only when m = n, τ(i, j) = (j, i).

All are graph automorphisms. Let A0 be the group they generate. As a permutation group A0 is
Z2 × Z2 = {id, ρ_r, ρ_c, ρ_rρ_c} when m ≠ n (smaller when m = 1 or n = 1, because then ρ_r or
ρ_c is the identity), and the dihedral group of order 8 when m = n ≥ 2.

For a partition π write χ(v) for the cell containing v, and u ≡ v when χ(u) = χ(v). If π is
equitable, then for each cell c there is a multiset M(c) of cells such that the multiset
{χ(w) : w ∈ N(v)} equals M(χ(v)) for every v. (Conversely, this property is exactly
equitability.) If g is any automorphism, the colouring χ∘g has the same neighbour rule M:
{χ(g w) : w ∈ N(v)} = {χ(w') : w' ∈ N(g v)} = M(χ(g v)).

Define H(π) = {g ∈ A0 : χ∘g = χ}, a subgroup of A0. Its orbits are contained in cells.

**Main Theorem.** For all m, n ≥ 1, a partition π of V is equitable if and only if it is the
orbit partition of a subgroup of A0. More precisely, if π is equitable then π is exactly the
orbit partition of H(π).

The "if" direction is general: the orbit partition of any group H of automorphisms is equitable,
since w ↦ h w is a bijection from N(v) ∩ B onto N(h v) ∩ B for every H-invariant set B.

## 3. General lemmas (π equitable throughout)

**L1 (cell invariants).** (a) deg is constant on cells. (b) If S is a union of cells, then so is
{v : N(v) ∩ S ≠ ∅}, since |N(v) ∩ S| is a sum of the d_B(v), B ⊆ S.

**L2 (row determinism).** Let χ, χ' be colourings of V with the same neighbour rule M. If χ and
χ' agree on row 1, they agree everywhere. The same holds with row 1 replaced by row m, column 1
or column n.
Proof. Induction on rows. Suppose they agree on rows 1..i, i < m. For any j, the neighbours of
(i, j) are (i + 1, j) together with neighbours lying in rows ≤ i. Hence χ(i + 1, j) is the unique
element left after removing from M(χ(i, j)) the multiset of χ-values of the other neighbours,
and the same computation gives χ'(i + 1, j). The other sides are the same argument in another
direction. ∎

**L3 (propagation).** Let λ : V → N be a function with the following properties:
(i) λ is constant on cells, and λ∘g = λ for every g ∈ A0;
(ii) for every w with λ(w) ≥ 2 there is a neighbour a of w with λ(a) = λ(w) − 1 such that w is
the only neighbour of a with λ ≥ λ(w).
If every cell meeting {λ = 1} is an orbit of H(π), then every cell is an orbit of H(π).
Proof. Induction on k = λ(w). Let w ≡ w' with λ(w) = k + 1 ≥ 2. Take a as in (ii). Since
d_{χ(a)}(w) ≥ 1, w' has a neighbour a' ≡ a. By induction there is g ∈ H(π) with g a = a'. Then g w
is a neighbour of a' with λ(g w) = k + 1, and by (ii), transported by the automorphism g that
preserves λ, it is the only neighbour of a' with λ ≥ k + 1. But w' is a neighbour of a' with
λ(w') = λ(w) = k + 1 by (i). Hence w' = g w. ∎

Given L3, the Main Theorem reduces in each case to choosing λ and proving **border transitivity**:
if u ≡ u' and λ(u) = 1, there is g ∈ A0 with g u = u' and χ∘g = χ.

Transposition (i, j) ↦ (j, i) is an isomorphism P_m □ P_n → P_n □ P_m that conjugates A0(m, n)
onto A0(n, m), and it transports equitable partitions and orbit partitions. So we may assume
m ≤ n when convenient.

## 4. Case m, n ≥ 3

Let ℓ(i, j) = min(i, j, m + 1 − i, n + 1 − j) and B = {ℓ = 1} (the border). Interior vertices
have degree 4, corners 2, other border vertices 3.

*ℓ is constant on cells.* {ℓ = 1} = {deg ≤ 3} is a union of cells by L1(a). For k ≥ 1,
{ℓ ≤ k + 1} = {ℓ ≤ k} ∪ {v : N(v) ∩ {ℓ ≤ k} ≠ ∅}: one inclusion holds because ℓ changes by at most 1
along an edge. For the other, if ℓ(v) = k + 1 ≥ 2 attained, say, by i (so i ≤ j, n + 1 − j,
m + 1 − i), then ℓ(i − 1, j) = i − 1. So L1(b) gives the claim by induction, and A0 preserves ℓ.

*Property (ii).* If ℓ(w) = k + 1 ≥ 2 attained by i, take a = (i − 1, j): ℓ(a) = k, and its other
neighbours (i − 2, j) and (i − 1, j ± 1) have ℓ ≤ k. The other three cases are symmetric.

*Border rule.* Because B is a union of cells, for v ∈ B the multiset of colours of N(v) ∩ B is a
function M_B(χ(v)). For m, n ≥ 3 a corner's two neighbours are non-corner border vertices, and
a non-corner border vertex has exactly two border neighbours, its neighbours along its side. The
third neighbour is interior: for instance (2, j) with 2 ≤ j ≤ n − 1 has ℓ = 2.

**L4 (side walks).** Let x_0, …, x_d and y_0, …, y_d be non-backtracking walks along sides of the border (x_(t+1) ≠ x_(t−1) and y_(t+1) ≠ y_(t−1) at internal steps; each step
to a neighbour on the same side) such that x_t and y_t are non-corners for 1 ≤ t ≤ d − 1. If
χ(x_0) = χ(y_0) and χ(x_1) = χ(y_1), then χ(x_t) = χ(y_t) for all t ≤ d.
Proof. For 1 ≤ t ≤ d − 1, M_B(χ(x_t)) = {χ(x_{t−1}), χ(x_{t+1})}, and likewise for y. Induct. ∎

**Corner timing.** Corners have degree 2 and other border vertices degree 3, so no cell contains
both. If two side walks as in L4 start with matching colours, the first corner is reached at
the same step on both. Otherwise, at the first step where one walk is at a corner and the other
is not, L4 would give equal colours.

**Border transitivity.** Let u ≡ u' with u ∈ B. Using the transport and conjugation argument below, assume u lies on a
horizontal side, which by the symmetry ρ_r we can take to be row 1: u = (1, j). Then u' ∈ B, since
ℓ is constant on cells.

*u a corner* (j = 1; j = n is the mirror image). Then u' is a corner. Let p = (1, 2), q = (2, 1).
The neighbours p', q' of u' satisfy {χ(p'), χ(q')} = {χ(p), χ(q)}; name them so that χ(p') = χ(p).
The walk x_t = (1, 1 + t) first reaches a corner at t = n − 1. The walk from u' through p' along
its side first reaches a corner at t = s − 1, where s is the number of vertices on that side. By
corner timing, s = n, and by L4, χ(x_t) = χ(y_t) for t ≤ n − 1. A side with n vertices is a row
when m ≠ n, and any side when m = n. In either case there is g ∈ A0 with g(1, 1) = u' and
g(1, 2) = p', and it maps row 1 isometrically onto the walk y, so g(1, 1 + t) = y_t. Hence
χ∘g = χ on row 1. By L2 (χ∘g has rule M), χ∘g = χ.

*u not a corner* (2 ≤ j ≤ n − 1). Then u' is a non-corner border vertex. Its two border
neighbours a', b' satisfy χ(a') = χ(1, j + 1) and χ(b') = χ(1, j − 1) (equal multisets M_B).
Corner timing applied to the walks (1, j + t) and (u', a', …) shows that the corner in direction
a' is at distance n − j from u'. Applied to (1, j − t) and (u', b', …), it shows that the corner in
direction b' is at distance j − 1. So u' lies on a side with n vertices, at distance j − 1 from
the corner c' reached through b'. Take g ∈ A0 with g(1, 1) = c' and g(1, 2) the neighbour of c'
on that side. Then g(1, j) = u' and g(1, j + 1) = a'. By L4 in both directions, χ∘g = χ on row 1,
and by L2, χ∘g = χ.

L3 with λ = ℓ now finishes the case m, n ≥ 3.

## 5. Case m = 2 (ladders), n ≥ 2

*n = 2.* G = C_4 and A0 = D_4 = Aut(C_4). For u ≡ u', the neighbours of u' have the same colour
multiset as those of u, so there is a dihedral map σ ∈ A0 with σ u = u' and σ(v_1) = v_1' for a
neighbour v_1 of u and a neighbour v_1' of u' with χ(v_1') = χ(v_1). Walk-determinism around the
4-cycle (the argument of L4 on the whole cycle) gives χ∘σ = χ. An exhaustive check also confirms
this case: there are 7 equitable partitions, equal to the 7 orbit partitions
(`outputs/grid-equitable-upto16.json`).

*n ≥ 3.* Let λ(i, j) = min(j, n + 1 − j). Corners are exactly the degree-2 vertices, and
{λ = 1} = corners. As in Section 4, λ is constant on cells and property (ii) holds: for
w = (i, j) with λ = j ≥ 2, take a = (i, j − 1), whose other neighbours (i, j − 2) and (3 − i, j − 1)
have λ ≤ j − 1.

*Column determinism.* If χ, χ' have the same rule and agree on column 1 (or on column n), they
agree everywhere. Indeed χ(i, j + 1) is M(χ(i, j)) minus the colours of (i, j − 1) and
(3 − i, j).

*Border transitivity.* Let u ≡ u' be corners. The neighbours of u are its corner partner u*
(the other vertex of its column) and a non-corner h(u). Corner and non-corner colours are
disjoint, so the equality of neighbour-colour multisets forces χ(u'*) = χ(u*). A0 acts regularly
on the four corners. The element g ∈ A0 with g u = u' maps u* to u'* and maps the column of u
onto the column of u'. So χ∘g = χ on the column of u, and by column determinism, χ∘g = χ.

## 6. Case m = 1 (paths)

For n = 1 the claim is trivial. For n ≥ 2 let λ(j) = min(j, n + 1 − j). The endpoints are exactly
the vertices of degree 1 and form {λ = 1}. λ is constant on cells and (ii) holds with a = j − 1.
Determinism: χ(2) is the single element of M(χ(1)), and χ(j + 1) = M(χ(j)) − {χ(j − 1)}. If
1 ≡ n, the reversal r satisfies χ∘r = χ at vertex 1, hence everywhere. So in all cases endpoint
cells are H(π)-orbits, and L3 finishes.

The cases n ≤ 2 < m follow by transposition. This proves the Main Theorem. ∎

## 7. Automorphism group, stabilizers and the lattice statement

**Trivial A0-stabilizers.** If m ≠ n, then x = (1, 1) has trivial stabilizer in A0: its A0-images
are distinct, and when m = 1 or n = 1 the group has order ≤ 2. If m = n ≥ 4, the eight images of
x = (1, 2) are distinct, because 2 ≠ n − 1. If m = n = 1, A0 is trivial. If m = n ∈ {2, 3}, every
vertex is fixed by a non-identity element of A0: diagonal vertices by τ; in 2×2, (1, 2) and
(2, 1) by the anti-diagonal reflection (i, j) ↦ (3 − j, 3 − i); in 3×3, the other two corners (1,3) and (3,1) by the anti-diagonal reflection (i,j) ↦ (4−j,4−i), and edge midpoints by ρ_r or ρ_c.

**Corollary B (Aut G = A0 when a vertex x has trivial A0-stabilizer).** The orbit partition of
S = Stab_{Aut G}(x) is equitable. By the Main Theorem it equals the orbit partition of some
K ≤ A0. Since x is a singleton S-orbit, K fixes x, so K = 1. Hence every S-orbit is a singleton,
and S = 1 because automorphisms are determined by their vertex maps. The orbit partition of
Aut G equals the orbit partition of some K' ≤ A0. So for g ∈ Aut G, g x = k x for some k ∈ K', and
k⁻¹g ∈ S = 1 gives g = k ∈ A0. (In the 2×2 and 3×3 cases only A0 ≤ Aut G is used below.)

**Corollary C (the lattice statement).** Let Φ : Sub(Aut G) → EqPart(G), H ↦ orbit partition,
with refinement order on partitions. Φ is monotone, and it is surjective by the Main Theorem,
since A0 ≤ Aut G.

* If some vertex x has trivial Aut-stabilizer, then Φ(H) ≤ Φ(K) implies H x ⊆ K x, hence
  H ⊆ K (if h x = k x then k⁻¹h ∈ Stab(x) = 1). So Φ is an order isomorphism, and therefore a
  lattice isomorphism. By Corollary B and the stabilizer computation, such an x exists exactly
  when not (2 ≤ m = n ≤ 3): when such an x exists, Stab_{Aut}(x) = 1; in the 2×2 and 3×3 cases,
  Stab_{Aut}(x) ⊇ Stab_{A0}(x) ≠ 1 for every vertex x.
* If m = n ∈ {2, 3}, let ρ(i, j) = (j, n + 1 − i) be the rotation. ⟨ρ⟩ (order 4) and A0 (order 8)
  are distinct subgroups with the same orbit partition. In 2×2 it is the single cell; in 3×3 it
  is {centre}, {corners}, {edge midpoints}. So |EqPart| < |Sub(Aut G)|, both finite, and the two
  lattices are not isomorphic (not even equinumerous).

Together these give all three sentences of Conjecture 5.6, for all m, n ≥ 1. ∎

## 8. Computational cross-check (diagnostic only)

`scripts/grid_equitable.py` enumerates all equitable partitions exhaustively: restricted-growth
colourings with exact pruning of completed vertices. It compares them with the orbit partitions
of all subgroups of A0 and records whether a trivial A0-stabilizer exists. Agreement holds for
every size covered, listed in `logs/grid-eq-16.log`, `logs/grid-eq-42.log` and
`logs/grid-eq-b.log` (runs stopped by the 120 s CPU cap after the last listed size):

* 1×n for n ≤ 20; 2×n for n ≤ 20; 3×n for n ≤ 13; 4×n for n ≤ 10; 5×5 through 5×8.
* The equitable-partition counts are 1, 2, 5 or 10, except 2×2 (7 against 10 subgroups) and
  3×3 (9 against 10 subgroups). A trivial A0-stabilizer is absent exactly at 2×2 and 3×3.

The source authors already reported computations up to 20×20. The computation here only guards
against an error in the proof.

## 9. Prior-art and significance notes (bounded)

* The source gives no proof. It names an eigenvector approach and "the techniques of [?]".
* There is no follow-up proof in the authors' 2024 paper arXiv:2411.10904 (v1, v2 grepped) or
  on their companion site (fetched 2026-11-03, `sources/nss-companion.html`).
* Web searches on 2026-11-03 found no proof (queries recorded in SUMMARY.md). The coupled-cell
  literature (Wang–Golubitsky; Dias–Pinho) classifies balanced colourings of infinite lattices
  and periodic networks; it has many non-symmetric patterns and does not cover finite grids with
  free boundary.
* The Omega D5/Problems trees at 5aef460c and the OpenAI preprints tree at 4eaee875 have no
  grid/equitable path hits (`outputs/registry-screen.json`).
* Possible objections a reviewer should weigh:
  1. The argument is elementary, about two pages, and self-contained. It does not bridge from
     the source's own propositions; the source contains no grid results.
  2. Path and ladder cases are classical in flavour.
  3. The lattice sentence follows formally from the first sentence plus a stabilizer count.

## 10. Lean plan

See `lean-draft-UNCOMPILED/PLAN-343536.md` and `lean-draft-UNCOMPILED/Grid343536.lean`.


## Formalization corrections and current boundary

For every WLOG isomorphism f : G → G', define χ'(z)=χ(f⁻¹z). If g' preserves χ'
and sends fu to fu', then g=f⁻¹g'f sends u to u' and χ(gz)=χ(z). Transposition
conjugates the row and column generators into the column and row generators; reflection
conjugates A0 to itself. Thus g belongs to the required original A0. This explicitly
justifies the side and dimension reductions.

L4 must assume non-backtracking at every internal step. Together with the fact that an
internal side vertex has exactly two border neighbours, this identifies those neighbours
as the distinct preceding and following vertices. Multiset cancellation now applies.
All uses of L4 in this proof are monotone side walks.

The layer propagation lemma must also require λ(v) ≥ 1 for every vertex. The old skeleton
omitted this hypothesis, so it did not cover λ=0. The concrete layers in this proof are
positive. A future abstract propagation lemma must include positivity.

Completed Lean: definitions, orbit equitability, monotonicity and order reflection at a
free vertex, natural order isomorphism conditional on surjectivity, explicit reflections,
transposition, corrected A0, Hpi, exceptional no-free proofs, small regression tables,
and the endpoint conditional on exactly MainOrbit, FreeClassification, ExceptionalNoIso.
These three Props are unproved; they are not axioms. No unconditional endpoint is claimed.

The next round must formalize neighbour-count multiset determinism, positive layers,
non-backtracking corner timing, conjugation transport, border transitivity, paths and
ladders, then the positive stabilizer classification and exceptional subgroup collisions.
The regression tables establish seven and nine distinct equitable labelings respectively;
they do not certify completeness or the ten-subgroup counts. No lattice typeclass for
EqPart is supplied in this round; the endpoint uses its source-ordered poset and an order
isomorphism, which preserves lattice operations once existence is established.

## Round 2 formal progress

GridPropagation proves positive-layer L3 and neighbour-existence saturation.
GridNeighbours proves the Definition 5.1 equivalence with actual multisets of
quotient cells, retaining multiplicities. GridLattice closes the lattice gap
independently of MainOrbit: if s is the join of equitable partitions r in S,
coarsening maps the r-neighbour multisets to the s-neighbour multisets. Each r
lies below the kernel of the s-multiset map. The universal property of join
places s below that kernel, proving equitability, including the empty join.
Meets are joins of equitable common refinements, using the source order.

GridDeterminism proves single-unknown-neighbour cancellation and first-row L2
by strong induction on the row coordinate using literal grid adjacency.
GridTransport proves equitable partition transport and the precise conjugation
f.symm composed with g composed with f. Membership in the original A0 still
requires generator conjugation identities. The ordinary proof remains a candidate
roadmap: MainOrbit, FreeClassification and ExceptionalNoIso are still unproved.
GridFinal2.mathdb_343536 explicitly retains exactly these three premises.

## Round 3: exceptional obstruction closed

Restrict any equivalence relation on four points to its six unordered pairs.
The 64 Boolean cases either contradict transitivity or equal the kernel of
one of the 15 explicit restricted-growth label functions. GridFiniteCodes
proves this exhaustively, using explicit reflexivity, symmetry and transitivity.

In the 3×3 grid, equitable vertices have equal degree, by taking cardinalities
of equal neighbour-cell multisets. Degrees are 2 on corners, 3 on edge midpoints
and 4 at the centre. Restrict the partition to the four corners and four edge
midpoints. The four-point classification gives 15 choices for each restriction;
the centre is alone and different degree classes cannot merge. Hence every
equitable partition is one of 225 explicit kernels. Exactly 9 of those candidates
satisfy Definition 5.1, checked by decide. A surjection from this nine-element
subtype proves the required upper bound. For 2×2, the same four-point
classification gives 15 candidates, of which 7 are equitable.

For both exceptional sizes, eight explicit automorphisms (the row and column
reflections and their products with transposition) have a checked multiplication
table. Ten lists of their indices are closed under multiplication and inverses,
contain the identity, and are pairwise different. Their associated carriers
are actual subgroups of the full graph automorphism group. Injectivity of the
eight automorphisms as vertex maps proves that the ten subgroups are distinct.
Thus any proposed order isomorphism would give equality of cardinalities,
contradicting 10 ≤ |Subgroup| and |EqPart| ≤ 7 or 9.

This route does not assume MainOrbit or FreeClassification and does not use the
regression enumeration as an oracle.

## Round 3: free-vertex work and remaining gap

For G m 1, an automorphism fixing (0,0) fixes its entire first row, which is a
singleton. Apply round-2 row determinism to the equality partition to conclude
that it fixes every vertex. A graph isomorphism transports a free vertex by
conjugation, so transposition handles G 1 n.

For m,n ≥ 2 outside the exceptional squares, the positive stabilizer theorem
is still missing. A prospective continuation is to prove the grid degree
formula and show that a fixed oriented corner flag forces its entire side,
then apply first-row determinism. In a nonsquare, corner timing must rule out
interchanging the two directions. In a square of size at least four, the
near-corner vertex has a unique adjacent corner, and degree separation should
fix the oriented flag. Ladders require their own degree-separated end-column
argument. None of these proposed steps is presented as a proved theorem here.

MainOrbit remains exactly the inherited Prop, including all paths and ladders.
Its non-backtracking side walks, conjugation membership, border transitivity
and invariant-layer construction remain unproved in Lean.
