# I188 analytic attempt: patch-rooted geometry

2026-10-11. **Original E183: UNRESOLVED.** Completed unsealed proof-only record, written incrementally. Steps 1–5 are established deductions; step 6 proves the exact exterior restriction and states the unpaid survivor implication. No substantial finding or E183 proof is claimed. Eight accepted, two remaining.

## 0. Exact hypotheses and quantifier

For every finite connected simple bipartite locally cubic disk X, let its five distinct degree-two ports b_0,...,b_4 have boundary order (0,2,1,4,3) and colors (1,1,1,0,1) in label order. Every other vertex is cubic. Join these ports by e_0,...,e_4 respectively to (1,5,6,28,29) of the disjoint exterior Y. Its vertices are {1,...,11,28,29}, and its internal edges are exactly

```
1-7,1-28,2-3,2-8,2-29,3-4,3-9,4-5,4-10,5-11,
6-7,6-11,7-8,8-9,9-10,10-11,28-29.
```

The glued G is simple, planar, bipartite and a brace. All fibres and compatible exterior products are complete, not samples. A packing spans its side, has degree one precisely at used ports and degree two elsewhere, and has no isolated cycles. The eleven complete nonempty survivor fibres, written as used labels; local pairing, are

```
02;02  12;12  14;14  24;24  0123;02,13  0123;03,12
0134;03,14  0234;02,34  0234;03,24  1234;12,34  1234;14,23.
```

The complete lost fibres are P=(01;01), D=(0134;01,34). The internal port-disjoint patch has simple boundary C=(x,a,b,y,d,c,x), chord xy, A={xa,by,dc}, B={ab,yd,cx}. For every admissible p in P with E(p) intersect E(C)=A and q=p symmetric-difference E(C) also in P, E183 asks for SOME perfect matching M containing A whose complement is Hamiltonian of ANY of the eleven survivor local types. There is no prescribed completion, cut 2, single difference cycle or sequence of local moves.

I187 Section 2 and its finalized review pay no cuts of size one or two, no nontrivial three-edge cut, and 3-vertex-connectivity. In particular T=G* is a simple properly face-two-colored sphere triangulation without separating triangles. These reviewed deductions, whose full proofs were read, are inputs here. The underlying count is 3(n_black-n_white)=alpha-beta; two-extendability excludes a two-edge cut and forces the three edges of any three-edge cut to share a vertex. The dual of a separating triangle would contradict the resulting triviality of three-edge cuts. Source prop:pairs therefore applies.

The four remaining patch edges are aa',bb',cc',dd'. Their terminals are outside C and pairwise distinct by the read I183 final review, items 2–3, also retained in I187 Section 1. Color x,b,d black and a,y,c white. All source face colors refer to this coloring, independently of the names of the five ports. Write N for the dual nonroots, and call its black-face domain Bcal, to avoid collisions with X, patch A and lost P.

All five I187 anchors and the retained manuscript matched before this proof work. Salvage A–F was treated as questions, not evidence.

## 1. Faciality, including both sides and chords

For S_1=(x,a,b,y,x), the four incidences leaving its vertices are cx,aa',bb',yd. Its possible chords are xb and ay, excluded by bipartiteness. If both open sphere sides contain vertices, let U_1,U_2 be the vertex sets strictly on those sides. Their edge boundaries are disjoint subsets of those four incidences: an edge cannot cross the embedded cycle, and there are no vertices of S_1 in U_i. Each boundary has size at least three by the paid small-cut result. This requires at least six distinct incidences, a contradiction. Thus one side has no vertices. Since there are no chords, that side has no edges either and is a face. The other side contains c,d, so this is the unique empty side.

For S_2=(x,y,d,c,x), the same argument uses xa,yb,dd',cc'; its possible chords xd,yc are forbidden by bipartiteness. It too bounds a face.

The two empty facial sides at xy are opposite. At a degree-three vertex x, the face S_1 uses the consecutive pair xa,xy and S_2 uses xy,xc. These are the distinct sectors immediately on the two sides of xy. They cannot be one sector because xa and xc are distinct edges. Thus the two faces are distinct and genuinely adjacent along xy. This also follows by identifying the face on each edge-side, rather than by assuming a drawing.

## 2. All dual identifications and the patch disk

Call these square-face dual vertices ell,r respectively. At x the third dual vertex is o, giving t_x=(o,ell,r). At a, the two known incident primal faces across xa give ell,o; call the third u. At b the third, besides ell,u, is v, and propagation across by and xy gives t_y=(ell,r,v). At d call the remaining vertex w; propagation across dc and cx gives t_c=(r,o,w). Thus the actual facial triangles and their colors are

```
t_x=(o,ell,r) black,    t_a=(ell,o,u) white,
t_b=(ell,u,v) black,    t_y=(ell,r,v) white,
t_d=(r,v,w) black,     t_c=(r,o,w) white.
```

These identifications follow successively from the two sectors bordering each shared primal edge at its endpoints; they do not yet assert names distinct. The dual edges, each with its original primal identity, are

```
xa: o-ell     xy: ell-r     cx: r-o
ab: ell-u    aa': o-u      bb': u-v
by: ell-v    yd: r-v       dc: r-w
dd': v-w     cc': o-w.
```

For eleven of the fifteen pairs of the six names, an edge in this list excludes equality by absence of dual loops. The remaining four are (o,v),(u,w),(ell,w),(r,u). If o=v, the distinct edges aa'* and bb'* both join o to u. If u=w, aa'* and cc'* both join o to u. If ell=w, dc* and xy* both join r to ell. If r=u, ab* and xy* both join ell to r. All contradict dual simplicity, which is already paid; none of these pairs can be identified. This explicitly exhausts all fifteen pairs. No parallel incidence is discarded in the reasoning: each would have arisen from two distinct primal edges, and has just been excluded by a proved hypothesis.

The square faces have length four, so deg_T(ell)=deg_T(r)=4, with neighbors (o,u,v,r) and (o,ell,v,w), respectively. The six listed actual triangles form an embedded closed disk Delta whose boundary is the simple four-cycle Gamma=(o,u,v,w,o). Indeed start from t_x and attach t_a,t_c along o-ell,o-r, then t_y along ell-r, and t_b,t_d filling the sectors at ell,r. The displayed incidences give a disk with precisely that boundary; all six faces have disjoint open interiors and no extra identifications. Equivalently the full stars of ell and r, joined along their common edge, have exactly these six triangles. Every other dual vertex is in the open complementary disk: the interior of Delta is already tiled by actual faces, and its only vertices are the six proved distinct names.

Gamma is dual to the four-edge cut {aa',bb',dd',cc'} bounding the six primal patch vertices. Put the point at infinity in t_0=t_x and choose f_0=xa*=o-ell. The three roots are o,ell,r. The distinct vertices u,v,w are nonroots. The white-tree root is t_a.

## 3. The marked cycle and its embedding sign

In an undirected source group D, the edge chosen at a nonouter black face joins its two distinct state values, both nonroots. At t_b=(ell,u,v) the only eligible edge is uv; at t_d=(r,v,w) it is vw. Therefore these two edges are forced in EVERY group. Since D is a disjoint union of simple cycles on N, they lie consecutively on one cycle C_0. Simplicity and the proved u,v,w distinctness give two orientations of C_0; exactly one traverses u to v to w.

The I187 endpoint mark becomes exactly

eta(s)=1 iff s(t_b)=v and s(t_d)=w,

because by*=ell-v and dc*=r-w each have just one nonroot endpoint. Thus it fixes exactly one cycle orientation in every D and never conflicts. All other cycle orientations are free. It does not fix two independent signs.

Here is why this fixed sign is the SAME across all D, not merely a consistent direction on named vertices. Remove the arc u-v-w from C_0, leaving a simple return path R from w to u. Its interior cannot use o,ell,r (roots), or v (simplicity of C_0). These are all remaining vertices on or in Delta. An edge cannot run through an actual face interior or cross Gamma. Hence the interior of R is in the complementary disk to Delta and meets Gamma only at u,w. This remains true when R is the single edge wu, if such an edge exists.

The arc u-v-w together with R bounds one subdisk of that complementary disk incident with the u-v-w boundary arc. This is the side of C_0 away from Delta; it contains none of the roots. The other sphere side contains the interior of Delta and the chosen infinity point in t_x. Therefore the bounded disk of C_0 is always on the same side of the directed uv edge, namely the side opposite t_b. Its clockwise/counterclockwise orientation is fixed by that local sector, for every possible return path. Denote this single embedding-determined sign by epsilon_* in {+1,-1}, using +1 for counterclockwise exactly as I187. No absolute sign is inferred from an unordered triangle notation. Reflection changes the conventions consistently and causes no phase disagreement between groups.

## 4. Restricted product and nonvanishing

Use the actual source spoke weights from lem:circulation. For each cycle C_j of D, put L_j^+ and L_j^- for its counterclockwise and clockwise head sums, and d_j=(L_j^+-L_j^-)/2>0. The inequality uses the source's simple spoke detour proof, not arbitrary weights. Index the forced cycle by 0. There is at least one D by prop:pairs with the paid no-separating-triangle hypothesis. Each D has c(D)>=1 and retains exactly 2^(c(D)-1) orientations.

I187 (13), with precisely the fixed sign from Section 3, now reads

G_D^eta(z)=(-i epsilon_*) exp(z L_0^{epsilon_*})
           product_{j!=0}[-i exp(z L_j^+)+i exp(z L_j^-)].

Each free factor has a simple zero, with coefficient -i(2d_j). Thus the order is c(D)-1 and its leading Taylor coefficient is

(-i)^{c(D)} epsilon_* product_{j!=0} 2d_j.

Set c_min=min_D c(D). Summing the groups, the coefficient in degree c_min-1 is exactly

(-i)^{c_min} epsilon_*
  sum_{D:c(D)=c_min} product_{j!=0} 2d_j.

This is a common nonzero phase times a strictly positive finite real sum. Groups with more cycles contribute zero in that degree. It follows that Z_eta is not identically zero. For c_min=1 the products are empty and equal one, so the nonzero coefficient is the constant coefficient; nothing divides by c_min-1. A hypothetical N={u,v,w} gives the same formula for its triangular C_0. (The exact thirteen-vertex exterior makes this minimal size unnecessary.) A possible chord uw causes no change to the disk or positivity arguments.

The mark depends on s alone, so the actual fixed-s involution in lem:cancel preserves it. Therefore

Z_eta(z)=sum_{s in F} eta(s) alpha_s exp(z omega(s)),

where F consists of partnered forest states. Each such state's partner is unique by orienting its Q_s components toward their unique roots, and alpha_s=i^{J(r_s,s)} is nonzero. Nonvanishing implies that at least one partnered forest state satisfies s(t_b)=v,s(t_d)=w. This is an existence deduction, not a surjectivity assertion about any named Hamiltonian cycle.

## 5. Exact white-tree recovery: both parent tests are automatic

For a partnered forest state, source lem:root-components and complementary plane-tree duality give the spanning white-face tree W_s of deleted-spoke duals. Each tau_t joins the white faces across the two sides of t incident with s(t). It is rooted at t_a. The selected forest K_s contains f_0 and chooses, for every other black face, the side across the endpoint of tau_t farther from t_a. This is the actual source recovery and exactly I187 (4)–(5).

Account for every possible tree incidence at t_y. Its neighboring black faces are t_x,t_b,t_d, from the primal neighbors x,b,d of y. There is no deleted spoke at outer t_x. The spoke at t_b meets t_y iff its chosen corner belongs to by*=ell-v; the root ell is unavailable, so this is iff s(t_b)=v. At t_d it meets t_y iff s(t_d)=v, since yd*=r-v and r is unavailable. These are all incidences. Spanning connectedness of W_s requires at least one; the state bijection permits at most one. Thus EVERY partnered forest state has exactly one of s(t_b)=v and s(t_d)=v. Under eta=1 it is the first, and t_y is a nonroot leaf with unique edge tau_b. Its unique edge is its parent edge, so by* belongs to K_s.

Similarly the only neighboring black faces of t_c are t_x,t_d,t_{c'}. Outer t_x supplies no deleted spoke. At t_d a spoke meets t_c iff s(t_d)=w, since dc*=r-w. At t_{c'} it meets t_c iff s(t_{c'})=w, since cc'*=o-w. The second possibility is forbidden by bijectivity when s(t_d)=w. There is no additional incidence; c' is outside the patch and distinct from d,x. Hence under the mark t_c is another nonroot leaf, with parent edge tau_d, proving dc* belongs to K_s. No hypothetical parallel white-tree edges were suppressed: all candidate spokes were listed by their owner.

Finally f_0=xa* belongs to K_s by construction. Hence EVERY marked partnered forest state recovers M_s containing all of A, and the source lem:P-forest gives an actual Hamiltonian H_s=G-M_s. As a separate consistency check, if xa and by were matching edges and dc were not, vertices x,y force cx,xy,yd into H_s and omission of dc from the matching closes the proper Hamiltonian component c-x-y-d-c. The disjoint exterior rules that out. The leaf proof above establishes the stronger exact parent-edge condition directly.

Conclusion at this checkpoint: Leads A–E hold under the full paid hypotheses, with explicit proofs. The frozen fixed-root source image is nonempty. The source-image membership of the known lost completion H_0 is still unproved, and no survivor conclusion follows from this checkpoint alone.

## 6. Survival: exact exterior trace and the remaining implication

### 6.1 What every frozen recovered cycle does inside the patch

If M contains A, its six patch vertices are already matched internally. All four continuations aa',bb',cc',dd', the chord xy, and precisely B on the hexagon belong to H=G-M. Its two patch routes are exactly

```
a'--a--b--b'             c'--c--x--y--d--d'.
```

They pair the four continuations as (a'b')(c'd'). This is the same patch restriction as the known lost completion of q. Conversely an actual Hamiltonian cycle with precisely these routes has complementary matching containing A. Switching the six boundary edges interchanges these routes with

```
a'--a--x--y--b--b'       c'--c--d--d',
```

and preserves their continuation pairing. Thus such a switch preserves connectedness and the full five-port local type, but changes which half is in the matching. It cannot turn a lost type into a survivor. In particular the p,q hypothesis supplies a known member of the frozen P population; it is not an extra condition relating the survivor fibres to that population. This observation uses no sequence of local improvements and does not revive the parked ear route.

The color of the endpoints of a Hamiltonian path in the bipartite patch is consistent with both pairs above. Planarity gives no contradiction: the four outgoing incidences have the cyclic order a,b,d,c, and the pairing ab,cd is noncrossing.

### 6.2 Deriving the complete cut-2-absent exterior alternatives

This is a written symbolic degree argument in the fixed Y, not a graph or matching scan. Write U for the used cut labels of an actual Hamiltonian cycle and K_Y for its restriction to Y. From the degrees of X, summing black and white internal degrees gives

3(n_1-n_0)=4-1=3,

so n_1-n_0=1. For its spanning local packing, the two color degree sums give

#(U intersect {0,1,2,4}) - 1_{3 in U}=2.                 (15)

The global cycle crosses the cut and has an even positive number of crossings, so |U| is two or four. If 2 is absent, (15) leaves precisely U=01,04,14,0134. For two used ports the local pairing is necessarily the single pair. For U=0134 the inherited boundary order is 0,1,4,3; disjoint disk paths permit pairings 01,34 and 03,14. The pairing 04,13 alternates around the boundary and is impossible by separation of a disk by a simple path. Thus no list of abstract sign patterns is being substituted for the actual port geometry.

Use the following binary edge variables for inclusion in K_Y:

```
a=1-7, b=1-28, c=28-29, d=29-2,
e=6-7, f=6-11, g=5-4, h=5-11,
j=7-8, k=11-10, l=8-2, m=8-9,
n=9-3, p=9-10, q=10-4, r=2-3, s=3-4.
```

Here the variable q is a local binary symbol ONLY in this subsection, not the named lost packing q; similarly these exterior edge letters are not patch vertices. Set u_i=1_{i in U}. The exact degree equations are

```
a+b=2-u_0, b+c=2-u_3, c+d=2-u_4,
e+f=2-u_2, g+h=2-u_1,
a+j+e=2, f+h+k=2,
j+l+m=2, m+n+p=2, p+q+k=2,
d+l+r=2, r+n+s=2, s+q+g=2.
```

For u_2=0, e=f=1, whence a+j=1 and h+k=1. We require no isolated cycle in K_Y, because H also visits X.

Define the following three displayed vertex paths; successive pairs are edges of the exact Y and every path contains all thirteen vertices once:

```
R1: 1-28-29-2-3-4-10-9-8-7-6-11-5
R2: 1-28-29-2-3-9-8-7-6-11-10-4-5
R3: 1-28-29-2-8-7-6-11-10-9-3-4-5.
```

For U=01, b=c=d=j=1 and a=0. If h=1 then g=k=0, s=q=p=1 and m=r=1-n, l=n. The choice n=0 gives R1; n=1 leaves the isolated cycle 3-4-10-9-3. If h=0 then g=k=1, s=p=1-q, r=m and l=1-r. For q=1 the equations force r=m=n=1,l=0 and give R2. For q=0 they force r=m=1-n,l=n; n=1 gives R3, while n=0 leaves the isolated cycle 8-7-6-11-10-9-8. Therefore R1,R2,R3 are the COMPLETE valid exterior fibre for U=01, with exterior pairing 01.

For U=04, b=c=g=h=j=1 and a=d=k=0. The equations force l=r=n=p=q=1 and m=s=0. There is the path 1-28-29 and the isolated cycle 2-8-7-6-11-5-4-10-9-3-2. Hence no admissible exterior packing exists, eliminating U=04 for any Hamiltonian H.

For U=14, a=b=c=g=k=l=r=m=1 and d=j=h=0 in the only valid case, with n=q=0,s=p=1. Its full path is

```
S: 29-28-1-7-6-11-10-9-8-2-3-4-5,
```

with pairing 14. To see completeness rather than just verify S, the boundary equations first force a=b=c=1,d=j=0,l=r=m=1. If h=1 then g=k=0 and s=p=q=1,n=0, leaving the cycle 2-3-4-10-9-8-2 beside the port path. If h=0 then g=k=1 and s=p=1-n,q=n; n=0 gives S and n=1 leaves the cycle 2-3-9-8-2. These exhaust the binary possibilities.

For U=0134, a=c and b=d=1-c.

* If c=0, then a=0,b=d=j=1. The remaining equations are exactly the U=01 equations above. There is a separate edge-path 1-28, while each Ri with its initial vertices 1,28 removed is a path from 29 to 5. These three packings have exterior pairing 03,14, cover all vertices and have no cycle.
* If c=1, then a=1,b=d=j=0,l=r=m=1. The remaining equations are the U=14 equations just solved. The only valid packing consists of the edge-path 28-29 and the path

```
T: 1-7-6-11-10-9-8-2-3-4-5.
```

  This has exterior pairing 01,34. The other two choices produce precisely the two isolated cycles excluded in the U=14 case.

A pair of spanning two-path packings on opposite sides gives one global cycle exactly when the two endpoint pairings differ. With equal pairings it gives two cycles. This follows by contracting each path to a labelled edge on the four ports: unequal perfect matchings form a four-cycle, while equal matchings form two distinct doubled edges. No multiplicity is suppressed.

Consequently the complete compatible exterior fibres when cut 2 is absent are as follows, with no representativeness assumption:

| Local type in X | Compatible complete exterior fibre |
| --- | --- |
| P=(01;01), lost | R1, R2, R3 |
| (14;14), survivor | S |
| D=(0134;01,34), lost | (1-28) together with each Ri after deleting initial 1,28 |
| (0134;03,14), survivor | (28-29) together with T |

The cut labels are attached at (1,5,6,28,29), so the endpoint labels in this table are literal, not a relabelled exterior. Together with the prescribed eleven-type list, this yields an exact survival criterion for any recovered Hamiltonian H:

H survives iff [2 in U] OR [theta=(14;14)] OR [theta=(0134;03,14)].  (16)

Indeed the other nine listed survivors use 2; both lost types omit it; and the calculation above exhausts all possible no-2 completions. If cut 2 is used, (15) and the noncrossing disk pairing rule give exactly the remaining three two-port types 02,12,24 and the two noncrossing pairings for each of 0123,0234,1234, all in the given survivor list. This argument uses the full eleven survivors and both lost fibres, rather than imposing use of cut 2.

### 6.3 What the complete fibres add, and what they do not yet prove

Let L_A(X) be the collection of all spanning cycle-free local packings in X that use exactly the two patch routes of Section 6.1 and have a compatible exterior packing. This is a collection of actual packings, not source states. By completeness, each such packing is in the complete fibre of its full type, and every compatible product is available. Taking any compatible exterior packing then yields an actual Hamiltonian cycle with complementary matching containing A. Conversely every A-containing Hamiltonian complement restricts to a member of L_A(X). Thus ORIGINAL E183 is exactly

L_A(X) intersects (union of the eleven survivor fibres) != empty. (17)

The known q proves L_A(X) intersects P != empty; for this q all three Ri are available as completions, by the table. Similarly any member of L_A(X) of lost type D would have all three displayed compatible exterior completions. These are fully specified exterior witnesses for conditional actual local packings, NOT a new fully hypothesized graph example and NOT a claim that any such completion has a paired-state preimage.

The hypotheses also give, for each of the eleven survivor types theta, a nonempty complete fibre F_theta(X). They do not state that a member of F_theta uses the two routes in Section 6.1. That is the missing simultaneous constraint. Choosing a different Ri for fixed q never changes E(H) intersect E(X), its used ports or its pairing. In U=0134 the opposite exterior pairing determines which local pairing can be completed, but cannot change the local pairing. In particular replacing a D-compatible exterior by the T exterior, while holding the local D packing fixed, produces TWO cycles, not the desired survivor.

One can make the route restriction more concrete without any source terminology. Delete the six patch vertices. For an A-containing matching the residual complement has degree one at each of a',b',c',d' and degree two elsewhere in G-C. It consists of two paths and possible cycles. Adding the fixed pair (a'b')(c'd') through the patch is Hamiltonian exactly when there is no residual cycle and the two residual paths cross-pair these four named terminals, as in the paid I183 reduction. To recover the five-port type one must retain the actual cut edges and trace the full lifted paths in X. In particular residual matching/connectedness alone does not decide between the two 0134 pairings. Terminals that happen to be original ports require both incidence labels to be retained when doing a local X-C trace; a zero-length interval between such labels cannot be dropped.

There is also no reason merely from a survivor's existence that it visits the patch through all four continuations. A local cycle-free spanning patch restriction can use two continuations. For example the patch paths a-b-y-x-c-d and b-a-x-y-d-c use only their two end continuations. With all four, the other feasible route pairing is (a'c')(b'd'), through a-x-c and b-y-d with xy omitted. These are actual local edge patterns, not assertions of global realizations. They show exactly which patch-routing condition is absent from the statement that a survivor fibre is nonempty. No hypothetical pattern is used as a counterexample to the full assumptions.

### 6.4 The precise remaining source implication and quantifier boundary

Let F_eta be the partnered forest states satisfying eta=1, and let I_eta={H_s:s in F_eta} for this particular root t_x and f_0. Sections 1–5 prove I_eta is nonempty and every member freezes A. The converse WITHIN the source image also holds: if recovered M_s contains A, I187's endpoint necessity forces s(t_b)=v,s(t_d)=w, hence eta=1. Thus I_eta is exactly the A-containing part of this fixed-root source image. It is not asserted to contain every A-containing Hamiltonian cycle.

The unpaid sufficient implication for the present route is now specifically

[all exact hypotheses in Section 0]
   => exists s in F_eta with
      (2 in U_s OR theta_s=(14;14) OR theta_s=(0134;03,14)).    (18)

Equivalently the nonempty marked image must not concentrate entirely on the P,D rows of the exact exterior table. This is the sole remaining existential obligation in this route: faciality, all dual names, consistent fixed phase, retained groups, nonvanishing for eta, parent edges and Hamiltonian recovery have been paid. No fully hypothesized instance is given on which concentration occurs, so (18) is neither proved nor refuted here.

For clarity, an identically nonzero survivor-marked sum is not a distinct mysterious extra condition once generic permissible weights are chosen; it is an equivalent expression of (18) INSIDE the source image. There are finitely many groups and their strict positive L^+-L^- inequalities hold on an open neighborhood of the source weights. Distinct states have distinct incidence vectors, so equality of their omega weights is a proper linear hyperplane. A small perturbation avoiding the finitely many such hyperplanes preserves all the strict inequalities and makes all omega(s) distinct. Fixed-s cancellation still gives

Z_{eta,surv}(z)=sum_{s in F_eta, theta_s survivor} alpha_s exp(z omega(s)).

If this set is nonempty, its largest real exponent dominates as z tends to positive infinity, with nonzero coefficient alpha_s; the sum cannot vanish identically. If the set is empty, it does vanish. This elementary argument proves the claimed equivalence, without proving that the set is nonempty. In particular one cannot add a survivor indicator to the orientation product of Section 4 and retain its sign argument without showing how that indicator behaves under the independent reversals. It depends on the recovered white tree and full path tracing, neither fixed by the local u-v-w direction.

The original target (17) could hold outside I_eta. Without surjectivity, failure of (18) would not itself refute E183. Conversely, there is already a lost A-containing H_0, but its canonical state meets the source criterion only if its opposite-edge graph is a forest with one root per component (I187 Section 4). That test is not proved for any of the three q completions here. The exterior table supplies no substitute for it. This is why neither a lost source-image example nor an E183 counterexample has been claimed.

### 6.5 Original verdict and contribution boundary

**E183: UNRESOLVED.** Leads A–E are verified as scoped deductions. Lead F remains unresolved at precisely (18) for the source route, and (17) for the full original quantifier. The exact exterior calculation leaves both lost rows compatible with the forced patch routes whenever the corresponding local frozen packing exists; it does not demonstrate their occurrence in I_eta. No universal survivor proof and no fully hypothesized counterexample have been written.

The nonempty frozen image is technical progress only, not a substantial finding. Eight accepted, two remaining; neither correctness nor contribution gate is lowered. There is no new implication for Z184, exchange, (T), Q164 or E182/E181/H180/L179. The known sufficiency Z184=>E183 is unchanged; neither a converse nor strict separation is proved. The parked ear mechanism was not restarted, and no sequel is initiated.

## 7. Source and validation limits

The retained pinned manuscript was read in full, main TeX lines 1–838, and authenticated to the supplied SHA-256. The source operations actually used are prop:pairs (245–345), lem:disk (354–403), lem:cancel (446–483), lem:circulation and spoke detours (485–561), eq:group-product and eq:leading-coefficient (525–589), lem:root-components (598–614), white-tree recovery (623–660), lem:P-forest (663–718), and lem:duality (189–206). Its separating-triangle assembly (720–758) was read but is not required after I187's paid cut proof. Root-edge avoidance and Pfaffian P4 conclusions (794–828) are not upgraded into the combined prescription.

All five I187 outputs, its brief and finalized disposition were read. The focused I183 final analytic review and I184 brief were read for the exact continuation and quantifier boundaries, and I164 Section 5 for the image/multiplicity limit. Their old task instructions were not reactivated. The family-180 catalogue entry and the complete preprint listing were checked for focused companion paths; the retained README was read. No external cited theorem, remote priority claim or unread companion result is invoked.

Validation consists of the written deductions above, manual checking of each listed exterior path and the binary case exhaustion, plus input hashing and document integrity checks. There was no graph/state/matching scan, research code, experiment, historical replay/control rebuild, source copy, snapshot/seal, further agent, shared-ledger edit, staging, commit or publication. The inherited controls were not rerun. This is not independent review or proof-assistant verification, and no new-to-literature claim is made.
