# I193 analytic attempt

Status: COMPLETE written assignment, PARTIAL mathematical resolution. Sections 1–8 are finalized; original-target verdict UNRESOLVED at J193. No universal coefficient exclusion or failing graph has been established. Written deductions only; no computation, experiments, or historical replay. Earlier PARTIAL versions were updated incrementally within this same unsealed record.

## 1. Domain and the exact equality reduction

Let B consist of finite simple undirected cubic bipartite planar 3-vertex-connected graphs with a specified embedding. An admissible step deletes disjoint facial edges e=uv and f=xy in cyclic terminal order u,v,...,y,x,... and inserts new vertices p,q,r,s with arms up,vq,xr,ys and square pq,qs,sr,rp. Both G and H must belong to B. All assertions below use this full I168–I170 domain and therefore hold on its brace steps; brace means that every two disjoint edges extend to a perfect matching. No all-brace generation theorem is assumed.

All vector spaces are over Q. Objects denote incidence vectors, edges unit vectors, and diff(F) the span of pairwise differences, zero for an empty or singleton family. Put K=G−{e,f}, D_G=diff(HC(G)), d(G)=dim D_G. The complete old Hamiltonian classes Nij have e,f statuses i,j; S=N10∪N01∪N11 and L=diff(S). The new exterior classes are spanning ux paths Pux, spanning vy paths Pvy, and cycle-free spanning two-path covers D11 paired uv,xy. Set

    V=diff(N00), U=diff(Pux)+diff(Pvy)+diff(D11),
    ell=d(G)−dim L, t=dim(L+U)−dim L,
    b=P+Q+D+2e+2f−3C0, eta=dim(L+U+<b>)−dim(L+U).

Here C0∈S and P,Q,D belong to the indicated classes. The actual manuscript cor:pfaffian-paths, lines 812–828, supplies all six nonempty classes: the child paths p-r-s-q, r-p-q-s, p-q-s-r, q-p-r-s, u-p-r-x, u-p-q-v force respectively N10,N01,Pux,Pvy,D11,N11. For the four square paths the endpoints must use arms, since closing only the square is not spanning. For the last two paths degree saturation excludes the competing square edges and forces the other two-arm segment. These are existence deductions, not rank assumptions.

R168's exact identity is

    d(H)=2+dim(L+U+<b>),
    d(H)−d(G)−2=t+eta−ell,   eta∈{0,1}.             (1)

It includes all cross-class offsets. Its projection on child differences is pi=(arm_up−arm_vq, square_pq−arm_xr). Transported differences have image zero; the three new-class reference differences have images (1,0),(−1,1),(0,−1). Their unique image relation is their sum, which pulls back to b under the homogeneous transport map T0. The remaining kernel pulls back to L+U. This explains both (1) and representative independence.

Assume the complementary arc a=ux is one edge; interchange roles if vy is short instead. Degree two in K forces a in every N00 cycle and in every Q∈Pvy. The exact bijections N↦N−a from N00 to Pux and Q↦Q−a from Pvy to D11 follow by deleting/adding that edge. For the second map, deleting a separates u,x; the crossing pairing u-y,v-x is impossible in the complementary disk, leaving uv,xy. Adding a to that cover joins its components. Thus N00 is nonempty and, with Z=diff(Pvy),

    U=V+Z, W'=L+V+Z=L+U,
    r=N−C0, F_Q=Q−a+e+f, z=F_Q−C0,
    b=r+2z mod W', t≥ell−1.                        (2)

F_Q is an actual spanning two-factor with exactly two components: Q−a has the uv and xy paths, and e,f close them separately. In particular F_Q is not a Hamiltonian cycle. Choosing P=N−a,D=Q−a makes the bridge equality exact before taking the quotient. The bound follows from D_G=L+V+<r>⊆W'+<r>.

If t=ell−1 then dim W'=d(G)−1, and that inclusion forces

    D_G=W'+<r>, r∉W'.                              (3)

If z∉D_G, (2) gives eta=1 and exchange. Otherwise the one-dimensional quotient has a unique coefficient z=lambda r mod W'. Its normalized functional w has w(r)=1, and

    eta=0 iff lambda=w(z)=−1/2.                     (4)

Changing Q changes z by Z, changing N changes r by V, and changing C0 changes both by L. Thus lambda is independent of all anchors. Extend w linearly to edge coordinates if desired; every such extension has the same value on z∈D_G. No extension value on z outside D_G is intrinsic. The affine functional h(C)=w(C−C0) is 0 on S and 1 on N00.

For a quadrilateral write a'=vy, s0=e+f−a−a'. All three new classes are translates of N00, so U=V. Taking Q=N−a' gives z=r+s0, b=3r+2s0. When s0∈D_G, alpha=w(s0), lambda=1+alpha, and failure is exactly alpha=−3/2. All these statements are inherited reductions, restated with their hypotheses rather than claimed as new exclusions.

## 2. What the read manuscript operations supply

The retained manuscript was read at lines 60–837, including the full proof body. All stipulated results are accepted as true. The state convention (229–237) is a bijection from nonouter black triangles to nonroot dual vertices. prop:pairs (245–345) supplies two disjoint such states when there is no separating triangle. lem:disk (362–403) has a state-tail hypothesis, and expressly does not apply to arbitrary oriented cycles. These states are not the four-terminal Hamiltonian families in (1).

The cancellation lemma (446–483) cancels partners of a fixed second state with cyclic Q_s, for arbitrary incidence weights a(t,v). lem:circulation (497–519) then CHOOSES special spoke weights with positive counterclockwise circulation. Equations (539–588) use those chosen weights to show a nonzero leading coefficient and hence the existence of a forest state. They do not say that an arbitrary rational edge functional annihilating W' has positive circulation. Reversing all spoke weights already reverses every nonzero circulation, so positivity cannot be a property of arbitrary weights. No map from the present w and F_Q to those state weights with the required sign has been proved here.

The forest-to-cycle construction (591–718) and separating-triangle assembly (720–791) yield induced trees and a Hamiltonian cycle with a facial prescription. cor:edge-avoidance (794–805) gives avoidance of one edge; cor:pfaffian-paths (812–828) gives containment of a three-edge path. Neither states a linear identity, convex representation, or constant-weight reconnection from the specified F_Q. Their stronger use would require a new proof.

The actual Pfaffian definition (807–810) gives odd orientation parity on an even cycle whose vertex complement has a perfect matching. Each of the two components of F_Q qualifies: the other even component has an alternating perfect matching. Thus both component cycles are oddly oriented. This fixes a parity of orientation signs, not the value of the unrelated rational functional w. No relation between w and an orientation-sign vector is supplied by that definition. No external determinant/Pfaffian identity or unread matching theorem is invoked.

## 3. Two deletion pairings on the same quadrilateral

The following deductions use actual complete Hamiltonian families; no formal coefficient pattern is substituted for a graph. Write A for cycles avoiding e,f (the original N00), B for cycles avoiding a,a', and T for all other Hamiltonian cycles. Every terminal has only one edge outside the square, so at least one of its two square edges must be used. A Hamiltonian cycle therefore uses two opposite square edges or three square edges; all four would isolate the square. The whole graph has vertices outside it, since a simple cubic bipartite graph on four vertices cannot exist. Thus A,B,T partition HC(G): A uses a,a', B uses e,f, and T uses three edges. Each of the four three-edge patterns occurs by the actual P4 corollary. A and B are also nonempty, by the six-family theorem and the short-edge bijection applied to the respective admissible expansions. The complementary expansion is admissible: the general connectivity proof in Section 7 below applies to either opposite pair, and the square colors permit both.

Let W_A=diff(B∪T)+diff(A), W_B=diff(A∪T)+diff(B). These are the respective L+V spaces, both contained in D_G. For either pairing their codimension in D_G is zero or one. Fix C*∈T. The codimension of W_A is one exactly when there exists a linear functional h_A on D_G whose affine values h_A(C−C*) are 1 on A and 0 on B∪T. Indeed, such a functional annihilates W_A and is nonzero on an A-anchor; conversely a nonzero quotient normalized on that anchor supplies it. The same equivalence holds for B.

Put sigma(x)=x_e+x_f+x_a+x_a' and g=−sigma on differences. On Hamiltonian displacements from C*,

    g(C−C*) = 1_A(C)+1_B(C).                       (5)

Consequently h_B=g−h_A realizes exactly the B-indicator whenever h_A exists, and conversely. We obtain an exact pairing statement:

    codim_D_G W_A = codim_D_G W_B ∈ {0,1}.          (6)

In their common equality case the complementary square vector is −s0. Since sigma(s0)=0, if s0∈D_G then

    alpha_B=h_B(−s0)=−g(s0)+h_A(s0)=alpha_A.        (7)

Both normalized two-factor values are therefore 1+alpha_A. If s0∉D_G, both pairings have an independent bridge. If the common codimension is zero, both W spaces equal D_G, and eta for either pairing is 1 exactly when s0∉D_G. It follows that the two expanded graphs have the same Hamiltonian affine dimension, and either both expansions satisfy exchange or both fail it. In particular combining the pairings does not replace alpha by −alpha or its reciprocal: it reproduces the SAME forbidden coefficient. This is a proved symmetry, not an exclusion of that coefficient.

## 4. Expanding the newly inserted square

This argument starts with any admissible step, not just a short gap. Keep its notation W=L+U, M=W+<b>, and T0. Let x_P,x_Q,x_D be the differences of the three chosen new-class child cycles from T(C0). The exact projection argument in Section 1 gives

    D_H=T0(W)+<x_P,x_Q,x_D>,
    x_P+x_Q+x_D=T0(b),
    D_H∩ker pi=T0(M).                              (8)

There are no further relations modulo T0(W): a relation's three coefficients must agree by their pi images, and its remaining condition is that this common coefficient times b lie in W.

Now expand the central facial square of H, deleting pq and rs, to obtain J. These are opposite edges, and the step is admissible by the connectivity argument in Section 7. Inspecting the six original fibre patterns, the central-square patterns are as follows. The N10 lift misses pq, the N01 lift misses rs; the Pux lift misses pr, and the Pvy lift misses qs. These four patterns use three square edges. The N11 lift uses pq,rs. The D11 lift uses pr,qs. Therefore the second step's complete lost family is exactly the original D11 fibre.

For a quadrilateral, codimension Delta_c=ell_c−t_c is one exactly when the lost-family indicator is an affine functional on D_H (the elementary criterion just proved in Section 3). Use T(C0) as a surviving base. This indicator must annihilate T0(W), take values 0 on x_P,x_Q, and 1 on x_D. By (8) this is possible exactly when b∉W. If b∈W, applying it to the displayed sum would give 1=0. If b∉W, those assignments respect all relations modulo T0(W), so define the required functional. Hence the unconditional identity is

    Delta_c = eta for the first step.               (9)

The other central deletion pair has the same deficit and exchange outcome by Section 3. Thus when the first bridge is dependent, both central expansions have t_c=ell_c and satisfy exchange automatically. This conclusion alone supplies no contradiction to first-step failure.

There is a sharper written identity on a short gap. Take the aligned anchors P=N−a,D=Q−a and z=D+e+f−C0 as before. Write the central alternating square vector as

    s_c=pq+rs−pr−qs.

It has pi image (0,1), opposite to x_D. Reading the K coordinates and the up,xr arm coordinates of s_c+x_D gives D−C0|K and 1−C0(e),1−C0(f), respectively. These are exactly the coordinates of z under the inverse of T0. Thus

    s_c = T0(z)−x_D,
    s_c∈D_H iff z∈M.                               (10)

Suppose the first step is an equality case with z∈D_G and z=lambda r mod W. If lambda≠−1/2 then eta=1 and M=D_G. Let h_c be the normalized lost-D11 indicator of the second step. Its restriction to T0(W) is zero and h_c(T0(b))=1 by (8). As b=(1+2lambda)r mod W, (10) gives

    alpha_c = lambda/(1+2lambda)−1,
    lambda_c = 1+alpha_c = lambda/(1+2lambda).      (11)

Here lambda_c is the normalized value of the second step's actual disconnected two-factor, and its equality hypothesis is provided by (9). Formula (11) excludes second-step failure except at lambda=−1/4; it does not exclude that original coefficient. This is a conditional formula on actual steps, not an existence claim for any chosen lambda.

Most relevantly, if the first step FAILS, then lambda=−1/2, M=W and z∉M by r∉W. Equations (9)–(10) give Delta_c=0 and s_c∉D_H. For the second quadrilateral step its W_c equals D_H, and its bridge is 3r_c+2s_c mod W_c, so eta_c=1. Equation (1) twice yields exactly

    d(H)=d(G)+1,
    d(J)=d(H)+3=d(G)+4.                            (12)

Both choices of central deletion have this same outcome. Thus a hypothetical failed first step is followed by an automatic extra-rank recovery at the next central step. Iterating the construction or comparing its two pairings supplies no contradiction from dimension arithmetic alone. The failure is compensated, not shown impossible. No graph realizing the hypothesis of (12) has been supplied.

## 5. Structural and parity constraints: proved sufficient conditions and their gaps

### 5.1 Convexity cannot identify the disconnected factor with a cycle average

For any disconnected spanning two-factor F, the exact incidence vector F is not a convex combination of Hamiltonian incidence vectors. If F=Σ theta_i C_i with theta_i>0 and Σ theta_i=1, every edge outside F has zero total coordinate and hence is absent from every C_i. Each C_i is then a spanning degree-two subgraph of the degree-two graph F, forcing C_i=F at every vertex. That contradicts disconnectedness. This rules out an exact convex representation, even in a brace. It does NOT rule out a convex representation after passing to the quotient by W', where some coordinates disappear. Such a quotient representation would be an additional theorem; none is obtained here. Merely observing h=0 or 1 on Hamiltonian cycles gives no bound on h(F_Q) outside their convex hull.

### 5.2 Symmetric differences and an honest conditional subcase

Let C∈S and F=F_Q. Since G is cubic, the two degree-two subgraphs F,C share at least one incident edge at every vertex. After cancelling common edges, each vertex therefore has either no remaining edges or one F-only and one C-only edge. It follows by tracing edges that F△C is a vertex-disjoint union of simple even alternating cycles R_1,...,R_k. Put v_i=1_(F∩R_i)−1_(C∩R_i). Then

    F−C=Σ_i v_i.                                  (13)

Flipping any selection of these cycles yields a spanning two-factor, by the degree count. Connectivity is not preserved by that count. If EACH single flip C_i=C+v_i is Hamiltonian, however, its normalized affine value is 0 or 1. In the equality case this gives

    w(F−C0)=Σ_i w(C_i−C)+w(C−C0)
            =Σ_i h(C_i) ≥ 0,

because h(C)=0. All terms then lie in D_G. Consequently exchange is proved under this explicit single-flip Hamiltonicity hypothesis. This is a sufficient subcase, not a claim that the hypothesis always holds. A single alternating switch already turns N into F on the original quadrilateral, so degree-preserving switching alone cannot supply that hypothesis. No bounded dual-transfer proposal is retried.

More generally, if F_Q−C0 belongs to the integer span of old Hamiltonian differences, its w-value is an integer, since each such difference has value −1,0 or 1. This also excludes −1/2. Rational span membership z∈D_G is insufficient for this integer-span conclusion; the paid prism values lambda=1/(m−2) are already fractional for m>4. This is an arithmetic sufficient condition only.

### 5.3 The precise parity obstruction is a lattice divisibility question

Assume the equality case and z∈D_G. Let Gamma=D_G∩Z^{E(G)}. The rational subspace W' intersects Gamma in a saturated subgroup: if an integer multiple of an element of Gamma belongs to W', that element belongs to W' as well. Since W' has codimension one, Gamma/(Gamma∩W') is a free abelian group of rank one. To see the integral functional explicitly, take the rational linear functional with kernel W', clear denominators on an integral basis of Gamma, and divide its integer values by their greatest common divisor. This gives a primitive homomorphism phi:Gamma→Z with kernel Gamma∩W', unique up to sign. Fix its sign so that

    m=phi(r)>0, k=phi(z)∈Z, lambda=k/m.            (14)

Thus failure requires the exact arithmetic equation 2k=−m. If m is odd, exchange is proved. If m is even, parity alone does not exclude failure. The primitiveness of phi does not imply m=1: a specific primitive edge vector r need not generate the quotient lattice. No universal parity of m is proved here, by brace extension or by the Pfaffian orientation. In particular orientation parity of the component cycles is a different datum from divisibility in this Hamiltonian quotient lattice. Clearing denominators of w without tracking m would be an invalid integrality argument.

### 5.4 What brace matching extension actually adds here

The complement of F_Q is a perfect matching M0, because G is cubic. Each even component of F_Q has two alternating matchings, so F_Q can be split into two perfect matchings M1,M2 by making independent choices on the two components. These assertions follow directly from degrees and alternation, without a matching-polytope theorem. The unions M0∪M1 and M0∪M2 are spanning two-factors, but neither union is forced to be a Hamiltonian cycle by this decomposition. Brace extension guarantees a perfect matching containing any specified pair of disjoint edges; it does not guarantee that the complementary two-factor, or either of these particular unions, is connected. No weighted identity involving Hamiltonian cycles follows just from the existence of these matchings.

This does not prove that no stronger brace argument could work. It identifies the missing connectivity/weight step in this route. No unread brace-generation, matching-polytope, determinant-sign, or reconfiguration theorem is used to supply it.

## 6. Counterexample branch and exact original-target status

No fully specified failing admissible step has been found in this written investigation. The authenticated I168–I170 reports say that all 636 retained labelled steps satisfy exchange, and I170's additional bounded quadrilateral and longer-face collections also contain no failure. Those are historical report conclusions only; their data and code were not opened or rerun here. The formal hypothesis lambda=−1/2 in Section 4 describes the CONSEQUENCES of a failure, not a realized example. Equations (7), (11), (12), and (14) are not graph-construction certificates.

The exact single remaining assertion is:

> **J193 (unpaid).** For every B-admissible short-gap step, take its complete families as in Section 1. If t=ell−1 and F_Q−C0∈D_G, then the unique normalized functional on D_G/W' with w(N−C0)=1 satisfies w(F_Q−C0)≠−1/2.

The quantifier includes brace steps; that restricted assertion also remains unpaid. It is independent of the choices of N,Q,C0 by Section 1. This is exactly equivalent to the requested short-gap exchange theorem: t≥ell−1 is already proved; t≥ell gives exchange by (1); when t=ell−1 but z∉D_G the bridge is independent; and in the sole remaining branch (4) is an equivalence. A counterexample to J193 would give d(H)=d(G)+1, not just failure of a sufficient containment. No weaker statement is being substituted for the target.

**Original-target verdict: UNRESOLVED.** Sections 3–5 prove additional structural identities and conditional exclusions but not J193. The secondary both-long-gap clause of J192 was not investigated, because the primary target did not resolve. Both the long-gap rank clause and its bridge clause remain open. Even a future proof of J193 alone would not establish universal exchange, the affine-fullness target, or Q164. No substantial finding is nominated.

## 7. Settled cases, including the inherited infinite family

For completeness, every unconditional or conditional successful subcase used in this record has a written reason. If ell=0 or t≥ell, t+eta≥ell by eta≥0. The formal case N00=∅ has ell=0 (and cannot occur on a short gap by the path bijection). If t=ell−1 and z∉D_G, then r+2z∉W' since r∈D_G and W'⊂D_G. If z∈D_G with lambda≠−1/2, (2)–(4) give eta=1. On a quadrilateral this becomes s0∉D_G or alpha≠−3/2. The single-flip, integer-span and odd-m subcases are proved in Section 5. When an earlier step has eta=0, either central-square successor has Delta_c=0 and succeeds by (9); if that earlier step actually fails on a short gap, its successors gain exactly three by (12). These statements do not assert that the conditional failure occurs.

All quadrilateral and hexagonal admissible steps have a short gap: their two complementary arc lengths are positive odd integers summing to the facial length minus two. For lengths four and six at least one length is one. This proves applicability of the reduction, not exchange in every remaining equality case.

The paid P169 infinite family remains fully settled. Here is its written proof, reused at its exact scope. Let G=C_m□K2, even m≥4, with rails t_i,b_i and rungs rho_i (indices modulo m). Its Hamiltonian cycles are the m cycles C_i taking all rails except t_i,b_i and only rungs rho_i,rho_(i+1), and two cycles X,Y taking all rungs and opposite alternating rail matchings. For exhaustion, if some but not all rungs occur, the omitted rails in either layer match precisely the selected rung vertices. Each run of selected vertices along the layer is a path and has a unique perfect matching when its length is even; otherwise it is impossible. Thus omissions agree in the two layers. Two or more omitted positions would separate the resulting factor into components, so exactly one position is omitted. If all rungs occur, each layer uses one of its two alternating matchings; equal choices form disjoint squares and the two unequal choices are X,Y. No rungs gives two layer cycles. This proves the list.

In an affine dependence with coefficients c_i,x,y summing to zero, top-minus-bottom rail coordinates force x=y. Put S=Σ c_i. Every rail coordinate then gives c_i=S+x; the affine equation gives S=−2x, so c_i=−x and (m−2)x=0. Hence all coefficients vanish and d(G)=m+1. Coordinate comparison proves

    (m−2)(rho_0+rho_1−t_0−b_0)
      =(m−3)C_0−Σ_(i≠0) C_i+X+Y.                 (15)

The coefficients sum to zero. At the index-zero rails the right side is −(m−2), at other rails zero; at rungs 0,1 it is m−2, and at every other rung zero. Deleting rho_0,rho_1 leaves exactly C_(m−1),C_0,C_1,X,Y surviving; affine independence gives ell=m−3,t=m−4. Modulo L+V the total coefficient of the lost cycles in (15) gives alpha=−(m−3)/(m−2). Deleting t_0,b_0 loses only C_0, gives ell=1,t=0, and the negative of (15) gives the same alpha. Therefore

    lambda=1/(m−2), 3+2alpha=m/(m−2)>0,
    eta=1, d(H)=m+3=d(G)+2.                        (16)

The prism is 3-connected: deleting two vertices either leaves an intact layer linking all remnants or leaves one path in each layer and a surviving rung. It is also simple, cubic, bipartite and plane. More generally the square insertion preserves 3-connectivity for any parent in B whenever its distinct-terminal placement is plane and bipartite. Here are the needed cases. Removing two old vertices leaves a connected parent remainder whose surviving selected edges can be replaced through the intact square; the square attaches to at least two remaining terminals. Removing two new vertices leaves all old vertices connected in G−{e,f}: a cubic simple 3-vertex-connected graph has no edge cut of size one or two. Indeed each side of such a cut has at least three vertices (smaller sides have at least three crossing edges), and deleting its at most two boundary vertices on one side contradicts 3-connectivity. Every surviving new vertex attaches by its arm. With one old and one new vertex removed, the three square vertices form a path. If the old vertex is a terminal, G minus that vertex is 2-connected, and deleting the other selected edge leaves it connected; the square path has remaining attachments. Otherwise every component of (G minus that vertex)−{e,f} contains at least two terminals, since zero would already be disconnected and one would give a bridge in a 2-connected graph. Three square-path attachments therefore meet and join every such component. Fewer deletions are included. Simplicity, cubicity and planarity follow directly from the facial insertion; the required alternating colors give bipartiteness. This validates both prism pairings and the central/complementary expansions used above without a graph test.

## 8. Validation and contribution limits

Validation here means written coordinate comparison, rank-nullity, degree/connection arguments, and checking hypotheses against the actual read sources. There was no research code, graph/state/matching scan, test, experiment, sealed replay or rebuild, source copy, snapshot, seal, further agent, ancestor/shared-ledger edit, staging, commit, archive, publication, or parent bookkeeping. Input and final output hashes are detached byte authentication, not a new computational certificate.

The deductions newly written in this iteration are the paired-deletion symmetry (5)–(7), the central-square relation (9) with the coefficient transport and conditional recovery (10)–(12), and the explicit sufficient-condition/route limits in Section 5. They are not claimed new to the literature or nominated as substantial findings. The actual source catalogue has one family-180 manuscript; no external literature search or companion theorem outside that entry was read or used. E183 and all its named parked dependencies remain parked. Reading its required parking disposition and the required I192 report's historical discussion did not reopen that problem.
