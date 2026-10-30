# R162CB — full author proof of the frozen statement

This proof is relative to the stipulated operative proofs of Source162 at commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. It does not audit those proofs. The frozen statement is STATEMENT.md, SHA256 b69dd8585357682a27bb327cfcd789ebab99c828c00f928ec79322e1b525f53a. All conclusions below concern integral vertex covers of one finite hypergraph. Auxiliary weighted counts in one case are bookkeeping, not fractional-cover claims.

## 1. Source input and one fixed configuration

Use the extension-field manuscript, actual build/paper.tex and its construction.tex, incidence.tex, linecover.tex and selection.tex. The balanced manuscript supplies the three elementary appendix estimates used by that proof. In particular, use the extension manuscript's Lemma lem:gadget, its entire ambient-placement construction, Lemmas con-deletion-count and con-pool-properties, and the conflict-free selection satisfying con-separation and con-selected-line-bound. Its constants are chosen once in the source order. None is retuned independently for a different cover below.

There is a threshold s_0, enlarged to be at least 7, such that for each prime s>=s_0 with s=2 modulo 3 the source supplies the following small-plane data. There is a set Y in F_s^2, obtained by omitting one affine line ell_t in each finite nonzero slope t in F_s^*. Every other line of each such slope contains at least five points of Y. The map

    f(x,y)=(x^3,y)

is a bijection and preserves the horizontal and vertical parallel classes. Every affine line contains at least s/8 points of f(Y). Most importantly, any cover of f(Y) by a lines and b individual points satisfying a+b/2<=s must have a=s, b=0 and its lines must form one full parallel class. In particular, f(Y) cannot be covered by fewer than s lines or by at most s lines containing two nonparallel lines. Repeated resources may be removed before applying this assertion.

Fix these s,Y and omitted lines. For every sufficiently large odd n, put q=s^n. All proper subfields of F_q have order at most q^(1/3), as proved in the source. The source's own incidence and independent-deletion arguments apply at these q; no prime-plane stability theorem is applied at q.

The selected source groups are indexed by I=Lambda disjoint-union {*}, where Lambda represents F_q^*/F_s^* and includes 1. Their selected embedded subplanes and retained exceptional points are

    P_i=b_i+M_i(F_s^2),       Y_i=b_i+M_i(Y).

For lambda in Lambda, M_lambda(x,y)=(x,lambda y), S_lambda=lambda F_s^*, and A_lambda={0,infinity}. In particular M_1 is the identity. Choose distinct u,v in F_s^* as in the source. The extra map is M_*=[[1,1],[u,v]], S_*=P^1(F_s) minus {u,v}, and A_*={u,v}. Each S_i has s-1 directions, A_i has the two images of the axes, and the join directions in P_i are exactly S_i union A_i.

Every ambient direction d belongs to z_d in {1,2} of the S_i. The doubled directions are exactly

    T=F_s^* minus {u,v},      |T|=s-3,

and the two groups in every doubled direction are 1 and *. The conflict sets are D_1=D_*=P^1(F_s), with D_i=S_i for the other groups. They contain S_i, and contain A_i for i=1,*.

The selected groups satisfy the following source separation property:

    i != j, dir(ell) in D_i, ell meets P_i  =>  ell misses P_j.       (1)

The P_i are pairwise disjoint. Let B_i be all ambient lines of directions in S_i meeting Y_i, let B=union_i B_i, and let

    X=F_q^2 minus union_{ell in B} ell.

For every d in S_i there are exactly s-1 lines of B_i in direction d, each containing at least five points of Y_i. No line belongs to B_i and B_j for distinct i,j, by (1).

The SAME sampled pool and selected translates supply constants delta>0, rho=delta/10, independent of n, with the following properties:

(a) Every set of at most q lines covering X contains at least (1-rho)q lines through one projective point p. This follows from X containing X_pool and con-pool-properties(i).

(b) Every line ell not in B contains at least delta*q/2 points of X (con-selected-line-bound).

(c) For every finite p and line ell not through p, at most five groups i have any selected point y in P_i intersect ell whose join to p has direction in S_i. This is the selected consequence of con-pool-properties(iii), which was established for every candidate in the common pool.

Increase the n threshold to ensure delta*q/2>1+rho*q. The source guarantees all the preceding properties simultaneously for every sufficiently large odd n after s,Y and the constants are fixed.

The original source hypergraph G has parts indexed by directions d. An ordinary point x in X contributes an edge e_x consisting of the ordinary line label o_{ell_d(x)} in every direction. An exceptional point w in Y of group i contributes e_{i,w}, with label

    v_{i,d,L_{t_i(d)}(f(w))}      when d in S_i,
    o_{ell_d(b_i+M_i w)}          when d not in S_i.                (2)

All special labels are tagged by group and direction. Here t_i(d) is the unique finite nonzero small-field slope mapped to d. The source proves that G is simple and intersecting. We will use its stronger label rules directly and prove the covering property anew for the quotient, not infer it from tau(G).

## 2. Labels and the omitted ordinary lines

First discard isolated labels of G. Exactly the ordinary labels o_ell with ell in B are isolated. Indeed such ell belongs to some B_i with dir(ell) in S_i. Its points yield no ordinary edges; exceptional edges of group i use special labels in this direction, and (1) makes ell miss every other P_j. Conversely, if ell is not in B, property (b) supplies ordinary edges using o_ell. Every special label is nonisolated because each small-plane line meets f(Y).

It follows that the number of nonisolated labels in direction d is

    q - z_d(s-1) + z_d*s = q+z_d.                                (3)

All ordinary lines counted as deleted are distinct, and all special labels are distinct, so this is an exact count.

For each d in T let O_d be the AMBIENT extension of the omitted small-field line ell_d in group 1, translated by b_1. It has direction d and meets P_1, but it misses Y_1. It also misses every P_j with j!=1 by (1), because d is in D_1. Consequently:

(i) O_d is not in B. It cannot be a group-1 deletion line because it misses Y_1, and it cannot be another group's deletion line because it misses that group's subplane.

(ii) Its ordinary label o_{O_d} is nonisolated and belongs to no exceptional edge of any group.

(iii) Two distinct O_d have distinct directions and meet at a point of P_1. To see this, undo b_1: their equations have coefficients in F_s and distinct slopes, so their unique intersection is in F_s^2.

Choose for each d in T any one small-plane line L_d of slope d, and let v_d=v_{1,d,L_d} be its special label in group 1. There is no requirement to coordinate or optimize these choices. Make the disjoint identifications

    o_{O_d} ~ v_d                  (d in T),                       (4)

and no other identifications. Each pair is in one part; different pairs are in different parts. Write m_d for the resulting label and pi for the quotient map on nonisolated vertices. The hypergraph H is the set of images pi(e) of the edges of G, with the inherited direction parts.

Each part still meets every edge in exactly one vertex. By (3), each doubled part loses exactly one vertex, and other parts lose none. Thus every part has exactly q+1=r vertices. Every resulting label is nonisolated, since every original retained label was nonisolated.

A quotient label has at most one ordinary representative. In particular m_d represents precisely the line O_d on the ordinary points X, even though it also covers the exceptional positions of L_d in group 1. Distinct quotient labels having ordinary representatives have distinct representative lines. By (ii), the exceptional action of m_d is EXACTLY that of v_d; its ordinary component adds no exceptional positions. This fact will control all additional labels in every cover case.

## 3. Pairwise intersections and simplicity

We first record the implicit linearity of G, directly from its original labels, as a paid source interface.

Two distinct ordinary edges share precisely the ordinary label of their joining line. An ordinary edge and an exceptional edge have distinct base points and share precisely the ordinary label of their join: the source deletion condition puts its direction outside the exceptional group's S_i, and ordinary edges have no special labels. Two exceptional edges from different groups share precisely their unique ordinary join label, by (1), and cannot share special labels because those are group-tagged.

For two distinct exceptional edges in one group i, any possible shared ordinary label must be along their original small-plane joining direction, hence in S_i union A_i. Directions in S_i have been replaced by special labels, so ordinary sharing can only occur along an axis in A_i. The transformed points f(w),f(w') have a unique joining direction. If it is an axis, preservation of the axis parallel classes supplies exactly that original ordinary label and no common special label. If it is nonaxis, the original coordinates agree on neither axis, and exactly one common special label is present, in the transformed joining direction. Thus every distinct pair of edges of G has exactly one common vertex.

We next show that

    X intersect P_i is empty for every i.                         (5)

If p=b_i+M_i a were an ordinary survivor in P_i, then for each nonzero small slope t the small-plane t-line through a would have to be the omitted ell_t. Otherwise it contains at least five points of Y, so its ambient extension is a deletion line through p. All s-1 omitted lines would therefore pass through a. Their complement Y would be contained in the union of the horizontal and vertical lines through a: every other point has a nonzero finite joining slope to a and lies on one of the omitted lines. Since f preserves these parallel classes, f(Y) would be covered by the two nonparallel coordinate lines through f(a). This contradicts the source small-plane cover obstruction (s>=7). This proves (5).

By (iii) and (5), an ordinary point x in X lies on at most one of the O_d. Therefore its edge e_x acquires at most one merged label of type m_d in place of an ordinary label. No exceptional edge originally contains any o_{O_d}. Among exceptional edges, (4) simply renames selected special labels, so introduces no new pairwise intersection. Among ordinary edges, it simply renames selected ordinary labels and likewise introduces no new intersection. Between an ordinary edge and an exceptional edge, at most one new common label can be introduced; the exceptional edge must belong to group 1 for this to happen.

Old common labels remain common under the quotient, so for any two distinct ORIGINAL edges e,f,

    1 <= |pi(e) intersect pi(f)| <= 2.                             (6)

Since every image edge has r>2 vertices, (6) also implies that no two distinct original edges have the same image. Thus H is simple, and (6) proves the frozen pairwise intersection assertion. In particular it is intersecting.

## 4. An arbitrary small quotient cover forces a pencil

Suppose, for contradiction, that C is a vertex cover of H with |C|<=q. Use every selected label with an ordinary representative as that representative line. These distinct lines cover X: pure special labels cover no ordinary edge, and each m_d covers ordinary edges precisely on O_d. By property (a), at least (1-rho)q representative lines pass through one projective point p.

Every line ell through p which is not in B must have its corresponding quotient label in C. If it were absent, representatives through p would cover at most the single point p on ell (zero such points if p is infinite). At most rho*q selected labels remain outside the large pencil subcollection, and each contributes at most one point of X on ell. Pure special labels contribute none and merged labels still have only one ordinary representative. This would give

    |X intersect ell| <= 1+rho*q < delta*q/2,

contrary to (b).

Let F_p be precisely these forced quotient labels for the undeleted lines of the pencil. They are distinct, because representatives are injective. Call C minus F_p the additional labels. Let

    a(p)=|{d in T: p lies on O_d}|,

with the usual incidence convention at infinity. The ordinary components of F_p act just like the forced pencil in the source. The ONLY new exceptional coverage supplied by F_p consists of the a(p) special lines L_d of group 1 associated with these O_d. We call these the free special resources. They have not been removed from the budget: they occur inside already counted forced labels, and the following cases account for them explicitly.

## 5. A center at infinity

Let p be the infinite point of direction g. The z=z_g groups with g in S_i contribute precisely z(s-1) deletion lines of direction g. Thus

    |F_p|=q-z(s-1),       |C minus F_p|<=z(s-1).                   (7)

Ordinary components of F_p cover no exceptional edge of these groups, since those groups use special labels in direction g.

If z=1, then g is not in T and a(p)=0. All exceptional positions of the one affected group must be covered by the at most s-1 additional labels. For each additional label its action on this group is contained in a single small-plane line: this is con-label-action for old labels, and for a merged label its action is precisely one group-1 special line or is empty. Therefore f(Y) would have a cover by at most s-1 lines, a contradiction.

If z=2, the two affected groups are 1 and *, g belongs to T, and a(p)=1. There is exactly one free special line of group 1. For each affected group translate a covering label into the source line-and-point resources: a special label or an ordinary axis-direction label gives one line of weight 1; a nonaxis ordinary label meeting that group gives at most one point, of weight 1/2; a label meeting no position contributes zero.

Each additional label contributes at most 1 to the SUM of these weighted counts across groups 1 and *. A merged label contributes only its group-1 special line. An unmerged special label is confined to one group. An ordinary axis label meeting one of these groups cannot meet the other by (1), since A_1 is contained in D_1 and A_* in D_*. Every remaining ordinary label contributes at most one singleton to each group, with total weight at most 1. These possibilities exhaust all additional labels.

The free special line contributes at most 1 to the same total. Yet each copy of f(Y) requires weighted cover cost at least s. Using (7), the resulting contradiction is

    2s <= (total weighted cost) <= |C minus F_p|+1
       <= 2(s-1)+1 = 2s-1.

This excludes every infinite center. These weights measure actual resources on the two fixed exceptional copies; no fractional transversal is asserted.

## 6. A finite center in one embedded subplane

For finite p let

    h_p=|{ell in B: p lies on ell}|.

The pencil has q+1 affine lines, so

    |F_p|=q+1-h_p,       |C minus F_p|<=h_p-1.                    (8)

If h_p=0 there is already a contradiction. Thus assume h_p>=1.

Suppose p belongs to P_i. By (1), every deletion line through p comes from group i, so h_p<=s-1. As in the source, the ordinary components of F_p can cover exceptional positions of group i only on the two coordinate lines through f(M_i^(-1)(p-b_i)). Indeed an exceptional base point distinct from p has joining direction in S_i union A_i; an altered direction gives no ordinary label, and the other possibilities are the two axes. A base point equal to p, if present, is on both axes as well. We may include both full axes as covering resources whether or not both ordinary labels are in F_p.

If i!=1, every O_d misses P_i, so a(p)=0. Each additional label acts on group i within one small-plane line or acts trivially. Thus the two axes together with the additional labels would cover f(Y) by at most

    2+(h_p-1)<=s

lines containing two nonparallel lines, contrary to the small-plane obstruction.

If i=1, put a=a(p). In each of the a directions d with p on O_d, the line of that direction through p is omitted from Y_1 and is not a deletion line. These are distinct directions of S_1, and every deletion line through p is in another direction of S_1. Consequently

    h_p+a <= s-1.                                                (9)

The forced labels cover this group's exceptional positions within the two axes and the a free special lines. Every additional label again supplies at most one small-plane line. By (8) and (9), this gives a cover of f(Y) using at most

    2+a+(h_p-1) = 1+a+h_p <= s

lines containing the two nonparallel axes. Removing repeated replacement lines preserves those two distinct axes and reduces the count. This contradicts the source obstruction. Thus all internal finite centers are excluded, including points of P_i outside Y_i.

## 7. A finite center outside all embedded subplanes

Suppose now p is finite and outside every P_i. Two lines of B_i through p would have distinct small-field directions, and their small-field equations would intersect inside P_i. Therefore each group contributes at most one deletion line through p. Different groups contribute distinct lines by (1). The h_p deleted pencil lines thus come from h_p distinct groups.

Choose five distinct points of Y_i on each group's contributing deletion line, using con-deletion-count. Let W be the resulting set of 5h_p exceptional EDGES, with their original point parameters retained. They remain distinct in H by (6).

No ordinary component of a forced label covers an edge in W. The unique join of its exceptional base point to p is its contributing deletion line, whose direction is altered for that group. This is exactly the source witness set and missed-by-pencil argument.

There is at most one free special resource: if two O_d passed through p, (iii) would put p in P_1. If there is no group-1 contributing line, that free resource covers no edge of W. If there is a group-1 contributing line, undo b_1. Its equation is

    y=t x+c,            t in F_s^*.

The chosen special line has slope d in T, hence d is nonzero, and has equation Y=d X+b in the transformed coordinates. Its intersections with the transformed original line satisfy

    t x+c = d x^3+b.                                             (10)

This is a nonzero polynomial equation of degree three over F_s, because d!=0. It has at most three solutions. Thus the one possible free special resource covers at most three of the chosen five group-1 witnesses, and at most three edges of W altogether. This argument applies to EVERY choice of the special lines L_d made in (4).

Every additional label covers at most five edges of W. For an unmerged special label this follows from its confinement to one group, from which W contains only five edges. For a merged label, its ordinary component belongs to no exceptional edge, so the same statement applies. An unmerged ordinary line through p covers none of W. An unmerged ordinary line ell not through p meets each contributing pencil line in at most one point, and hence covers at most one witness in each contributing group. Every group it meets is one of the at most five groups allowed by property (c). This proves the five-edge bound for every possible additional label.

By (8), the forced labels and all additional labels together therefore cover at most

    3+5(h_p-1)=5h_p-2 < 5h_p

edges of W. This contradicts that C covers H. It also covers h_p=1; h_p=0 was already excluded by the forced-label count.

## 8. Conclusion and quantifiers

Every possible projective pencil center has been excluded. Therefore H has no cover of size at most q, so tau(H)>=q+1=r. Every part of H consists of exactly r vertices and covers every edge, so tau(H)<=r. Thus tau(H)=r.

Sections 2 and 3 prove all remaining frozen assertions: r disjoint parts of size r, one vertex per part per edge, no isolated vertices, simplicity, and intersections of distinct edges of size one or two. All arguments use ONE successful source placement and the SAME Y,X,B,pool,constants and labels throughout. The simultaneous quotient is deterministic after that placement and requires no additional probabilistic event.

Choose s_0 at least 7 and large enough for the source gadget lemma. For each eligible s, choose one permitted Y and its omitted lines, then choose the source constants and an n_0(s)>=3 beyond all source thresholds and delta*q/2>1+rho*q. For EVERY odd n>=n_0(s), use the source's successful placement at q=s^n and apply (4). This is the exact order of quantifiers in the frozen statement. The proof provides no numerical threshold, efficient constructor, fractional equality, linear quotient or theorem for other ranks.

End of full author proof. Independent adversarial correctness and actual-primary contribution review remain unassigned and belong to the parent.
