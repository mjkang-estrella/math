# Elementary cubic-cap construction: author derivation

This is mathematical coauthor assistance, not an independent campaign review or gate. The unchanged full research target is simultaneous absence of every bigeodesic for every nonatomic iid law on finite [0,infinity), without moments or fixed directions. The lemmas below do not complete that target. Bounded-support cases are already source-paid. Source212's stipulated theorem has the minimum-of-four second-moment assumption; it is not applied to the dependent cap field.

Let E be the unoriented nearest-neighbor edges of Z². Let (t_e) be iid with nonatomic law G, all weights finite. Work on the probability-one event t_e>0 for all e. Choose M>0 with q=P(t_e>M)<1/3. Independently let U_e be iid uniform on (0,1). An open edge means t_e<=M. Let L_e be the least length of an open simple primal circuit strictly enclosing both endpoints of e. Set

  K_e=M(L_e^3+U_e),  s_e=min(t_e,K_e).

The auxiliary circuit C_e used in proofs is any measurable translation-covariant choice of a length-L_e circuit. It is not needed to define the cap. For example enumerate circuits by length, then by the finite vertex list translated relative to the lexicographically first endpoint of e. This gives such a choice. Caps themselves inherit all lattice symmetries regardless of the tie convention.

## 1. Protecting circuits and their tails

For a fixed finite inner square Q containing e and a concentric outer square of radius R, planar annulus duality says that failure of an open circuit separating Q from the exterior of the outer square implies a closed dual crossing from the inner to the outer boundary. Erase loops. Its length is at least R-c_Q, its starting dual edge has O(|boundary Q|) choices, and after the initial step each next step has at most three choices. Independence of closed-edge indicators bounds the failure probability by

  C_Q sum_{k>=R-c_Q}(3q)^k <= C'_Q exp(-cR).

The dual/primal boundary convention can be shifted by two lattice units so that the separating circuit strictly encloses the specified endpoints. A simple circuit contained in the outer square has at most C R² edges. Fixing a constant-size inner square around e and using translation invariance therefore gives constants A,c,C, depending only on q, with

  P(L_e>A R²)<=C exp(-cR),
  P(L_e>r)<=C exp(-c sqrt(r)).                         (1)

In particular L_e is finite a.s. and has every finite moment. Countability gives this for every e. Applying the same annulus argument to each integer inner box also shows, on one event, that every finite box is surrounded by open circuits arbitrarily far away. These last circuits can avoid any prescribed finite edge set.

Every circuit enclosing a horizontal nearest-neighbor edge has horizontal span at least 3 and vertical span at least 2. Its length is at least twice the sum of these spans, hence L_e>=10; the vertical case is identical. In particular K_e>=2ML_e and K_e>M. Consequently

  0<s_e<=M(L_e³+1),  E[s_e^p]<infinity for every finite p>0.   (2)

More explicitly P(s_e>u)<=C exp(-c u^(1/6)) for all sufficiently large u, with constants allowed to depend on M and G. No independence of different L_e is claimed.

## 2. Atomlessness, unique finite geodesics, and stationarity

Conditional on the entire open/closed indicator field, the t_e retain independent nonatomic conditional laws, and the U_e remain independent uniforms independent of them. Each L_e is then fixed. Hence the s_e are conditionally independent and nonatomic: for any a,

  P(min(t_e,M(L_e³+U_e))=a | indicators)
  <=P(t_e=a | indicators)+P(M(L_e³+U_e)=a | indicators)=0.

A regular conditional version follows directly from the product disintegration over the two status classes. In particular, conditional on all indicators and all (t_f,U_f) with f different from e, s_e is nonatomic. All other capped weights are measurable in that conditioning field. Thus two distinct simple paths with the same endpoints have unequal costs a.s.: choose an edge in their symmetric difference, cancel common edges, condition as above, and use atomlessness at the resulting fixed threshold. A countable union treats every endpoint pair and every competing finite simple path. The original t metric has the same no-tie property by ordinary independence.

One may also deduce atomlessness conditional on the other capped weights by the tower property, since that smaller conditioning field is measurable in the one just used. This is NOT upward finite energy. It is also NOT absolute continuity with respect to Lebesgue measure: singular continuous input is allowed. Freezing U_e as well can create a cap atom and is not the conditioning used in the no-tie proof.

The cap map is translation-covariant and lattice-symmetry invariant. The (t,U) field is iid, so s is stationary and is mixing, hence ergodic, for every nonzero lattice translation. Finite minimizing paths exist by the lower-cost path estimate in shape-and-length.md; positive weights force them to be simple. Thus the no-tie statement really gives unique finite geodesics. Infinite rays exist by the usual locally finite geodesic-tree compactness argument, although no ray selector is constructed here.

## 3. Exact equality of all bigeodesics

The following argument is deterministic whenever all weights are positive and all protecting circuits exist, with K_e>=2M|C_e| and circuit edges unchanged. The latter is automatic: an open edge has t_f<=M<K_f.

Call an edge changed if s_e<t_e. A t-bigeodesic cannot use such an edge e. Both arms eventually leave the finite region bounded by C_e. Its segment between boundary contacts bracketing e costs at least t_e>K_e, while the cheaper boundary arc costs at most M L_e/2. This contradicts t-minimality. Thus the entire t-bigeodesic gamma is unchanged edgewise.

For vertices a,b on gamma and any finite s-walk pi from a to b, eliminate changed-edge occurrences. Fix one such occurrence e and C=C_e of length L. If both a,b are outside or on C, choose a boundary contact before and one after that occurrence along pi; replace that portion by a cheapest C-arc. If a is inside and b outside/on, choose a boundary contact u of pi after the occurrence, and replace the whole prefix to u by a gamma segment from a to a boundary contact w, then a shortest C-arc from w to u. The gamma portion can be chosen between its first and last C contacts; that entire gamma interval costs at most ML/2, because its endpoints have a cheaper boundary-arc competitor. Thus the added prefix costs at most ML. The case b inside is reversed. If both endpoints are inside, replace all of pi by gamma[a,b], which is within that same first/last-contact interval and costs at most ML/2.

Every removed portion contains e, of s-cost K_e>=2ML; every inserted portion costs at most ML. Added edges belong to the unchanged circuit or unchanged gamma. Hence the number of changed-edge occurrences strictly decreases, without any recursive new change. Finitely many steps give a walk using only unchanged edges of cost no greater than the original s-cost of pi. Its t-cost equals its s-cost. Original minimality then proves

  cost_s(gamma[a,b])=cost_t(gamma[a,b])<=cost_s(pi).

Every t-bigeodesic is therefore an s-bigeodesic.

Conversely an s-bigeodesic using a changed edge e would have a boundary-to-boundary segment of cost at least K_e>=2ML_e, while an unchanged C_e arc costs at most ML_e/2. Thus it has no changed edges. Since s<=t, any unchanged s-geodesic segment is also t-minimizing. Both inclusions hold simultaneously for all paths; no measurable bigeodesic selection or countable union over paths was used.

## 4. Finite endpoint sets and exact all-ray-tail preservation

Let E_x={e: x is strictly inside C_e}. A circuit of length L has coordinate spans at most L/2. Since x and the endpoints of e are inside it, e in E_x implies L_e>=c dist(x,e)-C. Equation(1) and the O(r) edges at distance r give

  sum_e P(e in E_x)<infinity.

Borel–Cantelli gives finite E_x, simultaneously for every x. Put B(x)=sum_{e in E_x}t_e, finite a.s., with no asserted moment. Let U_x be the finite vertex set contained in or on the circuits C_e for e in E_x.

For every t-ray or s-ray p rooted at x, each changed edge used by p belongs to E_x. Otherwise p starts outside/on C_e and eventually exits that finite circuit, and the boundary shortcut just used contradicts minimality. This holds for every rooted ray, not just a chosen ray.

Every s-ray consequently has an unchanged tail, which is a t-ray by s<=t. For the nontrivial reverse inclusion, take a t-ray p from x and cut after its last visit to U_x. This tail is unchanged. Consider two tail vertices a,b and an s-competitor pi. For any changed occurrence e on pi:
- If e belongs to E_x, both a,b lie outside/on C_e and the pure circuit shortcut applies.
- Otherwise x lies outside/on C_e. When a tail endpoint is inside C_e, connect it to a FORWARD exit contact of p with C_e. Its original cost is at most ML_e/2: bound it by the whole p interval from the first to last C contact, whose original minimality bounds that interval by a shortest C arc. The forward portion lies after the inside tail endpoint, so all its edges are unchanged. Then complete the replacement with a C arc as in the bigeodesic argument.
- When both endpoints are inside, use p[a,b], which is unchanged and costs at most ML_e/2 by that same interval bound.

Thus all inserted edges are unchanged, and elimination of changed occurrences proves s-minimality of the entire tail. The choice of FORWARD contact is essential bookkeeping: an earlier contact could reinsert capped edges of p's initial segment.

In fact the cutoff can be uniform over all rays rooted at a fixed x. The lower-cost path bound gives a finite bound on the lengths of every t- or s-geodesic from x to any point of the finite U_x. Take the maximum of these bounds over U_x. No rooted ray can visit U_x after that index. This yields a finite random N_x working for all t- and s-rays from x simultaneously. It does not identify their initial portions or supply a canonical bijection of rooted rays/coalescing families. In particular, no assertion is made that the preserved tail can be attached back to the same root x as a ray for the other metric.

## 5. Endpoint metric bounds, with the counting repair

For any x,y, start with a finite s-walk. Eliminate changed edges outside E_x union E_y by boundary-to-boundary C shortcuts. Neither endpoint lies strictly inside the relevant C, so only unchanged circuit edges are inserted. Erase loops. The remaining simple walk uses changed edges only in E_x union E_y, once each. Restoring t-cost adds at most B(x)+B(y). Taking infima proves

  0<=T_t(x,y)-T_s(x,y)<=B(x)+B(y).                       (3)

Along any original ray p rooted at x and any y on it, there is the sharper

  0<=T_t(x,y)-T_s(x,y)<=B(x).                            (4)

To prove this, eliminate only changed occurrences outside E_x. If y lies inside such a protecting circuit, use a forward p segment from y to its exit and a circuit arc, as above; the added t-cost is at most ML_e. These added ray pieces may themselves contain changed edges, but only from E_x. Therefore the strictly decreasing count must be the number of changed-edge occurrences OUTSIDE E_x, not the total number of changed occurrences. After all those have been removed, loop erase and restore the remaining E_x edges once each. This proves(4) without assuming the whole rooted ray was uncapped.

Neither(3) nor(4) yields a uniform original-metric shape theorem. B(x) is only finite, and stationarity alone does not make it uniformly sublinear.

## 6. Finite cap influence: stronger pathwise statement

By(1), for every rational eta>0,

  sum_e P(L_e>=eta(1+|e|))<infinity.

Thus L_e/(1+|e|) tends to zero uniformly outside growing boxes, almost surely. Intersect with the event of open circuits around every finite box from section1. On this ONE event, let t' be ANY positive finite configuration differing from t on a finite edge set F, and keep all U fixed. All new protecting circuits exist: take an old open circuit sufficiently far around F and the desired edge, disjoint from F.

For all sufficiently distant e, L_e<dist(e,F) in a fixed lattice norm (adjust an absolute geometric constant if using another norm). A circuit enclosing e and meeting F must have length at least dist(e,F). Hence an old shortest C_e avoids F and remains open, so L'_e<=L_e. Any new minimizer has length <=L_e and also avoids F; it was therefore open before, giving L_e<=L'_e. Thus L'_e=L_e away from a finite set, and s'_e=s_e there.

This does not require absolute continuity of a second marginal. Absolute continuity is still needed in other arguments to transfer almost-sure selector/label statements to a modified law. If originals only increase, open circuits can only disappear, so L'_e>=L_e and s'_e>=s_e everywhere. An unchanged original edge of an already uncapped path then remains uncapped. These facts do not identify an abstract selector in the modified field.
