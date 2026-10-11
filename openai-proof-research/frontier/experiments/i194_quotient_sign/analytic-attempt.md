# I194 analytic attempt

Status: COMPLETE written assignment, PARTIAL mathematical resolution. Sections 1–7 finalized; original-target verdict UNRESOLVED at J194. Earlier partial versions were updated incrementally. Unsealed, proof-only written record; no research code or computation.

## 1. Exact target, domain, and inherited reduction

Let B consist of finite simple undirected cubic bipartite planar 3-vertex-connected graphs with a specified embedding. An admissible step replaces disjoint facial edges e=uv,f=xy, in terminal order u,v,...,y,x,..., by arms up,vq,xr,ys and square pq,qs,sr,rp on four new vertices; both G and its child H belong to B. The brace restriction additionally requires every two disjoint edges to extend to a perfect matching in the graphs in question. No all-brace generation assertion is assumed. All spaces below are over Q; objects in vector expressions are incidence vectors.

Put K=G−{e,f}, D_G=diff(HC(G)), d(G)=dim D_G, where diff means the span of pairwise differences. Nij is the COMPLETE family of Hamiltonian cycles using e,f with statuses i,j. Set S=N10∪N01∪N11, L=diff(S), V=diff(N00). Pux and Pvy are the complete spanning path families in K, and D11 is the complete family of cycle-free spanning two-path covers paired uv,xy. Put U=diff(Pux)+diff(Pvy)+diff(D11), ell=d(G)−dim L and t=dim(L+U)−dim L. Choose C0∈S and representatives P,Q,D of the three new families. R168 gives

    b=P+Q+D+2e+2f−3C0,
    eta=dim(L+U+<b>)−dim(L+U) ∈ {0,1},
    d(H)−d(G)−2=t+eta−ell.                         (1)

These are inherited exact identities, including cross-class offsets. The actual cor:pfaffian-paths (manuscript 812–828) supplies six-family nonemptiness: child paths p-r-s-q, r-p-q-s, p-q-s-r, q-p-r-s force N10,N01,Pux,Pvy; u-p-r-x and u-p-q-v force D11,N11. A cycle cannot close just the new square, and the saturated internal vertices force the remaining arms. The theorem's hypotheses hold for H and its stated planar applicability was read.

Assume a=ux is a one-edge complementary arc, reversing terminal roles if necessary. Degree two in K forces a in each N∈N00 and Q∈Pvy. Deleting a gives the exact bijections N00→Pux and Pvy→D11. In the latter case the crossing endpoint pairing is excluded in the complementary disk; the remaining pairing is uv,xy. The inverse joins the two paths. With Z=diff(Pvy),

    U=V+Z, W'=L+V+Z,
    r=N−C0, F=F_Q=Q−a+e+f, z=F−C0,
    b=r+2z modulo W',   t≥ell−1.                  (2)

F has exactly two even cycle components, one containing e and one f: deleting a from Q gives exactly the two paths, which e and f close individually. In particular F is not Hamiltonian. Taking P=N−a and D=Q−a makes the bridge equality exact.

Since D_G=L+V+<r>⊆W'+<r>, equality t=ell−1 forces

    D_G=W'+<r>,  r∉W',  dim(D_G/W')=1.            (3)

In this equality case, the unique normalized functional w:D_G→Q has kernel W' and w(r)=1. Its affine version h(X)=w(X−C0), defined on C0+D_G, is 0 on S and 1 on N00. Uniqueness is on D_G, NOT on the full edge space. If z∉D_G there is no intrinsic w(z), and exchange already holds because b∉W'. The sign conjecture's domain is the remaining branch z∈D_G. Then

    lambda=w(z),   eta=0 iff 1+2lambda=0.          (4)

Changing Q changes z by Z; changing N changes r by V; changing C0 changes r,z by L. Thus w and lambda are independent of all these anchors (with the affine base changed accordingly). Any extension of w to edge space agrees on z. On a quadrilateral a'=vy, U=V and s=e+f−a−a'; choosing Q=N−a' gives z=r+s and lambda=1+w(s).

The target is lambda≥0 in EVERY such equality case, including its brace restriction. It is stronger than J193's lambda≠−1/2. Neither integrality nor odd primitive lattice index by itself proves this sign target; those are only exchange exclusions.

## 2. Exactly when one alternating flip disconnects

Let C be a Hamiltonian cycle and R a simple C-alternating cycle in a cubic graph. Write A=R∩C and B_R=R\C, each a matching of q edges on the same 2q endpoints. Simplicity gives q≥2. The flipped factor is C_R=(C\A)∪B_R. Deleting A from the single cycle C gives exactly q vertex-disjoint paths covering every vertex. Their endpoint pairing is a perfect matching tau on the 2q endpoints. Let beta be the endpoint matching B_R. Suppress the interiors of the q paths. This identifies components of C_R bijectively with components of the 2-regular multigraph tau∪beta. Parallel matching edges are counted separately and represent a legitimate closed component after unsuppression. Therefore

    components(C_R)=components(tau∪beta).          (5)

Proof: every remaining path has two distinct endpoints and every endpoint is incident with one added edge; following path, added edge, path, added edge traces exactly the factor's components. No untouched cycle exists because C was connected and A nonempty. Suppression cannot join or separate components. This proves (5) in both directions. Equivalently the union is connected iff the involutions tau and beta act transitively together on the endpoints. One may also count components as half the number of orbits of tau∘beta: on each alternating cycle of the union this product has precisely two orbits, including a doubled-edge component.

A flip fails Hamiltonicity exactly when this union has at least two components: the factor then gains components relative to C. This is an exact reconnection criterion, not a theorem that beta has the desired connectivity. In particular a four-edge flip (q=2) fails exactly when beta=tau, producing two components; the other endpoint matching joins the paths into one cycle whenever it is the matching supplied by the graph. For q>2 a single alternating flip need not gain just one component.

For two arbitrary spanning two-factors T,F in a cubic graph, their symmetric difference is a disjoint union of simple alternating cycles: at each vertex they share at least one edge, and after cancelling common edges the degree is zero or two, with one edge from each factor. In the case T=C∈S, write these cycles R1,...,Rk and vi=1_(F∩Ri)−1_(C∩Ri). Then

    F−C=Σ_i vi,
    T_I=C+Σ_(i∈I) vi                             (6)

is a spanning two-factor for every subset I. It need not be connected, and T_I−C need not belong to D_G even though the total z does. Applying w term-by-term without checking that domain would be invalid.

## 3. Conditional extensions and why an order alone does not pay the sign

If every singleton T_{i} is Hamiltonian, vi∈D_G and w(vi)=h(T_i)∈{0,1}, since C∈S. Thus lambda=Σ_i h(T_i)≥0, reproducing I193 with its precise hypothesis.

Here is a block extension with all coefficients visible. For every nonempty I for which T_I is Hamiltonian, put a_I=h(T_I)∈{0,1}. Suppose there are nonnegative rational numbers theta_I on such subsets with

    Σ_(I containing i) theta_I=1 for every i.      (7)

Then summing (6) coordinate by coordinate gives F−C=Σ_I theta_I(T_I−C), whence

    lambda=Σ_I theta_I a_I≥0.                     (8)

This allows a fractional cover by overlapping successful blocks and does not require each singleton flip to work. It also proves z∈D_G when that was not known. It is a sufficient condition, not an established universal representation. For example, if k≥3 and every T_{all except i} is Hamiltonian, assign weight 1/(k−1) to each of those k subsets. Every index is covered k−1 times, proving lambda=(Σ_i h(T_{all except i}))/(k−1)≥0. For k=2 this is exactly the singleton condition; k=1 has no nonempty proper successful block because F is disconnected.

If the successful subsets partition {1,...,k}, all theta_I=1 and lambda is an integer. More generally any integer linear combination of Hamiltonian differences has integral w-value, since Hamiltonian difference values are −1,0,1. Thus fractional lambda obstructs every such integral certificate, even with signed coefficients. It does not obstruct (7) with genuinely fractional overlapping coefficients.

Ordering the flips in (6) does not supply (8). If C=T_0,T_1,...,T_{k−1} are Hamiltonian and T_k=F, then

    lambda=h(T_{k−1})+w(F−T_{k−1}).                (9)

The intermediate differences telescope to h(T_{k−1})∈{0,1}; the last jump is to a disconnected factor and its sign is unknown. Even intermediate Hamiltonian increments can be −1 (a lost-to-surviving transition). A chain including F cannot have all its members Hamiltonian. If disconnected intermediates are allowed, some individual increments may also be outside D_G. Thus neither a proposed order nor telescoping alone establishes controlled signs. The missing assertion is not mere degree preservation.

## 4. A fully written positive brace example that defeats the direct-flip certificate

This is a method obstruction within the paid prism family, NOT a negative-value example and not a new finite experiment. Let G=C4□K2 with vertices T_i,B_i, i modulo 4; edges t_i=T_iT_{i+1}, b_i=B_iB_{i+1}, rho_i=T_iB_i. Delete e=t_0,f=b_0 with u=T_0,v=T_1,x=B_0,y=B_1 on the lateral square. Thus a=rho_0 and a'=rho_1. The expansion inserts p,q on the top rail and r,s on the bottom, and is exactly C6□K2: the two cyclic layer orders are T_0,p,q,T_1,T_2,T_3 and B_0,r,s,B_1,B_2,B_3, with corresponding rungs. Both graphs are B-admissible braces, as proved below.

The complete old Hamiltonian family consists of C_i (all rails except t_i,b_i, and just rho_i,rho_{i+1}) and X,Y (all rungs, with opposite alternating rail matchings). To see completeness directly, selected rung vertices in a non-full rung set occur in even runs: omitted rails must match precisely those vertices. Each run's matching is unique, so the omissions in the two layers agree. More than one omitted position separates the factor into components. Thus one omitted position gives exactly C_i. With all rungs, the two layer matchings must be opposite to avoid disjoint squares, giving X,Y. With no rung, the layers remain separate. The same proof works for every even prism C_m□K2, m≥4.

The m+2 listed Hamiltonian vectors are affinely independent. In an affine dependence with coefficients c_i,x,y and total sum zero, top-minus-bottom rail coordinates give x=y. If A=Σ_i c_i, each rail coordinate gives c_i=A+x, and the coefficient sum gives A=−2x. Hence c_i=−x and (m−2)x=0; all coefficients vanish. For our cube, d(G)=5. Only C_0 avoids e,f, so N00={C_0}, S={C_1,C_2,C_3,X,Y}. Choose the surviving base C*=C_1. Then dim L=4,V=U=0, ell=1,t=0,W'=L. (U=V is the paid square bijection.) The unique normalized w on D_G has affine values 1 on C_0 and 0 on the other five cycles.

Choose Q=C_0−rho_1; then

    F=Q−rho_0+t_0+b_0=Σ_i(t_i+b_i),

the two layer squares. Coordinate comparison gives

    2(rho_0+rho_1−t_0−b_0)=C_0−C_1−C_2−C_3+X+Y. (10)

The coefficients on the right sum to zero. On rails of index 0 the value is −2, on other rails zero; on rungs 0,1 the value is 2, on rungs 2,3 zero. Thus this is an exact written vector identity. With s=t_0+b_0−rho_0−rho_1, it gives w(s)=−1/2 and

    lambda=w(F−C*)=w(C_0−C*)+w(s)=1/2.            (11)

For each surviving C_i, i=1,2,3, F△C_i is exactly the alternating lateral square {t_i,b_i,rho_i,rho_{i+1}}. For X it is the edge set Y (and conversely), a single alternating eight-cycle: rung edges alternate with the other rail matching. Therefore F△C consists of ONE alternating cycle for every C∈S. Its only nonempty flip is F itself, which is disconnected. In (5) it has two components. No choice of surviving C, no order of these direct difference cycles, and no fractional successful-block cover (7) exists for this example. Thus brace structure cannot force those particular certificates universally. This does not rule out paths through cycles using edges outside C∪F, other decompositions modulo W', or a different sign proof. From the lost cycle C_0, the same square flip has w-increment −1/2; the starting affine value is 1, so this is fully consistent with positive lambda.

For completeness, all even prisms used here are braces without invoking an unread matching theorem. Two prescribed rungs extend to the matching of all rungs. A prescribed rung and a disjoint rail extend by taking that rail, the corresponding rail in the other layer, and all remaining rungs; disjointness ensures the prescribed rung remains. Two disjoint rails in one layer extend by taking both and their counterparts, and all remaining rungs. Two rails in different layers extend by taking, independently in each even layer, the alternating perfect matching containing its prescribed rail. These cases exhaust two disjoint edges and construct a perfect matching in each case. The graphs are simple, cubic, bipartite and planar. Two vertex deletions in the same layer leave the other layer intact and all surviving vertices attached by rungs; one deletion in each layer leaves a path in each layer and at least one surviving rung. Thus they are 3-vertex-connected. This verifies both the cube and its C6-prism child in the brace restriction.

For general even m, the same coordinate comparison as (10) gives the paid identity

    (m−2)(rho_0+rho_1−t_0−b_0)
       =(m−3)C_0−Σ_(i≠0) C_i+X+Y.               (12)

At the two index-0 rails its right side is −(m−2), at other rails zero; rungs 0,1 receive m−2 and all other rungs zero. For rail deletion only C_0 is lost, so ell=1,t=0; negating (12) gives w(s)=−(m−3)/(m−2). For adjacent-rung deletion the survivors are C_{m−1},C_0,C_1,X,Y; affine independence gives dim L=4, dim V=m−4, and dim(L+V)=m, hence ell=m−3,t=m−4. The total lost-cycle coefficient in (12) again gives w(s)=−(m−3)/(m−2). Therefore both lateral deletion pairings have lambda=1/(m−2)>0. Their general B-admissibility is inherited from P169/I193's full deletion-case proof, read in full; the rail child also has the explicit prism description above. This reuses the infinite-family theorem, not its finite tests. Since 0<1/(m−2)<1 for all even m≥4, every integral Hamiltonian-difference certificate for z is impossible on these steps. In particular the singleton and disjoint-block sufficient conditions cannot be universal, even though the conjecture holds throughout this family.

## 5. Three perfect matchings: exact signs and the remaining term

Since G is cubic, M0=E(G)\F is a perfect matching. Alternating edges independently around each of F's two even components splits F into perfect matchings M1,M2. The three matchings partition E(G). Write E for the all-edge incidence vector, F01=M0∪M1 and F02=M0∪M2. Then, as vector equalities,

    F=M1+M2,
    F01+F02=E+M0=2E−F,
    F+F01+F02=2E.                                (13)

Each union is a two-factor, not necessarily Hamiltonian. Put tau_E=2E−3C0, a zero-degree vector. If F01,F02∈C0+D_G, equation (13) shows tau_E∈D_G and

    lambda=kappa−h(F01)−h(F02),
    kappa=w(tau_E).                               (14)

More generally one can extend w to all edge vectors and (14) holds there, but kappa and the other terms need not individually be intrinsic. Membership of z alone does not justify evaluating them with w. No parent affine-fullness hypothesis is being inserted.

If both F01,F02 are Hamiltonian, let j be the number of them avoiding both e,f. Equation (14) becomes lambda=kappa−j. Here j is exactly 0 or 1: since e,f belong to different F-components, one can color them differently (opposite phase) or identically (same phase). In opposite phase one union uses e only and the other f only, so both are survivors and j=0. In same phase one union uses both and the other neither, so j=1. Thus positivity in these conditional cases is respectively equivalent to kappa≥0 or kappa≥1. Neither bound follows from (13). There is no guarantee that both unions are Hamiltonian in either phase.

There is a small exact compatibility restriction. Up to swapping M1,M2 there are exactly two phase choices. Denote the opposite-phase pair A,B and the same-phase pair A',B'. Their sums coincide, A+B=A'+B'=E+M0. They CANNOT all four be Hamiltonian in an equality case: subtract twice C0 and apply w to get 0+0=0+1, a contradiction. Consequently, if one phase yields two Hamiltonian unions, the other has at least one disconnected union. This is only a consequence of the existing affine lost-family indicator; it supplies neither the existence of a Hamiltonian phase nor a bound on kappa. It is not a decisive dichotomy resolving the sign or realizing a negative value.

The cube makes this limitation concrete without a new computation. Its M0 consists of all rungs. The phase with opposite layer rail matchings yields X,Y, both survivors. The phase with equal layer rail matchings yields disjoint squares in each union. From (13) and (11), kappa=lambda=1/2. Thus even in a brace, only one successful phase can suffice and kappa need not be an integer. This is consistent with, not a proof of, a general lower bound.

Brace matching extension supplies a matching containing any two disjoint edges. It does not supply a Hamiltonian complement of a specified matching or preservation of the fixed M0 and full component colorings. Applying P4 to the path v-u-x-y (edges e,a,f) supplies a cycle with that path, but does not force its other edges to equal one of the unions in (13). Replacing an arbitrary disconnected union by such a cycle adds an unknown displacement; its quotient weight must be included. Discarding that displacement would be the missing sign assertion in another form. No matching-polytope, Pfaffian determinant, or reconfiguration theorem is invoked.

## 6. Other requested routes, source operations, and settled boundaries

**Manuscript operations.** The actual manuscript cor:edge-avoidance (794–805) gives a Hamiltonian cycle avoiding a single edge; cor:pfaffian-paths (812–828) gives a Hamiltonian cycle containing a three-edge path under its stated hypotheses. Their proofs do not identify either cycle with the unions in (13) or assign its difference from F a w-value. In the state argument, lem:cancel (446–483) fixes the second state; lem:circulation (497–519) CHOOSES weights on an incidence-spoke graph; lines 521–589 then fix those weights and infer existence of a forest state by a nonzero leading coefficient. Lines 591–718 convert such a state to a connected cycle when there is no separating triangle. None of these read operations transports this particular quotient functional w with its normalization. The required positive spoke circulations are not asserted for arbitrary given weights. No such transport has been proved here, and no upstream theorem is audited or questioned.

The actual Pfaffian definition at 807–810 concerns an even cycle whose vertex complement has a perfect matching. Each component of F qualifies because the other even component has an alternating perfect matching. Its odd orientation condition gives orientation parity, not an inequality for the rational functional w. An identification of the two kinds of weights would need a new argument; it is not assumed.

**Convexity.** An exact convex representation F=Σ theta_C C by Hamiltonian cycles, theta_C≥0 and Σ theta_C=1, is impossible. A zero coordinate off F forces every positive-coefficient C to be contained in F. Both have degree two at every vertex, so C=F, contradicting disconnectedness. A nonnegative representation of F−C0 modulo W' would prove the sign, but that is a different assertion and no universal such representation was found. The block criterion (7) is one proved sufficient way to obtain it; Section 4 proves it is not necessary.

**Integral and odd-index conditions.** If z is an integer combination of Hamiltonian differences, lambda∈Z and exchange follows; a negative integer would still refute the sign conjecture. More generally Gamma=D_G∩Z^E has a saturated rank-one quotient by Gamma∩W'. Taking a rational kernel functional, clearing denominators and dividing by the gcd of its values gives a primitive integer homomorphism phi with this kernel. Orient phi so m=phi(r)>0. Then lambda=phi(z)/m=k/m, k∈Z. Failure of exchange is 2k=−m, excluded if m is odd. This does not show k≥0. Primitivity of phi does not say that its value on this specific r is 1. These are the precise I193 sufficient conditions, with no promotion to sign theorems.

**Pairing and central composition.** The inherited same-square calculation gives identical lambda for complementary deletion pairings, not opposite values. I193's proved central identities are Delta_c=eta_first, lambda_c=lambda/(1+2lambda) when lambda≠−1/2 in the first equality case; at lambda=−1/2 the following central step has zero deficit and gain three, compensating the first gain one. Thus nonnegative lambda propagates to every successive central expansion and gives lambda_j=lambda/(1+2j lambda), by induction; the denominator stays positive. This is a settled sign subcase for descendants of an already settled input, including the positive prism inputs.

A negative formal initial coefficient supplies no contradiction through this recurrence. If lambda=−p/q in lowest terms, its equality-branch iterates, while defined, are −p/(q−2jp). Either it reaches −1/2 (only when p=1 and q is even), followed by the paid compensation branch, or the denominator changes sign without hitting zero and the value becomes positive. This is conditional algebra on an actually realizable input, not evidence that any negative input exists. Iterating local composition cannot by this arithmetic alone exclude all negatives. Nor does proving a positive coefficient for a particular successor prove positivity of its predecessor: the inverse lambda=lambda_c/(1−2lambda_c) changes sign at 1/2.

**Exchange branches distinct from the sign question.** Equation (1) proves exchange for ell=0 or t≥ell. The formal N00-empty branch has ell=0; on a short gap it cannot occur by the bijection. Equality with z∉D_G is settled as above. Equality with z∈D_G is settled for exchange whenever lambda≠−1/2, in particular under (7), for prisms and their central successors, or by the integral/odd-index criteria. On a quadrilateral this is w(s)≠−3/2. Every admissible quadrilateral or hexagon has a short gap because its positive odd complementary arc lengths sum to facial length minus two. This is applicability, not a proof of every equality case. D168's bounded-bidirectional-transfer obstruction and M168's typed-fullness obstruction remain binding; neither method was reopened.

## 7. Counterexample branch and one precise remaining assertion

No negative-value admissible step is exhibited. Section 4 specifies an actual brace step, complete old families, the quotient w and a written positive value; it refutes a method, not the conjecture. All other negative coefficients discussed above are formal hypotheses whose graph realizability is unproved. The retained reports' finite evidence is inherited history only; no graph data or diagnostic was read or run to create new evidence here.

> **J194 (unpaid sign assertion).** For every B-admissible short-gap step with the complete families of Section 1, if t=ell−1 and z=F_Q−C0∈D_G, the unique functional w:D_G→Q with kernel W'=L+diff(N00)+diff(Pvy) and w(N−C0)=1 satisfies w(z)≥0 (with ux chosen as the short arc, or the symmetric notation when vy is short).

This is a single precise assertion, independent of all anchors. Its restriction to brace steps is also unresolved. The block and matching conditions above are conditional subcases or method limitations, not additional asserted universal premises. A proof of J194 implies J193 since −1/2<0, hence short-gap exchange by (1)–(4). A negative lambda would refute J194; it refutes exchange for that step only if lambda=−1/2.

**Original-target verdict: UNRESOLVED at J194.** The new written flip criterion and conditional fractional-cover lemma do not supply a universal cover; the cube disproves universality of that route even in braces. The matching compatibility observation does not force a sign. No decisive new structural dichotomy in the brief's sense, and no verified negative instance, has been obtained. Accordingly this final focused attempt stops here. The parent should apply the prescribed parking rule to the short-gap front; I do not edit its ledger or start another route. E183/Z184/E182/E181/H180/L179 remain parked throughout.

Even a future proof of the sign conjecture would leave the long-gap clauses of J192, universal exchange and Q164 open. There is no new consequence for the stronger affine-fullness target or (T), and no all-brace construction claim. Historically Q164 is the numerical count bound h(G)≥|V(G)|/2+2; this record does not prove that bound. No substantial finding or literature priority is nominated.
