# The annular construction and its central remainder

Prefreeze derivations. This note does more than declare the reduced transfer unavailable in the maximal norm: it installs a maximal transfer on a long twisted circle, gives explicit compatible radial maps, performs the source stack comparison, and computes the operator carried to the core. The source graphs, projections and all upstream proof operations are taken as true.

## 1. A long-circle middle on which maximal transfer is available

For j≥2 let B_j=C_{6j}, identified with the actual boundary of the source disc D_j. Define Y_j=B_j×Q_{j−1}, with left Cayley edges and right transport g_{j−1}^{a_B(h,h')} along boundary edges. The quotient is constant on Y_j. Let f:Y→B forget that quotient; choose the same type of separated-union metrics as in the source.

Degrees are at most |S|+2. The horizontal matchings commute with the left group action. If two paths of a prescribed bounded length have the same endpoints in a sufficiently long cycle, their seam winding agrees. Thus the matrix transport L(T) along chosen shortest base paths satisfies:

* L(T) is locally compact and controlled, with the matching bound;
* L(T) commutes with the universal Kazhdan projection P_Y;
* D(T,T')=L(T)L(T')−L(TT') has finite vertex support, for each fixed pair of algebraic operators.

The maximal source's proof of PD=0 applies with its exact hypotheses: P_nD remains on a fixed finite union of components, and maximal/concrete norms agree there. Consequently

    Phi:A_B→A_Y,   Phi(T)=P_Y L(T)

is a homomorphism. Projecting to B preserves propagation through the averaging approximants. The same identity-cover argument as the source gives f_*Phi_*=id. This closes the long-circle transfer; no generic property-(T) assertion is substituted for the finite-defect proof.

## 2. Explicit radial maps, including the twist corrections

Let the six unit hexagon vertices be

    e_0=(1,0), e_1=(0,1), e_2=(−1,1),
    e_3=(−1,0), e_4=(0,−1), e_5=(1,−1),

with indices modulo six. A boundary vertex is (k,h), 0≤k<6, 0≤h<j, at (j−h)e_k+h e_{k+1}. For t=1,...,j set

    m_t(h)=floor(th/j),
    w_t(k,h)=(t−m_t(h))e_k+m_t(h)e_{k+1}.

At t=j this is the identity parametrization of C_j. At t=1 each side collapses to its first hexagon vertex, except that its last edge goes to the next vertex. Every horizontal edge maps to a point or an edge, since m_t(h+1)−m_t(h) is 0 or 1 (with the side endpoint convention). Every radial step is an edge: m_{t+1}(h)−m_t(h) is 0 or 1, so w_{t+1}−w_t is e_k or e_{k+1}. All images stay outside the origin.

The small square between two consecutive boundary parameters and two consecutive radii lies in one triangular-lattice sector, between radii t and t+1. Its boundary has zero winding and avoids the origin. Thus pulling the ray-charge cochain a back to this cylinder gives a closed integral cochain. Its restriction at t=j is a_B. Since the cylinder retracts onto that boundary, there is an integral vertex function c_t(k,h), normalized by c_j=0, with

    c_t(h')−c_t(h)=a(w_t(h),w_t(h'))−a_B(h,h'),
    c_{t+1}(h)−c_t(h)=a(w_t(h),w_{t+1}(h)).       (3)

These formulas can also define c_t by the charge along the radial path from the boundary; path consistency is exactly the zero charge of the elementary squares. The correction cannot simply be omitted: the fixed ray need not cut the same parameter edge at every radius.

Define

    s_t(h,q)=( w_t(h), bar(q) g_{j−t}^{c_t(h)} ) ∈ X_j,

where bar(q) is reduction from Q_{j−1} to Q_{j−t}. Left Cayley edges map to Cayley edges or points. The first equation in (3) makes horizontal edges map to their prescribed right-twisted edges or points. The second equation makes s_t(h,q) and s_{t+1}(h,q) adjacent under the actual normalized reduction relation of X_j. Thus each s_t is 1-Lipschitz on Y_j and consecutive maps are distance one apart. At t=j the fibre is trivial, so s_j=i f. At t=1 the image lies on the radius-one ring with fibre Q_{j−1}.

The six sectors and their radial interpolation supply the required topological compatibility; no homeomorphism or global lifting of the disc across its center has been assumed.

## 3. Maximal sliding through the annulus

Choose exact covering isometries D_{j,t}:H_{Y_j}→H_{X_j} over s_t. All their vertex fibres are finite, so ample vertex modules allow the required orthogonal copies even when their cardinalities grow with j. For distinct radii t their images are disjoint, since rho(w_t)=t. There is no uniform bound on the ranks of the resulting compact vertex entries, and the locally compact Roe algebra does not require one.

For a controlled T on Y, compress to components T_j. Stack copies at t=1,...,j−1 and compare to copies at t=2,...,j. The source's doubled-module rotation has propagation at most prop(T)+1, independent of j and of the angle. Compression defects are on finitely many components and become compact after finitely many copies there. Hence these are homomorphisms modulo K_X; their homotopy is continuous in maximal norm by the fixed-propagation estimate. Cancel the common interior stack and use K_1(K_X)=0 to obtain

    (s_1)_* = (i f)_*: K_1(A_Y)→K_1(A_X).        (4)

This proof does not assert that s_1 and i f are close: their separation grows with j. It is exactly the source's stronger stabilized operation that makes (4) available.

For ANY b∈K_1(A_B), apply (4) to Phi_*(b) and use f_*Phi_*=id:

    i_*(b) = (s_1)_*Phi_*(b).                    (5)

In particular, naturality supplies a genuine reduction for the actual boundary class:

    mu_X^max(alpha_D)
       = (s_1)_*Phi_*(mu_B^max(beta)).            (6)

Equation (6) is a core-supported maximal index, not a zero. It already closes the variable-depth annular transport without having to prove that the reduced disc's original entry lift is multiplicative everywhere.

## 4. Computing the image of a concrete base shift

Let e be a rank-one projection in H_0. On l²(B_j) tensor e, let S_j be the cyclic forward shift, and take the identity on its complement. The family S lies in 1+C[B], has propagation one and is unitary. Its transferred class has representative

    v=1+P_Y(H−1)e,

where H is the horizontal twisted shift on Y, with the appropriate holonomy on the seam. Indeed L(S−1)=(H−1)e on the algebraic domain. P_Y commutes with H and e, so v is a unitary in A_Y^+.

At s_1 the 6j positions map to the six radius-one vertices. Choose its covering isometry using the displayed right translations and H_0 label embeddings independent of q. It is then exactly equivariant for the left Gamma action, since the quotient level is unchanged. This equivariance is required only at s_1, not at the other radii where the group quotients change. Conjugating P_{Y,n} times any algebraic compact-entry operator therefore equals P_{X,n} times its conjugate, as an algebraic identity; maximal convergence gives the same identity with the Kazhdan projections. This justifies transporting the abstract invariant corner, without inferring it from concrete constants alone. The quotient level remains j−1. The correction c_1 exactly identifies their right transports with the six-edge ring transport. Now identify each ring fibre with the distinguished fibre F_j by a chosen path in a spanning tree of the hexagon. Each such identification moves a point at most five edges in X_j. Move the copies into orthogonal H_0 labels over F_j using these paths. This is a controlled change of covering isometry, so it preserves the induced K-theory class. In this description the horizontal shift is a cyclic companion matrix with 6j labels and ONE holonomy W_j=R(g_{j−1}); all other transports are the identity. The product around the cycle is W_j because (3) telescopes and the positively oriented ring has charge one.

Factor that cyclic matrix as a scalar cyclic permutation matrix C_j times a diagonal matrix with W_j in one entry and identities in the others. On the invariant corner, the first factor is null-homotopic uniformly: choose a selfadjoint logarithm A_j of C_j with ||A_j||≤π and use exp(itA_j). This acts only on the finite set of H_0 labels at each vertex. Its rank 6j is allowed to grow. The logarithms act as propagation-zero bounded multipliers before the constant-fibre compression; their norms are uniformly bounded. Multiplying the finite-rank label projection by P gives a locally compact maximal element. Consequently the homotopy is uniformly norm-continuous and may be assembled over all j. No unbounded concatenation of 6j sequential rotations is needed.

The diagonal W_j factor is precisely the core unitary u of HOLONOMY.md, up to a controlled cover and the choice of which H_0 label carries e. Thus the purely operator calculation gives

    (s_1)_*Phi_*[S] = [u],
    i_*[S]=[u].                                 (7)

Combining (7) with HOLONOMY.md's detector proves that the base shift remains of infinite order in maximal K-theory after boundary inclusion, whereas its image under reduction is zero. This is an operator calculation, and still does not silently replace mu_B^max(beta) by [S]. The latter identification is the specific index-comparison obligation described at the end of HOLONOMY.md. Its completion would be a comparison of already available operations; it has not been frozen as a new nominee.

## 5. A direct defect of the unmodified disc lift

Here is a second, entirely explicit diagnostic. Choose the elementary triangle at the origin through which the ray exits. Label its vertices u,v,w in an orientation with total charge +1. Make that same choice in every D_j. Let T have the single base block from v to u equal to e in every component, and let T' have the block from w to v equal to e. They have propagation one. Their product is the block from w to u. Use the reduced source's actual normalized child operators/permutations for these three edges and let L denote that entry lift.

D=L(T)L(T')−L(TT') is a controlled locally compact operator. All edge operators are partial isometries and preserve normalized constants in both directions; they intertwine the left group action. Thus D commutes with P, and concretely PD=0.

However, the charge representation computes Theta(PD). For fixed n first use P_nD and then take n→infinity exactly as in HOLONOMY.md §4. Its (u,w) block is

    ( z^{a(w,v)+a(v,u)}−z^{a(w,u)} )
             |xi_u><xi_w| tensor e.

The exponent difference is +1 or −1 according to the chosen source-to-target convention. At z=−1 its norm is two for every sufficiently large j. Therefore ||Theta(PD)||=2. Each of L(T),L(T'),L(TT') is an algebraic partial isometry of universal norm one, and ||P||≤1; hence

    ||PD||max = 2,     ||lambda(PD)|| = 0.        (8)

This proves that THIS entry lift followed by universal averaging is not multiplicative. It is not an assertion that no other transfer, no other graph, or no relative construction can work. In particular, (5) has just provided a valid maximal transfer-and-slide on the annulus. The obstruction exposed by (8) is at the chosen central curvature operation, not a failure of the source's true maximal transfer.

## 6. Stable cancellation is available, with its actual cost

The primary/source machinery does supply a cancellation, so it would be wrong to stop by naming a nontrivial unitary. For any unitary u,

    V(t)=diag(u,1) R(t) diag(1,u*) R(t)*,
    R(t)=[[cos t,−sin t],[sin t,cos t]],  0≤t≤π/2,

joins diag(u,u*) to 1. Here u_n=1+P_nE(W−1) has propagation ≤n+6 and ||u_n−u||max≤2rho^n. Substituting u_n and u_n* in the displayed formula gives uniform approximation error at most 4rho^n+4rho^{2n}, with propagation at most 2n+12, independently of j and t. Thus there is no missing component-uniform analytic cancellation for an inverse pair.

But its charge detector is (+1)+(−1)=0. Adding an inverse copy pays the analytic cancellation and cancels this very winding test. Keeping two disconnected copies does not help: then separate charge representations still detect the individual summands, and their assembly/domain problem has changed. Gluing them requires a new relative analysis of which cocycles extend across the gluing, rather than merely adding their numerical windings.

Adding the maximal source's already-null endpoint class also does not cancel [u] in K_1: adding zero leaves (2) unchanged wherever Theta extends. That is a compatibility calculation, not a claim about all possible geometric gluing operations. A new construction might alter the extension domain of Theta, but then its all-scale nonzero-domain argument must be proved afresh.

The exact unpaid operation is a common relative core replacement with compatible controlled transports and maximal null-homotopies, together with a new integral all-scale detection argument for the SAME proposed class after replacement. The annular maps, universal averaging, stable inverse-pair cancellation and the source's separate divisibility argument are paid. Their simultaneous relative assembly has not been constructed here. No conditional theorem, parameter substitution, neighboring impossibility statement, or weaker old target is offered.
