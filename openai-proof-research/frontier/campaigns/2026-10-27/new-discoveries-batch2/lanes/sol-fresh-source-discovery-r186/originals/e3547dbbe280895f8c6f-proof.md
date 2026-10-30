# All particle numbers: a calibrated nonattainment construction

Myeongjin Kang; no affiliation. Original prose CC BY4.0.
Author proof of the unchanged statement in original-scope.txt; no independent verdict. Source373's three-particle construction and Gerolin–Kausamo–Rajala's shared-component mechanism are antecedents. The only proposed new realization is the arbitrary-particle geometry; whether this is substantial is a separate question.

Fix integers N≥3,d≥2 and s>0, and put m=N−1. All choices below may depend on this fixed triple. Write h(v)=|v|^(−s) away from0 and c(x_0,…,x_m)=Σ_(i<j)h(x_i−x_j). Embed the unit circle in the first two coordinates of R^d.

## 1. Two discrete contact configurations

Let

 a_(1,j)=(cos(2πj/m),sin(2πj/m),0,…,0),
 a_(2,j)=(cos((2j+1)π/m),sin((2j+1)π/m),0,…,0),
 j=0,…,m−1.

Their two sets A_1,A_2 are disjoint regular m-gons and their union is a regular2m-gon. For m=2 they are the two perpendicular antipodal pairs. In all cases Σ_j a_(k,j)=0.

We record the classical circle-energy calculation, rather than infer an N-body gap from the three-body source. Put f(t)=(2sin(t/2))^(−s) for0<t<2π. Then

 f''(t)/f(t)=(s/4)csc²(t/2)+(s²/4)cot²(t/2)>0.

For m distinct circle points in cyclic order with lifted angles θ_0<…<θ_(m−1)<θ_0+2π and θ_(i+m)=θ_i+2π, their unordered energy is

 (1/2)Σ_(r=1)^(m−1)Σ_(i=0)^(m−1) f(θ_(i+r)−θ_i).

For each r the inner arguments sum to2πr, so Jensen gives an energy at least

 E_m=(m/2)Σ_(r=1)^(m−1)f(2πr/m).

Equality requires equality in the r=1 strict Jensen inequality, hence all consecutive gaps equal2π/m. Conversely a regular m-gon attains the bound. This also proves the case m=2. It is a classical special case of universal optimality (Cohn–Kumar, Table1 and Theorem1.2), not a new inequality.

Every regular m-gon contained in A_1∪A_2 is A_1 or A_2: starting from an index j in Z/(2m), its next regular vertex has index j+2, so the set is exactly one parity class. Therefore among m distinct outer centers, exactly these two sets minimize the energy. Adjoining the central0 adds m, since all outer radii are1. Define C_0=m+E_m. Both contact configurations b_k=(0,a_(k,0),…,a_(k,m−1)) have cost C_0 and central gradient

 ∇_(x_0)c(b_k)=sΣ_j a_(k,j)=0.

All other configurations of N distinct centers that contain0 have cost strictly greater than C_0. Configurations of N distinct outer centers have positive cost.

## 2. Local supporting potentials with every coordinate invertible

The following is the source's local minimization construction with all its matrix blocks retained. In branch k keep y=x_1, centered at a_(k,0), free. Let z be the vector of the remaining m coordinates: the central x_0 and the m−1 other outer coordinates. Its dimension is md.

For a parameter K>0 define the common central potential

 u_0(x)=C_0−(K/2)|x|².

For outer index j=1,…,m−1 in branch k put

 v_(k,j)(x)=ℓ_(k,j)·(x−a_(k,j))−(K/2)|x−a_(k,j)|²,
 ℓ_(k,j)=∇_(x_(j+1))c(b_k).

Define F_k(z,y)=c(z,y)−u_0(x_0)−Σ_(j=1)^(m−1)v_(k,j)(x_(j+1)), with the arguments of c in their specified original order. Its z-gradient vanishes at the center: the central gradient is0, and the linear terms cancel every other z-gradient. At that center write

 M_k=D²_zz c(b_k), Q_k=D_y∇_z c(b_k).

The Hessian of F_k in z is M_k+KI_(md). Each d×d block of Q_k, corresponding to a center b_i other than y's center a_(k,0), is

 −D²h(b_i−a_(k,0)).

For every v≠0,

 D²h(v)=s|v|^(−s−2)[(s+2)vv^T/|v|²−I_d].

Its radial eigenvalue is s(s+1)|v|^(−s−2) and each tangential eigenvalue is −s|v|^(−s−2). Every such block is invertible, also when d>2 and the centers lie in a two-plane.

Choose K sufficiently large that M_k+KI is positive definite for both k and every block of (M_k+KI)^(-1)Q_k is invertible. This is possible because

 K(M_k+KI)^(-1)Q_k→Q_k

as K→∞ and there are finitely many blocks. The implicit function theorem gives a smooth stationary branch z=Z_k(y), with

 DZ_k(a_(k,0))=−(M_k+KI)^(-1)Q_k.

The inverse function theorem, separately for each coordinate block, makes every coordinate Z_(k,i) a diffeomorphism onto its open image after a common restriction of y. Denote the central coordinate by X_k.

By continuity, after restricting to a product of small balls, the z-Hessian of F_k remains positive definite. Shrink the y-ball so the stationary point stays in that product. For every such y the z-domain is convex, so strict convexity shows that Z_k(y) is its unique global minimizer there. Define w_k(y)=F_k(Z_k(y),y). Then w_k is smooth, w_k(a_(k,0))=0, and

 c(x_0,y,x_2,…,x_m)≥u_0(x_0)+w_k(y)+Σ_(j=1)^(m−1)v_(k,j)(x_(j+1)),

with equality exactly when z=Z_k(y). This step is an explicit finite-dimensional extension of source lem:local; it introduces no new uniform estimate.

## 3. One calibration on all components

Choose pairwise disjoint small open balls around0 and every center in A_1∪A_2, lying in the local domains of Section2. Define a single potential u on their union U: u_0 on the central ball, w_k on the distinguished outer ball in each branch, and v_(k,j) on its other balls. Its center values are C_0 at0 and0 at every outer center. It is smooth on each component and bounded on sufficiently small preliminary balls, say |u|≤M.

There are finitely many component patterns for N coordinates. For a pattern with distinct centers that includes0, Section1 gives a strict positive cost-minus-potential gap unless its outer centers are exactly A_k. For a distinct-center pattern without0, its potential sum is0 and its cost is positive. All these strict inequalities persist on products of sufficiently small balls, by continuity and finiteness. For a pattern with a repeated component, two coordinates have distance at most2r if all ball radii are at most r. Positivity of all pair terms gives c≥(2r)^(−s). Choosing r so that this exceeds NM excludes every repeated-component pattern, including actual collisions.

On each prescribed branch pattern, Section2 gives the supporting inequality and exact equality family. Permutation symmetry handles all its coordinate orders. We conclude, on U^N,

 c(x_1,…,x_N)≥Σ_i u(x_i),                                      (1)

with equality precisely on permutations of the two local contact families. Further restrictions preserve all strict gaps. Fix the central and nondistinguished outer balls first and shrink the two distinguished y-balls until every coordinate of Z_k lies in its corresponding ball. The images X_k of these final y-balls are open neighborhoods of0. Choose one open ball B about0 inside their intersection and the central ball.

Invert X_k over B. For each k and each of its m outer coordinates define H_(k,j):B→R^d by taking that coordinate of the family at y=X_k^(-1)(x); for the distinguished coordinate this means H_(k,0)=X_k^(-1). All2m maps are diffeomorphisms onto open images, since every coordinate map Z_(k,i) is locally a diffeomorphism. Their images and B lie in pairwise disjoint component balls. Equality in(1) holds on

 (x,H_(k,0)(x),…,H_(k,m−1)(x)), x∈B.                           (2)

Moreover, for any equality tuple whose central coordinate belongs to B, all its other coordinates are exactly the images in one of(2), up to permutation. This follows from the injectivity of X_k, not from component totals.

## 4. Smooth identical marginals and a finite optimizer

Take a nonnegative g_0∈C_c^∞(B) with ∫g_0²=1, and put ν=g_0²dx. Define

 μ=(1/N)ν+(1/(2N))Σ_(k=1)^2Σ_(j=0)^(m−1)(H_(k,j))#ν.           (3)

The coefficients sum to (1+m)/N=1. For each H define

 g_H(y)=g_0(H^(-1)y)|det DH^(-1)(y)|^(1/2) on H(B),

extended by0 elsewhere. Its support is compactly contained in H(B), so this extension is C_c^∞. The determinant never vanishes on H(B), and its absolute-value square root is smooth there. All g_H and g_0 are nonnegative and supported in disjoint components. Thus

 g=N^(-1/2)g_0+(2N)^(-1/2)Σ_H g_H

is nonnegative C_c^∞, μ=g²dx, and ∫g²=1. This proves the exact density and square-root assertions.

Sample x with lawν, choose k uniformly from{1,2}, and independently choose a uniform permutation of the N entries of(2). The resulting coupling π_0 has each marginal exactly(3). Its support is compact and pairwise collision-free, because different coordinates lie in distinct compact component sets. Its cost is finite and equality in(1) holds. Every coupling π with the same N marginals gives U^N full measure. Integrating(1), with bounded u, gives

 ∫c dπ≥N∫u dμ=∫c dπ_0<∞.

Therefore π_0 is a finite optimal coupling. Any optimizer has nonnegative slack in(1) with integral0 and is concentrated on its equality set.

## 5. Excluding every deterministic optimizer

Suppose (Id,T_2,…,T_N)#μ is optimal, where each T_i is a Borel map preservingμ. On ν-almost every x∈B, its tuple is an equality tuple with x the unique central coordinate. Section3 forces

 T_2(x)∈{H_(k,j)(x): k=1,2; j=0,…,m−1}.

For each of these finitely many maps H let S_H={x∈B:T_2(x)=H(x)}. These are Borel sets and cover B up to a ν-null set. H(S_H) is Borel because H is a homeomorphism onto an open image. Formula(3), disjoint components and injectivity give

 μ(S_H)=ν(S_H)/N,
 μ(H(S_H))=ν(S_H)/(2N).

Since S_H⊂T_2^(-1)(H(S_H)), preservation implies ν(S_H)/N≤ν(S_H)/(2N). Thus every S_H has zeroν-mass, a contradiction. This excludes all Borel preserving tuples, without regularity or cyclic restrictions. Symmetry of the cost/marginals also gives the same exclusion if another coordinate is used as the base. No uniqueness of optimal couplings is needed or asserted.

## 6. Equality of infima with exact maps

This is the source/CDM separated-cell recovery operation, written for N coordinates. Let K_a be the compact support of g_0 or one of its2m images, and let η=min_(a≠b)dist(K_a,K_b)>0. Partition their union into finitely many positive-μ-mass Borel cells A_i of diameter at mostδ, each lying in one component, discarding a μ-null remainder. Write

 q_(i_1,…,i_N)=π_0(A_(i_1)×…×A_(i_N)).

For each i_1 split A_(i_1) into Borel sets B_(i_1,…,i_N) of these prescribed masses. Absolute continuity makes these splits possible (successive first-coordinate distribution cuts suffice). On a positive-mass piece B_I, for each r=2,…,N choose a Borel map sending μ|_(B_I)/q_I to μ|_(A_(i_r))/μ(A_(i_r)). Existence follows from the source's lem:borel-transport, or the classical atomless probability-space construction. Restrictions of absolutely continuous measures to the Borel pieces remain absolutely continuous. Modify exceptional images on null sets into the target cell, then glue the finitely many maps and define them arbitrarily on the remaining null set.

For each resulting T_r and every Borel D,

 μ(T_r^(-1)D)=Σ_I q_I μ(D∩A_(i_r))/μ(A_(i_r))=μ(D).

The graph plan gives every product of cells exactly the mass q_I. Any active product comes from N distinct components, because π_0 uses such configurations. All pairwise distances in that product are at leastη, including for the graph plan. For two tuples in the same product, each pair cost differs by at most2sδ η^(−s−1), so the whole cost differs by at most

 N(N−1)sδ η^(−s−1).

Both costs are bounded by binom(N,2)η^(−s) on active products. Summing the oscillation against their common product masses yields

 |∫c d(Id,T_2,…,T_N)#μ−∫c dπ_0|≤N(N−1)sδ η^(−s−1)→0.

Every graph coupling is admissible, so the reverse infimum inequality is automatic. Section5 gives strict inequality for every individual tuple, while these tuples have finite costs tending to the minimum. This proves all clauses of original-scope.txt.

## 7. Scope and contribution limits

The proof treats every fixed N≥3,d≥2,s>0; no constant is uniform in these parameters. The geometric center sets are planar, but the local maps and smooth bump are fully d-dimensional. Singular behavior at collisions causes no integral restriction on s: the optimizer and recovery plans have separated components. N=2 is not included; then m=1 lacks a balanced outer polygon and the splitting construction fails, consistently with two-marginal Monge existence.

The construction is not spectator padding: every outer coordinate is a diffeomorphic function of the central variable on each branch. There is no independent spectator variable in which a deterministic map could encode the branch choice. It does not solve the earlier everywhere-positive-density question; its disconnected support is intentional and is the same type of support allowed by the present frozen statement.

All main proof operations are short adaptations of credited antecedents: classical strict circle energy, the source's large-K implicit-function argument, finite-pattern continuity/singularity, GKR/source image-set mass domination, and source/CDM cell redistribution. The all-N assembly is a complete author-level result, but a substantial contribution verdict is not claimed. No formal or independent proof gate has yet occurred.
