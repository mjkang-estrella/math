# Prefreeze: cyclic transversality, symplectic reduction, and the full source filtration

No nominee is frozen. This note carries the strongest integrated linear-algebra construction to completion. The nonvanishing operation is the generalized Moore/Gabidulin determinant over cyclic extensions, including characteristic zero, from Augot–Loidreau–Robert arXiv1703.09125v1, Theorem5 and Proposition7. Its actual proof was read before this note, including the fixed-field condition. Alternating trace forms, rational symplectic reduction, and the source's stable-subobject/maximality proof complete the composition. We do not count this as substantial by calling its sharper number optimal.

## 1. Precise coefficient field and universal property

Fix a characteristic-zero field k and a cyclic extension E/k of degree2M, M>=1, with generator sigma. For any symplectic k-space V of dimension2m with1<=m<=M, we construct an E-Lagrangian L_V in V_E such that

    dim_E(L_V cap W_E)=max(0,dim_k W−m)                 (C1)

for EVERY k-linear subspace W subset V. The extension E is common to any finite list of such spaces. The property tests all k-subspaces, not all E-subspaces. It is stronger than the stable-isocrystal tests required by SOURCE001. The cyclic extension is an explicit hypothesis at this stage; we construct an appropriate one with finite local-field descent in §5.

## 2. Moore nonvanishing and a self-contained root bound

A nonzero operator P=sum_(i=0)^d c_i sigma^i, c_i in E, with d<2M has kernel over k of dimension at most d. Here is the elementary induction behind the primary operation. If it has no nonzero root the conclusion holds. Otherwise take x!=0 with P(x)=0. For y=x z, put a_i=c_i sigma^i(x), so sum a_i=0. Then

    P(xz)=sum_(i=1)^d a_i (sigma^i(z)−z)
          =sum_(j=0)^(d−1) b_j sigma^j(sigma(z)−z),
    b_j=sum_(i=j+1)^d a_i.

The last coefficient b_(d−1)=a_d is nonzero, so the operator Q=sum b_j sigma^j has degree d−1. On the k-subspace x^(−1)ker P, the map z->sigma(z)−z has kernel k (because E^sigma=k) and image contained in ker Q. Induction gives dim ker P<=1+(d−1)=d. Degree zero is multiplication by a nonzero scalar.

Thus for k-independent w_1,...,w_a in E, a<=2M, the square Moore matrix (sigma^i(w_j))_(0<=i<a,1<=j<=a) is invertible: a row dependence would give an operator of degree<a with at least a independent roots. Any consecutive a rows, including a cyclic shift, are invertible by applying a power of sigma. This is exactly the existing primary nonvanishing operation, not a new proof primitive.

## 3. An actual alternating form and a Lagrangian over E

Put tau=sigma^M. Pick a in E^times with tau(a)=−a; it exists by taking b−tau(b) for b outside the fixed field of tau. On the2M-dimensional k-space V0=E set

    B(x,y)=Tr_(E/k)(a x tau(y)).                         (C2)

Applying tau inside the trace gives B(y,x)=−B(x,y). Trace nondegeneracy and invertibility of a and tau make B nondegenerate.

Use the E-linear splitting

    V0 tensor_k E -> E^(2M),  x tensor c -> (sigma^i(x)c)_i.

In these coordinates, the extended form is

    B_E(X,Y)=sum_(i=0)^(2M−1) sigma^i(a) X_i Y_(i+M),

with indices modulo2M. Hence

    L0={X_M=...=X_(2M−1)=0}                            (C3)

is isotropic of dimension M, and therefore Lagrangian. This explicitly retains the alternating form; arbitrary Moore rows are not simply declared Lagrangian.

For a k-subspace W subset E of dimension a<=M, the projection to coordinates M,...,2M−1 has rank a on W_E by Moore nonvanishing. Therefore L0 cap W_E=0. If a>M, an M-dimensional k-subspace of W already maps with rank M, and rank-nullity gives dim(L0 cap W_E)=a−M. So L0 has the universal property for dimension2M.

## 4. All smaller blocks over the SAME extension

For m<=M choose a k-isotropic subspace U of V0 of dimension M−m and put T=U^perp. The symplectic quotient T/U has dimension2m. Universal transversality gives

    dim_E(L0 cap T_E)=m,    L0 cap U_E=0.

Thus the image L_m of L0 cap T_E in (T/U)_E is an m-dimensional isotropic subspace, hence Lagrangian. If W subset T/U has dimension a, its full inverse image Wtilde in T has dimension a+M−m. Projection identifies

    L0 cap Wtilde_E  ->  L_m cap W_E.

It is injective because L0 cap U_E=0 and surjective by the definition of L_m. Therefore its dimension is max(0,a−m). Every symplectic2m-space over k is k-isometric to T/U; transporting L_m proves (C1).

This reduction is essential to using the maximum block size rather than a compositum with degree product or lcm of all block sizes. It is ordinary symplectic reduction applied to the already universal Moore construction. It pays all blocks, not only equal-sized blocks, and no generic-independence assumption between blocks is needed.

## 5. Finite local-field descent, including residue characteristic2

Apply the construction to the source blocks after choosing a finite H/Q_p that splits E_CM and u² and carries their symplectic bases, as in SOURCE001 §4. Enlarge H to contain mu_(2M), where M is the largest half-block size. Put k=K0 H. Choose a uniformizer pi of H. It is also a uniformizer of k, by the Eisenstein argument in the osculating note. Let

    F=H(theta), theta^(2M)=pi,   E=k(theta).

Eisenstein gives [E:k]=2M. All2M roots zeta^i theta lie in E, so E/k is cyclic, generated by sigma(theta)=zeta theta. Take a=theta; tau(theta)=−theta, even when M is even. In the monomial k-basis1,theta,...,theta^(2M−1),

    B(theta^i,theta^j)=0 unless i+j=2M−1,
    B(theta^i,theta^(2M−1−i))=2M pi (−1)^(2M−1−i).

This follows by summing the2M conjugates: among exponents i+j+1 in[1,4M−1], only2M is divisible by2M. It exhibits a nondegenerate alternating anti-diagonal matrix over H. Darboux changes of basis, the chosen isotropic U, the quotient identifications and the original block isometries can consequently all be made over H. The embedding-coordinate formulas use only zeta and theta, so every resulting flag is defined over F. Thus E=K0 F and the complete filtered data retain finite local-field descent. No unramified/tame assumption is made; all fields here have characteristic zero, including when p=2 or p divides2M.

The precise degree is relative to the augmented splitting field k=K0 H containing mu_(2M). If H_base was already fixed before adjoining those roots, the total relative degree over K0 H_base is at most2M phi(2M), not silently2M. The Wronskian alternative works over H_base with degree M²+1. Accordingly the minimum of these two upper bounds is available over that fixed starting field. Neither is an absolute bound over K0 independent of splitting data.

## 6. Integration into the entire endomorphism-stable filtration

Keep the source's full hypotheses: A0/Fbar_p has rational CM-field action, polarization inducing conjugation, rank2s over E_CM tensor K0, and an invertible Rosati-symmetric u with ue=bare u. Set D=H1_cris(A0)[1/p] and B=beta(−,u−). The source semisimplicity proof decomposes D_k into B-symplectic blocks M_(tau,z) of dimension2m_(tau,z), and u exchanges opposite embeddings, with B(ux,uy)=z B(x,y).

Apply §4 independently to one block in each opposite pair, using the ONE E/k of §5 and M=max m_(tau,z). Assign the opposite Lagrangian by u. Their sum L is E_CM- and u-stable and beta-Lagrangian with dimension s at each E_CM embedding. For any E_CM,u-stable isocrystal subobject D' over K0, every M'=D'_k cap M_(tau,z) is a k-subspace. Hence (C1) applies simultaneously to ALL such D', including those whose block coordinates do not descend to H.

Retain the source's slope grading even when Frobenius permutes the blocks. Its slopes lie in[0,1]; B pairs slope lambda with1−lambda; a block of dimension2m has Newton sum m. For a-dimensional M', its Newton sum is at least max(0,a−m), since the quotient has dimension2m−a and slopes at most1. Therefore

    dim(L cap M'_E)=max(0,a−m)<=Newton_sum(M').

Summing gives t_H(D')<=t_N(D') for all stable D', and equality for D itself.

For arbitrary isocrystal subobjects P, define f(P)=t_H(P)−t_N(P). Values form a finite set, and

    f(P)+f(Q)<=f(P cap Q)+f(P+Q).

Maximizers are closed under sums and intersections, so there is a unique largest maximizer. Filtration-preserving automorphisms E_CM^times and u fix it. Its defect is thus nonpositive by the stable tests. All P satisfy the weak-admissibility inequality. Geometric cocharacter membership is exactly the source balanced-polarized orbit calculation, and descent to F has just been supplied. Colmez–Fontaine and the source transport can therefore be applied with their unchanged hypotheses. No missing weak-admissibility or opposite-block compatibility is left merely asserted.

## 7. What is optimal and what is not

For one symplectic2M-space, the degree2M is minimal among finite field extensions admitting a half-dimensional subspace with (C1), whether or not it is Lagrangian. To prove this, write d=[E:k] and expand a vector of L in a k-basis of E as a d-by-2M matrix. If a nonzero such matrix had rank<=M, its rows would span a k-subspace W of dimension<=M with the vector in W_E, contradicting (C1). Hence all nonzero matrices have rank>=M+1, so d>=M+1.

Delete M rows of each matrix. The resulting linear map on L is injective, because a vector in its kernel would have rank<=M. Since dim_k L=dM, dimension counting gives

    dM <= (d−M)2M,  hence d>=2M.

This is the usual rectangular rank-metric Singleton argument. It concerns universal subspace transversality over the FIXED k, not the minimum field degree for weak admissibility of a particular isocrystal. Its apparent sharpness supplies no lower bound for the actual abelian lift or for cycle denominators.

## 8. Outcome of this calculation

The full constrained filtration is constructed with the relative field bound above. This goes beyond naming a hard gap or repeating rational specialization. But the identifiable operations after source reduction are generalized Moore nonvanishing, an alternating trace form, symplectic reduction and the source's maximality/slope argument. They are compatible classical/primary operations. This note does not nominate them as a substantial theorem, assign a contribution grade, or weaken any old scope.

The remaining arithmetic question is different: bounded integral level/marking in a period fiber and bounded integral cycle image. Existence of a point after finite extension is already paid by the source and primary uniformization. The separate period-fiber note traces that stronger interface; a flag-field estimate cannot be relabeled as its solution.
