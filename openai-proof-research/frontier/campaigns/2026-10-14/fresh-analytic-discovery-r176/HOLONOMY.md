# A controlled charge representation and an explicit comparison unitary

These are prefreeze feasibility derivations, not a frozen theorem. The source graph throughout this note is the REDUCED disc graph X=X^D. The calculation integrates its actual small-loop operation with the maximal source's universal averaging operation. It does not transfer a kernel assertion from one assembly map to another.

The operation being investigated is whether scalar winding persistence can be retained in a new common construction with a maximal null-index transfer. Before trying to manufacture such a transfer, one must calculate what its curvature does in the universal completion. The calculation below closes that preliminary question for an explicit central holonomy. It does not settle the full construction.

## 1. One coherent family of charge functions

Let J(A) be the threshold in the reduced source's small-loop lemma. Choose nondecreasing integer radii r_j→infinity so slowly that every closed path in X_j of length ≤3r_j has zero charge. For example, take increasing thresholds M_n≥max(n,J(3),...,J(3n)), and let r_j be the largest n≤j with M_n≤j; omit the finitely many indices with no such n. This choice uses only the stipulated small-loop result and requires no effective bound for the chosen transcendental t.

For d(x,y)≤r_j define b_j(x,y) as the charge of a path from y to x of length ≤r_j. This matrix-entry convention is source-to-target. For three vertices of pairwise distance ≤r_j,

    b_j(x,y)+b_j(y,z)=b_j(x,z),   b_j(y,x)=−b_j(x,y).

Indeed two paths differ by a loop of length ≤2r_j; a triangle uses ≤3r_j. Also |b_j(x,y)|≤r_j, and on any actual path of bounded length the computed charge agrees for all sufficiently large j. A single coherent choice r_j is preferable to unrelated tests at every scale: it permits products of operators with different fixed propagation bounds.

Put H_j=l²(X_j) tensor H_0, E_j=C(S¹,K(H_j)),

    E=product_j E_j,   E_0=c_0-direct-sum_j E_j,   Q=E/E_0.

The product is the C*-algebra of norm-bounded sequences of continuous functions. There is NO assertion of uniform equicontinuity in the circle parameter. It is not silently replaced by C(S¹,product K). All spatial stabilizations occur in the already ample H_j.

## 2. The actual homomorphism on the maximal Roe algebra

For algebraic T of propagation R, discard its finitely supported cross-component part. Define, whenever r_j≥R,

    (theta_j(T)(z))_{xy}=z^{b_j(x,y)} T_{xy},  z in S¹,

and define theta_j(T)=0 at the remaining finitely many indices. Each X_j is finite, so theta_j(T) is a continuous compact-operator-valued function, even if the compact entries have unbounded ranks as j varies.

A matching decomposition of the support of T has at most c_R=2N_R−1 colors. On one matching, scalar phases preserve the block operator norm. Therefore

    sup_{j,z} ||theta_j(T)(z)|| ≤ c_R ||T||op.

This makes [theta_j(T)] an element of Q. Changing finitely many initial definitions changes nothing there. Additivity is exact in Q by choosing a common propagation bound. If T,T' have propagation R,R', then for all sufficiently large j the three vertices in each product summand have pairwise distances at most R+R'≤r_j. The cocycle equation gives

    theta_j(TT')=theta_j(T)theta_j(T')

on those components. Cross-component multiplication defects involve finitely many vertices and also disappear in Q. Adjoint preservation follows from antisymmetry of b_j. Thus

    Theta_0:C[X]→Q,   T↦[theta_j(T)]

is an ACTUAL algebraic *-homomorphism. Composing with a faithful representation of Q and using the universal definition gives

    ||Theta_0(T)||≤||T||max.

It extends to Theta:A_X→Q. No bound independent of R in the concrete norm has been shown or used. In particular, this argument does not extend Theta to C*(X).

These are the explicit controlled-matrix versions of the product/quotient holonomy mechanism in Hanke–Schick and Hunger. We use the actual formulas rather than importing their fixed-base group-assembly theorems with changed hypotheses.

## 3. A bounded-propagation central holonomy

In every disc choose the same radius-one hexagon around the origin, based at a fixed vertex v. It has six edges, all vertices at rho=1, and charge +1 after choosing its positive orientation. At this ring every fibre is Q_{j−1}. Horizontal transport around it is therefore

    W_j delta_q=delta_{q g_{j−1}}

on the distinguished fibre F_j over v. This permutation has propagation ≤6 IN X_j: the six transported horizontal edges furnish the path. Its displacement need not be bounded in the intrinsic Cayley metric of Q_{j−1}. Confusing these two metrics would remove the point of the construction.

Extend W_j by the identity outside F_j and set W=direct-sum W_j. It is a bounded finite-propagation unitary and hence a maximal multiplier. Let E_F be the projection onto all F_j, and let e be a fixed rank-one projection on H_0, repeated at all vertices. Put E=E_F tensor e. E is a propagation-zero locally compact projection in C[X]. W commutes with E.

The global left SL_3(Z) action preserves every fibre and is generated by propagation-one unitaries U_s. The maximal source's multiplier argument applies verbatim to this bounded-geometry graph. The universal group Kazhdan projection gives P in M(A_X), and

    P_n=(1−Delta/2)^n → P in maximal multiplier norm.

Write rho<1 for the common contraction factor away from invariant vectors. Thus ||P_n−P||≤rho^n in that norm. P commutes with W and E, because left multiplication commutes with right transport and preserves the chosen fibre. Q_F=PE is consequently a projection in A_X.

Define the unitary

    u = 1 + PE(W−1)  in A_X^+.

On the corner PE it is W and on its orthogonal complement it is the identity, so u*u=uu*=1. Local compactness comes from E; P alone is not locally compact.

Under lambda:A_X→C*(X), P is projection onto constant vectors in every finite fibre. W fixes those constants. Therefore

    lambda(u)=1.

This is an operator identity, before taking K-theory.

## 4. Its image under Theta, without assuming a multiplier extension

We do NOT assume Theta extends nondegenerately to the whole multiplier algebra. Instead compute the algebraic approximants P_n E(W−1). For fixed n and late j, a Cayley path occurring in P_n has charge zero, whereas that path followed or preceded by W_j has charge one. The charge identities hold because r_j eventually exceeds n+6 and the required triangle bounds. Hence

    theta_j(P_n E(W−1))(z)
       = P_{n,j} E_j (z W_j−1).

In this displayed formula E_j denotes the spatial projection E restricted to H_j, not the function algebra used above. Let p_j be projection onto the normalized constants in l²(F_j), and let q_j=p_j tensor e, a RANK-ONE projection in K(H_j). Concrete Kazhdan convergence is uniform over j, so the last family converges in the product norm, as n→infinity, to

    (z−1) q_j.

Maximal convergence of P_n E(W−1) to PE(W−1), contractivity of Theta, and the quotient norm therefore give

    Theta^+(u) = [ z↦1+(z−1)q_j ]_j.                 (1)

The image is not zero: its distance from 1 in Q^+ is two. Consequently ||u−1||max=2, while ||lambda(u)−1||=0. This distinction is produced by one controlled, explicitly defined operator; it is not a complaint about the stipulated source proof.

## 5. The K_1 calculation does not use an unjustified product formula

For each j, the unitary z↦1+(z−1)q_j has winding +1 under the usual K_1(C(S¹,K))=Z convention. To detect its class in Q, it is enough to construct a homomorphism

    d:K_1(Q) → (product_j Z)/(direct-sum_j Z).

We do not assume K_1(product E_j)=product K_1(E_j). The coordinate maps do give a homomorphism K_1(E)→product Z. In the six-term exact sequence for 0→E_0→E→Q→0, the map K_0(E_0)→K_0(E) is injective: a finite-support class with a nonzero coordinate remains nonzero under that coordinate evaluation. Thus the connecting map K_1(Q)→K_0(E_0) is zero and K_1(E)→K_1(Q) is onto. Two lifts differ by the image of K_1(E_0)=direct-sum Z. Coordinate winding modulo the direct sum is therefore a well-defined d.

The representatives in (1) really do form a unitary in E^+: their differences from 1 are compact-valued and have norm at most two, and the scalar part is the SAME 1 at every coordinate. Therefore

    d(Theta_*[u]) = [(1,1,1,...)] .                  (2)

Every nonzero integer multiple of this sequence is nonzero modulo the direct sum. In particular [u] has infinite order in K_1(A_X) and lambda_*[u]=0. No claim that [u] is an assembly image was needed for this calculation.

This auxiliary calculation is not being offered as the desired new substantial theorem. Full-versus-reduced Kazhdan corners and product/quotient index detection are actual primary mechanisms; applying them to the source's short-loop data does not by itself identify an additional nonroutine theorem-sized bridge. Parent may assess the derivation separately, but this packet assigns it no mathematical grade.

## 6. The exact missing index identification is kept separate

The geometric boundary class alpha_D in KX_1(X) is already infinite order and has zero reduced index. A natural further comparison is to identify its maximal index with the corner holonomy [u], or at least to prove that Theta_*mu_max(alpha_D) has the sequence (1,1,...) as its winding detector. Such a statement needs an actual common controlled representative and a comparison of the odd exponential index with the circle-holonomy family. Winding resemblance alone does not give it.

On a single circle of length L, the flat family with holonomy exp(2πit) has the Dirac spectral progression 2π(k+t)/L; after a fixed small shift, one eigenvalue crosses zero in a positive traversal. This gives the expected family index +1. The remaining assembly comparison must carry this family through the changing Rips modules, vertex block choices, the polynomial exponential formula, and ONE uniform propagation/approximation bound. Hunger's actual fixed-finite-complex theorem supplies the abstract index mechanism in its scope, not these changing-space identifications automatically.

We do not assert that mu_max(alpha_D)=[u], do not infer it merely from (2), and do not infer impossibility of any neighboring maximal-kernel construction. The explicit [u] computation above is independent of that uncompleted comparison.
