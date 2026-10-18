# A small-slot telescope and its exact remaining finiteness obligation

Author-side derivation supporting the frozen T253F investigation, not a nominee. Source truths at fd4aeeb2 are stipulated. Let G=A_m for a fixed finite positive m, with the source's fixed λ and polygon space X. We use the source's strict comparison and alternating-extension lemmas exactly. The latter explicitly applies in arbitrary clopen regions.

## 1. Bonding maps by restriction

Put Q_b=[0,τ^(−b)]² in a single track, interpreted in the Boolean algebra, and s_b=μ(Q_b)=τ^(−2b). These are nested nonempty clopen polygons. Let E_b be the semisimplicial set of ordered tuples of pairwise disjoint piecewise-translation embeddings Q_b→mX. G acts by postcomposition. Define

    r_b:E_b→E_(b+1),  (e_0,...,e_p)↦(e_0|Q_(b+1),...,e_p|Q_(b+1)).

These are genuine equivariant semisimplicial maps. The restricted images remain disjoint and nonempty, so distinct entries in one simplex do not coalesce. Nothing is asserted about injectivity on the entire vertex set: distinct embeddings can have the same restriction. No tiling of Q_b by smaller squares is required. This repairs the previously missing bonding-map obligation in r31, without changing the full target or the source groups.

## 2. Quantitative connectivity, including homotopy

If R vertices of E_b are specified and (R+1)s_b<m, the union of their images has area at most R s_b. Strict comparison embeds Q_b in its complement, providing a vertex disjoint from every specified vertex. Prepending that vertex cones any semisimplicial subcomplex using only the specified vertices. The ordered convention causes no problem: faces of (w,e_0,...,e_p) are the original simplex and the prepended faces, so this is the usual topological cone.

Here is a bounded-vertex construction that upgrades the source's chain contraction to homotopy connectivity. Set B_0=3 and B_p=p+3+(p+1)B_(p−1) for p>=1. Fix one base vertex v. For each vertex x, choose w_x disjoint from both x and v and use the path x—w_x—v. This homotopy on the zero-skeleton uses at most B_0 vertices on each vertex prism. Inductively suppose the homotopy from the identity to v is defined compatibly on the (p−1)-skeleton and uses at most B_(p−1) vertices on each face prism. The boundary of a p-simplex prism has image supported on at most

    (p+1)+1+(p+1)B_(p−1)=B_p−1

vertices: the bottom simplex, the constant top, and its p+1 face homotopies. Choose a vertex w disjoint from all these vertices and cone the boundary map. A prism is a ball and is homeomorphic relative its boundary to the cone on that boundary; composing with the cone map gives the extension. On overlaps it agrees with the already constructed homotopy. The image is supported on at most B_p vertices and has dimension at most p+1. This works separately on every p-simplex; the CW weak topology gives a continuous global skeletal homotopy. Choices need not be equivariant.

Consequently, when B_d s_b<m, the identity of the d-skeleton of |E_b| is nullhomotopic into its (d+1)-skeleton. Cellular approximation implies that |E_b| is d-connected. The same conclusion holds for a truncation at any dimension at least d+1. This argument supplies actual nullhomotopies, not merely vanishing homology or a zero direct limit.

## 3. Finite cell orbits and a contractible G-complex

Start at b_* large enough that m/(11s_b)>=1. Put

    d_b=floor(m/(11s_b))−1,
    Z_b=|E_b restricted to degrees <=d_b|.

The integers d_b are nonnegative, nondecreasing and tend to infinity. Restriction maps carry Z_b into Z_(b+1). For p<=d_b,

    10(p+1)s_b <= 10m/11 < m.

For two p-simplices, composing their parameterized embeddings gives a piecewise-translation bijection between their image unions. The source alternating-extension lemma extends this bijection to G. Thus G is transitive on p-simplices for each p<=d_b. Such simplices exist by successive strict comparison, because (p+1)s_b<m. Each Z_b has finitely many cell orbits in total. There are no inversions: stabilizing an ordered simplex fixes each parameterized embedding and hence the simplex pointwise.

Let T be the mapping telescope of Z_b and the restriction maps. The cellular mapping-cylinder construction makes T a G-CW complex. A finite stage T_B, containing levels b_* through B and the intervening cylinders, has finitely many cell orbits and G-equivariantly deformation retracts onto Z_B. For each d, all sufficiently large B satisfy both B_d s_B<m and d_B>=d+1, so T_B is d-connected. Any map of a sphere into T has bounded height, lies in a finite stage, and becomes nullhomotopic in a sufficiently late stage. Thus T is weakly contractible and, being a CW complex, contractible.

This is also an essentially trivial system in Brown's sense: for each homology/homotopy degree, all sufficiently late stage groups are already zero. It is stronger than merely a zero direct limit. Brown's allowance of noninjective equivariant bonding maps is consistent with this construction; the telescope supplies literal inclusions of finite stages if desired.

## 4. Exact stabilizers and the unresolved obligation

For a simplex σ=(e_0,...,e_p), let W=mX\union_i e_i(Q_b). Its point stabilizer is exactly

    G_σ=A_m ∩ F(W),

with elements extended by the identity outside W. It contains A(W), but equality has not been asserted. Prism-cell stabilizers in the telescope are the corresponding source simplex stabilizers. The vertex corresponding to the standard inclusion Q_b⊂mX has stabilizer

    G_b=A_m∩F(mX\Q_b).

Brown (1987), Theorem 2.2, requires stabilizers of p-cells to be FP_(n−p), in addition to the verified acyclicity and finite-orbit filtration. Thus it cannot be applied to this telescope merely because T is contractible. A sufficient remaining statement, for each n, is that a tail of these complexes has all its p-simplex stabilizers of type FP_(n−p), for 0<=p<=n. This includes FP_n for its vertex stabilizers. Prism cells impose only weaker requirements on the same groups. A choice of a different tail for each n would be allowed, but no such stabilizer theorem is proved.

In particular, an induction assuming only FP_(n−1) for all punctured-region groups does not close: Brown asks for FP_n at vertices. The decrease in area is not a well-founded induction on a discrete parameter. The full group's ordinary coefficient homology, the source's low-degree argument and Li's reduction homology invariance do not establish this module-resolution condition.

The companion note `reduction-obstruction.md` proves that, for every square m>1, all sufficiently late standard vertex stabilizers G_b are not even abstractly isomorphic to any A_ell. This closes the proposed normalization to standard track groups on those tails; it does not show that G_b fails FP_n or F_infinity. Other constructions or a direct finiteness theorem for these reductions remain possible.

T253F remains unresolved at its frozen full scope. The telescope and the normalization obstruction are technical support and route diagnostics, not substitute targets or countable results.
