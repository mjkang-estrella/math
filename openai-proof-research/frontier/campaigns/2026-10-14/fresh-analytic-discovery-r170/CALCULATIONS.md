# r170 — integrated calculations, before any theorem freeze

Authorized Codex / GPT-6 Astra / high / default service tier. These are local research deductions from stipulated-true pinned proofs, not a frozen nominee, independent review, or mathematical grade. The pin is fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Both complete canonical manuscripts, including their nested includes and bibliographies, were read before this notebook was written. Primary versions and selected history are recorded privately.

Write AP for *Approximation Paving over Arbitrary Maximal Abelian Subalgebras*, and QSP for *Quadratic Strong-Operator Paving over Arbitrary Maximal Abelian Subalgebras*, both dated September 25, 2026. Paving partitions may contain zero projections. All Hilbert spaces and algebras are complex; no separability is assumed in the conclusions below.

## 1. Exact source interfaces and the construction pursued

For a partition P=(p_i) in a MASA A of a represented von Neumann algebra M⊂B(H), put S_P(z)=Σp_i z p_i. QSP thm:main chooses r_ε=⌈4·10^8 ε^−2⌉+⌈4/ε⌉+1 before M,A,x,F,δ, and gives, for every self-adjoint x and every finite F⊂H and δ>0, a=a*∈A, ∥a∥≤∥x∥, and q=q²=q*∈M with

    ∥(1−q)ξ∥<δ (ξ∈F),   ∥q(S_P(x)−a)q∥≤ε∥x∥.

Neither q∈A nor a partition independent of the strong neighborhood is promised. AP thm:main gives y=y*, ∥y∥≤3∥x∥, strong approximation on F, and ∥S_P(y)−a∥≤ε∥y∥ with ∥a∥≤∥y∥, at O(ε^−6) colors. Its quadratic expected-MASA corollary is already explicit. The error relative to the *actual* approximant norm must be preserved.

The integrated construction pursued here is a common partition for m self-adjoint operators at linear rather than exponential cost in m, followed by contractive approximants with the same quadratic ε exponent. The finite input already supplies linear multipaving: Ravichandran–Srivastava (RS), arXiv:1706.03737v2, Theorems 15, 25 and the full Section 5 proof. The point is to run that input through the operative QSP proof, not to invoke its scalar theorem m times.

## 2. A signed tuple polynomial, with exact normalization

Fix m≥1 zero-diagonal Hermitian contractions T_1,…,T_m on a finite common site set I. Use one supporting graph, the union of their supports. At an unassigned vertex choose uniformly a triple

    (color i, operator j, sign σ) ∈ {1,…,r}×{1,…,m}×{±1}.

At an assigned vertex retain its color, and choose uniformly (j,σ). For each triple use the matrix σ D_W T_j D_W−diag(τ_v W_v), restricted to the sites where that triple is allowed. Here τ_v=t before assignment and βt afterwards, β=80. Average the characteristic determinant of the disjoint triple blocks. Call this polynomial P_I; deletion of v gives Q_v.

The normalized determinant-derivative expression in QSP lem:polynomial-quotients applies to this finite list of allowed matrices: at each site differentiate k_v−1 times and divide by k_v!, where k_v=2mr or 2m. Its proof is the Leibniz calculation for a list of matrices, not a property specific to two signs of one T. Thus ∂_{z_v}P_I=P_{I\{v}}, half-plane stability, real-rootedness, and

    F_v=P_I/Q_v=z+a_v−∫(z−s)^−1 dκ_v(s),   κ_v≥0

hold. The rooted probability measure ρ_v has transform 1/F_v. Conditioning on a color keeps Q_v fixed; the color-conditioned residues average to the parent residues with weights 1/r. Increasing the shift by (β−1)tW_v therefore satisfies QSP lem:assignment verbatim. In particular min_i(d_v^i−d_v)≤24 m_v, where m_v=∫s_+dρ_v. This notation m_v is a local cost, not the family size m.

There are two changed endpoints:

* All sites unassigned: RS Theorem 25 applied to the 2mr-tuple gives largest unshifted root <3/√(mr). Hence t>3/√(mr) gives zero initial positive-root cost, for every principal restriction and all positive weights, by the exact multiaffine positivity argument in QSP lem:finite-cost-endpoints.
* All sites assigned: each color contributes χ[T_1|_C,−T_1|_C,…,T_m|_C,−T_m|_C]. RS's replacement-by-zero monotonicity, proved for zero-diagonal complex Hermitian tuples in Theorem 15/Proposition 16, permits retaining any one signed entry. The resulting polynomial is det(zI−(±T_j|_C)/(2m)). Consequently its largest root is at least (2m)^−1 max_j∥T_j|_C∥. The weighted-coordinate argument now shows that a fully assigned ball with max_j∥(T_j)_c∥>2mβt+α forces cost at least (α/(2m)) min_v W_v.

This last factor 2m is necessary in this reduction. Keeping the old factor 2 would incorrectly suggest that more matrices make paving easier.

## 3. Why the nonsingular measurable proof survives the extra label

Here are the operations that must be checked rather than hidden under “repeat the proof.”

Every outcome is a direct sum of principal matrices drawn from the T_j, and has norm at most 1 before weights/shifts. At a root, the off-diagonal contribution to the second rooted moment is

    Σ_{u≠v} W_vW_u E[1_{ω_u=ω_v}|(T_{j(ω_v)})_{vu}|²].

Condition on ω_v and bound the probability at u by 1. Each selected T_j has squared row sum ≤1, so this is ≤K W_v² when neighboring weights have ratios in [K^−1,K]. This also holds under a color condition at v. Thus all rooted/deletion moment bounds, compact support under an upper weight cutoff, and uniform integrability survive without a factor growing with m.

The cycle expansion still has connected supports in the union graph, so each fixed Laurent coefficient is local. The invariant integral change formula still telescopes each polynomial moment and uses mass transport. For deletion comparison, perturb *all* 2m signed operator matrices of the selected color in the same root-band rows and columns. Every such matrix has perturbation norm ≤2|ζ|√K b_2+|ζ|²b_2. In the determinant expansion the conditional color probability is still 1/r, and the logarithmic derivative is still (2/r)Σ_v λ_v J_i(v,z). Thus the upper-half-plane derivative bound is uniform in the upper weight cutoff. The finite list is larger, but no argument bounds the norm of their sum.

It follows that QSP lem:rank-comparison, lem:homogeneous-costs and lem:strip-locality have the same conclusions for this tuple. Their constants may depend on the fixed finite family, graph, r,t, degree/cocycle bounds, and the prescribed ball radius; none of those approximation constants sets the final color count. The Maharam measure/cocycle cancellation, joint lower/upper cutoff passage, and conditioning on fresh times *before* the limit are unchanged. The bad-ball proof uses the changed lower cost α/(2m), which enlarges its failure-probability constant but not the palette. The hazard iteration can still make its cost arbitrarily small after the number of colors is fixed.

The finite permutation action on the r color names commutes with all these operations. Uniform tie permutations and completion labels therefore give conditional color marginals exactly 1/r. Operator/sign labels are internal polynomial choices; they are not extra output colors.

The resulting precise measured conclusion is: for fixed r and t>3/√(mr), every finite radius L and α,η>0 admit a single Bernoulli coloring with uniform conditional marginals and

    μ̃{ max_{1≤j≤m} ∥(T_j)_{B(v,L),c}∥ ≤2mβt+α }>1−η.

This is the source's full nonsingular/Bernoulli interface for a tuple. It is not a measurable selection of independently found finite pavings, nor an exchange of an infinite ball limit with the color construction.

## 4. One model partition and one actual compression

Suppose first A lies in the centralizer of a faithful normal state φ. The source's separable reduction is run starting with all m operators, still a countable set. Normalize each nonzero x_j separately to ∥x_j∥=1. Put

    a_j=E_Ax_j, y_j=E_Nx_j−a_j, w_j=x_j−E_Nx_j.

Here y_j,w_j are self-adjoint of norm ≤2; E_Ay_j=0 and E_Nw_j=0. Approximate all y_j at once by finite-support Cartan y_{j,n} with norm ≤2 on a common union graph, cutting the finite union of cocycle ratios. The graph bounds may grow with n.

Use r=⌈4·10^8 m ε^−2⌉ and t=4/√(mr), α=ε/32 in Section 3, with ball radius n and failure η=(ε/16)^{2n}. In K=M*_N Ñ, the shared color projections satisfy Ẽ_N(p_i)=1/r. For every j the Cartan bound is

    2(2mβt+α)=1280√(m/r)+ε/16≤253ε/2000<ε/4,

and the source free-compression lemma gives simultaneously

    ∥Σ_i p_i w_j p_i∥≤2/r+4/√r<ε/4.

Uniform marginals suffice for each w_j; their mutual freeness is unnecessary. For each j the high-moment path argument and clipping in QSP completion.tex give a bounded state-null difference between Z_{j,n}=Σ_i p_i(x_j−a_j)p_i and operators of norm ≤3ε/4. The multiplier-calculus lemma handles the varying sequences without prescribing an exponentially fast Cartan approximation rate. Therefore, for each *fixed* integer k,

    limsup_n Φ(Z_{j,n}^{2k})≤(3ε/4)^{2k}.

Fix a lost-mass tolerance ρ>0, choose k with m(3/4)^{2k}<ρ/4, and then n. Approximate the one shared partition by one finite-symbol cylinder partition. Transfer the finite sum of its m even moments by QSP prop:moment-transfer. That proposition already permits arbitrary fixed M-letters in fixed words, including different x_j. Its shortest-pair/kernel proof needs no extra independence among them. Positivity of the sum gives a deterministic evaluated partition P⊂A with

    φ(B)<ρ ε^{2k},   B=Σ_j z_j^{2k}≥0,   z_j=S_P(x_j)−a_j.

Take q=1_[0,ε^{2k}](B). Then φ(1−q)<ρ, and q commutes with every p_i because B does. For a unit vector ξ∈qH,

    |⟨z_jξ,ξ⟩|^{2k}≤⟨z_j^{2k}ξ,ξ⟩≤⟨Bξ,ξ⟩≤ε^{2k}.

The first inequality is scalar Jensen for the spectral probability measure of z_j at ξ. Self-adjointness now gives ∥qz_jq∥≤ε simultaneously. No operator-convexity of t↦t^{2k} is invoked. No intersection of noncommuting high-state-mass projections is used.

This proves the faithful-central-state multipaving interface with count R_m(ε)=⌈4·10^8 m ε^−2⌉ and arbitrary ρ, with the exact fixed diagonals a_j=E_Ax_j. It also supplies, for fixed ε, partitions with arbitrarily state-small spectral excess for each z_j; their clipped corrections have norm at most 2.

## 5. The corner without centralizing normal functionals

For a MASA D⊂P with no nonzero centralizing normal positive functional, the proof of QSP lem:no-central works on a finite tuple with one coloring. Here are the joint choices.

Fix a normal state φ and T(z)=h_φ^{1/4}z h_φ^{1/4}. Choose a coarse partition P_0 with ∥S_{P_0}(h_φ^{1/2})∥_2 small. A *joint* weak-star subnet of (S_P(x_1),…,S_P(x_m)) has a limit (b_1,…,b_m)∈D_sa^m with each norm ≤1. Convexity in the Hilbert direct sum L²(P)^m gives a single convex combination approximating (T(b_j))_j. The independent coarse-cell choice used by QSP has summed variances at most mκ². Choose one realization with all errors small by bounding their squared sum. One further independent r-coloring of its cells has summed variances at most 2mκ² and mean

    E S_col(x_j)=x_j/r+(1−1/r)S_R(x_j).

Since m is fixed and κ can be arbitrarily small, the same partition makes every

    v_j=S_col(x_j)−(1−1/r)b_j−x_j/r

arbitrarily small in the symmetric seminorm, with ∥v_j∥≤2. QSP's positive-cone/Jordan and spectral-cut argument, applied to each v_j, now gives projections q_j with arbitrarily small φ(1−q_j) and ∥q_j v_j q_j∥≤ε/4. Set r=⌈8/ε⌉ and a_j=(1−1/r)b_j. Thus ∥q_j(S_col(x_j)−a_j)q_j∥≤3ε/8.

To get one projection, put D=Σ_j(1−q_j), choose s=(ε/16)², and q=1_[0,s](D). Then φ(1−q)≤φ(D)/s can be made arbitrarily small, and ∥(1−q_j)q∥≤√s for each j. For z_j=S_col(x_j)−a_j, ∥z_j∥≤2, expansion around q_j gives

    ∥qz_jq∥≤∥q_jz_jq_j∥+4√s≤5ε/8<ε.

Again this is a spectral approximate intersection, not a claimed state union bound for projection meets. The number of colors here is independent of m; only the approximation tolerances depend on it.

## 6. Arbitrary algebra and representation

Let e be the supremum of supports of A-central normal positive functionals, h=1−e. AP gen:support-decomposition supplies e∈A, a faithful normal expectation on eMe, and the no-central-functional property on hMh. Alternatively QSP prop:state-reduction supplies the directed central support construction.

Given finite F and δ, choose a central support f≤e with e−f small on F. On fMf use Section 4 with a faithful central state. Small mass for that state makes every fixed normal vector functional small, exactly as proved in QSP state reduction. On hMh use Section 5 for the sum of the vector functionals. Discard g=e−f. Use disjoint palettes for f,h,g, and take corner sums of the diagonals and compression projections. Cross-corner terms of every x_j disappear under this partition, even though f,h,g need not be central in M. The diagonal norms remain ≤1 and the common q approaches 1 on F. Hence the retained calculation is the following fully quantified conclusion:

For every m≥1 and 0<ε<1, let

    r_m(ε)=⌈4·10^8 m ε^−2⌉+⌈8/ε⌉+1 ≤5·10^8 m ε^−2.

For every A⊂M⊂B(H), every x_1,…,x_m∈M_sa, finite F⊂H and δ>0, there are one r_m(ε)-partition P⊂A, a_j=a_j*∈A with ∥a_j∥≤∥x_j∥, and one projection q∈M such that

    ∥(1−q)ξ∥<δ (ξ∈F),
    ∥q(S_P(x_j)−a_j)q∥≤ε∥x_j∥ (1≤j≤m).

Zero operators are assigned diagonal zero and omitted from normalized tests. Scale each nonzero operator back individually. The palette was fixed before the inclusion, family, and neighborhood.

This is a retained integrated deduction, not a nomination. The linear family-size dependence is supplied by RS's actual mixed-tuple operation; the QSP measured/kernel machinery already has the generic finite-list interfaces used above. The apparently new common-cut difficulty is settled by scalar spectral Jensen. Contractive approximation is developed in CONTRACTIVE.md.
