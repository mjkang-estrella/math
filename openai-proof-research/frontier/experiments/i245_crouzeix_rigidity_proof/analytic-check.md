# I245 — independent proof check of E4

**Verdict: PASS.** Exact reviewed input: `frontier/experiments/i242_crouzeix_four_dimensional_rigidity/analytic-attempt.md`, SHA-256 `03c0f05cef564e1bde2630ed725ff755d3bb603ea07dbd39a711e595e96d6627`. The completed argument (after its explicitly superseded partial notes) proves the stated attained-polynomial E4 relative to the stipulated pinned operations and the named external scalar theorem. No mathematical correction is required. Details below make several compressed transitions explicit; they do not replace a missing inverse estimate or add a hypothesis.

## 1. Quantifiers and normalization

For every finite coefficient size m, finite polynomial degree, 1≤n≤4, A∈M_n(C), and M=max_{W(A)}||P||>0, the hypothesis is actual attainment ||P[A]||=2M. The conclusion is a positive-radius disk W(A) and unit coefficient vectors u,v with p=v*Pu satisfying ||p(A)||=2M and max_{W(A)}|p|=M. The further conclusion p(a+ρz)=Mηz^k, |η|=1, 1≤k≤deg P, also follows. Neither a supremum over changing witnesses nor a limiting coefficient dimension is used.

Normalize P by M. Under a unitary irreducible reducing decomposition A=⊕B_j, evaluation is the corresponding direct sum (up to the fixed tensor permutation). Thus some B satisfies ||P[B]||=2. The pinned inequality and W(B)⊂W(A) give 2≤2 max_{W(B)}||P||≤2. Scalar blocks have evaluation norm at most one and cannot be active. An irreducible block of size ≥2 has numerical range with interior: otherwise, after affine rotation, all its quadratic forms are real, making it Hermitian and reducible. If Bv=λv at a boundary point, a supporting Hermitian pencil has v in its top eigenspace. Combining this equality with Bv=λv yields B*v=barλv. This is a reducing one-dimensional subspace, a contradiction. Hence σ(B)⊂int W(B). This proves the spectral separation actually needed later, including repeated eigenvalues.

## 2. Exterior derivative estimate: sign, branch and strong convergence

Let K=W(B), with 0 temporarily chosen in its interior, and let rDbar⊂K⊂Ω_j⊂RD be analytic convex outer approximations. The pin supplies Ω_j and exterior conformal collars. Normalize h_j(z)=c_jz+c_0j+O(z^−1), c_j>0. Schwarz applied to r/h_j(1/w) gives r≤c_j; applied to 1/Φ_j(R/w), Φ_j=h_j^−1, gives c_j≤R. The mean of h_j on T gives |c_0j|≤R.

For z=e^{it}, the positively oriented tangent is izh'_j. Its argument derivative is Re(1+zh''_j/h'_j). Convexity makes this nonnegative, even if curvature vanishes at isolated points. The harmonic minimum principle gives Re g_j≥0 throughout |z|>1, with g_j(∞)=1. Herglotz after the reciprocal change of variable supplies a probability measure μ_j and

    g_j(z)=∫(z+ξ)/(z−ξ) dμ_j(ξ).

Because h'_j has no zero and the exterior together with infinity is simply connected, there is a single logarithm L_j=log(h'_j/c_j), L_j(∞)=0. Its logarithmic derivative is

    z L'_j(z)=g_j(z)−1=2∫ξ/(z−ξ) dμ_j(ξ).

Now z(d/dz)log(1−ξ/z)=ξ/(z−ξ), so the sign is **positive**:

    L_j(z)=2∫log(1−ξ/z) dμ_j(ξ).

Every scalar logarithm is the branch zero at infinity. Since |1−ξ/z|≤2, Re L_j≤log4 and |h'_j|≤4c_j. This holds up to the analytic boundary. It is an upper bound only; no false uniform lower derivative bound is needed.

Take subsequences c_j→c≥r and μ_j→μ weakly. Boundary Fourier coefficients are −2∫ξ^k dμ_j/k, k≥1, with zero constant. Their tails in squared L² norm are at most 4Σ_{k>N}k^−2 uniformly in j. Coefficient convergence plus this tail bound gives strong L² convergence L_j→L. This also constructs the boundary L² logarithm if μ has atoms. Its real part is at most log4 almost everywhere by an almost-everywhere convergent subsequence. For complex s,t with Re s,Re t≤log4,

    exp(s)−exp(t)=(s−t)∫_0^1 exp(t+θ(s−t))dθ,

so |exp(s)−exp(t)|≤4|s−t|. Thus h'_j=c_j exp L_j converges strongly in L² to c exp L, and q_j=zh'_j does likewise. No weak-to-quadratic inference is used.

## 3. Identification of h, its boundary values and q

The boundary bound |h'_j|≤4R makes h_j|T equi-Lipschitz; their values have modulus at most R. Also h_j−c_jz has boundary modulus at most 2R, hence that same bound in the exterior by the maximum principle. These bounds give a subsequential holomorphic limit h on |z|>1 and a uniform continuous boundary limit, consistently on the closed exterior. Its leading coefficient c≥r prevents a constant limit; the nonconstant limit of univalent maps is univalent.

Here are explicit details of the inverse argument, rather than an appeal to an unverified boundary limit. Each fixed point of K is omitted by all h_j, hence also by h, by Hurwitz and nonconstancy. For any compact subset of C\K, Φ_j are eventually defined and satisfy

    |Φ_j(w)|≤(|w|+2R)/r.

A diagonal Montel subsequence has limit Φ, with |Φ|≥1. It cannot be constant: at large w the inequality |w−c_jΦ_j(w)|≤2R implies |Φ(w)|≥(|w|−2R)/R. The minimum-modulus principle applied to Φ yields |Φ|>1. Local uniform convergence in the compositions gives h(Φ(w))=w, and similarly Φ(h(z))=z. Thus h maps the exterior disk onto C\K. Uniform boundary convergence and Hausdorff convergence of the convex boundaries give h(T)=∂K: for surjectivity choose boundary points converging to a given point of ∂K and a convergent subsequence of their circle preimages.

Since ∂K is a Jordan curve, the boundary extension of this conformal map is a homeomorphism (the same Jordan-boundary theorem used in the fully read Jin Lemma 4, applied to the exterior). A regular analytic subarc permits Schwarz reflection of the map and its inverse after straightening the arc. Therefore h extends conformally with nonzero derivative locally across its preimage. This establishes that a nonempty open geometric arc has an open circle-interval preimage, not merely a nonempty possibly-null preimage.

Local uniform holomorphic convergence identifies the derivative limit with h' in the exterior. The strong boundary limit c exp L is its boundary derivative: integration along any exterior circle, followed by the L² boundary limit, or equivalently uniqueness of the reciprocal Hardy expansion, identifies the coefficients. Hence q=zh' is the actual boundary normal on the reflected arc. This identification is not inferred from weak convergence alone.

## 4. Bounded fixed-pair Faber normalization and exact residual

B is fixed, with σ(B) strictly inside K. The resolvent (wI−B)^−1 is continuous on a compact neighborhood of ∂K disjoint from σ(B); its norm is bounded there. This is not a normal-matrix estimate solely in terms of distance to spectrum. Uniform convergence of h_j on T gives uniform convergence of these resolvents. Therefore

    R_j=q_j(h_jI−B)^−1 → R=q(hI−B)^−1 in L²,

with a common L∞ bound, and H_j=R_j+R_j*→H in L². Positivity passes through an almost-everywhere convergent subsequence, so H≥0 a.e.

Fix any unit top singular pair x=vec(X), y=vec(Y) of P[B]. With M_j=max_{closure Ω_j}||P||→1, the same pair is a top pair of F_j=P/M_j, γ_j=2/M_j→2. The source identity and Parseval give

    a_j²=Σ_{k≥0}||Y*b_kj(B)X||_HS²=||Y*R_jX||²_L².

This is uniformly bounded. No varying singular vectors, changing coefficient size, lower bound on a_j, or uniform Faber collar width is required. All coefficient series are first justified at a fixed j by the pin; only the boundary fields are then passed to the limit.

Writing M_k=Y*b_kj(B)X, L_k=X*b_kj(B)Y, the cross norm is

    C_j=4||M_0||²+Σ_{k≥1}(||M_k||²+||L_k||²)
       =a_j²+Rres_j,
    Rres_j=3||Y*X||²+Σ_{k≥1}||L_k||².

Both ordered multiplier tests and reciprocal diagonal weights are exactly those in the source. Thus E_X=4a_j²/γ_j²−D_X≥0, E_Y≥0, E_B=D_X+D_Y−2C_j≥0 and

    E_X+E_Y+E_B+2Rres_j=2(4/γ_j²−1)a_j².

The right side tends to zero and every term on the left is nonnegative. Consequently X*Y=0 and E_B→0. The coefficient constant is three, the multiplier orders are both retained, and the source's unnormalized Hilbert–Schmidt convention is unchanged.

## 5. Quadratic passage and inertia, without square-root convergence

Set D=XX*−YY*, W=[X Y], J=diag(I_m,−I_m). Cyclicity and Hermitian symmetry give pointwise

    tr((W*H_jW)J(W*H_jW)J)=tr(H_j D H_j D)
                           =||H_j^(1/2) D H_j^(1/2)||_HS².

For the L¹ limit it suffices to expand

    H_j D H_j D−H D H D=(H_j−H)D H_jD+HD(H_j−H)D.

Finite-dimensional trace Cauchy–Schwarz and the bounded L² norms give convergence in L¹. The integral is E_B→0. Since H≥0, its limit is a nonnegative function with integral zero. Thus H^(1/2)DH^(1/2)=0 a.e. This does not require continuity, Lipschitz continuity, or convergence of the square-root map at singular matrices.

The last matrix identity means u*Dv=0 for any u,v in ran H^(1/2)=ran H. It is full total isotropy, not just vanishing of one trace. Because X*Y=0, ran X and ran Y are orthogonal. Hence D has inertia (p,q,d−p−q), p=rank X≥1, q=rank Y≥1. If L is totally isotropic, its projections to the positive and negative spectral subspaces have kernel L∩ker D: a vector with zero positive component must have zero negative component by its zero D-quadratic form, and conversely. Therefore

    dim L≤dim ker D+min(p,q)=d−max(p,q).

On a reflected arc with simple maximal support eigenvalue, writing ν=q/|q|,

    (hI−B)*H(hI−B)=2|q|[Re(barν h)I−Re(barν B)].

The bracket has nullity one, so rank H=d−1. The a.e. identity holds at some point of its open circle-interval preimage. Thus d−1≤d−max(p,q), forcing p=q=1.

The optional backward-moment conclusion is also valid: after the zero constant term, X*R_jY→0 in L² by its squared coefficient sum. Strong convergence identifies X*RY=0. The reciprocal Hardy uniqueness, q≠0 in the exterior, the open image of h, and the resolvent expansion at infinity give X*B^kY=0 for all k≥0. The rank argument only needs k=0, so it is not resting on an unnecessary stronger moment inference.

## 6. Simple support and positive curvature for d≤4

If no top eigenvalue of H_θ=Re(e^−iθB) were simple, the bottom would also always be multiple, by replacing θ by θ+π. For d=2,3 the largest and smallest eigenspaces cannot be disjoint spaces of dimensions at least two; thus each pencil value would be scalar. This contradicts irreducibility.

For d=4, centering B by tr(B)/4 makes each pencil value either zero or have eigenvalues ±s, each with multiplicity two. Squaring yields scalar H²=aI, K²=bI, HK+KH=2cI. If a=0 then H=0 and B is normal. Otherwise K'=K−(c/a)H anticommutes with H and squares to δI, δ=b−c²/a≥0. In H's two eigenspaces,

    H=√a diag(I₂,−I₂),  K'=[[0,C],[C*,0]],  CC*=C*C=δI₂.

For δ=0, K'=0. For δ>0, separate unitary changes on the two eigenspaces make C=√δI₂. Pairing corresponding coordinates exhibits two common two-dimensional reducing subspaces for H,K and B. Both cases contradict irreducibility. This checks the elementary calculation independently, not by invoking an unproved higher-dimensional pencil claim.

A simple top eigenvalue persists on an open θ interval. Differentiating H_θv=λv, with H''_θ=−H_θ, gives

    λ+λ''=2Σ_{j≠top}|v_j*H'_θv|²/(λ−λ_j).

All denominators are strictly positive. If it vanished, H'_θv would be parallel to v; then H_θ and H'_θ, hence B and B*, have a common eigenvector, contrary to irreducibility. Therefore the radius of curvature λ+λ'' is positive. The exposed point e^{iθ}(λ+iλ') parametrizes a regular analytic arc with outward normal e^{iθ}. This supplies exactly the arc required above, including nongeneric B with repeated ordinary eigenvalues.

## 7. Tensor scalarization and the external scalar step

The source uses base-first order x=Σ_i Xe_i⊗e_i. Since rank X=1 and ||X||_HS=1, write **X=ξu^T**, with unit ξ∈C^d and u∈C^m; then x=ξ⊗u. Equivalently, if X is written ξa*, take u=bar a. Likewise Y=ηv^T and y=η⊗v. Hence for p(z)=v*P(z)u,

    y*P[B]x=Σ_k(η*B^kξ)(v*C_ku)=η*p(B)ξ=2.

This explicitly resolves the conjugation convention. Also |p|≤||P|| on the entire W(A). The scalar pinned bound on B gives ||p(B)||=2 and max_{W(B)}|p|=1. Thus the scalar polynomial constant ψ(B) is exactly two: lower bound from this p, upper bound from the pin. These are the exact hypotheses of Jin v2 Theorem 1; it has no inverse-algebra assumption, simple-spectrum hypothesis, or degree restriction. It gives W(B)=a+ρDbar, ρ>0. The external theorem is credited as an input, not conflated with the stipulated OpenAI source.

For completeness, here is an explicit justification of the remaining H∞-interpolation transition. Let T=(B−aI)/ρ and g(z)=p(a+ρz). Then σ(T)⊂D, ||g(T)||=2 and ||g||_D=1. Prescribe its contiguous jets at every spectral point through the largest Jordan-block order (or through algebraic multiplicity, as in Jin). Suppose an H∞ interpolant f had norm c<1. For fixed 0<r<1, f_r(z)=f(rz) is holomorphic near Dbar and has norm at most c there. Taylor polynomials converge uniformly on Dbar to f_r. Applying the scalar pinned inequality to T and taking this limit yields ||f_r(T)||≤2c. As r↑1, all relevant interior jets converge, hence ||f(T)||≤2c<2. But f has g's jets, so f(T)=g(T), a contradiction. Thus the minimal interpolation norm is one.

Jin Lemma 4's fully read finite Schur recursion then gives uniqueness in the unit Schur ball and a finite Blaschke solution. Since g itself is such a solution, g is a finite Blaschke product. As a polynomial it has no nonzero Blaschke zero: its reflected reciprocal pole would be outside D and could not cancel a numerator zero inside D. Therefore g=ηz^k, |η|=1; k≥1 because a constant cannot have evaluation norm two, and k≤deg P.

The identity is polynomial, hence global. Because |p|≤1 on W(A), every point of W(A) lies in a+ρDbar. The reverse inclusion is W(B)⊂W(A). This pays the outer-summand step; classifying W(B) alone would not pay it. Rescaling restores M and the stated scalar witness for A.

## 8. Counterexample pressure and limits

The exact I238 example remains decisive against a different claim. Let N=[[0,2],[0,0]] and P(z)=[[0,z],[1,0]]. Then ||P[N]||=2 and max_Dbar||P||=1. In coefficient-first block order P[N]=[[0,N],[I,0]], unitarily a chain with weights (1,2,1). Its unique top right singular vector has first two iterate norms 2,2, so its scalar square-function sum is 1+1+1/4=9/4. It cannot lie in a reducing norm-two two-dimensional nilpotent block, which would annihilate the second iterate. This is fully consistent with the proved input scalarization: take u=e₂,v=e₁, so v*P(z)u=z. No output nilpotent assertion is smuggled in.

Other reducing summands contained in the active disk preserve the theorem and obstruct whole-operator classification. An outside summand would contradict the scalar monomial bound on W(A), as proved above. Normal/segment/point ranges have complete constant one and cannot meet the nonzero equality hypothesis. A matrix Schur function with a constant unitary channel defeats scalar maximum-principle reasoning before rank reduction, but does not defeat the rank argument. Corners or flat boundary parts do not harm the L² limit, because only one reflected curved arc is needed.

No counterexample within E4 was found by these exact analytic checks. No numerical experiment or parameter scan was performed. The proof gives no positive-deficit exponent or uniform constants across nearly reducible blocks, and no conclusion about a nonattained complete supremum. The supplied count of nine is unchanged by this review.
