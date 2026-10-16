# Independent reconstruction of the base-three transfer

Myeongjin Kang; no affiliation. Original prose CC BY 4.0. Source [P] is accepted on its stated base S⁴; the calculations below establish the required analogues on S³. References are to the authenticated [P] TeX files under inputs/author/inputs/pinned/power/build/sections/. The candidate's table alone is not used as a theorem. The repaired envelope construction is reviewed in review.md and repairs.md.

## 1. Framework and round beam

Framework lines 5–44 define a positive symmetric contravariant tensor A, positive density factor ρ, G⁻¹=A/ρ and L=ρ⁻¹ div_μ(A df). The integration by parts identity and nonnegative quadratic form do not introduce a dimension-dependent coefficient. On S³⊂R⁴ the homogeneous harmonic polynomial Re(x₁+ix₂)ᴺ has eigenvalue N(N+2): applying ∂²_r+3r⁻¹∂_r+r⁻²Δ_S³ to rᴺu gives N(N−1)+3N=N(N+2). Its angular formula is (1−t)^(N/2)cos(Nθ). These statements include the critical points at t=1 by smooth polynomial restriction.

Replace the three-disks of framework lines 97–117 by two-disks. A finite compact family of strict opposite signs still persists under C⁰ perturbation and each longitudinal segment contains a zero. The base-three step must have the same common exponent and C¹ neighborhood, with this two-area certificate. The remaining sections establish it rather than invoking framework Proposition step on another dimension.

## 2. Phase Hessian (waves 23–137)

At a normal-coordinate center write H=∇²h, p=|p|e₁, Q=√(1+|p|²), P=p+iQv, v⊥e₁, b=|p|/Q. Then P·P=−1 and the linear eikonal equation is SP=0. For S=U+iD this means Dv=bUe₁ and De₁=−Uv/b when b>0. Symmetry of these two columns is precisely b²U₁₁+U_vv=0.

For b≥k^(−12δ), put c₀=(b²H₁₁+H_vv)/(1+b²) and U=H−c₀I. Define D by the source's displayed block matrix relative to Re₁⊕Rv⊕E; now E has dimension one. The two prescribed columns and their compatibility still hold; the unused E–E block can be zero. Thus H−U≥(1/2)k^(−2δ)I, |U|≤Ck^(4δ), |D|≤Ck^(16δ), which imply the advertised k^(−3δ) gap and k^(20δ) norm for large k.

For 0≤b<k^(−12δ), let K=k^(14δ), U=−K(I−vvᵀ)+b²Kvvᵀ and D=−bK(e₁vᵀ+ve₁ᵀ). These formulas also work at b=0. In Rv⊕v⊥ the latter block of H−U−k^(−3δ)I is ≥K/2. The scalar block is ≥k^(−2δ)−k^(−20δ)−k^(−10δ)−k^(−3δ). Its Schur subtraction is ≤Ck^(8δ)/K=Ck^(−6δ). Positivity follows. Reducing the dimension of v⊥ from three to two changes no exponent or sign.

## 3. Polynomial inversion and six real packet parameters (waves 139–280, 495–529)

For q∈C³ with c≤|q|≤C, one coordinate satisfies |q_i|≥c/√3≥c/2. With I_i integration in that coordinate and K_q=D'I_i/q_i, the operator K_q lowers the total degree in the other two variables. On degree m it has K_q^(m+1)=0. Hence (I_i/q_i)Σ_{r=0}^m(−K_q)^r is a uniformly bounded right inverse of q·∂. No nonisotropic bilinear-square assumption enters.

Choose a favorable e₂ and complete to e₁,e₂,e₃, also when p=0. Take η=k^(−9δ), v₂=e₂ and v₃=(e₂+ηe₃)/√(1+η²). Their two-by-two transverse spanning matrix has least singular value ≥cη (determinant η/√(1+η²) and bounded maximum norm). Use pairs (p,v₂), (p,v₃), (p+Qk^(−3/4)e₁,v₂). The Hessian-test errors are ≤Ck^(−5δ) from the v change and ≤Ck^(−3/4+4δ) from changing |p|²/(1+|p|²). Both are negligible against ck^(−δ); the phase lemma applies to all three.

The normalized complex first jet lies in C⁴. Ignoring an O(κ⁻¹) error, two real columns are (1,b e₁) and (1,(b+k^(−3/4))e₁); their determinant on the value–e₁ plane is k^(−3/4) and their norms are bounded. Imaginary columns have zero value and span the orthogonal slope plane with least singular value ≥ck^(−9δ); Q'/Q≥1. Orthogonality of these two real spaces gives a real 4×6 jet matrix with least spanning singular value ≥ck^(−3/4). The perturbation O(k^(−1+100δ)) is smaller. This works at p=0 as well. Differentiating the normalized jet costs at most Ck³, so an O(k^(−10)) displacement changes it by O(k^(−7)); the nearby bound ≥k⁻¹ follows. No continuity of the selected frame in the center is required.

## 4. Finite Taylor construction and residual (waves 282–494)

Use the frame only as a frozen normal chart for spatial differentiation. On the fixed smooth metric the compact orthonormal frame bundle supplies chart and inverse-chart derivatives of every fixed order, uniformly in centers and frames. Such constants may depend on higher derivatives of that one input metric. They cannot change the k exponents because a q-th derivative of the pullback of h is a finite sum of derivatives of h of orders ≤q with fixed smooth coefficients.

Set r₀=k^(−100δ), X=ξ/r₀, κ=kr₀Q and h_sc=(h(ξ)−h(0))/(r₀Q). The q≥2 bound is C_q Q⁻¹k^{δ(101−99q)}. Multiplying L+k² by r₀² gives g^{ij}(r₀X)∂_ij+r₀β^i(r₀X)∂_i+κ²/Q² with uniformly bounded fixed-order coefficient jets. Set Φ(0)=0, ∂Φ(0)=P/Q and ∂²Φ(0)=r₀S/Q. The constant and linear eikonal equations vanish. At homogeneous degree m≥2 the new Φ_(m+1) enters only through 2(P/Q)·∂. Its Hermitian norm lies in [1,3]; Section 3 solves each equation. The prescribed Hessian has size ≤k^(−80δ); therefore all coefficients of the finite polynomial remain bounded for each fixed order T.

Construct a₀ first, then a₁,…,a_s, with constants a₀(0)=1 and a_j(0)=0 for j>0. At each homogeneous degree, the transport equation has the same invertible directional derivative, while L a_(j−1) is already known. This removes circularity despite its second derivatives. All finite polynomial coefficients are uniformly bounded for fixed T,s. The packet is

    e^{kh(z)} e^{κΦ(X)} [Σ_{j=0}^s κ^(−j)a_j(X)] ω(k^(1/3)X).

Its support radius is Ck^(−1/3−100δ). The amplitude is 1+O(k^(−1/3)) there. The envelope gap yields

    Re Φ−h_sc ≤ k^(−3/4)|X|−ck^(−106δ)|X|²+C|X|³.

On the support, the cubic term is absorbed. The maximum of the first two terms is O(k^(−3/2+106δ)); κ≤k makes its exponential bounded by 2. On |X|≥k^(−1/3)/4 the negative exponent is ≥ck^(1/3−206δ), whereas the linear error is O(k^(−1/12)). Thus the exponential tail is at most e^(−2k^(1/4))e^{kh}.

Direct substitution into the scaled operator leaves κ²E_Φa, κTa₀, κ^{1−j}(Ta_j+La_(j−1)) and κ^(−s)La_s. Taylor remainders through q≤J derivatives are bounded by C|X|^(T−q). Undoing scaling costs k^(200δ); each prescribed ordinary derivative costs at most k². The residual divided by e^{kh} is at most

    C k^(200δ+2J)[k^(2−T/3)+k^(1−T/3)+k^{−(1−100δ)s}].

Choose T>3(M+200δ+2J+3), s>(M+200δ+2J+1)/(1−100δ) before k. The tail absorbs all cutoff commutators. This gives arbitrary finite residual accuracy with the fixed derivative exponent 2j. Every formula is a finite sum over three coordinate indices; no integration or Jacobian contributes a missing dimension power in this block.

## 5. Wavelength estimates (waves 531–708)

For x∈V, put R_x=(kQ_x)⁻¹ and S_x²=Σ|w(x)|² over all packets, not merely centers in V. A packet meeting the radius-2R_x ball has |z−x|≤Ck^(−1/3−100δ)+C/k. Since |DQ|≤Ck^(4δ), |Q_z−Q_x|=o(1) and all relevant Q ratios are bounded. Also k|h(x+R_xY)−h(x)|≤C on |Y|≤2. A nearest center at mesh k⁻¹⁰ supplies S_x≥ce^{kh(x)}.

For every fixed q, |D_Y^qX_z|≤C_qr₀⁻¹R_x^q and κ_z|D_Y^qX_z|≤C_q. The first-order matrix κ_zD_YX_z=(Q_z/Q_x)D_xξ_z has bounded inverse. The displacement in X is O(k^(−1+100δ)/Q_x)=o(k^(−1/3)). For tails starting at |X_z(x)|≥k^(−1/3)/2, use the exponential annulus estimate on the entire ball, including points with w(x)=0. For non-tails the cutoff is identically one and amplitude nonzero; bounded logarithmic derivatives give sup|D_Y^jw_x|≤C_j|w(x)|. Moreover Im ∂_XΦ=(Q'/Q_z)v+O(k^(−1/3)), and the amplitude logarithmic derivative is o(1). The inverse matrix bound gives |Im(d_Yw_x/w_x)(0)|≥c. Squaring and summing shows Σ sup|D_Y^jw_x|²/S_x²≤C_j and the non-tail mass ratio is 1−o(1). Polynomially many tails contribute at most Ck^{K₁}e^(−2k^(1/4)). These estimates are unchanged on R³.

## 6. Gluing, counts and noncancellation (global 21–202)

With k²=N(N+2), N/k≤1 and N/k→1. Therefore −a_*+N/[2k(1−t)]≥c₀ on t≤1/2 for small a_*. After adding the bounded constant matching h(s₂)=b_N(s₂), the gaps ±cw hold. The round pair is exact on the support of β, so only its cutoff derivatives create a beam residual, absorbed by e^(−cwk). Let W=e^{kh}+βe^{kb_N}. All derivative costs and |dW|/W≤Ck² follow as in the source.

A three-dimensional net has at most Ck³⁰ centers and three packets per center; retaining Ck⁴⁰ is valid. On the event |g_v|≤k (failure probability ≤Ck⁴⁰e^(−k²/2)), the unchanged upper bounds are |D^qu|≤C_qk^{2q+41}W and |D^q r|≤Ck^(−M)W after choosing packet residual accuracy M+42. On W/e^{kh}>k⁵⁰ the uncut beam dominates the entire Ck⁴³e^{kh} first-jet perturbation and supplies a deterministic cW bound. Else a nearest packet family yields a covariance square root ≥k^(−52)W for the four ordinary real jet components. The derivative rescaling multiplies slope rows by kQ_z≥1; fixed coordinate comparisons only change constants. Other families add nonnegative covariance; the beam only changes the mean.

Thus the normalized four-dimensional Gaussian density is ≤Ck²⁰⁸, and a radius C₀k^(−D) ball has probability ≤Ck^{208−4D}. On the bounded-coefficient event the jet Lipschitz constant is ≤k⁴⁶. Mesh k^(−D−48) has ≤Ck^{3D+144} points, so the union bad probability is ≤Ck^{352−D}. At D=500 it vanishes. Interpolation costs O(k^(−D−2)); thresholds absorb chart comparisons. The result |u|+|du|≥k⁻⁵⁰⁰W is a global bound, not only at centers.

## 7. Area certificates (global 204–391)

Choose a maximal disjoint family of balls B(x,R_x), x∈V. Radii have a positive minimum for each fixed k. Intersecting balls have comparable Q, and fixed enlargements cover V. In three base dimensions,

    ∫_V kQ ≤ CΣ kQ_x R_x³ = CΣR_x²,
    ΣR_x² ≥ ck^{1+γ}.

The beam vanishes on the enlarged balls. Normalize by S_x. The independent real and imaginary coefficients give U_x(0) variance one. The coefficient vectors c_v=(−Im v,Re v)/|v| for non-tails are orthonormal and perpendicular to the value vector. Projecting off that value vector therefore leaves gradient covariance trace ≥c Σ_non-tail |v|²/S_x²≥c'>0, using Section 5. In R³ its largest eigenvalue is at least trace/3, so a deterministic direction e_x has conditional variance bounded above and below; its regression coefficient is bounded too.

The squared derivative sums through order 5 bound E||U_x||²_H⁵(B₂). Since 5>2+3/2, E||U_x||²_C²(B₁)≤C. The event 1≤∂_eU_x(0)≤2, |U_x(0)|<c'/H has probability ≥c₁/H; the C² norm exceeds H with probability ≤C/H². Fix H large. On their intersection the values at ±(1/4)e/H have opposite signs, with fixed margins, and retain them on transverse disks of radius σ_*=(1/4)/(4H²). Weight successes by R_x². No independence across balls is needed: a [0,1]-valued weighted success fraction with expectation ≥π_* satisfies P(F≥π_*/2)≥π_*/(2−π_*). A successful disk has area ω₂σ_*²R_x². Hence the certificate size is ≥c_*k^{1+γ} with fixed positive probability. Subtract the vanishing noncancellation failure probability to choose one simultaneous real sample.

## 8. Exact correction, simplicity and collars (global 393–631)

The correction is an algebraic divergence identity in any dimension. Let I=g₀⁻¹, D=u²+I(du,du), F=−r/D, δA=FuI and δρ=k⁻²[Fu−div_μ(FIdu)]. Expanding div(δAdu)+k²δρu gives F D=−r. Since D≥(1/2)k⁻¹⁰⁰⁰W², the corrections are smooth and zero where the residual vanishes on an open set. Product/reciprocal differentiation gives

    |D^qD|≤C_q k^{2q+86}W²,
    |D^q(D⁻¹)|≤C_qk^{1000+1088q}W⁻²,
    |D^qF|≤C_qk^{−M+1000+1088q}W⁻¹.

No derivatives of W⁻¹ are used: the displayed weights bound already differentiated factors. Multiplying by u or Idu, then taking the divergence and k⁻², yields ||(δA,δρ)||_Cᴿ≤C_Rk^{−M+2129+1088R}. With M≥2131+1088R this tends to zero. Positivity and the common C¹ neighborhood survive sufficiently small corrections.

The protected round patch has independent (u,t) coordinates. E=χ[I−(Idu)⊗(Idu)/I(du,du)] is nonnegative and annihilates du. On the eigenspace, the form ∫E(df,df) has kernel span{u}: zero energy forces f=b(u) on a product patch. The composition equation is b''(u)|du|²=k²(ub'−b). Tangential projection of the homogeneous polynomial on S³ gives exactly |du|²=N²[(1−t)^(N−1)−u²]. Holding u fixed and differentiating in t forces b''=0 for N>1, then b(u)=cu. Unique continuation extends the equality on connected S³. The source's compactness argument for A+τE uses only H¹ compactness in L² and elliptic regularity; an orthogonal normalized eigenfunction sequence at the unchanged eigenvalue would converge to a vector in that kernel, a contradiction. Thus sufficiently small τ>0 makes k² simple while preserving u,ρ and all signs.

For a fixed collar width w>0, require Ck^(−1/3−100δ)<w/100 and cwk>(M'+P)log k+log C_q(w) for the finitely many needed orders. These hold for all sufficiently large k, whatever finite accuracy has been fixed. Corrections vanish below s₁−w/100. The patch l_-+w/20<t<l_-+w/10 is untouched; choose sin(Nθ)≠0 there. Since dt≠0 for 0<t<1, du and dt are independent in base dimension three. Select τ only after k and its tensor E are fixed. Its support is above l_-, so the next collar remains round. This proves the base-three quantitative step with one common γ.

## 9. Spectral persistence, diagonal limit and ordinary metric (global 633–905)

The coercive form for −L+1 gives a compact selfadjoint inverse in L²(ρdμ), real smooth eigenfunctions and min–max eigenvalues. C⁰ multiplicative comparisons of A,ρ give convergence of each ordered eigenvalue. Near a simple eigenvalue, neighboring ordered eigenvalues stay separated. A sufficiently small finite coefficient norm controls L'−L:H^{a+2}→H^a for a=0,2; absorbing this term in the fixed elliptic estimate yields H⁴ bounds on normalized eigenfunctions in a bounded eigenvalue interval. Rellich gives H³ convergence and H³⊂C⁰ in dimension three. The limit eigenfunction equals the old one up to sign. Its finitely many strict compact disk signs therefore persist in a closed ball of one finite C^s norm. Varying densities cause no difficulty because they remain uniformly positive and converge.

Choose l^(j)=1/4+2^(−j−2). At stage j use

    r_j=max(j+1,1,s₁,…,s_(j−1)),
    η_j=min(2^(−j), b2^(−j−1), min_(i<j)2^{−(j−i+1)}ε_i).

The step constant c_j is fixed before the stage frequency. Choose k_j>2k_(j−1) and c_j k_j^(γ/2)>j. The resulting area certificate exceeds j k_j^(1+γ/2). Only then choose s_j,ε_j. Increments are summable in every fixed norm, so one smooth positive pair P_∞ exists, stays in the C¹ neighborhood and lies within ε_i/2 of P_i in its persistence norm. Its real nonzero v_i have the same disks and λ_i∈(k_i²/2,2k_i²). The intervals are disjoint and tend to infinity. Frequencies and finite regularity demands never alter γ.

Define G_∞⁻¹=A_∞/ρ_∞, q=ρ_∞dμ/dvol_G∞ and g=G_∞+q²dφ² on S³×S¹. Its volume density is ρ_∞μ dφ and, for base functions,

    Δ_g f = (ρ_∞μ)⁻¹∂_a(ρ_∞μ G_∞^{ab}∂_bf)=L_∞f.

This supplies ordinary Laplace eigenfunctions for one smooth closed connected four-dimensional metric. All cylinders lie in a fixed compact chart; smooth extensions of its coordinate functions give one metric-to-coordinate Lipschitz bound K for every orientation and radius. The nodal subset in C_a×I₀ projects onto D_a×I₀, so H³_g≥K⁻³|I₀|H²_Euc(D_a). These disjoint Borel subsets add. Consequently H³_g(Z(u_i))≥c i k_i^(1+γ/2). With ε₀=γ/4, the denominator is at most 2^(1/2+ε₀)k_i^(1+γ/2), giving divergence. One may retain this exact factor rather than the candidate's coarse 2; choosing θ smaller ensures γ≤1, which also justifies that coarse factor. This completes the entire T4 target, with the explicit local repairs recorded separately.
