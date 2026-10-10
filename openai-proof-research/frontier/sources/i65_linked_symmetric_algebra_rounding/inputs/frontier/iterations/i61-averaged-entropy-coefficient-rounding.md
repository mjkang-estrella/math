# I61: dimension-uniform coefficient extraction by paired spectral calculus

Date: 2026-10-09, America/Los_Angeles. **CE is proved here at author level, including a dimension-independent logarithmic modulus. AR, even with exact B=I, and U remain unproved and unrefuted.** This is one proposed mechanism for independent proof and contribution review, not an accepted finding or three separate findings. The accepted count stays seven. The new mechanism is the simultaneous use of the curls at x and −x, followed by a spectral cutoff acting on all three tensor indices. Gaussian second and fourth *operator* moments pay for that cutoff without a small-ball probability or a maximum-eigenvalue estimate.

Only the three assigned I61 paths are written. The exact current assignment and the full historical assignments are frozen in `../sources/i61_averaged_entropy_coefficient_rounding/brief.txt` and its input task JSON. All pinned statements **and proof operations** at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are accepted premises; this report audits applications and new deductions, not upstream truth. The full original I59, I53, I55 and I56 texts were read and preserved. No agent was started, and no shared/prior file, Git index, commit or publication was changed.

## 1. Exact new assertion and its limits

Let q(a)=φ(a)/Φ(−a). For each m≥1 let X₁,…,Xₘ be real symmetric m×m matrices, put

\[
 L(x)=\sum_r x_rX_r,\qquad B=\sum_rX_r^2\preceq K I,
 \qquad \mathsf X_{ijr}=(X_r)_{ij},
\]

and let Sym denote orthogonal projection onto fully symmetric real cubic tensors. Throughout, matrix/tensor norms are unnormalized Frobenius norms. Define

\[
 t=\frac1m\mathbb E\sum_{i,r<s}
  |(Dq(L)[X_r])_{is}-(Dq(L)[X_s])_{ir}|^2,
 \quad
 E_X=\|\mathsf X-\operatorname{Sym}\mathsf X\|^2+
           \sum_{r,s}\|[X_r,X_s]\|^2.
\]

**Theorem CE61.** For every finite K≥0 there is a function χ_K, independent of m and of the matrices, with χ_K(t)→0 as t↓0, such that E_X/m≤χ_K(t). More specifically, for 0<t≤1/2,

\[
                    E_X/m\le C_K/\log(e/t),                 \tag{1}
\]

where C_K<∞ depends only on K. At t=0 the residual is zero. For every t≥0 the explicit infimum (12) below is also valid. No normalization B≈I, full coefficient symmetry, commuting hypothesis, density, or inverse-q estimate is assumed.

This closes precisely the bounded-energy coefficient-extraction question in the assignment. It does **not** construct an orthogonal basis, prove AR, remove the original source's heavy directions, or prove U. Section 5 pays the passage from nearly symmetric bounded-energy coefficients to an actual bounded-energy symmetric cubic. Section 8 states the resulting entropy reduction and its remaining assumptions.

## 2. Independent verdicts on inherited inputs

These verdicts are analytic audits carried out here, separate from the parent's I59 replay and from the new finite diagnostics. Originals remain unchanged. No repair to the following mathematical statements was needed.

1. **I59 Proposition 2.1: PASS ORIGINAL in the smooth source class.** In the actual `matrix.tex`, retain the identity
   log det C+m=tr(SC)−log det S−D_S(C) before `mat:deficit-reduction`. Every later inequality acts on the other terms. At `mat:final-polynomial`, the unused coefficient is (1−2u)(1+68u)/50; multiplication by d||Y_d||² at u=1/d gives (d−2)(d+68)/(50d). The separate difference 7/50−69/500=1/500 remains. Thus the displayed D, Ω and chaos terms coexist. For d=2 its coefficient is d/1000; for d≥3, (d−2)(d+68)≥d². This proves, simultaneously, Y²≤1000δ, ∂Y²≤2000δ, Ω≤2000δ and D≤2δ. The transport separation surplus is consumed by the scalar-pair estimate and is not available again. The source's finite-energy and positive bounded Hessian hypotheses are essential at this stage.
2. **I59 Proposition 2.2: PASS ORIGINAL.** The left polar decomposition S¹ᐟ²P=K_c¹ᐟ²O, K_c=S¹ᐟ²CS¹ᐟ², gives coupling cost ||K_c¹ᐟ²−I||²≤tr K_c−log det K_c−m. This does not require S and P to commute. S≤40I/37 and forward q-Lipschitzness give 40000δ/37. The bounds tr(SB)≤40m/3 and the Q-energy estimate follow by tracing scalar spectral inequalities against S. They do not identify Q with q(S¹ᐟ²L), or make its linear slices symmetric.
3. **I59 Proposition 3.1: PASS ORIGINAL.** For a row v of chaos degree k, ∂*v has degree k+1, and its gradient projection is ∂∂*v/(k+1). The creation/annihilation identity gives Σ_{r<s}||∂ᵣvₛ−∂ₛvᵣ||²=(k+1)||v||²−||∂*v||². Since curl has degree k−1, its resolvent is exactly (N+2)⁻¹. Completion proves the distributional statement; there is no dimension factor. This is a row-gradient projection, not coefficient extraction.
4. **I59 Proposition 3.2: PASS ORIGINAL under B≤KI.** On the negative tail all fixed derivatives of q have Gaussian decay. On the positive tail q(r)=r/F(r⁻²), F(u)=∫₀∞exp(−v−uv²/2)dv, gives q''=O(r⁻³), q'''=O(r⁻⁴) by differentiated Taylor remainder. Thus q'',q'''∈L², and weighted Cauchy–Schwarz/Plancherel gives c_q=(2π)⁻¹||widehat(q'')||₁<∞. The two ordered Duhamel simplices have total volume one. For either order of H and Xᵣ between unitaries, summing in r is bounded by K||H||². Minkowski proves the *family* derivative bound, not m separate bounds. Adding Dq(A)[∂Y], using its Frobenius contraction, and then antisymmetrizing pays the stated √2. No inverse-q bound occurs. Hence
   \[
   t\le A_K\delta/m,\qquad
   A_K=2(\sqrt{2000}+c_q\sqrt{1000K})^2.                  \tag{2}
   \]
5. **I59 channel identity and tensor-from-dephasing implication: PASS ORIGINAL on all matrix units.** Vectorization gives ||Φ||²=||P_T||²=tr B² and ⟨Φ,P_T⟩=Σᵣₛtr(TᵣTₛTᵣTₛ). Expansion gives ||Φ−P_T||²=Σ||[Tᵣ,Tₛ]||². At B=I the slice Gram matrix is I, so P_T is a rank-m orthogonal projection. The unital trace-preserving CP map Φ is a Frobenius contraction by Schwarz and trace preservation. If ||P_T−D_U||²=b, off-diagonal matrix mass is b/2, whereas off-diagonal tensor mass is at most 3b/4: two of the three double-index placements are counted. Sign rounding adds at most the latter mass. Thus tensor cost≤3b/2, exactly as stated.
6. **I59 heavy-star, missing-dimension and conditional-budget statements: PASS ORIGINAL with their stated limitations.** The star has B=diag((m−1)/2,1,…,1), cross-slot mass (m−1)/2 and all-slot loss 3(m−1)/2. It has large commutators and is not a realized density counterexample. Lifting a good marginal coupling and appending independent centered exponentials costs precisely b+2k as an upper bound. The entropy chain rule is δ=ΣEδᵢ+ΣElog sᵢ; isotropy makes the second sum nonpositive. The rotated two-exponential example cancels its two positive scalar gaps against this negative term. These facts forbid an unpaid arbitrary flag or rank-only deletion.
7. **I59 radial Theorem 7.1: PASS ORIGINAL, independently audited but unused by CE.** Concavity of the log density ratio against a same-mean Gamma(m) gives a two-crossing sign pattern and v≤μ²/m. Dirichlet transverse covariance is M₂/[m(m+1)]; the axial variance is v/m. The shared Dirichlet coupling with an *independent* Gamma radius gives exactly its displayed cost, bounded by 4m/(m+1). Gaussian maximum entropy, Jensen and the lower Stirling bound give δ≤1. This is not a vanishing-deficit modulus and does not rule out a violation of U's rate when δ≪1/m.

The actual source normalization, scalar absorption, scalar-pair cancellation, exact rigidity jets, forward divided-difference estimate, and weighted approximation were inspected. I53's full law reconstruction and I55's original-proof verdict remain compatible with these inputs. I56's normal derivative equals 2, but its Taylor remainder √5d² uses *total* distance; after division by √m it still has a √m coefficient. Its fixed-dimensional entrance compactness is not AR. Published BDS Proposition 4.1 and Robeva Lemma 3.7 remain credited for the tangent calculation.

The inherited numerical caveats are preserved: exact chosen-orientation costs bound the orbit infimum; unvalidated quadrature values do not. In particular, the I59 truncated-exponential m=512 values at two resolutions disagree visibly. No such value enters the proof below. Density approximation preserves laws/entropy/covariance, not the new coefficient arrays across growing dimensions.

## 3. Construction A: paired divided differences

### 3.1 Strict scalar positivity, with quantitative compact bounds

We need q'>0 and **q''>0**, not just convexity. The source proves q'>0 and q''≥0. Strictness follows without an external theorem. Let S_a(u)=Φ(−a−u)/Φ(−a), the survival function of G−a given G>a. Since q is strictly increasing,

\[
 S_a(u+v)<S_a(u)S_a(v)\quad(u,v>0).
\]

Writing d=∫S_a and E_aX²=2∫∫S_a(u+v)du,dv gives

\[
 q''(a)=q(a)(d(a)^2-\operatorname{Var}_aX)
 =2q(a)\iint_{(0,\infty)^2}
       [S_a(u)S_a(v)-S_a(u+v)]\,du\,dv>0.                 \tag{3}
\]

For R≥1 define a_R=min_{[-R,R]}q'>0 and h_R=min_{[-R,R]}q''>0. In fact

\[
 a_R\ge R\varphi(R),\qquad
 h_R\ge\frac{R}{2\pi}\exp(-R^2-4R-20).                 \tag{4}
\]

For the first bound use monotonicity of q', q(−R)≥φ(R), and d(−R)≥R. For the second restrict (3) to u,v∈[1,2]. On the relevant interval [−R,R+4], q≤R+5 and q'≥q'(−R). Consequently S_a(u)S_a(v)≥exp(−4(R+5)), while
∫₀ᵛ[q(a+u+s)−q(a+s)]ds≥q'(−R). Since 0<q'(−R)<1, 1−exp(−q'(−R))≥q'(−R)/2. Also q(a)≥φ(R). Substitution proves (4). All constants in (4) are deliberately loose analytic bounds, not sampled minima.

### 3.2 The two scalar equations at one spectral triple

At a fixed x diagonalize L(x), and rotate **all three** coefficient indices by that same orthogonal matrix. Denote the transformed tensor again by X, and eigenvalues by λᵢ. Use precisely the same eigenbasis at −x; its eigenvalues there are −λᵢ. No eigenvector is differentiated.

For a fixed ordered triple (i,s,r), set A=X_{isr}, C=X_{irs}, d=A−C, and

\[
 \alpha=q[\lambda_i,\lambda_s],\quad\beta=q[\lambda_i,\lambda_r],
 \quad\gamma=q[-\lambda_i,-\lambda_s],\quad\eta=q[-\lambda_i,-\lambda_r].
\]

The corresponding curl entries at x and −x are

\[
                  e_+=\alpha A-\beta C,
          \qquad e_-=\gamma A-\eta C.                    \tag{5}
\]

These are derivatives of the field evaluated at −x, **not** derivatives of its reflected composition; there is no extra minus sign. If |λᵢ|,|λₛ|,|λᵣ|≤R, then a_R≤α,β,γ,η≤1. Furthermore α−β and γ−η have opposite signs, and

\[
 |\alpha-\beta|\ge(h_R/2)|\lambda_s-\lambda_r|.           \tag{6}
\]

Indeed ∂_b q[a,b]=∫₀¹u q''((1−u)a+ub)du≥h_R/2. The reflected divided difference reverses monotonicity.

When λₛ≠λᵣ, multiply the equations (5), written as αd+(α−β)C and γd+(γ−η)C, by |γ−η| and |α−β| and add. The C terms cancel; the coefficient of d is at least a_R times the sum of the weights. If the eigenvalues coincide, the first equation directly controls d. In both cases,

\[
 d^2\le\frac2{a_R^2}(e_+^2+e_-^2),\qquad
 |(\lambda_s-\lambda_r)C|^2
 \le\frac8{h_R^2}(1+2/a_R^2)(e_+^2+e_-^2).             \tag{7}
\]

The second inequality follows from (6) and (α−β)C=e_+−αd. Thus the polynomial-curl entry

\[
 z=(\lambda_i+\lambda_s)A-(\lambda_i+\lambda_r)C
   =(\lambda_i+\lambda_s)d+(\lambda_s-\lambda_r)C
\]

satisfies z²≤M_R(e_+²+e_-²), where

\[
 M_R=16R^2/a_R^2+16h_R^{-2}(1+2/a_R^2).                \tag{8}
\]

Unlike a single curl equation, the two equations cannot lose coefficient symmetry through cancellation between the two unequal divided differences. The use of the explicit strictly convex Mills function, and reflection, is the substantive compatibility step.

## 4. Paying for all spectral tails and extracting coefficients

Here the spectral cutoff depends on x. It is not a compression of the original input space, not an approximation to the OU semigroup, and not a derivative of a spectral projection.

### 4.1 Operator moments and tensor-slot estimates

Gaussian orthogonality gives E L²=B≤KI. Wick's formula gives

\[
 \mathbb E L^4=B^2+\sum_rX_rBX_r+
                      \sum_{r,s}X_rX_sX_rX_s\preceq3K^2I. \tag{9}
\]

For clarity, the last sum is self-adjoint, and its operator norm is at most K²: apply the row-column inequality ||ΣA_jB_j||≤||ΣA_jA_j*||¹ᐟ²||ΣB_j*B_j||¹ᐟ² with A_{rs}=B_{rs}=X_rX_s. Both positive sums are bounded by K²I. The first two terms in (9) are separately bounded by K²I. This proves (9) without an operator bound on each Gaussian realization.

On (Rᵐ)^{⊗3}, let L_j act on slot j and put P=1_{[-R,R]}(L), Π=P^{⊗3}. Operators acting on different slots commute. For any deterministic tensor V,

\[
 \mathbb E\|L_jV\|^2\le K\|V\|^2,\qquad
 \mathbb E\|L_jL_aV\|^2\le3K^2\|V\|^2.                \tag{10}
\]

If j=a the second assertion is (9). Otherwise, joint spectral calculus gives L_j²L_a²≤(L_j⁴+L_a⁴)/2; taking expectation again gives (10). This also controls the **third**, coefficient/input slot. It does not assume that its flattening Gram matrix is bounded. Equivalently E(1−P)≤B/R²≤KI/R², which can be traced against any fixed positive input Gram matrix.

Write J for transposition of tensor slots 2 and 3,
S=(I−J)X, and Z(x)=(I−J)(L₁+L₂)X. Then S_{isr}=X_{isr}−X_{irs} and Z is the ordered curl of L². Since Π commutes with J and each L_j, and I−Π≤Σ_jL_j²/R², (10) proves

\[
 \mathbb E\|(I-\Pi)S\|^2\le12K\|X\|^2/R^2,
 \quad
 \mathbb E\|(I-\Pi)Z\|^2\le144K^2\|X\|^2/R^2.
\]

For the second constant: ||I−J||≤2 contributes 4, the square of L₁+L₂ contributes 2, there are 3·2 slot pairs, and each contributes at most 3K². Since ||X||²=tr B≤Km, these are respectively ≤12K²m/R² and ≤144K³m/R².

On Π apply (7)–(8), sum over ordered triples, and integrate. Each ordered curl norm is twice the r<s norm; reflection preserves Gaussian measure. Hence the sum of e_+²+e_-² integrates to 4mt. Orthogonality of Π and I−Π now gives

\[
 \frac{\|S\|^2}{m}\le8a_R^{-2}t+12K^2/R^2,
 \qquad
 \frac{\mathbb E\|Z\|^2}{m}\le4M_Rt+144K^3/R^2.         \tag{11}
\]

There is no differentiation of P, no restriction to the rare event ||L||op≤R, and no multiplication by a matrix count.

### 4.2 Coefficient commutators and the modulus

Because X is symmetric in slots 1 and 2, ||X−Sym X||²=||S||²/3. This follows by writing Sym X as the average of its three distinct slot permutations; their pairwise inner products are equal.

Let S_{rs}=X_re_s−X_se_r, so its full ordered array norm is ||S||. Direct expansion, with no symmetry in the third slot assumed, yields

\[
 Z_{\cdot rs}(x)=[X_r,X_s]x+
       \sum_t x_t\{X_rS_{ts}-X_sS_{tr}+X_tS_{rs}\}.
\]

For each of the three arrays in braces, its squared coefficient norm is at most K||S||²; for example Σ_{rst}|X_rS_{ts}|²≤KΣ_{ts}|S_{ts}|². Thus Gaussian orthogonality and the triangle/Cauchy inequalities imply

\[
 \sum_{r,s}\|[X_r,X_s]\|^2
           \le2\mathbb E\|Z\|^2+18K\|S\|^2.
\]

Combining with (11), set

\[
 F_K(R)=8(1/3+18K)a_R^{-2}+8M_R,
 \qquad D_K=4K^2+504K^3.
\]

Then an explicit admissible modulus is

\[
 \boxed{\quad\chi_K(t)=\min\left\{K+4K^2,
                \inf_{R\ge1}\bigl(F_K(R)t+D_K/R^2\bigr)\right\}.\quad} \tag{12}
\]

The first bound uses ||X−Sym X||²≤Km and Σ||[Xᵣ,Xₛ]||²≤4tr B²≤4K²m. For any tolerance first fix R large enough for the second term, then send t to zero. This proves CE with no asymptotic exchange of dimension-dependent constants. At t=0 the infimum is zero.

The logarithmic rate (1) is also rigorous. Bounds (4) give a_R⁻²≤2πexp(R²) and h_R⁻²≤4π²exp(50R²) for R≥1. Substituting in (8), absorbing R² into exp(R²), gives F_K(R)≤C(1+K)exp(52R²) for an absolute finite C. If 0<t≤exp(−104), take R²=log(1/t)/104. The two terms in (12) are at most C(1+K)√t and 104D_K/log(1/t). Both are bounded by C_K/log(e/t). For exp(−104)≤t≤1/2, enlarge C_K and use K+4K². For K=0 all matrices vanish. This proves the whole stated theorem.

The argument actually applies to any smooth scalar function with 0<f'≤1 and f''>0 on every compact interval, with its own compact constants; the logarithmic estimate above is proved for the actual Mills function. An affine f has f''=0 and does not qualify. A fully symmetric nonassociative cubic gives zero curl for affine f, so this condition cannot be dropped.

## 5. A paid symmetric bounded-energy repair

Symmetrizing X alone need not preserve its energy cap: the third flattening can have large operator norm. The following avoids concealing that issue.

**Lemma 5.1.** Suppose B_X≤KI with K>0, and put T=Sym X and e²=||T−X||². There is a fully symmetric tensor Z with B_Z≤4KI and

\[
 \|Z-X\|^2\le26e^2,\quad
 \|B_Z-B_X\|^2\le234Ke^2,
 \sum_{rs}\|[Z_r,Z_s]-[X_r,X_s]\|^2\le936Ke^2.         \tag{13}
\]

**Proof.** Flatten along the first slot as a map from Rᵐ⊗Rᵐ to Rᵐ. Its product with its transpose is B_X, using matrix symmetry. Let P=1_{[0,4K]}(B_T), k=rank(I−P), and a=||(I−P)T||. Then a≥2√(Kk), while a≤e+√(Kk). Hence a≤2e (and k≤e²/K). Define Z=P^{⊗3}T. Tensor symmetry and the commuting projection inequality give ||T−Z||²≤3a²≤12e². Therefore ||Z−X||²≤2||Z−T||²+2e²≤26e². Its first flattening is P M_T(P⊗P), so B_Z≤PB_TP≤4KI. For two flattened maps,
||MM*−NN*||_F≤(||M||op+||N||op)||M−N||_F; this gives the second estimate. Finally write the commutator difference as [Z_r−X_r,X_s]+[Z_r,Z_s−X_s]. Summing over the bounded-energy families gives norms at most 2√K||Z−X|| and 4√K||Z−X||. Squaring proves the third bound. ∎

In particular, if β=||B_X−I||²/m and η=E_X/m, then

\[
 \frac{\|B_Z-I\|^2+\sum_{rs}\|[Z_r,Z_s]\|^2}{m}
       \le2\beta+(2+2340K)\eta.                         \tag{14}
\]

This is a global normalized estimate, not I56's small-total-error statement. It handles the new heavy directions created by symmetrization because closeness to an *already capped* original flattening pays their **mass**. It does not handle the original unbounded source coefficients. In particular, the I59 star is excluded by the initial cap with fixed K; (13) is not a repair of that original obstruction.

## 6. Construction B: linked channel algebra, developed to its obstruction

Assume first T is fully symmetric and B=I. Define Δ:Rᵐ→Rᵐ⊗Rᵐ by Δe_r=Σ_{ij}T_{ijr}e_i⊗e_j. Then Δ*Δ=I and ΔΔ*=P_T under vectorization. Full symmetry supplies a self-adjoint multiplication μ=Δ* with Euclidean Frobenius compatibility. The two triple-output maps obey the exact identity

\[
 \| (\Delta\otimes I)\Delta-(I\otimes\Delta)\Delta\|_{HS}^2
                    =\sum_{r,s}\|[T_r,T_s]\|^2.          \tag{15}
\]

Indeed their entry difference is Σ_a(T_{ija}T_{akr}−T_{jka}T_{iar})=[T_i,T_k]_{jr}, with ordered indices. Thus the approximate structure is linked simultaneously to an isometry, a rank-m projection and the symmetric Kraus channel Φ. This is more information than generic approximate idempotence.

Nevertheless the straightforward functional-calculus rounding fails to supply the required conclusion. If E=Σ||[Tᵣ,Tₛ]||², then

\[
 \|\Phi^2-\Phi\|_{HS}\le3\sqrt E.
\]

Let R=1_{[1/2,∞)}(Φ), with arbitrary fixed tie convention. Since Φ is a self-adjoint contraction, scalar spectral calculus gives

\[
 \|\Phi-R\|_{HS}\le2\|\Phi^2-\Phi\|_{HS}\le6\sqrt E,
 \quad \|R-P_T\|_{HS}\le7\sqrt E,
 \quad |\operatorname{rank}R-m|\le49E.                   \tag{16}
\]

The first scalar inequality is dist(λ,{0,1})≤2|λ²−λ| for −1≤λ≤1. The last uses the Hilbert–Schmidt distance between orthogonal projections. Thus a genuine projection of approximately the right rank is obtained at normalized scale. It need not be completely positive or have a range closed under ordinary multiplication, let alone be dephasing. Those are unpaid conclusions, not consequences of (16).

There is a concrete reason that exact idempotence and the correct rank alone cannot suffice. Let m=k², identify Rᵐ=Rᵏ⊗Rᵏ, and define

\[
 \mathcal E(H)=\frac1k\operatorname{Tr}_2(H)\otimes I_k.
\]

It is a real, unital, trace-preserving, self-adjoint CP projection of superoperator rank k²=m. For a unit vector u and p=uuᵀ, write ρ=Tr₂p. Then ||E(p)||²=tr(ρ²)/k≤1/k. Hence, for every real orthonormal basis U,

\[
 \langle\mathcal E,\mathscr D_U\rangle_{HS}
 =\sum_j\|\mathcal E(u_ju_j^T)\|^2\le m/k,
 \quad
 \frac{\|\mathcal E-\mathscr D_U\|_{HS}^2}{m}
                       \ge2(1-1/k).                     \tag{17}
\]

This is an exact lower bound against *all* orientations. It does not refute AR: the range contains nonsymmetric matrices, and E is not the projection onto slices of a linked fully symmetric cubic satisfying Φ=P_T. The point is to identify precisely which hypotheses must survive a channel-rounding proof.

Kitaev's current v2 gives dimension-independent stability of approximate C*-algebras, but assumes uniform multiplicative norm defects and, for channels, ||Φ²−Φ||cb≤η. Equation (16) gives only a normalized superoperator Hilbert–Schmidt bound. These norms cannot be substituted. Already a direct sum of one fixed harmonic cubic block (below) and arbitrarily many scalar odeco blocks has E/m→0 while ||Φ²−Φ||cb≥2. Moreover Kitaev explicitly warns that the spectral projection of an almost-idempotent UCP map need not be CP; his conclusion is encoding/decoding through a C*-algebra, not the claimed dephasing conclusion. We therefore do not import his theorem here.

For B≈I instead of B=I, polar normalization of Δ would give an isometry on its support, but ΔB⁻¹ᐟ² changes only the input slot and generally destroys full cubic symmetry and the linked identities. Normalizing all three slots does not in general set the new Gram matrix to I. Small normalized ||B−I||² does not authorize a uniform inverse or an exact normalization preserving all identities. Neither that passage nor dephasing rounding at B=I is proved here. The general statement (14) is retained as the actual nonzero-normalization interface.

## 7. A separate variational deflation attempt

For a fully symmetric normalized tensor B=I, choose a global spherical cubic maximizer v, c=T(v,v,v)>0. As in I53's exact first and second variations,

\[
 T_v=\operatorname{diag}(c,H),\quad H\preceq(c/2)I,
 \qquad c^2+\|H\|^2=1.
\]

Now retain a *contracted*, rather than total, associator energy

\[
 a(v)=\sum_j\|[T_v,T_{w_j}]v\|^2
      =\|H^2-cH\|^2
\]

for an orthonormal basis w_j of v⊥. Since |λ²−cλ|≥c|λ|/2 for λ≤c/2,

\[
                 \|H\|^2\le4a(v)/c^2,
             \qquad c^2(1-c^2)\le4a(v).                 \tag{18}
\]

If c≥τ>0, one deflation loses at most 12a(v)/τ² mixed squared mass. With h_j=Hw_j and T' the all-slot restriction, the exact identities are

\[
 B_{T'}=I_{v^\perp}-2H^2,\qquad
 [T'_j,T'_k]=[T_j,T_k]_{v^\perp}-(h_jh_k^T-h_kh_j^T).
\]

The commutator-array perturbation has norm≤2||H||², and the new normalization error has Frobenius norm≤2||H||². These are explicit local budgets. At successive steps, however, both B and the commutators change. The selected vectors depend on the current tensor. We have not bounded the sum of current contracted energies by the original E with a small enough feedback term, nor ruled out the small-c branch of (18) at normalized scale. The total bound a(v)≤E≤εm is useless when εm is large. Repeating I53's total-error bootstrap would reintroduce exactly the excluded dimension loss.

For an exact diagnostic, in dimension two set T₁₁₁=1/√2, T₁₂₂=T₂₁₂=T₂₂₁=−1/√2 and other entries zero. Then B=I and p(cos θ,sin θ)=cos(3θ)/√2, so c=1/√2, H=−1/√2, a(v)=1 and E=4. Its channel eigenvalues on I, the two real symmetric traceless matrices, and the skew matrix are 1,0,0,−1; P_T projects onto the two symmetric traceless matrices. This verifies that normalization alone neither makes the maximal coefficient close to one nor makes Φ close to P_T. Adding scalar diagonal blocks gives the norm-conversion obstruction used after (17), but is not an AR counterexample: only a vanishing fraction of the tensor mass is then defective.

These are developed constructions with explicit identities, a projection candidate, a universal generic-channel obstruction, and a paid one-step deflation estimate. They do not establish global AR, even at B=I. No routine fixed-dimensional variant is nominated.

## 8. What CE61 actually pays toward entropy stability

Let f belong to the source smooth class, be centered isotropic, and suppose its normalized first-chaos matrices satisfy B_X≤KI with fixed K. Put u=δ(f)/m. The audited (2) and CE61 give η≤χ_K(A_Ku). The original source weight also gives

\[
 \|B_X-I\|^2/m\le (2000/c_K)u,
 \quad c_K=\min_{0\le\lambda\le K}
         \frac{\omega(\lambda)}{(\lambda-1)^2}>0,          \tag{19}
\]

with the continuous positive value used at λ=1. Lemma 5.1 constructs one symmetric bounded-energy tensor Z with normalized equation residual bounded by
2(2000/c_K)u+(2+2340K)χ_K(A_Ku). This tends to zero uniformly in dimension. Thus the previously unpaid bounded-energy analytic-to-algebraic passage is now closed.

If AR with cap 4K supplied a modulus ρ_{4K} for that residual, then one global tensor T*=U^{⊗3}Σeᵢ³ would obey

\[
 \|X-T^*\|^2/m\le52\eta+
        2\rho_{4K}\bigl(4000u/c_K+(2+2340K)\eta\bigr).
\]

Forward q-Lipschitzness and Gaussian Poincaré give
||F−H_U||²/m≤2000u+104η+4ρ_{4K}(…). The original lower normalizer bound P≥q(0)I and covariance comparison then give d_m(f)²/m at most 4/q(0)² times this expression. This is a **conditional propagation calculation**, not a renamed lemma asserted true. It specifies exactly where AR would enter and uses a single global U.

There are two remaining barriers to U: AR is not proved; and general source coefficients do not satisfy a uniform cap. The source Ω-weight controls the number of heavy directions but not their unregularized cross-slot mass. CE61's tensor-slot cutoff is a pointwise Gaussian spectral estimate for an already bounded B, and cannot be applied to the I59 heavy star or to Q=S¹ᐟ²q(L) by pretending Q=q(S¹ᐟ²L). The paid repair in §5 has a different hypothesis. No arbitrary covariance is assigned to f, and no independent conditional orientations are used. If a good marginal were eventually constructed, the missing k dimensions would still cost 2k after its cost b. The negative conditional log-scale correction and sign/mean/scale costs remain as in I59.

The new logarithmic coefficient rate is not the square-root law in U. Even successful AR and heavy handling would require their actual rates to claim U rather than a weaker dimension-uniform modulus. A density-level theorem could be extended using the source approximation only once established uniformly for suitable approximants; a cap or coefficient convergence is not inherited automatically.

## 9. Primary comparison, source contracts and nomination boundary

Current primary captures, served versions, exact bytes and failures are in the new `literature/manifest.json`; the versions and proof-read contracts are recorded separately. No external theorem is stipulated merely because it is recent. No MathDB score is invented. The bounded searches below do not certify worldwide priority.

* The pinned entropy proof's `rigidity.tex` uses two jets at the Gaussian origin. I53/I55 pay that passage by a dimension-dependent small-ball estimate. I56 pays fixed-dimensional rounding by transverse coercivity and compactness. CE61 instead compares two integrated spectral equations and charges **all three slots** to operator moments. None of those source operations already supplies this normalized passage.
* The general-Mahler companion's `06-linear-equality.tex` already uses a spectral two-point measure and identifies Σ||[Mᵣ,Mₛ]||² with EΣ||[L,Mᵣ]||². This is a genuine conceptual antecedent to spectral averaging and is explicitly credited. Its measure weights matrix entries and its deficit comes from a different projection/layer calculation. It does not provide (5)–(7), simultaneous approximate coefficient symmetry, or the input-slot cutoff estimate for the entropy curl. No comparison between its deficit and δ(f) is assumed.
* Two further pinned operator-algebra companions were inspected. `Tracial-projection-methods-and-uniform-property-Gamma`, §10, already averages noncommuting centered symmetries, proves a fourth-moment bound of 3, and clips spectrally with coefficient-moment losses 3/R³ and 3/R². This is a substantive antecedent to fourth-moment cutoff budgeting, not a new operation claimed here. Its hypotheses concern a simple, separable, unital, infinite-dimensional nuclear C*-algebra with strict comparison and supplied projections; it constructs new approximately central observables, not a basis for the linked cubic. CE61 instead needs operator moments against arbitrary fixed tensor-slot marginals and the paired equations (5). `Near-Inclusions-of-von-Neumann-Algebras-Without-Small-Spatial-Embeddings` uses operator-norm gap and a trace-log obstruction. Its simultaneous support, common-corner compression and polar replacement operate inside already commuting ambient algebras. Those hypotheses do not follow from normalized cubic residuals. Neither companion is an AR counterexample or supplies the missing linked-range rounding.
* [Bansil–Kachkovskiy, 2608.31000v1](https://arxiv.org/abs/2608.31000v1), Theorems 1.1/1.3 and Corollary 1.4: pair power 1/3, a √N family factor, and squared-distance exponent 2/3^(N−1). The actual spectral partition minimization, weighted averaging and many-matrix modifications were inspected. [Filonov–Kachkovskiy, 1008.4002v2](https://arxiv.org/abs/1008.4002v2), Theorems 2–3 and their block iteration, likewise retain matrix-count dependence. Neither closes AR with m slices.
* [BDS, published Proposition 4.1](https://rendiconti.dmi.units.it/volumi/54/017.pdf), [Robeva, Lemma 3.7](https://arxiv.org/abs/1409.6685), and [BDHR, Lemma 11/Proposition 12](https://arxiv.org/abs/1512.08031v1) supply tangent/exact-associativity results. Their real positive-inner-product case is relevant; complex isotropic counterexamples are not real AR counterexamples. No normalized entrance follows just from their Jacobian ranks. [Auddy–Yuan, 2007.09024v2](https://arxiv.org/abs/2007.09024v2), Theorems 2.4/3.1 and polar-factor proof, require an existing odeco comparison or nearly isometric factorization. Those inputs have not been manufactured from AR residuals.
* [Kitaev, 2405.02434v2](https://arxiv.org/abs/2405.02434v2), Definition 2.1, Theorem 2.3, §1.2 and the proof strategy, are an especially relevant comparison. The result has universal constants but **uniform Banach-algebra/cb hypotheses**, and an abstract C*-algebra conclusion. Its own discussion identifies the positivity problem with spectral rounding and the dimension loss in naive cohomological correction. We have not verified or invoked the full external theorem as a premise; the actual hypotheses already fail to follow here.
* [Coecke–Pavlovic–Vicary, 0810.0812v1](https://arxiv.org/abs/0810.0812v1), Theorem 5.1 and §6, characterize exact orthogonal/orthonormal bases by commutative dagger Frobenius structures. The classification is not an approximate normalized estimate. [Poinsot's author manuscript](https://lipn.fr/~poinsot/Articles/Hilbertian_Frobenius_algebras_rev.pdf) discusses exact Hilbertian Frobenius algebras and approximate *units*; the latter are not approximate associativity of the multiplication. These exact algebra antecedents are credited, not treated as stability black boxes.
* Fresh FMS and MNR primary captures retain the inherited entropy comparison. Their cone/rearrangement/localization operations do not close the two remaining interfaces. No new radial/product test is offered as another finding.

**Proposed review candidate:** CE61 and its analytic-to-algebraic bounded-energy application, counted as a single mechanism if it eventually passes both gates. Its justification for review is a closed dimension-uniform bridge that the prior reports explicitly left unpaid, not an improved fixed-m exponent or an absent search hit. The logarithmic corollary and symmetric repair belong to this same construction. There is no nomination of U, AR, generic channel rounding, the inherited remainders, or the deflation diagnostics. Substantiality and acceptance remain for the parent's independent reviews.

## 10. Evidence and reproduction

The new capture freezes fourteen inputs (including the four mutable ledgers), fifteen initial and four supplementary pinned blobs, the complete 13,223-entry tree/749-manuscript inventory, all 9,340 ignored corpus files, and 339 prior evidence-file hashes without recursive archive copying or old-seal updates. The prior reports themselves are frozen immutable inputs. Whole-corpus `rg --no-ignore` searches are retained as **line multisets** (117, 5, 39 and 46 hits); inventory/search coverage is not a claim to have read every manuscript. Current source/read contracts and the full prior objections are retained in this source directory.

The standard-library diagnostics independently check finite tensor identities, Wick contractions, all-index moment estimates, polynomial curl extraction, the channel/coassociator identity, the exact generic projection obstruction and harmonic block, and scalar paired inequalities: 4,640 exact rational assertions and 10 labeled floating Mills-function records. Neither type is a universal proof or independent analytic review. The inherited quadrature nonconvergence is preserved rather than rerun as a claimed certification.

There are 30 explicit read contracts and 37 frozen passages, 23 successful fresh literature responses with 13 PDF-to-text replays, and four successful fresh pinned-raw responses matching their Git blobs. Served arXiv versions are taken from the actual PDF headers. Eight individual original brief/objection records are copied without copying prior archive trees. Separate analytic verdicts and new objections/responses identify what was proved, inherited, or left open.

From the project root:

```bash
PYTHONDONTWRITEBYTECODE=1 python frontier/experiments/i61_averaged_entropy_coefficient_rounding/diagnostics.py
PYTHONDONTWRITEBYTECODE=1 python frontier/experiments/i61_averaged_entropy_coefficient_rounding/verify.py
```

The verifier is offline and read-only. It checks the new seal, frozen inputs and permissible ledger drift, complete tree and corpus Git/SHA hashes, unchanged prior evidence, search multisets, exact proof passages, primary bytes and PDF replays, and deterministic diagnostics. Capture/fetch helpers are separate one-shot writers that refuse to overwrite their manifests. A successful evidence replay must not be called independent analytic acceptance of CE61 or U.
