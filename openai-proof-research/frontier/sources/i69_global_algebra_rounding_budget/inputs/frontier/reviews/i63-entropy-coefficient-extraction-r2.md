**I63 independent full original-proof review — CE61.** Review date: 2026-10-09, America/Los_Angeles. All pinned OpenAI statements **and lower proof operations** at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are premises. This review tests new deductions and applicability, not upstream truth.

**The ORIGINAL complete CE61 theorem passes WITHOUT REPAIRS**, including its stated coefficient scope, explicit infimum modulus, zero endpoint, and logarithmic rate. The original symmetric repair, bounded-energy conditional entropy propagation, I59 inputs as used, and channel/deflation partial statements also **PASS ORIGINAL WITHOUT REPAIRS in their stated scopes**. No hypotheses, constants, exponents, or proof steps in the original report need replacement. The expansions below explain the original steps; they do not silently substitute a repaired proof.

AR and U remain **UNPROVED AND UNREFUTED**. In particular, this is not a density-level uniform stability theorem, not an algebra-rounding theorem, and not U's square-root rate. The generic channel obstruction is a counterexample only to the specified generic channel-to-dephasing proposal. The historical heavy star and conditional-budget counterexample retain their narrower scopes. This review makes no contribution, count, acceptance, or priority decision. I64 owns the separate contribution assessment.

I read the FULL original [I61](../iterations/i61-averaged-entropy-coefficient-rounding.md), [I59](../iterations/i59-dimension-uniform-entropy-stability.md), [I53](../iterations/i53-sharp-entropy-stability-discovery.md), [I55](i55-sharp-entropy-stability-r2.md), and [I56](i56-sharp-entropy-stability-novelty.md), and the complete original I61 verifier. The parent replay and author diagnostics are not analytic premises. Actual source proofs were read at the ranges recorded in `read-contracts.json`, including the full entropy transport, matrix, scalar, rigidity, and approximation arguments, Mahler linear equality, tracial fourth-moment/clipping section, and near-inclusion common-corner argument. The full original assignment and earlier briefs/objections are frozen separately. Only the assigned I63 report/source/experiment paths were written; no agents, commits, staging, publication, or prior/shared edits were performed.

**1. Exact assertion under review.** For each fixed finite (K\ge0), each (m\ge1), and any real symmetric (m\times m) matrices (X_1,\ldots,X_m) with (B=\sum_rX_r^2\preceq KI), put (L(x)=\sum_rx_rX_r), (\mathsf X_{ijr}=(X_r)_{ij}), and
\[
 t=m^{-1}\mathbb E\sum_{i,r<s}|(Dq(L)[X_r])_{is}-(Dq(L)[X_s])_{ir}|^2,
 \qquad q(a)=\varphi(a)/\Phi(-a).
\]
The passed conclusion is
\[
 m^{-1}\bigl(\|\mathsf X-\operatorname{Sym}\mathsf X\|_F^2+
 \sum_{r,s}\|[X_r,X_s]\|_F^2\bigr)\le\chi_K(t),
\]
with one dimension-independent function tending to zero at zero and with the original (C_K/\log(e/t)) bound for (0<t\le1/2). All array norms include every ordered displayed index. No (B\approx I), third-slot cap, full coefficient symmetry, commutativity, density realization, or uniform inverse of (q) is assumed. Gaussian expectation is over the single common vector (x), not independent vectors in different slots. The curl is finite: (Dq) is a Frobenius contraction, so its full derivative-array energy is at most (\operatorname{tr}B\le Km).

**2. Strict scalar convexity and constants: PASS ORIGINAL.** For the conditional excess (W_a=G-a\mid G>a), direct Gaussian integration gives
\[
 d=\mathbb EW_a=q-a,\quad \operatorname{Var}W_a=1-qd,\quad
 q'=qd,\quad q''=q(d^2+qd-1)=q(d^2-\operatorname{Var}W_a).
\]
The source already proves (0<q'<1). Its strictly increasing hazard, not a merely weak IFR assertion, gives
\[
 S_a(u+v)=S_a(u)S_a(v)e^{-J_a(u,v)},\qquad
 J_a(u,v)=\int_0^v(q(a+u+s)-q(a+s))\,ds>0
\]
for (u,v>0). Tonelli and the survival moment identities give
\[
 \mathbb EW_a^2=2\int_0^\infty\int_0^\infty S_a(u+v)\,du\,dv,
 \qquad
 q''(a)=2q(a)\iint[S_a(u)S_a(v)-S_a(u+v)]\,du\,dv>0.
\]
This verifies the factor two and the sign in I61 (3). The integrals are finite for every real (a). There is no circular use of strict (q''): strict monotonicity of (q), already given by (q'=qd>0), supplies it.

Consequently (q') is increasing and (a_R=q'(-R)\ge R\varphi(R)), since (q(-R)\ge\varphi(R)) and (d(-R)=q(-R)+R\ge R). For (a\in[-R,R]), (u,v\in[1,2]), all arguments lie in ([-R,R+4]). The global (q'<1) and (q(0)<1) imply (q\le R+5) there. Thus (S_a(u)S_a(v)\ge e^{-4(R+5)}), (J_a(u,v)\ge q'(-R)), and (1-e^{-q'(-R)}\ge q'(-R)/2). Substitution on this unit-area square gives
\[
 q''(a)\ge\varphi(R)e^{-4(R+5)}q'(-R)
 \ge \frac{R}{2\pi}e^{-R^2-4R-20}.
\]
The same argument controls negative and positive (a); it is not a numerical minimum or a positive-tail asymptotic used on the negative tail. These are precisely the original bounds.

**3. Paired spectral equations, basis and signs: PASS ORIGINAL.** At a fixed (x), choose (U) with (U^TL(x)U=\operatorname{diag}(\lambda_i)). Define
\[
 \widetilde X_{isr}=\sum_{a,b,c}U_{ai}U_{bs}U_{cr}X_{abc},\qquad
 \widetilde X_r=U^T\Big(\sum_cU_{cr}X_c\Big)U.
\]
If (C(x)_{isr}=(Dq(L(x))[X_r])_{is}-(Dq(L(x))[X_s])_{ir}), linearity and orthogonal equivariance of the Fréchet derivative imply that (U^{\otimes3})'s coordinate action on (C(x)) has entries
\[
 q[\lambda_i,\lambda_s]\widetilde X_{isr}
 -q[\lambda_i,\lambda_r]\widetilde X_{irs}.
\]
This explicitly rotates the derivative index. It is a pointwise tensor transformation of an already differentiated field; no derivative of (U(x)) is taken. The same (U) diagonalizes (L(-x)=-L(x)), and the transformed coefficients at the two evaluations are identical. They are not recomputed from an independently chosen basis at (-x).

Evaluation of the field derivative at (-x) is (Dq(-L(x))[X_r]). Differentiating the composition (x\mapsto q(L(-x))) would instead introduce (-X_r); that is not the expression used here. I61 uses the correct evaluated-field convention.

The integral formula (q[a,b]=\int_0^1q'((1-u)a+ub)du) handles all repeated eigenvalues. Its derivative in (b) is at least (h_R/2) inside the cutoff interval. Hence (alpha-eta) and (gamma-eta) have opposite signs and (|\alpha-\beta|\ge h_R|\lambda_s-\lambda_r|/2). Write (w_1=|\gamma-\eta|), (w_2=|\alpha-\beta|). When the eigenvalues differ,
\[
 (w_1\alpha+w_2\gamma)d=w_1e_++w_2e_-.
\]
The coefficient is at least (a_R(w_1+w_2)>0). In fact this proves the stronger (d^2\le a_R^{-2}(e_+^2+e_-^2)); I61's factor two is safe. When (lambda_s=lambda_r), (e_+=\alpha d) directly, so no division by an eigenvalue gap is needed. Also
\[
 |(\lambda_s-\lambda_r)C|^2
 \le4h_R^{-2}|e_+-\alpha d|^2
 \le8h_R^{-2}(1+2a_R^{-2})(e_+^2+e_-^2).
\]
Finally (|\lambda_i+\lambda_s|\le2R) and the two-term squared triangle inequality give exactly
\[
 z^2\le M_R(e_+^2+e_-^2),\qquad
 M_R=16R^2a_R^{-2}+16h_R^{-2}(1+2a_R^{-2}).
\]
This includes (r=s), coincident eigenvalues, zero eigenvalues, and either ordering of the two varying eigenvalues. The tensorial norm is basis-independent within repeated eigenspaces, so arbitrary such choices cause no measurable integral ambiguity.

**4. Gaussian fourth moment and all-slot tails: PASS ORIGINAL.** Wick contraction in fixed coordinates gives
\[
 \mathbb EL^4=B^2+\sum_rX_rBX_r+C,\quad C=\sum_{r,s}X_rX_sX_rX_s.
\]
The crossing sum is self-adjoint after interchanging (r,s), but need not be positive. For the row/column families (A_{rs}=D_{rs}=X_rX_s),
\[
 \sum A_{rs}A_{rs}^*=\sum_rX_rBX_r\preceq K^2I,\quad
 \sum D_{rs}^*D_{rs}=\sum_sX_sBX_s\preceq K^2I.
\]
Thus (|C|_{\rm op}\le K^2) and (C\preceq K^2I), which suffices for (mathbb EL^4\preceq3K^2I). Treating (C) as a positive summand would be an invalid explanation, but the original explicitly uses the norm bound. The independent finite suite includes three real symmetric Clifford generators with (C=-3I), so this issue is genuinely tested.

For a **fixed** tensor (V), slot (j) gives (mathbb E\|L_jV\|^2=\langle V,B_jV\rangle\le K\|V\|^2). If (j=a), the fourth-moment inequality gives the next bound. If (j\ne a), (L_j,L_a) commute for each common (x), so
\[
 L_j^2L_a^2\preceq\tfrac12(L_j^4+L_a^4),\qquad
 \mathbb E\|L_jL_aV\|^2\le3K^2\|V\|^2.
\]
There is no independence assumption; the common Gaussian produces the same Wick contractions in every slot. A deterministic third-slot marginal may have arbitrarily large operator norm. The bound traces (\mathbb EL^2\preceq KI) or (\mathbb EL^4\preceq3K^2I) against that marginal and uses only its trace. For example, (X_1=I_m,X_{r>1}=0) has (B=I) and third Gram matrix with eigenvalue (m). This family is covered.

Put (P=1_{[-R,R]}(L)), (\Pi=P^{\otimes3}), (J=(23)). Pointwise, (Pi) commutes with (J) and every (L_j). The orthogonal-projection union bound and spectral calculus give
\[
 I-\Pi\preceq\sum_j(I-P_j)\preceq R^{-2}\sum_jL_j^2.
\]
Since (S=(I-J)X) is fixed,
\[
 \mathbb E\|(I-\Pi)S\|^2\le3KR^{-2}\|S\|^2
 \le12KR^{-2}\|X\|^2.
\]
For (Z=(I-J)(L_1+L_2)X), which is **not fixed**, move only (I-J) through (Pi), bound its norm by two, and keep (X) fixed throughout:
\[
 \begin{split}
 \mathbb E\|(I-\Pi)Z\|^2
 &\le4R^{-2}\sum_{j=1}^3\mathbb E\|L_j(L_1+L_2)X\|^2\\
 &\le8R^{-2}\sum_{j=1}^3\sum_{a=1}^2\mathbb E\|L_jL_aX\|^2
 \le144K^2R^{-2}\|X\|^2.
 \end{split}
\]
This derives the original 144 without applying a fixed-tensor bound to (Z(x)). Using (|X|^2=\operatorname{tr}B\le Km) yields the original (12K^2m/R^2) and (144K^3m/R^2) tails. No random eigenbasis is averaged as though it were fixed.

Each ordered curl array has squared norm twice the (r<s) sum, with diagonal zero. Gaussian reflection preserves measure. Since the same cutoff satisfies (Pi(-x)=Pi(x)), the integrated upper bound from the two curls is (4mt); even discarding the cutoff on their right sides already proves this bound. Orthogonal splitting between (Pi) and (I-Pi), not a squared triangle inequality there, gives precisely I61 (11):
\[
 \|S\|^2/m\le8a_R^{-2}t+12K^2/R^2,
 \qquad \mathbb E\|Z\|^2/m\le4M_Rt+144K^3/R^2.
\]

**5. Exact coefficient extraction and modulus: PASS ORIGINAL.** For tensors invariant under (12), the three distinct permutations in the full symmetrization have equal pairwise inner product. If this common product is (b) and (a=\|X\|^2), the projection error is (2(a-b)/3), while (|X-JX|^2=2(a-b)). Hence the exact factor is (1/3), including repeated-index coefficients.

Use the vector convention (S_{rs}=X_re_s-X_se_r). Differentiate (L^2) algebraically and use (X_te_s=X_se_t+S_{ts}). The coefficient of (x_t) in the ordered polynomial curl is exactly
\[
 [X_r,X_s]e_t+X_rS_{ts}-X_sS_{tr}+X_tS_{rs}.
\]
This holds without third-index symmetry. Each of the three error arrays has squared norm at most (K\|S\|^2); for instance summing in (r) first gives (sum_r|X_rS_{ts}|^2=\langle S_{ts},BS_{ts}\rangle). Gaussian coefficient orthogonality and two triangle/Cauchy estimates therefore give
\[
 E_{\rm comm}\le2\mathbb E\|Z\|^2+18K\|S\|^2.
\]
Combining with the symmetry term produces
\[
 F_K(R)=8(1/3+18K)a_R^{-2}+8M_R,
 \quad D_K=12K^2(1/3+18K)+288K^3=4K^2+504K^3.
\]
The unconditional cap is also valid:
(|X-\operatorname{Sym}X|^2\le Km) and
(sum\|[X_r,X_s]\|^2\le4\sum\|X_rX_s\|^2=4\operatorname{tr}B^2\le4K^2m).
Thus the original explicit infimum
\[
 \chi_K(t)=\min\{K+4K^2,\inf_{R\ge1}(F_K(R)t+D_K/R^2)\}
\]
is finite, nonnegative and nondecreasing for (t\ge0). For any tolerance choose (R) first, independently of (m,X), then choose (t) small. At (t=0) its value is zero. An attained minimizing cutoff is not needed.

From the proved scalar estimates,
(a_R^{-2}\le2\pi e^{R^2}), (h_R^{-2}\le4\pi^2e^{50R^2}) for (R\ge1), since (2R^2+8R+40\le50R^2). Absorbing (R^2\le e^{R^2}) proves (F_K(R)\le C(1+K)e^{52R^2}). For (0<t\le e^{-104}), set (R^2=\log(1/t)/104\ge1): the two costs are bounded by (C(1+K)\sqrt t+104D_K/\log(1/t)), hence by (C_K/\log(e/t)). The remaining interval up to (1/2) is handled by enlarging (C_K) using the cap. No constant depends on dimension. At (K=0), all matrices are zero; at (m=1), the entire coefficient residual is zero for every scalar coefficient. Neither endpoint requires a density argument.

**6. Symmetric repair: PASS ORIGINAL, including constants.** Flatten the **first** slot of (X) as (M_X:\mathbb R^m\otimes\mathbb R^m\to\mathbb R^m). Matrix symmetry gives (M_XM_X^*=B_X\preceq KI). This is not the third flattening. For (T=\operatorname{Sym}X), (e=\|T-X\|), (P=1_{[0,4K]}(B_T)), (Q=I-P), (k=\operatorname{rank}Q), set (a=\|Q_1T\|). Then
\[
 2\sqrt{Kk}\le a\le e+\sqrt{Kk}.
\]
For (k>0), the first inequality may be strict, which only strengthens the result. These inequalities imply (sqrt{Kk}\le e) and (a\le2e); (k=0) is immediate. Full symmetry makes the three discarded one-slot masses equal. The commuting projection bound gives (|T-P^{\otimes3}T\|^2\le3a^2\le12e^2). With (Z=P^{\otimes3}T), (|Z-X\|^2\le26e^2).

The new first flattening is (P M_T(P\otimes P)). Hence
(B_Z\preceq PM_TM_T^*P=PB_TP\preceq4KI).
The last inequality alone would not follow from projecting only the output slot while claiming symmetry; all three projections are used.

Let (D=Z-X). The rectangular product estimate gives
\[
 \|B_Z-B_X\|_F\le(2\sqrt K+\sqrt K)\|D\|_F,
\]
so its square is at most (9K\cdot26e^2=234Ke^2). For arbitrary symmetric families (A,D), the full ordered commutator-array bound is
\[
 \|([D_r,A_s])_{rs}\|_F\le2\|B_A\|_{\rm op}^{1/2}\|D\|_F.
\]
Both product orders use (sum_s A_s^2\preceq\|B_A\|I); the coefficient indices have not been held fixed before summing. Expand
([Z_r,Z_s]-[X_r,X_s]=[D_r,X_s]+[Z_r,D_s]).
The two array norms are bounded by (2\sqrt K\|D\|) and (4\sqrt K\|D\|); thus the squared difference is at most (36K\cdot26e^2=936Ke^2).

Applying the squared triangle inequality to normalization and commutators yields
\[
 m^{-1}\bigl(\|B_Z-I\|^2+E_{\rm comm}(Z)\bigr)
 \le2\beta+2\eta+(468+1872)K\eta
 =2\beta+(2+2340K)\eta.
\]
This does not assume small total (e); division by (m) is valid throughout. (K=0) is outside the lemma's stated positive-(K) formulation but is trivial directly with (X=T=Z=0); no inverse (K) is used then.

The repair handles only new heavy mass produced by symmetrizing an already capped tensor. It does not repair I59's uncapped heavy star. An exact stress family is (X_1=I_d,X_{r>1}=0): its symmetrization has (B_T=\operatorname{diag}((d+8)/9,2/9,\ldots,2/9)), exceeding (4I) for (d>28). The stated projection really acts on this family and removes its symmetric block. Appending scalar odeco blocks allows small normalized symmetry error while the same cutoff remains active. This checks the distinction between total and normalized mass rather than assuming it away.

**7. I59 inputs as used: separate PASS ORIGINAL verdicts.** These are independent deductions from the actual source operations, not reliance on I61's seven summary verdicts.

* **P2.1 simultaneous remainder:** the exact logdet identity inserts (-D_S(C)) into the source's signed deficit reduction. All subsequent bounds concern other summands. At the final chaos step retain ((1-2u)(1+68u)/50); multiplication by (d\|Y_d\|^2), (u=1/d), gives ((d-2)(d+68)/(50d)\|Y_d\|^2). The distinct slack (7/50-69/500=1/500) remains. For (d=2), the full coefficient is (d/1000); for integers (d\ge3), ((d-2)(d+68)\ge d^2). This proves all four simultaneous bounds (D\le2\delta), (\|Y\|^2\le1000\delta), (\|\partial Y\|^2\le2000\delta), (\Omega\le2000\delta). The transport separation surplus is canceled by the pair inequality and is not available a second time. Source Gaussian (H^1) regularity makes these series manipulations legitimate.
* **P2.2 polar normalization:** ((S^{1/2}P)(S^{1/2}P)^*=S^{1/2}P^2S^{1/2}=K_c), so its left polar factorization is (K_c^{1/2}O). Coupling (K_c^{1/2}OV) to (OV), for isotropic (V\sim f), costs (|K_c^{1/2}-I|_F^2\le\operatorname{tr}K_c-\log\det K_c-m\le2\delta). This does not commute (S,P) or invent a covariance. Left multiplication by (S^{1/2}) and the forward Lipschitz estimate give (40000\delta/37). The bounds on (\operatorname{tr}(SB)) and the regularized field follow by scalar spectral inequalities traced against (S), even when (S) does not commute with (q(L)).
* **P3.1 Gaussian Hodge:** on vector chaos degree (k), (partial^*v) has degree (k+1), and the gradient projection is (partial\partial^*v/(k+1)). Creation/annihilation gives (sum_{r<s}\|\partial_rv_s-\partial_sv_r\|^2=(k+1)\|v\|^2-\|\partial^*v\|^2). The curl degree is (k-1), making the resolvent exactly ((N+2)^{-1}). At (k=0), every constant vector is a gradient and both sides vanish. Orthogonal summation/completion gives distributional curls. This is a row-gradient statement, not a coefficient theorem.
* **P3.2 Fourier/Duhamel family bound:** on the negative tail the denominator (\Phi(-a)) is bounded away from zero and differentiated numerators are Gaussian times polynomials. On the positive tail (q(r)=r/F(r^{-2})), with (F(u)=\int e^{-v-uv^2/2}dv); fixed derivatives of (F) are bounded at (u\ge0) near zero. Taylor expansion with differentiated remainders gives (q''=O(r^{-3})), (q'''=O(r^{-4})). Thus (q'',q'''\in L^2), and weighted Plancherel yields (c_q=(2\pi)^{-1}\|\widehat{q''}\|_1<\infty). Twice integrating Fourier inversion is legitimate on every finite spectral interval; the subtraction of the constant and linear Taylor terms removes the zero-frequency singularity. The two Duhamel orderings each have simplex volume (1/2). For a fixed unitary middle factor, (sum_r\|HUX_r\|_F^2\le K\|H\|_F^2) and (sum_r\|X_rUH\|_F^2\le K\|H\|_F^2). The unitaries depend on the interpolating matrix, not on (r). Minkowski over the two simplices, frequency, and interpolation parameter proves the original family bound without a matrix-count factor. Adding the (Dq(A)[\partial Y]) term and the antisymmetrization norm (sqrt2) gives the original (A_K=2(\sqrt{2000}+c_q\sqrt{1000K})^2).
* **Channel identity and tensor-from-dephasing:** full symmetry gives (langle T_r,T_s\rangle=B_{rs}). On all (m^2) matrix units, both superoperator norms squared are (operatorname{tr}B^2), and the cross inner product is (sum_{r,s}\operatorname{tr}(T_rT_sT_rT_s)). This proves the exact commutator identity. At (B=I), both slice projection and dephasing have rank (m). Their squared distance (b) leaves off-diagonal matrix mass (b/2). A double-index tensor coefficient appears in two of three off-diagonal matrix placements, while an all-distinct coefficient appears in all placements. Thus off-diagonal tensor mass is at most (3b/4); normalization pays at most the same amount for diagonal sign rounding, proving (3b/2). This requires one global basis and exact (B=I) at this step.
* **Heavy star, missing dimensions, and flags:** the original star's (B), cross-slot mass ((m-1)/2), and all-slot loss (3(m-1)/2) follow directly from its three nonzero placements. No density with the required small error is constructed. The marginal coupling lifts by disintegration, and an independent centered reference in (k) missing coordinates costs (2k), giving (b+2k). The chain rule is (delta=\sum\mathbb E\delta_i+\sum\mathbb E\log s_i), with the integrability qualification in I59. The rotated exponential pair has gaps (1-\psi(2)-\frac12\log2) and (\frac12\log12-1), canceled by (\psi(2)-\frac12\log6). This is an actual equality-law counterexample to an arbitrary-flag positive budget, not to U.
* **Radial theorem, audited but not needed by CE:** a log-concave ratio to the equal-mean Gamma density has interval superlevel set. Equal mass and mean force the two-crossing pattern unless the laws coincide. Multiplication by ((s-a)(s-b)) gives (v\le\mu^2/m). With independent Gamma radius and common Dirichlet direction, the transverse cost is (2(m-1)(1-\sqrt{m/(m+1)}\,\mu/\sqrt{M_2})) and the axial cost is exactly two. Their sum is at most (4m/(m+1)). Gaussian maximum entropy for the radius, Jensen for the logarithmic moment, and the stated Stirling lower bound give (delta\le1). The (m=1) coupling costs two, correctly not zero at equality. Affine whitening changes the comparison only by an orthogonal map. This proves the original scope and does not prove a deficit modulus.

I53's unrestricted fixed-dimensional result and I55's original-proof verdict are not reopened by these audits. I56's independent transverse derivative has normal norm factor two and quadratic remainder (sqrt5d^2) in **total** tensor distance. At normalized distance it carries a (sqrt m) factor. Its compactness entrance therefore does not close AR. The existing quadrature caveat and I59's (m=512) nonconvergence remain unchanged: exact specified-orientation costs bound the orbit infimum, whereas unvalidated numerical quadrature values do not certify those bounds.

**8. Conditional entropy propagation: PASS ORIGINAL AS CONDITIONAL.** The scope is the source smooth class (V\in C^\infty), (0<c_-I\le D^2V\le c_+I<\infty), centered and isotropic, whose normalized original coefficient energy satisfies the fixed cap (B_X\preceq KI). Put (u=\delta/m), (eta=E_X/m). The preceding audit gives (t\le A_Ku), and monotonicity of the explicit (chi_K) gives (eta\le\chi_K(A_Ku)).

From the actual source weight,
\[
 \frac{\omega(\lambda)}{(\lambda-1)^2}=
 \frac3{37+3\lambda}\left(\frac3{20}+\frac{49}{100}\frac{37}{37+3\lambda}\right)
 \min\left(\frac{13}{100},\frac{32}{25\sqrt\lambda}\right).
\]
It has a positive continuous extension on every finite ([0,K]), including the prescribed minimum at zero and the value (94107/16000000) at one. Hence (c_K>0) and (eta\le2000u/c_K). No large-(lambda) quadratic lower bound is asserted.

If the explicitly unproved AR hypothesis at cap (4K) provides the stated modulus (
ho_{4K}), the repair residual is at most
(4000u/c_K+(2+2340K)\eta). It returns one global (T^*=U^{\otimes3}\sum e_i^{\otimes3}). The triangle estimate is
\[
 \|X-T^*\|^2/m\le52\eta+2\rho_{4K}(4000u/c_K+(2+2340K)\eta).
\]
The exponential comparison map (H_U(x)=\sum_j u_j[-\log\Phi(-\langle u_j,x\rangle)-1]) has covariance (I) and derivative (q(L^*)). Forward q-Lipschitzness and Gaussian Poincaré give
\[
 r^2/m:=\|F-H_U\|_2^2/m\le2000u+104\eta+4\rho_{4K}(\cdots).
\]
Spectral-measure Jensen and first-chaos projection give (P^2\succeq(\mathbb EDF)^2\succeq q(0)^2I). Only one positive matrix is squared, so no false operator-monotonicity claim occurs. For (V=P^{-1}F), isotropy of (V,H_U) gives (|\mathbb E(VH_U^T)|_{\rm op}\le1), hence (r^2\ge\|P-I\|_F^2). The same Gaussian coupling then costs at most (4r^2/q(0)^2). These are exactly the original constants and orientation.

The conditional computation supplies no AR modulus and no initial cap for arbitrary densities or their approximants. Source weighted approximation concerns laws, entropy and covariance; it supplies neither coefficient convergence nor a uniform cap. There is no extension to nonsmooth densities in I61 to pass here. The logarithmic CE rate also cannot be advertised as U's square-root rate.

**9. Channel and deflation partials: PASS ORIGINAL, with boundaries preserved.** Full symmetry makes (Delta^*\Delta=B). At (B=I), (Delta) is an isometry and (Delta\Delta^*=P_T). The ordered ((i,j,k,r)) coefficient of its coassociator is
\[
 \sum_a(T_{ija}T_{akr}-T_{jka}T_{iar})=[T_i,T_k]_{jr}.
\]
Summing every ordered index proves I61 (15) with no factor two adjustment. The real Kraus formula extends to a complex CP map; unitality, trace preservation and Schwarz give its Frobenius contraction on all matrices, including skew matrices.

With (E=\|\Phi-P_T\|_{HS}^2), expand (Phi^2-P_T^2=\Phi(\Phi-P_T)+(\Phi-P_T)P_T). The two contraction bounds and one further subtraction give (|\Phi^2-\Phi\|_{HS}\le3\sqrt E). On ([-1,1]), distance to ({0,1}) is at most (2|\lambda^2-\lambda|); either tie convention at (1/2) is valid. Thus the original constants (6,7,49) follow. Rank difference is bounded by squared distance between orthogonal projections. This spectral projection need not be CP or an algebra projection.

For the generic obstruction, the partial trace is **unnormalized** and the prefactor is (1/k):
(mathcal E(H)=k^{-1}\operatorname{Tr}_2(H)\otimes I_k), (m=k^2).
Kraus operators (k^{-1/2}(I\otimes E_{ab})) demonstrate complete positivity; direct partial tracing proves unitality, trace preservation, self-adjointness, idempotence, and real/complex superoperator rank (k^2=m). For any real unit vector (u), (
ho=\operatorname{Tr}_2(uu^T)) is positive of trace one, so
(|\mathcal E(uu^T)\|_F^2=\operatorname{tr}\rho^2/k\le1/k).
Summing over **any** real orthonormal basis gives overlap at most (m/k); since both projections have squared HS norm (m), their squared distance divided by (m) is at least (2(1-1/k)). The same argument holds for complex bases using adjoints. It is not merely a product-basis calculation. For (k>1), the range contains nonsymmetric real matrices, whereas the span of real symmetric cubic slices does not. Thus this is not a linked AR counterexample.

At a global maximizer (v), oddness and nonzeroness give (c>0), stationarity gives (T_vv=cv), and the constrained Hessian gives (H\preceq cI/2). Symmetry and (B=I) imply (c^2+\|H\|^2=1). For an orthonormal complement (w_j),
([T_v,T_{w_j}]v=(H^2-cH)w_j). Therefore (a(v)=\|H^2-cH\|^2), and (|\lambda^2-c\lambda|\ge c|\lambda|/2) for every eigenvalue (\lambda\le c/2), including negative eigenvalues. This proves (18). The removed mixed mass is (3\|H\|^2\le12a(v)/\tau^2) when (c\ge\tau). Block multiplication gives (B_{T'}=I-2H^2) and the stated outer-product commutator correction. Each outer-product array has norm (|H\|^2), giving the original perturbation bounds. The next restricted tensor generally has (B_{T'}\ne I); the report correctly does not repeat the normalized identity without paying its change. Adaptive energy summation and the small-(c) branch remain unpaid.

For the harmonic two-dimensional tensor, direct multiplication gives (B=I,E=4,c=1/\sqrt2,H=-1/\sqrt2,a(v)=1). The channel eigenvalues on (I,Z,X,J) are (1,0,0,-1), where (J) is the real skew matrix of operator norm one. Hence ((\Phi^2-\Phi)(J)=2J), proving cb defect at least two; in the complex Hermitian convention use (iJ). Appending scalar blocks preserves this witness while (E/m\to0). It also leaves only bounded total defective tensor mass, so it does not refute AR. Input-only polar normalization of (Delta) generally breaks symmetry; no exact-(B=I) reduction is supplied by it.

**10. Actual antecedent scope and review limits.** The pinned entropy rigidity uses two origin jets; it supplies neither the integrated CE coercivity nor a dimension-independent small-ball payment. The general-Mahler proof already uses a two-point spectral measure and Gaussian commutator identity, with a different layer/projection deficit. The tracial companion's full §10 explicitly proves fourth moment at most three for noncommuting symmetries and coefficient clipping errors (3/R^3,3/R^2); that proof operation is inherited prior material, not a novelty credited here. Its hypotheses are nuclear-algebra approximation and supplied projections. The near-inclusion common-corner/polar construction explicitly starts with two commuting ambient algebras and operator-norm approximation. None of these hypotheses is furnished by the normalized AR residual.

Fresh current primary captures give Bansil–Kachkovskiy **2608.31000v1**, Filonov–Kachkovskiy **1008.4002v2**, Kitaev **2405.02434v2**, CPV **0810.0812v1**, BDHR **1512.08031v1**, BDS **2206.01521v1** and its published article, Robeva **1409.6685v3**, Auddy–Yuan **2007.09024v2**, and Poinsot's author manuscript. The proof passages read have identical extracted text to the corresponding I61 captures; that equality is separately recorded, rather than presumed from identifiers.

The [Bansil–Kachkovskiy statements](https://arxiv.org/abs/2608.31000v1) retain a family (sqrt N) factor and (N)-dependent iterated power; [FK](https://arxiv.org/abs/1008.4002v2) likewise retains count dependence. [Kitaev](https://arxiv.org/abs/2405.02434v2) requires uniform Banach-algebra/cb defects and concludes an abstract C*-algebra encoding, with an explicit warning about positivity of spectral rounding. [BDS Proposition 4.1](https://rendiconti.dmi.units.it/volumi/54/017.pdf) and [Robeva Lemma 3.7](https://arxiv.org/abs/1409.6685v3) concern tangent equations; [BDHR](https://arxiv.org/abs/1512.08031v1) concerns exact real associativity. [Auddy–Yuan](https://arxiv.org/abs/2007.09024v2) starts with odeco comparisons or nearly isometric factors. [CPV](https://arxiv.org/abs/0810.0812v1) is exact commutative dagger Frobenius classification, and [Poinsot](https://lipn.fr/~poinsot/Articles/Hilbertian_Frobenius_algebras_rev.pdf) treats exact Hilbertian algebras and approximate units, not approximate multiplication. None is imported as an external theorem proving AR. Full external theorem proofs beyond the recorded applicability passages were not independently certified, and no CE step requires such certification.

No exhaustive literature survey, human peer review, or proof-assistant certificate is claimed. Corpus inventory/search coverage is not a claim to have read all 749 manuscripts. Bounded searches establish no worldwide priority; no MathDB score was assigned. These are review limits, not unresolved steps in the original CE proof. Analytic acceptance here rests on the written derivations, not successful provenance replay or floating positivity.

**11. Reproduction and immutable evidence.** The I63 capture freezes 15 inputs, including exactly four mutable ledgers, 19 pinned files, ten individual predecessor brief/objection records, and hashes of 450 prior evidence files. It independently checks the complete 13,223-entry / 749-manuscript tree and all 9,340 ignored corpus files against SHA256 and pinned Git blob identities. There are 28 read contracts and 33 exact passage records. Three searches use the fixed corpus domain and line **multisets**, with 321, 32, and 729 matches. No growing review directory is part of a search domain; no old seal was refreshed and no recursive archive copied.

The unchanged author verifier passes: 110 sealed artifacts, 14 inputs, 19 pins, 339 prior hashes, 8 earlier brief copies, 37 passages, 30 contracts, 27 successful primary responses, 13 PDF replays, 4,640 exact assertions, and ten floating records. Its four ledger drifts are informational. I63's fresh retrieval records preserve 21 successful responses, including three pinned raw files, and ten PDF text replays. URLs, versions, UTC retrieval times, bytes and errors are in `primary/manifest.json`; no failed primary request occurred in this round.

The independent diagnostics make **33,917 exact assertions** and import no author code. They use integers and exact fractions for dense/non-full-symmetry and degenerate coefficient arrays through dimension nine, correlated-slot Wick moments against arbitrary fixed tensors, the exact negative crossing example, polynomial coefficient identities, all-matrix-unit channel identities, ordered coassociators, active symmetrization cutoffs with additional scalar blocks, rational Householder bases for the partial-trace obstruction, harmonic and deflation identities, full three-index derivative rotations, exact paired inequalities with repeated eigenvalues for a convex polynomial, and sparse Hermite Hodge identities through degree nine. Twenty-nine separate floating Mills records include negative/positive tails and repeated eigenvalues; these floats are diagnostics, not proofs. The analytic all-bases CP argument is not replaced by finitely many Householder tests.

Run from the project root:

```bash
PYTHONDONTWRITEBYTECODE=1 python frontier/experiments/i63_entropy_coefficient_extraction_r2/diagnostics.py
PYTHONDONTWRITEBYTECODE=1 python frontier/experiments/i63_entropy_coefficient_extraction_r2/verify.py
```

Both are offline and read-only. The verifier checks the I63 seal, complete input/pin/corpus inventories, unchanged prior files, multiset searches, exact passage/read contracts, primary/PDF bytes, author replay, and independent diagnostics. One-shot capture/fetch/evidence writers are separate. A local optional-library probe found NumPy unavailable; no dependency was installed, and the final independent checks use the Python standard library. Initial wrong-working-directory and overlong display attempts changed no files; substantive required texts were read in bounded chunks. These preparation limitations are recorded without changing any original history.

**Final analytic verdict: CE61 ORIGINAL COMPLETE PROOF PASSES WITHOUT CHANGES.** The repair and supporting conditional/partial claims pass separately as described. AR and U retain their original open status; substantiality and any count decision are outside this review.
