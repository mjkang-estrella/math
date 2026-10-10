# I50 — independent full-proof audit of H49

**H49: PASS ORIGINAL WITHOUT REPAIRS, under the accepted pinned OpenAI theorem and proof-operation premises.** This verdict covers the original unrestricted statement, including its displayed dimension-only exponent. Construction B's Euclidean inverse, admissible Neumann incompatibility example, and interval form-domain obstruction also pass in their stated diagnostic scopes. They are not counterexamples to H49.

The estimates below independently check the original argument. They expand its compactness, coordinate, BV, and endpoint interfaces; no replacement construction, strengthened hypothesis, changed exponent, or reversed limiting order is required. In particular, the symbol \(\nabla p\) in I49's radial Jacobian must mean the full gradient of the homogeneous gauge, as distinct from the explicitly subscripted \(\nabla_Sp\). That is the interpretation supplied by \(p=p_C=h_{C^\circ}\); the correct formula is made explicit below. Reading it as a spherical gradient would be false, even on a ball.

This is a proof verdict only. I51's significance determination, parent integration, and publication are separate. The planar P10 proof approval and TECHNICAL ONLY disposition are preserved without a new planar audit. The symmetric equality antecedent retains full attribution to **Yude Liu, Qiang Sun, and Ge Xiong, *The centered logarithmic Brunn–Minkowski inequality*, arXiv:2610.10152v2**. Their external centered nonsymmetric theorem is not assumed or certified here.

## 1. Quantifiers, inputs, and dependency contracts

For every integer \(n\ge3\), every \(0<r<R\), and every \(0<\tau_0<1/2\), the original claim is a constant \(c(n,r,R,\tau_0)>0\) such that every origin-symmetric convex pair
\[
rB\subset K,L\subset RB,\qquad \lambda\in[\tau_0,1-\tau_0]
\]
satisfies
\[
\Delta_\lambda=\log|\mathcal W[h_K^{1-\lambda}h_L^\lambda]|
 -(1-\lambda)\log|K|-\lambda\log|L|
 \ge c\,d_{\mathcal E}(K,L)^{\alpha_n}.
\]
Here \(\mathcal E\) includes every common complementary-block dilation pair, one block, and oblique subspaces. Comparison bodies have no prescribed original-ball bounds. The audit does not restrict facets, individual surface masses, regularity, reflections, or angles. The exponent is exactly the author's permissible choice
\[
\alpha_n=64n(n+2)(a_n+b_n+1)/b_n
\]
with the explicit constants in I49 (5.2a), not a new unspecified dimensional exponent.

I read the complete I49 report and brief, the complete I46, I47 and I48 reports, I44's relevant moment/completion/boundary arguments, I45's detailed audit of those arguments, and the parent I49 verification record. Their actual bytes, the full present brief and historical appended instructions are frozen. The four shared ledgers are mutable observations. No old archive was recursively copied, no old seal was refreshed, and no author file was edited.

The accepted pin is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. I read the actual logarithmic manuscript's statement, reduction, moment construction, adjunction, density, tensor and variance proofs, and its measure/\(L_p\) companion consequences. Accepted upstream operations are not re-audited for truth. Their new limiting and quantitative uses are audited. The complete preprint tree, rather than the truncated root cache or historical catalogue count, binds 13,223 entries and 749 manuscripts. The entire ignored 9,340-file corpus is enumerated and rehashed.

Fresh primary downloads match the corresponding I49 bytes. The operative interfaces are as follows.

* [Berman–Berndtsson, Theorem 1.1 and §§2.9, 2.12](https://afst.centre-mersenne.org/item/10.5802/afst.1386.pdf): arbitrary compact convex target, positive smooth density defined on the ambient space, weighted barycenter zero, smooth entire moment potential and gradient diffeomorphism onto the interior. Their proof constructs the variational solution and uses bounded sections for local regularity. Smooth target boundary is not a hypothesis.
* [Bonnet–Rubinstein, v1, Theorem 1.3, Propositions 3.3–3.4 and §3.5](https://arxiv.org/pdf/2604.09914v1): probability source densities converge in \(L^1\), after source translations, when centered nondegenerate moment measures converge in \(W_1\). The inverse is taken in the essentially continuous convex class. The proof compares constrained moment problems, then controls the truncation tail. This supplies convergence, not the final H49 rate.
* [Cule–Samworth, Proposition 2 and proof](https://arxiv.org/pdf/0908.4400): convergence of log-concave densities to a continuous positive density is locally uniform. [Figalli–Jhaveri–Mooney, Theorem 1.1 and §2](https://people.math.ethz.ch/~afigalli/papers-pdf/Nonlinear-Bounds-in-Holder-Spaces-for-the-Monge-Ampere-Equation.pdf): the interior second-derivative estimate requires controlled strict convexity as well as two-sided determinant and Hölder bounds. That requirement is paid below; determinant bounds alone would not pay it.
* [Klartag, Theorem 1 and its pp. 24–25 proof](https://www.math.tau.ac.il/~klartagb/papers/lc_moment.pdf): the bounded log-concave target gives \(\operatorname{tr}D^2\varphi\le2R(C)^2\). His approximation argument removes smooth/strictly convex target-boundary assumptions. We use this for the hard target only.
* [Hug–Schneider, Theorem 1.1, (1.2), and §3](https://home.mathematik.uni-freiburg.de/rschnei/ArchivHugSchneider.pdf): the surface-area specialization has exponent \(1/2\) in bounded-Lipschitz distance, with constants controlled by a ball containing the bodies plus \(2B\). Its parallel-volume/Vandermonde proof has no facet restriction. The radial verification in I49 is also checked below.
* [Figalli–Maggi–Pratelli, Theorem 1.1, (1.6), (1.8), and §3.5](https://people.math.ethz.ch/~afigalli/papers-pdf/A-mass-transportation-approach-to-quantitative-isoperimetric-inequalities.pdf): anisotropic perimeter deficit controls squared volume-normalized translation/dilation asymmetry for arbitrary convex Wulff shape. The proof removes shape dependence by affine normalization. The input orientation and all subsequent conversions are checked in §7 below.
* [Liu–Sun–Xiong v2, Lemma 3.4, (3.10)–(3.16), and the contact-measure argument](https://arxiv.org/pdf/2610.10152v2): the unnormalized completion, retained regularizer and contact-pair mechanism are fully credited. Their linear-tilt compactness lemma is not silently invoked for a quadratic tilt. [Kolesnikov–Livshyts–Rotem v3, §4.3, Proposition 4.8](https://arxiv.org/pdf/2507.12099v3) supplies the actual Hessian-Bochner antecedent cited by the pin; it is not an extra finite-deficit hard-field theorem.

The source directory records exact read ranges and literal extracts. These dependency checks do not supply a literature-significance verdict.

## 2. The finite-soft retained identity and hard sequence

### 2.1 Completion and coordinate covariance

Use \(x=\nabla\varphi(z)\), \(\tau=D_z^2\varphi\), \(M=\tau^{-1}\), \(h=D_x^2v\), \(P=\tau h\), \(B=P\tau\), \(W=Px-\operatorname{div}_zP\), and \(R=D_zW-B\). Both \(B\) and \(D_zW\) are symmetric. For \(F=\sum\beta_i\psi_i\), \(U=F-EF\), \(\gamma_i=\beta_i/q\), homogeneity and the two adjunctions give
\[
E\operatorname{tr}(\tau H_i)=qE\psi_i,\quad
E\operatorname{tr}(BH_i)=E(W\cdot\nabla\psi_i)=E(u\psi_i),
\]
\[
E(x^TH_ix)=q(q-1)E\psi_i,\quad E(x^TH_iW)=(q-1)E(u\psi_i).
\]
The noncompact Stein pairing is justified at each fixed \(q,\varepsilon\) by its finite polynomial moments and finite \(4/\varepsilon\) cap. Nothing here requires uniformity in the sequence index.

The two homogeneous squares have combined cross term \(-2\beta_i E(u\psi_i)\) and combined constant \(\beta_i^2E\psi_i\). Hence the exact completion is
\[
\begin{split}
D+\|u-U\|_2^2={}&T(v)+\varepsilon E[\operatorname{tr}(MB^2)+|W|^2]\\
&+\sum_iE\operatorname{tr}\{M(B-\gamma_i\tau)H_i(B-\gamma_i\tau)\}\\
&+\sum_iE[(W-\gamma_ix)^TH_i(W-\gamma_ix)],
\end{split}
\]
where \(D=\sum\beta_i^2E\psi_i-EU^2\). All displayed terms are nonnegative. The first trace defining \(T\) is \(\operatorname{tr}((D_xW)^2)\), not a Hilbert–Schmidt square.

In a constant frame with \(\tau=I\), let \(S=D_x^3v\), \(J_{ijk}=h_{ia}\varphi_{ajk}\), and \(K_{ak\ell}=\partial_\ell P_{ak}=S_{ak\ell}+J_{ka\ell}\). Full symmetrization gives
\[
2|S+\operatorname{Sym}J|^2+\tfrac16|J-J^{12}|^2
 =\tfrac12|K|^2+\tfrac32|\operatorname{Sym}K|^2.
\]
Consequently the accepted retained tensor calculation actually supplies
\[
T(v)\ge E\operatorname{tr}(MRMR)+\tfrac12E\mathscr D(P).
\]
The \(R\) square is available simultaneously with the full derivative contraction; retaining the latter does not consume the former. This proves I49 (3.3), including the term used to bound \(D_zW_j\).

For clarity, use the primal map \(x'=Tx\), dual source map \(z=T^Tz'\), and normalized potential
\(\varphi'(z')=\varphi(T^Tz')-\log|\det T|\). The laws are
\[
\tau'=T\tau T^T,\ M'=T^{-T}MT^{-1},\ P'=TPT^{-1},\ W'=TW,
\quad R'=TRT^T.
\]
For \(K_{ak\ell}=\partial_{z_\ell}P_{ak}\),
\[
K'_{ak\ell}=T_{ai}(T^{-1})_{jk}T_{\ell m}K_{ijm}.
\]
Substitution cancels all six indices in
\(M_{ab}\tau_{kr}M_{\ell s}K_{ak\ell}K_{brs}\). Also
\(\operatorname{tr}(M'R'M'R')=\operatorname{tr}(MRMR)\).
Probability measure changes cancel the volume Jacobians. Thus both integrated energies are invariant. The Euclidean \(W\) norm is only comparable, as I49 states. These are constant transformations; no differentiated moving frame is involved.

The signed boundary identity has the same covariance. At a regular normal set
\(u'=T^{-T}u/|T^{-T}u|\). Then
\(h_{TC}(u')=h_C(u)/|T^{-T}u|\),
\((TW)\cdot u'=W\cdot u/|T^{-T}u|\),
\(\rho'(Tx)=\rho(x)/|\det T|\), and
\(dS'=|\det T||T^{-T}u|dS\). The factors cancel, and the endpoint support ratio is unchanged at corresponding normals. Both \(m\) and \(\ell'\) are invariant; the same additive \(\log|\det T|\) enters each endpoint log volume.

### 2.2 Simultaneous changing directions, powers and time

The full Wulff path \(C_t\) lies between \(rB,RB\). The accepted inequality implies concavity of \(\log|C_t|\), even though the interpolated positive bound can be inactive. With \(g=\log|C_t|-\ell(t)\), concavity and the value at \(\lambda\) imply \(0\le g\le\delta/\tau_0\).

Nested nets with cardinality \(O_n(a_j^{-(n-1)})\) can be made by nested dyadic nets, using the next smaller mesh for a prescribed \(a_j\). Positivity and Lipschitz bounds of the endpoint supports give the uniform outer Wulff error \(O_*(a_j)\). Homogeneity gives
\[
N_j^{-1/q_j}P_j(t)\subset\{U_j\le1\}\subset P_j(t),\qquad
\int e^{-U_j}=\Gamma(1+n/q_j)|\{U_j\le1\}|.
\]
The analogous second-moment identity and Jensen pay the Gaussian insertion. Thus \(|G_j-\ell|\le C_*\delta\) on the entire interval. The accepted finite-soft variance inequality makes \(G_j\) smooth and concave. Interior secants bound \(|G_j'-\ell'|\), and integration of \(-G_j''\) over \([1/3,2/3]\) selects one time satisfying both estimates. This does not require a hard-path second derivative or a chamber of uniform length.

The choice \(\beta_{i,j}=-q_jb(p_i)\) gives \(m_j=EF_j=-G_j'(t_j)=-\ell'+O_*(\delta)\). Evenness removes the linear projection only. The accepted dense range supplies an even compact \(v_j\) with an arbitrarily prescribed error \(\eta_j\to0\), \(\eta_j^2\le\delta/j\), after each finite parameter choice. A norm bound for \(v_j\) is neither asserted nor used.

At fixed \(\varepsilon=\delta>0\), subselect \(t_j\to t\). On any compact subset of \(\operatorname{int}C_t\), all signed slab ratios are eventually at most one fixed \(\zeta<1\); this follows from positive distance to the boundary and continuous dependence on \(t,u\). For each fixed derivative order,
\[
\log(N_jq_j^k\zeta^{q_j-k})
\le q_j/j+k\log q_j+(q_j-k)\log\zeta\longrightarrow-\infty.
\]
Outside \(C_t\), a violated direction in the fixed dense union eventually occurs. A fixed spanning subcollection gives a uniform integrable superlinear tail majorant with every polynomial weight. Thus the targets converge in weighted \(L^1\), all fixed polynomial moments, and \(W_1\) to
\[
\mu=Z^{-1}1_Ce^{-\varepsilon|x|^2/2}dx.
\]
The sequence conditions are sufficient without an upper bound on \(q_j\): \(\log q_j/q_j\to0\). There is no exchange of limits requiring uniform finite-soft Hessian control.

## 3. Fixed-defect compactness, all fields, and signed boundary flux

### 3.1 Quadratic-tilt moment convergence

The hard target has the globally smooth positive density function \(g(x)=Z^{-1}e^{-\varepsilon|x|^2/2}\) restricted to an arbitrary symmetric convex body. Its barycenter is zero. Berman–Berndtsson therefore gives a smooth strictly convex entire moment potential with full interior gradient image and normalized source probability. Translating its minimum to zero and using uniqueness makes it even.

Both the soft and hard potentials are essentially continuous, since they are finite smooth functions on the whole source space. The targets have uniformly bounded first moments and a uniform positive lower bound on directional first moments from the density on \(rB\). Bonnet–Rubinstein therefore supplies source \(L^1\) convergence after translations. Cule–Samworth applies to the source log-concave densities, whose limit is continuous and everywhere positive. Logs and convex difference quotients give local \(C^1\) convergence.

The translated minima converge to the limiting minimum: on a fixed enclosing sphere a strictly convex limit has a positive height gap above its minimum. Uniform convergence preserves that gap. A convex function with a minimizer outside that sphere would contradict the gap along the segment from the center to the minimizer. Every subsequential limit of the minimizers is the unique limiting minimum. Recentring therefore preserves local convergence and the original even normalization.

On a fixed source ball and a larger compact neighborhood, local \(C^1\) convergence keeps all gradient images in one compact subset of \(\operatorname{int}C\). The moment equation has positive two-sided determinant bounds there, and every needed derivative of the target potentials is uniformly bounded. The strict-convexity modulus is not omitted: if the limiting Hessian is at least \(mI\) and the gradient error is \(e_j\), the tangent-plane separation is at least
\[
\tfrac m2|w-z|^2-2e_j|w-z|.
\]
At each fixed positive separation this is uniformly positive for the tail of the sequence; the finitely many earlier smooth strictly convex terms have a positive minimum on the compact pair set as well. Subtracting a tangent plane gives nested sections with uniform inner/outer radii and positive separation between fixed levels. Caffarelli's normalized-section estimate gives local \(C^{1,\beta}\). Composition makes the determinant right side uniformly Hölder. FJM now applies with the controlled strict-convexity modulus. The determinant lower bound and resulting Hessian upper bound give local uniform ellipticity. Differentiating the logarithmic equation gives
\[
(D^2\varphi_j)^{-1}:D^2\partial_k\varphi_j
 =\nabla V_j(\nabla\varphi_j)\cdot\nabla\partial_k\varphi_j
  -\partial_k\varphi_j.
\]
Interior Schauder estimates bootstrap all finite orders. Compactness and the already identified \(C^1\) limit give \(C^k_{\rm loc}\) convergence of the full subsequence, and local inverse maps converge on interior target compacts.

This verifies the quadratic-tilt extension using the actual hypotheses, rather than assuming it from LSX's linear-tilt statement. Every regularity constant in this paragraph is allowed to depend on the fixed deficit, body and core. None is carried into the later quantitative exponent.

### 3.2 Local Sobolev bounds and the retained budget

On a fixed source ball, coefficient convergence makes both the density and the tensor contraction uniformly elliptic. The completion bounds every component of \(D_zP_j\) in \(L^2\). Put \(A_j=\fint_{B_1}P_j\). Poincaré, bounded \(x_j\), and \(|\operatorname{div}P_j|\le\sqrt n|DP_j|\) imply
\[
\|W_j-A_jx_j\|_{L^2(B_1)}\le C\|DP_j\|_{L^2(B_1)}.
\]
The covariance \(Q_j=\int_{B_1}x_jx_j^Tdz\) tends to a positive definite matrix: a zero quadratic form would put the open gradient image in a hyperplane. Since \(\int|W_j|^2d\nu_j\le C_*\), it follows that \(A_j\) is bounded. Comparison of averages between \(B_1\) and larger balls now gives local \(H^1\) bounds for the entire matrix \(P_j\).

The retained square controls \(R_j\) locally in \(L^2\). With \(P_j\tau_j\) locally bounded in \(L^2\),
\(D_zW_j=R_j+P_j\tau_j\) bounds all first derivatives of \(W_j\). Thus both fields, not merely \(P_j\), have diagonal Rellich subsequences with strong local \(L^2\) and weak local derivative convergence. Smooth coefficient convergence passes
\[
W=P\nabla\varphi-\operatorname{div}P,\quad
P\tau=\tau P^T,\quad D_zW=(D_zW)^T,\quad R=D_zW-P\tau.
\]
Even \(P\) and odd \(W\) are retained. The assertion concerns a source-coordinate Sobolev gradient, not a target-coordinate gradient.

Quadratic lower semicontinuity on each ball passes the simultaneous bound for \(R,DP,\sqrt\varepsilon W\); monotone exhaustion then gives its global version. In particular the hard derivative energy is \(O_*(\delta)\) and the hard \(W\) energy is \(O_*(1)\). No argument has replaced the finite budget by zero. Conversely, the wording “nonzero defect” does not require the limiting energy to be strictly positive for every pair; zero is permitted. The divergent scores need no bulk \(L^2\) limit.

For local adjunction one may change variables to source coordinates with a smooth interior target cutoff. Its inverse images lie in a common source compact, so strong local convergence and smooth coefficient convergence pass the pairing. Equivalently, strong local target convergence follows by first approximating the limiting field by smooth functions and using the locally uniformly controlled diffeomorphisms and Jacobians. This pays the moving-map issue for the nonsmooth limiting field; continuity of arbitrary \(L^2\) compositions is not assumed.

### 3.3 Positive joint measures before signed multiplication

Split each even power into two one-sided powers and define the positive position/direction measure \(\Lambda_j\). Radial integration gives
\[
\Lambda_j(1)=n-\varepsilon E|x|^2,\qquad
\Lambda_j(|x|^2)=(n+2)E|x|^2-\varepsilon E|x|^4.
\]
The moment bounds give tightness. For smooth compact position tests, its marginal converges by integration by parts to \(h_C(\nu_C)\rho\,d\mathcal H^{n-1}\) on \(\partial C\). That marginal is absolutely continuous with respect to boundary area.

A compact neighborhood of a strictly slack pair has mass at most \(C N_jq_j(1-s/2)^{q_j}\to0\). Since the limiting position is already on \(\partial C\), every noncontact pair is slack: \(u\cdot x\le h_C(u)\le h_K(u)^{1-t}h_L(u)^t\). Thus joint limits are contact pairs. The normal is unique at boundary-area-almost every point, so the marginal uniquely determines the joint limit. Opposite directions are allocated to opposite one-sided powers and introduce no factor two.

Only after this positive-measure argument is it valid to multiply by the bounded continuous \(b(u)=\log(h_L/h_K)\). The signed score measures converge to \(-b(\nu_C)h_C(\nu_C)\rho\,dS\). The mean is retained, \(m_j\to m=-\ell'+O_*(\delta)\).

For the field pairing outside an interior compact \(C_s\), the global energy gives
\[
\left|\int_{C_s^c}W_j\cdot\nabla g\,d\mu_j\right|
 \le C_*\|\nabla g\|_\infty\mu_j(C_s^c)^{1/2}.
\]
First \(j\to\infty\), then \(s\downarrow0\), removes this term because the target boundary has zero volume. The dense-test error is at most \(\eta_j\|g\|_{L^2(\mu_j)}\). Hence the exact limit is
\[
\int_CW\cdot\nabla g\,d\mu
 =-\int_{\partial C}g\,b(\nu)h_C(\nu)\rho\,dS-m\int_Cg\,d\mu.
\]
A cutoff equal to one on \(C\) confirms the sign \(m=-\int_{\partial C}bh_C\rho\,dS\). The argument never inserts an arbitrary normal-dependent test into radial integration and never assumes a boundary trace of \(W_j\).

## 4. Uniform hard estimates and the explicit dimension-only exponent

### 4.1 John normalization and the mean-Hessian frame

Apply John normalization to the selected hard body, giving \(B\subset C\subset\sqrt nB\). The map and its inverse have bounds depending only on the original ball parameters. Its transformed quadratic potential \(Q\) still satisfies \(0\le Q\le1/2\) on \(C\), after the original small-deficit threshold \(\delta R^2\le1\). Thus the target density is dimensionally comparable to uniform volume. This transformation occurs after constructing the fields. It does not require proving a new soft inequality for an anisotropic regularizer.

Klartag applies because \(Q\) is convex and smooth with all derivatives bounded on the bounded target, regardless of its boundary. It gives \(\tau\le2nI\). A preliminary coercive bound follows from finitely many inner-ball slopes and their supporting planes, justifying the cutoff identity \(E_\nu z\cdot\nabla\varphi=n\). If \(g=\varphi-\varphi(0)\), symmetry of the supporting planes gives
\[
g(y)\ge g(z)+|\nabla\varphi(z)\cdot y|-z\cdot\nabla\varphi(z).
\]
Integration and the target inner-ball density give
\[
c_0|y|-n\le g(y)\le\sqrt n|y|,
\quad c_0=\frac{e^{-1/2}}{\kappa_n n^{n/2}}\int_B|x_1|dx.
\]
The normalization \(e^{\varphi(0)}=\int e^{-g}\) bounds \(\varphi(0)\) on both sides, with
\(\varphi(0)\le\log(e^nI_n(c_0))\), \(I_n(c)=n!\kappa_n/c^n\).
The equation \(\det\tau=Ze^{-\varphi+Q(\nabla\varphi)}\) now gives
\[
\tau\ge c_ne^{-\sqrt n L}I,\qquad e^{-\varphi}\ge c_ne^{-\sqrt n L}
 \quad\hbox{on }B_L.
\]
In particular on \(B_1\) it supplies exactly the author's
\[
h_* =\min\left\{1,
\frac{e^{-1/2}\kappa_n e^{-\sqrt n}}
 {e^nI_n(c_0)(2n)^{n-1}}\right\}.
\]
There is no missing determinant normalization or dependence on a soft convergence rate in this formula.

For \(A=\fint_{B_1}P\), Poincaré and the field relation give the stated core estimates. To bound \(A\) uniformly, the Hessian lower bound and evenness imply that \(\nabla\varphi(B_1)\) contains a dimensional ball: for \(|y|<h_*\), minimize \(\varphi(z)-y\cdot z\) on \(\overline B_1\); its positive outward derivative excludes a boundary minimizer. The Hessian upper bound gives a bounded change-of-variables Jacobian. Thus \(\int_{B_1}xx^Tdz\succeq c_nI\). Together with the global \(W\) energy this gives \(|A|\le C_*\).

With \(H=\fint_{B_1}\tau\), one has \(h_*I\preceq H\preceq2nI\), and averaging \(P\tau=\tau P^T\) gives \(|AH-HA^T|\le C_*\sqrt\delta\). Hence \(H^{-1/2}AH^{1/2}\) is within \(C_*\sqrt\delta\) of its symmetric part. The constant dual transformation \(x'=H^{-1/2}x\) leaves the target between
\[
r_nB\subset C'\subset R_nB,\qquad r_n=(2n)^{-1/2},\quad R_n=\sqrt{n/h_*}.
\]
These radii and this second map's condition number depend only on dimension. The transformed endpoint ball bounds can depend on the original parameters, which is allowed.

### 4.2 Checking the displayed constants against transformed cubes

The following explicit accounting verifies the author's fixed \(a_n\); it does not replace it by a newly enlarged unnamed constant. In the John frame,
\[
\mathscr D(P)\ge\lambda_{\min}(\tau)\lambda_{\max}(\tau)^{-2}|DP|^2
\]
and the density lower bound imply
\(\|DP\|_{L^2(B_T)}\le C_*e^{\sqrt nT}\sqrt\delta\).
Poincaré and comparison of the \(B_T\) average with the \(B_1\) average cost at most \(C_n(1+T)^{n/2+1}\). The formulas for \(W\) and the commutator cost only dimensional caps and these same estimates.

A cube \([-L,L]^n\) in any final orthonormal eigenbasis pulls back through the \(H\) transformation into a John-frame ball of radius at most
\[
\|H^{-1/2}\|\sqrt n L\le R_nL.
\]
The resulting exponential factor is therefore at most \(e^{\sqrt nR_nL}\), times a dimensionally controlled polynomial of degree at most \(n/2+1\). Symmetric-part replacement adds at most \(C_*L^{n/2}\sqrt\delta\). Since
\[
10(n+1)(R_n+1)>\sqrt nR_n+n/2+3\qquad(n\ge3),
\]
the original \(a_n=10(n+1)(R_n+1)\) absorbs all these factors for \(L\ge2\), with multiplicative dimensional constants. Subsequent transverse Poincaré contributes the explicit extra \(L\) already displayed in I49 (7.1). Coordinate Jacobians and powers of \(h_*^{-1}\) enter multiplicatively and depend only on \(n\). This is the required uniform estimate through transformed balls and cubes.

In the final frame, repeat the supporting-plane argument using the density on \(r_nB\). The coercivity coefficient is at least exactly
\[
c_1=\frac{e^{-1/2}}{\kappa_nR_n^n}\int_{r_nB}|x_1|dx.
\]
Thus \(\nu(B_L^c)\le C_n(1+L)^{n-1}e^{-c_1L}\). Absorbing its polynomial gives \(C_ne^{-c_1L/2}\). The square root used with global \(W\) energy costs a further factor two in the exponent; the later cap conversion costs a factor \(n\). Every required tail is bounded by \(C_*e^{-b_nL}\) for the original
\(b_n=\min\{1,c_1/(8n)\}\). No aspect ratio remains in either exponential rate.

It follows, with the author's actual constants, that
\[
\|S\tau-\tau S\|_{L^2(Q_L)}+
\|W-S\nabla\varphi\|_{L^2(Q_L)}\le C_*e^{a_nL}\sqrt\delta,
\quad
\int|W-Sx|d\mu\le C_*(e^{a_nL}\sqrt\delta+e^{-b_nL}).
\]
The latter estimate uses \(\nu(B_L^c)^{1/2}\|W\|_{L^2(\nu)}\), not a pointwise bound on \(W\) outside the core.

### 4.3 Clustering, mean, and the residual

Merge consecutive eigenvalues of \(S\) when their gap is below \(\gamma\). The cluster diameter is at most \((n-1)\gamma\), and every cross-cluster eigenvalue difference is at least \(\gamma\). Entrywise division of \([S,\tau]\) gives the mixed-Hessian estimate. No division by a within-cluster gap is made. Repeated eigenvalues and the single-cluster case are covered.

For
\[
\theta_n=\frac{b_n}{8(a_n+b_n+1)},\quad e=\delta^{\theta_n},\quad
L=\frac{\log(1/\delta)}{8(a_n+b_n+1)},\quad\gamma=e,
\]
one has
\[
e^{a_nL}\sqrt\delta\le\delta^{3/8}\le e^2,
\qquad e^{-b_nL}=e.
\]
The bounds \(a_n\ge1\), \(0<b_n\le1\) give ample margin in the second power comparison. Clustering therefore costs at most \(C_*e\) in global \(L^1\), and the mixed blocks cost at most \(C_*e\) on the cube.

For a fixed nonnegative interior test, integration by parts for \(A_\gamma x\) has coefficient
\(-\operatorname{tr}A_\gamma+(A_\gamma x)\cdot\nabla Q\).
The test has target integral bounded below, and \(\nabla Q=O_*(\delta)\) on the target. Comparing with the hard identity gives
\[
|\operatorname{tr}A_\gamma-m|\le C_*e,
\qquad |\operatorname{tr}A_\gamma+\ell'|\le C_*e.
\]
For arbitrary compact smooth position tests, subtraction then yields precisely the residual bound (5.9). Both the nonzero chord slope and the transformed Gaussian contribution have been paid. Setting \(m=0\) would invalidate the determinant step later; the original proof does not do so.

## 5. The radial BV lemma on arbitrary convex boundaries

Let \(r_1B\subset C\subset R_1B\), and retain the homogeneous gauge \(p_C\) on \(\mathbb R^n\); write \(p\) for its restriction to the sphere. As a support function of \(C^\circ\), it satisfies
\[
D_S^2p+pI\succeq0
\]
in matrix measures. The total trace is \((n-1)\int_Sp\), because the spherical Laplacian integrates to zero. Positivity bounds the total variation of that matrix measure by a dimensional multiple of its trace; subtracting \(pI\) therefore bounds \(D_S^2p\) in total variation. Also \(p\) and its first derivatives are uniformly bounded, with \(p\ge1/R_1\).

Set
\[
X(\theta)=\theta/p(\theta),\quad
G(\theta)=\nabla p_C(\theta)=p(\theta)\theta+\nabla_Sp(\theta),\quad
N(\theta)=G(\theta)/|G(\theta)|.
\]
The denominator is at least \(p\ge1/R_1\). Thus \(N\) is uniformly BV. For an explicit approximation justification, average the homogeneous support function over small rotations, retaining convexity, the positive lower bound and the Hessian-measure mass bound. The smooth approximants have gradients converging in \(L^1\); their normalized gradients have uniformly bounded variation by the ordinary chain rule. Lower semicontinuity gives the asserted bound. A Lipschitz extension of normalization away from \(|G|=0\) also gives the usual BV chain rule directly.

The radial map and its inverse are uniformly Lipschitz. Its area Jacobian is
\[
J(\theta)=p(\theta)^{-(n-1)}\sqrt{1+|\nabla_Sp(\theta)|^2/p(\theta)^2}
 =p(\theta)^{-n}|\nabla p_C(\theta)|.
\]
This is bounded above and below. In particular the formula is not \(p^{-n}|\nabla_Sp|\). The independent exact facet calculation gives \(J=27/8\) on the selected box ray and detects the latter erroneous interpretation.

If \(F(x,u)\) is bounded Lipschitz on the stated neighborhood, \(f=F(X,N)\) is bounded BV with a uniform norm. Chart convolution and a partition of unity give smooth \(f_s\) with
\[
\|f_s\|_\infty\le C,\quad\operatorname{Lip}f_s\le C/s,
\quad\|f-f_s\|_{L^1(S)}\le Cs.
\]
The last estimate is the BV translation bound; the differentiated kernel gives the second. Lipschitz composition can be justified by smooth approximation of \(F\) with the same bounds, so differentiability of \(F\) is not an extra assumption.

Use \(g_s(x)=\chi(|x|)f_s(x/|x|)\), with a compact smooth cutoff equal to one on all boundary radii and vanishing near zero. This is an admissible smooth position test with norm \(O(1/s)\). The weight need only obey \(0<c\le w\le C\):
\[
\int_{\partial C}F^2w\,dS
\le\left|\int_{\partial C}Fg_sw\,dS\right|
 +\|F\|_\infty\|wJ\|_\infty\int_S|f-f_s|
\le C(\eta/s+s).
\]
There is no differentiation or smoothing of \(w\). With \(s=\sqrt\eta\), Cauchy–Schwarz and the lower weight bound give \(\int|F|dS\le C\eta^{1/4}\). This proves the original BV lemma, including measurable bounded weights and nonsmooth contacts. Arbitrary bounded normal tests would not be justified by this argument and are not asserted.

For the actual residual \(F(x,u)=A_\gamma x\cdot u+b(u)h_C(u)\), all constants are uniform: the transformed bodies have positive support lower bounds and bounded radii, hence \(\log h_K,\log h_L\), their difference \(b\), and \(h_C\) are bounded Lipschitz on the sphere. The matrix norm is bounded. Thus \(F\) is uniformly Lipschitz jointly in \(x,u\), even when the normal map jumps. The Gaussian boundary weight has uniform positive bounds. I49 (6.2) follows.

The supplementary direct proof of surface-area continuity also passes. For homogeneous convex gauges \(p,q\) close by \(O(\zeta)\), integration by parts with an annular cutoff bounds
\[
\int\chi|\nabla p-\nabla q|^2
\le\|p-q\|_\infty\left[\int\chi\,d(\Delta p+\Delta q)
 +\int|\nabla\chi|\,|\nabla p-\nabla q|\right]\le C\zeta.
\]
The Laplacian measures have uniformly bounded mass and the gradients are bounded. Mollification justifies the identity for Lipschitz convex gauges. Homogeneity transfers it to the sphere. The formulas for \(N,J\), on their bounded range with positive denominators, are Lipschitz in \(p,\nabla p_C\). Their \(L^1\) differences are therefore \(O(\sqrt\zeta)\), giving the claimed bounded-Lipschitz surface-area estimate. This agrees with the actual Hug–Schneider interface and does not imply total-variation convergence.

## 6. One compatible product body, not separately fitted slices

In the orthogonal eigenblock coordinates, define \(F_i\) by averaging \(\Pi_i\nabla\varphi\) over the entire complementary cube. It is the gradient of the averaged convex function in its own variables. The Hessian cap bounds its Lipschitz constant dimensionally. Changing all transverse signs, together with global evenness of \(\varphi\), proves \(F_i(-z_i)=-F_i(z_i)\); separate reflection symmetry of \(\varphi\) is unnecessary.

Transverse Poincaré followed by Fubini gives
\[
\|\nabla\varphi-F\|_{L^2(Q_L)}
 \le C_nL\left(\sum_{i\ne j}\|\Pi_i\tau\Pi_j\|_{L^2(Q_L)}^2\right)^{1/2}
 \le C_*Le.
\]
All norms integrate over the full cube, so there is no restriction of an \(L^2\) Hessian to a line or a lower-dimensional slice. The vector field \(F\) is dimensionally Lipschitz, as is \(\nabla\varphi\).

For a maximum error \(s\), an intersected ball of radius proportional to \(s\) carries error at least \(s/2\). Its volume is at least a dimensional multiple of \(s^n\), including corners of the cube; the fields are uniformly bounded, so the radius can be taken within the cube scale. Hence
\[
\|\nabla\varphi-F\|_\infty\le C_*(Le)^{2/(n+2)}
 \le C_*e^{1/(n+2)}.
\]
The last weakening uses the elementary logarithm-versus-power bound \(L\le C_ne^{-1/2}\), where \(e\) is the error parameter, not Euler's number.

The full cube is a Cartesian product, so its \(F\)-image is precisely the product of the individual images. Taking products of finite convex-combination coefficients proves
\(\operatorname{conv}(\prod X_i)=\prod\operatorname{conv}(X_i)\).
Uniformly close images have uniformly close closed convex hulls by their support functions. Thus the single body
\[
D=\sum_i\operatorname{conv}\overline{F_i([-L,L]^{\dim E_i})}
\]
is close to \(C^{\rm core}=\operatorname{conv}\overline{\nabla\varphi(Q_L)}\). Each factor is symmetric. For one block the transverse average is the identity and the construction remains valid.

Because the moment map is a diffeomorphism and its target density is bounded below,
\[
|C\setminus C^{\rm core}|\le C_n\mu(C\setminus\nabla\varphi(Q_L))
 =C_n\nu(Q_L^c).
\]
The core contains a dimensional inner ball from the gradient image of a fixed source ball. A support excess \(s\) of \(C\) over the core creates a cone cap of volume at least \(c_ns^n\): join an exposed point of \(C\) to a perpendicular inner disk, and integrate sections above the core's supporting plane. The dimensional tail bound therefore gives \(d_H(C,C^{\rm core})\le C_ne^{-b_nL}\). Combining estimates proves the author's weaker convenient bound
\[
d_H(C,D)\le C_*e^{1/(2(n+2))}=\zeta.
\]
For a sufficiently small deficit, this implies a fixed inner ball in \(D\), and hence a positive relative inner ball in every factor. The body is full dimensional and all factor dimensions are legitimate.

Up to boundary-area zero, exactly one factor is on its boundary at a product boundary point. Boundary products with two boundary factors have dimension at most \(n-2\), also for one-dimensional factors. Thus \(S_D\) is supported on the union \(U\) of the block spheres. The function \(u\mapsto\operatorname{dist}(u,U)\) is uniformly bounded and 1-Lipschitz regardless of the number or dimensions of the blocks. Surface-area continuity gives
\[
\int\operatorname{dist}(u,U)dS_C(u)\le C_*\sqrt\zeta.
\]
No mass is asserted to lie on an exact block for \(C\), and no minimal facet mass enters.

## 7. Both original endpoints, volume slope, and FMP

At a regular boundary point of the full Wulff body, at least one constraint is active; otherwise compactness of the sphere gives a uniform positive slack. Every active direction is its unique normal. Therefore
\[
h_C(u)=h_K(u)^{1-t}h_L(u)^t
\]
holds \(S_C\)-almost everywhere. It is not needed for inactive directions.

Choose a nearest block sphere measurably, say the \(i\)-th. If \(d=\operatorname{dist}(u,U)\), the sum of other projection lengths is at most \(C_nd\). For any corresponding boundary position \(x\),
\[
|(A_\gamma x)\cdot u-a_ih_C(u)|\le C_*d.
\]
The residual estimate and the support lower bound then control the integrated \(|b+a_i|\) by \(C_*(e^{1/4}+\sqrt\zeta)\). This is a pushforward of a boundary-position inequality; multiple points on one facet cause no ambiguity.

Construct exactly the author's pair
\[
K^\sharp=e^{tA_\gamma}D,\qquad L^\sharp=e^{-(1-t)A_\gamma}D.
\]
The product support formula, bounded eigenvalues, and \(d_H(C,D)\le\zeta\) imply
\[
|h_{K^\sharp}(u)-e^{ta_i}h_C(u)|\le C_*(d+\zeta),
\]
with the corresponding formula for \(L^\sharp\). Contact expresses the original endpoint supports as \(h_Ce^{-tb}\), \(h_Ce^{(1-t)b}\). Exponentials are Lipschitz on the uniform bounded slope interval. Thus
\[
\int|h_K-h_{K^\sharp}|dS_C+
\int|h_L-h_{L^\sharp}|dS_C
 \le C_*e^{1/(4(n+2))}=\omega.
\]

Each absolute support difference is itself uniformly bounded Lipschitz. These are the functions transferred from \(S_C\) to \(S_D\), at cost \(O_*(\sqrt\zeta)\). The discontinuous nearest-block index is not transferred. For a positive block map \(T\) of multipliers \(s_i\), the cofactor formula on the product normal support gives
\[
dS_{TD}(u)=\det(T)s_i^{-1}dS_D(u),\qquad u\in E_i\cap S^{n-1}.
\]
The normal direction stays unchanged there, and the coefficients are bounded above and below. This proves the mixed-volume estimate with the correct orientation
\[
|V_1(K^\sharp,K)-|K^\sharp||+
|V_1(L^\sharp,L)-|L^\sharp||\le C_*\omega,
\quad V_1(A,B)=\frac1n\int h_BdS_A.
\]
It would be invalid to swap its arguments in dimension at least three. The original does not swap them.

The logarithmic volumes require an independent input. The inner ball and Hausdorff bound give \(\log|D|=\log|C|+O_*(\zeta)\). Also
\(\log|C|=\ell(t)+O_*(\delta)\) and \(\operatorname{tr}A_\gamma=-\ell'+O_*(e)\). Consequently
\[
\log|K^\sharp|=\log|D|+t\operatorname{tr}A_\gamma
 =\log|K|+O_*(\zeta+e+\delta),
\]
\[
\log|L^\sharp|=\log|D|-(1-t)\operatorname{tr}A_\gamma
 =\log|L|+O_*(\zeta+e+\delta).
\]
Thus both comparison volumes, not just their product, are controlled. This explicitly verifies the nonzero-mean/determinant signs.

To audit (8.8), let \(A,B\) be symmetric bodies between fixed positive balls and suppose
\(|V_1(A,B)-|A||+||B|-|A||\le s\). In FMP set the finite-perimeter set to \(A\) and the Wulff shape to \(B\). Its perimeter is \(P_B(A)=nV_1(A,B)\), and its nonnegative normalized deficit is
\[
\frac{V_1(A,B)}{|B|^{1/n}|A|^{(n-1)/n}}-1=O(s).
\]
Interior sets may be used in that theorem; convex boundaries have zero volume and their reduced boundaries agree with the boundary-area integration here. FMP gives a translate of \(aB\), \(a^n|B|=|A|\), with symmetric difference \(O(\sqrt s)\). The volume bound gives \(a=1+O(s)\).

Translation removal is valid for these symmetric convex bodies. Let \(f(x)=|A\cap(x+aB)|\). Reflection makes \(f\) even. Convexity gives the inclusion between Minkowski interpolations of two intersections and the intersection at the interpolated translation, so ordinary Brunn–Minkowski makes \(f^{1/n}\) concave on its support. Hence \(f(0)\ge f(x)\). The centered symmetric difference is no larger than that of any translate, including a minimizing sequence. Replacing \(aB\) by \(B\) costs \(||A|-|B||=O(s)\).

Finally, if \(h_A(u)-h_B(u)=\eta>0\), join an exposed point of \(A\), of height \(H\le R_1\), to its inner radius-\(r_1\) disk in \(u^\perp\). The cone lies in \(A\). At depth \(z\) below the tip its section has volume \(\kappa_{n-1}(r_1z/H)^{n-1}\). Its part above \(B\)'s support plane has volume
\[
\frac{\kappa_{n-1}r_1^{n-1}}{nH^{n-1}}\eta^n
 \ge\frac{\kappa_{n-1}r_1^{n-1}}{nR_1^{n-1}}\eta^n.
\]
Interchange the bodies for the other sign. Thus \(d_H(A,B)\le Cs^{1/(2n)}\), exactly as used.

Applying this twice gives
\[
d_{\mathcal E}(K,L)\le C_*\omega^{1/(2n)}
 \le C_*\delta^{\theta_n/(8n(n+2))}
 =C_*\delta^{1/\alpha_n}.
\]
The two block dilations have positive ratios \(e^{-a_i}\) and form one compatible pair. Undoing the bounded constant maps preserves complementary subspaces, allowing oblique ones, and only changes the prefactor in Hausdorff distance.

## 8. Degenerate budgets and Construction B

For zero deficit, replace it by any positive upper budget \(d\), take \(\varepsilon=d\), and run the construction with \(\delta\le d\). Every approximation, time selection and later estimate uses an upper bound, so \(d_{\mathcal E}\le C_*d^{1/\alpha_n}\) for all sufficiently small \(d\). Letting \(d\downarrow0\) suffices; closedness or the equality classification is unnecessary. For deficits above the parameter-dependent threshold, comparison with \((rB,rB)\in\mathcal E\) bounds the distance uniformly, and the theorem constant can be decreased. Arbitrary bodies were already used in the exhaustion and hard moment construction, so no unbounded-facet approximation exponent remains.

The direct Euclidean Neumann construction is separately valid. Weighted divergence supplies the trace estimate in I49 §4. The required Poincaré constant can be obtained without boundary smoothness: average \(|g(x)-g(y)|^2\) over \(x\in C,y\in rB\), integrate \(\nabla g\) along segments, and split the segment parameter at \(1/2\). On the first half change variables in \(x\), and on the second in \(y\); the inverse Jacobians are at most \(2^n\). This bounds the variance by a constant depending only on \(n,r,R\) times the gradient energy. Gaussian-weight comparability transfers it to \(\mu\). Convex-domain smooth density and the divergence formula extend the trace estimate to \(H^1\). The boundary area is bounded, so the stated load is a bounded functional annihilating constants. Riesz representation gives the mean-zero solution and its uniform gradient bound.

For the unregularized unit ball, the field from
\(u=-\kappa x_1x_2/2\) is divergence free and has normal component \(-\kappa\nu_1\nu_2\), exactly the required load. The moment potential is radial by rotational uniqueness. If its Hessian \(a(z)I+d(z)zz^T\) had \(d\equiv0\), it would be constant, contradicting the bounded full gradient image. At a radius with \(d\ne0\), choose \(z\) along the first coordinate. The off-diagonal constant matrix \(D_xW_N\) does not commute with this Hessian, so \(D_zW_N=(D_xW_N)\tau\) is nonsymmetric. This is an actual failure of the source-gradient compatibility condition.

The endpoint geometry is admissible. For \(q_0(u)=u_1u_2\), \(\|D_S^2q_0\|\le2\). For \(|c|\le1\),
\[
D_S^2(e^{c\kappa q_0})+e^{c\kappa q_0}I
 =e^{c\kappa q_0}[I+c\kappa D_S^2q_0+c^2\kappa^2dq_0\otimes dq_0]
 \succeq e^{c\kappa q_0}(1-2|\kappa|)I.
\]
Thus \(|\kappa|<1/4\) makes \(e^{-t\kappa q_0}\) and \(e^{(1-t)\kappa q_0}\) positive smooth strictly convex support functions. They are even, their logarithmic interpolation at the specified interior time is exactly one, and their ratio has logarithm \(\kappa q_0\). They are uniformly ball bounded. This proves the diagnostic is realizable by actual endpoint bodies. Its scope is the unregularized direct inverse; it is not a claim about failure of the regularized Construction A.

For the uniform interval, differentiation verifies \(x=\tanh(z/2)\), \(\tau=(1-x^2)/2\), and the normalized pushforward density \(dx/2\). The load of \(W=-bx\) is
\[
\int Wg'\,d\mu=b\int g\,d\mu-\tfrac b2[g(1)+g(-1)].
\]
The equation \(W=\tau f'\) gives \(f=b\log(1-x^2)+\mathrm{constant}\). The actual energy density is \(b^2x^2/(1-x^2)\,dx\), and hence
\[
\int_{-a}^a\tau(f')^2d\mu
 =b^2\left[\log\frac{1+a}{1-a}-2a\right].
\]
For the logarithmic boundary cutoffs, writing \(H=\log(a_0/\eta)\), the energy is \(O(H^{-1})\), while their \(L^2\) norm tends to zero and the endpoint load tends to \(-b\). Constant endpoint plateaus and interior smoothing make admissible smooth approximants with the same estimates. The load is therefore not continuous in the ordinary moment-form norm; tensoring gives the same obstruction in higher dimensions. The ordinary Neumann inverse and the moment-form inverse are different constructions. Neither diagnostic disproves the stability theorem or rules out tensor-compatible fields.

## 9. Evidence, failures, and final disposition

The independent exact checker passes **310 assertions**. It starts from an actual non-diagonal three-dimensional Gaussian soft target and a mixed quartic test, derives the fields by both row adjunctions, and evaluates Gaussian moments recursively. It verifies the entire signed completion with nonzero mean \(4/3\), curvature defect \(169/36\), retained \(R\) energy \(3659/378\), derivative energy \(3659/756\), and tensor remainder \(3659/189\). It separately checks all-index covariance under a nonorthogonal rational map, tensor symmetrization, a true facet radial Jacobian, full-cube transverse averaging, block surface scaling, nonsymmetric mixed-volume orientation, the Neumann compatibility failure, interval factors and exponent/determinant signs. The Gaussian polynomial fixtures have justified Gaussian-decay cutoff limits; they are diagnostics, not substituted admissible compact tests in the theorem.

These finite identities do not prove Rellich compactness, the BV chain rule, density of smooth tests, or the all-body quantifiers. Sections 2–8 give those analytic checks. Likewise hashes establish source identity rather than proof correctness.

The frozen parent record is preserved accurately: its **initial unmodified I49 verifier failed** at the order-sensitive raw `rg` stdout comparison. It subsequently obtained a successful unmodified retry and a successful explicitly order-normalized in-memory replay. My replay replaces exactly that one raw comparison with sorted line comparison, preserving duplicate lines, in memory only. It is recorded as **order-normalized replay**, not a vanilla PASS. The author's source hash and seal are unchanged. The replay verifies its 163 artifacts, 35 frozen inputs, 23 primary responses, 17 PDF text extractions, 49 read records, 506 exact assertions, 12 pinned files, all 9,340 corpus files, and six prior seals covering 2,253 artifact checks. The four live shared ledgers have drifted since I49's freeze; the replay reports that drift separately and does not refresh their frozen copies.

This review retains 13 successful fresh primary/raw responses, including nine PDFs, with exact bytes and reproducible text extraction. Version records and read passages are bound to them. No failed current HTTP response was discarded; this retrieval batch had none. The evidence also preserves the local preparation failures: an initial inspection omitted the project working directory, and the first independent checker had an unmatched parenthesis before execution. The frozen initial checker also contains a factor-two error in a not-yet-executed interval fixture, corrected to the directly derived energy density above. These are disclosed fixture/command corrections, not changes to the author proof or to a failed mathematical claim.

Run from the project root:

```sh
python frontier/experiments/i50_hard_moment_quantitative_stability_r2/check.py
python frontier/experiments/i50_hard_moment_quantitative_stability_r2/verify.py
```

The verifier is read-only and disables bytecode. It binds the exact I50 artifact set, frozen immutable inputs, mutable observations, source versions/passages, complete corpus, selected pinned blobs, prior seals and deterministic diagnostics. Corpus search replays compare line multisets, never unordered raw stdout. The author replay's normalization is disclosed and applied only in memory.

**Final original-proof verdict: PASS ORIGINAL WITHOUT REPAIRS for H49 with all stated quantifiers and the original displayed exponent.** The two direct-hard diagnostics pass only their stated method scopes. No significance, priority, count, integration, or publication decision is made. Only the three assigned I50 paths were written; no other agent, staging, commit, shared/prior edit, or publication was used.
