# I49 — finite-defect hard moment fields and a candidate higher-dimensional power theorem

**Disposition: complete author-level candidate proof of the unrestricted finite-power estimate in each fixed dimension \(n\ge3\), under the accepted pinned OpenAI operations. Independent proof review and a separate operation-level significance review are required. No acceptance, finding-count change, sharp exponent, or priority is asserted.**

The main construction takes the hard limit at **fixed positive regularizer and fixed nonzero deficit**. It produces weak Sobolev moment fields with the signed boundary identity and the retained derivative energy. The soft Hessian cap is not passed off as a radius-only estimate. After taking the limit, Klartag's hard-target cap supplies quantitative core estimates. A radial BV argument converts position-test errors to a normal-flux residual. Averaging the moment gradient across complementary coordinates constructs one product body. Its two block dilations are compared with the original endpoints by surface-area continuity and quantitative Minkowski stability. The exponent is finite and depends only on dimension; an affine normalization is essential to that last assertion.

A second, genuinely different construction directly solves the hard Euclidean Neumann problem with a uniform inverse bound. It pays the flux equation but does not supply the tensor-compatible fields. An explicit interval calculation shows why the ordinary hard moment spectral form has an unbounded boundary load. This is a method diagnostic, not a counterexample to the target. The successful route uses the first construction.

Only the three authorized I49 paths were written. Prior reports, seals, shared ledgers and corpus files were not edited; no agents, staging, commits or publication were used.

## 1. Statement and dependence convention

For fixed \(n\ge3,\ 0<r<R,\ 0<\tau_0<1/2\), let \(K,L\) be arbitrary full-dimensional origin-symmetric convex bodies with
\[
rB\subset K,L\subset RB,\qquad \lambda\in[\tau_0,1-\tau_0].
\]
Set
\[
C_t=\mathcal W[h_K^{1-t}h_L^t],\quad
\ell(t)=(1-t)\log|K|+t\log|L|,\quad
\delta=\log|C_\lambda|-\ell(\lambda).
\]
Let \(\mathcal E\) be the entire class
\[
\left(\sum_{i=1}^m K_i,\ \sum_{i=1}^m c_iK_i\right),\qquad
\mathbb R^n=E_1\oplus\cdots\oplus E_m,\quad c_i>0,
\]
where the \(E_i\) are nonzero complementary linear spaces and the \(K_i\subset E_i\) are origin-symmetric relative bodies. One block and oblique spaces are allowed. Comparison bodies have no original-ball constraint. The pair distance is the maximum of the two Hausdorff distances, minimized over \(\mathcal E\).

**Candidate theorem H49.** There is a finite \(\alpha_n\), depending only on \(n\), such that
\[
\delta\ge c(n,r,R,\tau_0)\,d_{\mathcal E}(K,L)^{\alpha_n}.                 \tag{1.1}
\]
No smoothness, facet, facet-mass, reflection, or angle hypothesis is imposed.

Throughout, \(C_*\) denotes a finite constant depending only on \(n,r,R,\tau_0\); it may change. Constants with subscript \(n\) depend only on dimension. Section 5 constructs \(a_n\ge1,\ 0<b_n\le1\) for the core and tail estimates. One permissible, deliberately weak exponent is
\[
\theta_n=\frac{b_n}{8(a_n+b_n+1)},\qquad
\alpha_n=\frac{8n(n+2)}{\theta_n}
         =\frac{64n(n+2)(a_n+b_n+1)}{b_n}.                              \tag{1.2}
\]
The constants \(a_n,b_n\) are specified by explicit uniform estimates below, not by an unspecified compactness modulus. No claim of usefulness of this numerical exponent is intended.

The complete I46 report, I47 proof review and I48 contribution review were read. I47's original P10 approval is preserved. I48's separate classical planar reduction and its statement that it did not read I47 are preserved. Neither planar route is reproved or sharpened here. I45's E,C,B,Q approval is used only as background and as a checked account of the limiting machinery; the new finite-defect interfaces are proved below. The external centered nonsymmetric theorem is not assumed.

## 2. Sources, antecedents and what is new to this proof

The accepted pin is openai/math at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. The actual logarithmic manuscript's introduction, reduction, moment, identities, density, tensor and variance proofs were read. Its finite-slab concavity, compact adjunctions, dense even range and tensor squares are premises. Its measure and \(L_p\) consequences do not state H49. The complete 13,223-entry tree and 9,340-file ignored corpus are bound by the verifier; the historical 719-manuscript catalogue count is not used.

Fresh primary PDFs were downloaded before the geometric construction was completed. The following distinctions govern the proof.

* **Liu–Sun–Xiong, [2610.10152v2](https://arxiv.org/abs/2610.10152v2), (3.10)–(3.16), Lemma 3.4 and §3.3:** full credit for the unnormalized completion, retained regularizer, moment compactness and contact-pair boundary mechanism. Their proof treats exact equality through vanishing derivative energy. Here the fixed-defect limit retains nonzero energy and weak derivatives. Their Lemma 3.4 is stated for a linear target tilt; §3.2 below explicitly checks the same argument for the fixed quadratic tilt used here. The authors' proposed-proof note is retained; their nonsymmetric theorem is not imported.
* **Berman–Berndtsson, [Theorem 1.1](https://afst.centre-mersenne.org/item/10.5802/afst.1386.pdf):** an arbitrary compact convex target, positive smooth target density, barycenter zero, entire smooth moment potential and full gradient image. No smooth target boundary is required.
* **Bonnet–Rubinstein, [2604.09914v1, Theorem 1.3](https://arxiv.org/abs/2604.09914v1):** \(W_1\) convergence gives \(L^1\) convergence of normalized source densities after translations, with a square-root/log bound under directional first-moment nondegeneracy. Cule–Samworth's [Proposition 2](https://arxiv.org/abs/0908.4400) and Figalli–Jhaveri–Mooney's [Theorem 1.1 and §2](https://people.math.ethz.ch/~afigalli/papers-pdf/Nonlinear-Bounds-in-Holder-Spaces-for-the-Monge-Ampere-Equation.pdf) supply local convergence and interior regularity. These results are used for existence of the limiting fields, with no rate in the soft index entering (1.1).
* **Klartag, [Logarithmically-concave moment measures I, Theorem 1 and pp. 24–25](https://www.math.tau.ac.il/~klartagb/papers/lc_moment.pdf):** \(\operatorname{tr}D^2\varphi\le2R(C)^2\) for the bounded log-concave target. The proof removes target-boundary smoothness. This is used only after the hard limit.
* **Hug–Schneider, [Theorem 1.1, (1.2), and its parallel-volume proof](https://home.mathematik.uni-freiburg.de/rschnei/ArchivHugSchneider.pdf):** surface-area and joint support measures are \(1/2\)-Hölder in bounded-Lipschitz distance under Hausdorff perturbations. We use precisely the surface-area specialization, with uniformly bounded bodies. A direct radial derivation is also given in §6.
* **Figalli–Maggi–Pratelli, [Theorem 1.1](https://people.math.ethz.ch/~afigalli/papers-pdf/A-mass-transportation-approach-to-quantitative-isoperimetric-inequalities.pdf):** anisotropic perimeter deficit controls squared Fraenkel asymmetry, with dimensional constant independent of the Wulff shape. Section 8 verifies every mixed-volume, centering and Hausdorff interface; this theorem is not itself logBM stability.
* **Kolesnikov–Livshyts–Rotem, [2507.12099v3, Theorem 1.4 and §4.3](https://arxiv.org/abs/2507.12099v3):** the actual proof of Proposition 4.8 supplies the transport-Hessian Bochner antecedent cited by the pin. Their homogeneous-density variance equivalence and local results are credited, not counted as a new consequence here. **Wang [2510.19061v2, Theorem 1.3 and its segment-variation proof](https://arxiv.org/abs/2510.19061v2)** gives smooth conditional rigidity; **He–Liu [2510.21530v1, Theorems 3–5 and §3](https://arxiv.org/abs/2510.21530v1)** gives smooth positive-density uniqueness and strict spectral information. The actual proofs use smooth variations or positive smooth densities. No uniform nonsmooth finite-deficit field or boundary rate is imported from them.
* **Böröczky–De, [2101.02549v6, Theorems 1.4–1.5 and Proposition 4.1](https://arxiv.org/abs/2101.02549v6):** existing power stability under \(n\) common linear reflections, with spectral grouping and cap reconstruction. Their coordinate-product inclusion depends on those reflections. **Böröczky–Henk**, [Theorems 1.1–1.3](https://users.renyi.hu/~carlos/cone-volume-stability.pdf), starts from almost saturated cone mass on an exact subspace. H49 does not assume that condition.
* **Lu [v3](https://arxiv.org/abs/2608.20730v3), Xi [v4, Theorem 4.4](https://arxiv.org/abs/2307.04266v4), and [van Handel §4](https://web.math.princeton.edu/~rvan/logzon221121.pdf):** respectively the reflection/fiber equality theorem, global zonoid equality against arbitrary symmetric comparisons, and nonsmooth local zonoid equality. No generating measure or extra reflection is available for the present general bodies.
* **Böröczky–Machado–Ramos, [2603.17726v3](https://arxiv.org/abs/2603.17726v3), verified against the current response:** quantitative classical and \(p>1\) Minkowski-problem stability. The actual current Theorem 1.1 has a Hausdorff exponent \(1/(n-1)\), differing from the search abstract's older description. Its \(L_p\) statement excludes the logarithmic endpoint. We do not use it as a \(p=0\) theorem.

The proposed advance is the combined finite-defect hard-field, normal-flux, product-image and two-endpoint argument. Each of its individual classical operations is credited. A separate review must decide whether the combination meets the project's substantiality gate; absence of an identical printed exponent is not a significance argument.

## 3. Construction A: actual finite-defect hard fields

### 3.1 Parameters, dense completions and time selection

Initially use the original Euclidean coordinates. It suffices to treat \(0<\delta<\delta_*\), where the threshold depends only on the fixed parameters. Put \(\varepsilon=\delta\), further restricting \(\delta_*R^2\le1\).

Take nested symmetric direction nets with mesh \(a_j\downarrow0\), containing a fixed spanning net, and \(N_j\le C_na_j^{-(n-1)}\). For representative directions put
\[
h_i(t)=h_K(p_i)^{1-t}h_L(p_i)^t,\quad
b_i=\log(h_L(p_i)/h_K(p_i)),\quad
U_j(x,t)=\sum_i|p_i\cdot x/h_i(t)|^{q_j}.
\]
Choose even \(q_j\to\infty\) with
\[
a_j\le\delta/j,\qquad
(1+\log N_j)/q_j\le\delta/j,\qquad
q_j\ge j(1+\log N_j).
                                                                    \tag{3.1}
\]
These requirements are compatible. For example \(a_j=c_*\delta/(j+1)\) and an even \(q_j\ge C_*(j+1)^2(1+\log N_j)/\delta\) suffice. Thus the prescribed elementary soft parameters are polynomial in \(j,\delta^{-1}\), up to logarithms.

Let \(G_j(t)=\log\int e^{-U_j-\varepsilon|x|^2/2}dx\). I46/I47's homogeneity calculation gives
\[
|\log Z_{q,\varepsilon}(t)-\log|P_j(t)||\le
C_*\varepsilon+C_n(1+\log N_j)/q.
\]
For clarity, its inputs are \(N^{-1/q}P_j\subset\{U_j\le1\}\subset P_j\),
\(\int e^{-U_j}=\Gamma(1+n/q)|\{U_j\le1\}|\), and a uniform second moment. The direction-net Wulff error is \(C_*a_j\). Concavity of the accepted full Wulff functional gives \(0\le\log|C_t|-\ell(t)\le\delta/\tau_0\). Hence
\[
|G_j(t)-\ell(t)|\le C_*\delta
\]
uniformly. Concavity and interior secants select \(t_j\in[1/3,2/3]\) with
\[
D_j=-G_j''(t_j)\le C_*\delta,\qquad
|G_j'(t_j)-\ell'|\le C_*\delta.                       \tag{3.2}
\]
No regularity or chamber selection for the hard path is needed.

At this time take
\[
F_j=-q_j\sum_i b_i\psi_{i,j},\quad m_j=E_{\mu_j}F_j=-G_j'(t_j),
\quad U_j^{\rm score}=F_j-m_j.
\]
Parity removes the linear projection, not \(m_j\). Choose an even compact test \(v_j\) from the accepted dense range so that
\(\|u_j-U_j^{\rm score}\|_{L^2(\mu_j)}\le\eta_j\), with \(\eta_j\downarrow0\) and \(\eta_j^2\le\delta/j\).
There is no bound on the norm of \(v_j\), and none is required.

Write \(x_j=\nabla\varphi_j,\ \tau_j=D^2\varphi_j,\ M_j=\tau_j^{-1}\), and
\[
P_j=\tau_jD_x^2v_j,\quad B_j=P_j\tau_j,\quad
W_j=P_jx_j-\operatorname{div}_zP_j,\quad
R_j=D_zW_j-P_j\tau_j.
\]
The accepted tensor identity and the LSX-attributed completion give
\[
\int\left(\|M_j^{1/2}R_jM_j^{1/2}\|_{\rm HS}^2+
\tfrac12\mathscr D_j(P_j)\right)d\nu_j
+\varepsilon\int|W_j|^2d\nu_j
\le D_j+\eta_j^2\le C_*\delta.                       \tag{3.3}
\]
Here
\[
\mathscr D(P)=M_{ab}\tau_{kr}M_{\ell s}
(\partial_\ell P_{ak})(\partial_sP_{br}).
\]
Both \(P_j\tau_j\) and \(D_zW_j\) are symmetric. This retains the \(R_j\) square as well as the derivative term. In particular \(\int|W_j|^2d\nu_j\le C_*\).

### 3.2 Fixed-\(\varepsilon\) moment convergence, with domains specified

Pass to \(t_j\to t\in[1/3,2/3]\), and write \(C=C_t\). The limiting target is
\[
d\mu(x)=\rho(x)dx=Z^{-1}1_C(x)e^{-\varepsilon|x|^2/2}dx.                \tag{3.4}
\]
On every compact subset of \(\operatorname{int}C\), the slab ratios are at most some \(\zeta<1\). Every fixed derivative of the soft part is bounded by \(C_kN_jq_j^k\zeta^{q_j-k}\to0\). Outside \(C\), a fixed direction from the dense union eventually gives a strict violated constraint. The fixed spanning net supplies a common integrable superlinear tail bound, including every fixed polynomial weight. Thus the target densities converge in weighted \(L^1\), in \(W_1\), and in every fixed polynomial moment; \(Z_j\to Z\).

Berman–Berndtsson applies to \(C\) and its positive globally smooth Gaussian density. It gives a probability-normalized smooth strictly convex \(\varphi\) on all \(\mathbb R_z^n\), with gradient diffeomorphism onto \(\operatorname{int}C\). Choose the unique minimum at zero; symmetry and uniqueness make \(\varphi\) even.

Here is the compactness interface for the quadratic tilt, rather than an assertion that LSX's linear-tilt lemma literally has this hypothesis. Bonnet–Rubinstein applies because the probabilities are centered, their first moments are bounded, and the limiting directional first moments are bounded below by the density on \(rB\). After translations it gives \(L^1\) source convergence. Cule–Samworth gives local uniform density convergence, and convex difference quotients give local \(C^1\) convergence of potentials. The translations can be replaced by minimum-at-zero normalization: for the translated potentials, uniform convergence to a strictly convex potential on a ball places their minimizers inside that ball (use a positive tangent-plane gap on its boundary), and their minimizers tend to the unique limiting minimizer. Recentering therefore preserves the convergence.

On a fixed source ball, its limiting gradient image is compactly inside \(C\); the nearby images stay in a common target compact. The equations
\[
\det D^2\varphi_j=Z_j\exp[-\varphi_j+V_j(\nabla\varphi_j)]
\]
give positive two-sided determinant bounds there. The strict convex limit supplies nested compact sections and a common separation modulus at each positive scale:
\[
\varphi_j(w)-\varphi_j(z)-\nabla\varphi_j(z)\cdot(w-z)
\ge \tfrac m2|w-z|^2-2e_j|w-z|,\qquad e_j\to0.
\]
The interior section estimates used in I45 give \(C^{1,\beta}\); composition in the equation gives a Hölder right side; Figalli–Jhaveri–Mooney gives \(C^{2,\beta}\). The determinant lower bound then gives local ellipticity, and differentiation plus Schauder estimates gives every fixed higher order. All derivatives of \(V_j\) on those target compacts converge to those of the fixed quadratic tilt, so the same bootstrap applies. Consequently
\[
\varphi_j\longrightarrow\varphi\quad\hbox{in every fixed }C^k_{\rm loc}(\mathbb R^n).
                                                                    \tag{3.5}
\]
The inverse maps converge on compact subsets of \(\operatorname{int}C\).

Constants in this existence argument can depend on the fixed \(\delta,C,\varepsilon\) and core. They do not enter the final rate: after passage, all estimates used for the rate are rederived from the hard cap and ball bounds. No rate of (3.5), and no finite-\(q\) radius-only cap, is asserted.

### 3.3 Weak Sobolev compactness at nonzero defect

On every source ball the convergent coefficients and density are uniformly elliptic and positive. Equation (3.3) bounds \(D_zP_j\) in local \(L^2\). To bound its constant part, set \(A_j=\fint_{B_1}P_j\). Poincaré and the formula for \(W_j\) imply
\[
\|W_j-A_jx_j\|_{L^2(B_1)}
\le C\|D_zP_j\|_{L^2(B_1)}.
\]
The matrix \(\int_{B_1}x_jx_j^Tdz\) tends to a positive definite matrix, because \(\nabla\varphi(B_1)\) is open. The \(L^2\) bound on \(W_j\) therefore bounds \(A_j\). Comparing averages on larger balls bounds \(P_j\) in \(H^1_{\rm loc}\).

The retained \(R_j\) square now bounds \(D_zW_j=R_j+P_j\tau_j\) locally in \(L^2\). Diagonal Rellich compactness gives fields
\[
P,W\in H^1_{\rm loc}(\mathbb R^n_z),\qquad
P_j,W_j\to P,W\ \hbox{strongly in }L^2_{\rm loc},
\]
with weak convergence of their first derivatives. These are fields on the whole source space. In target coordinates \(W(x)=W((\nabla\varphi)^{-1}x)\) is defined on \(\operatorname{int}C\). Smooth coefficient convergence gives, distributionally,
\[
W=P\nabla\varphi-\operatorname{div}_zP,\quad
P\tau=\tau P^T,\quad D_zW=(D_zW)^T,\quad R=D_zW-P\tau.                 \tag{3.6}
\]
They inherit even \(P\) and odd \(W\). In particular \(W\) is a local Sobolev gradient in source coordinates. The argument does not identify it with a gradient in target coordinates.

For every fixed ball, quadratic lower semicontinuity with locally uniformly converging coefficients passes (3.3). Exhaustion by increasing balls yields
\[
\int\left(\|M^{1/2}RM^{1/2}\|_{\rm HS}^2+
\tfrac12\mathscr D(P)\right)d\nu\le C_*\delta,\qquad
\int|W|^2d\nu\le C_*.                                                \tag{3.7}
\]
The same reasoning retains any other nonnegative bulk completion term that has a defined hard coefficient. No convergence of the divergent scores in bulk \(L^2\) is claimed.

This proves the existence that was conditional in I46/I47. Density completion precedes each limit, with error tending to zero; time selection precedes subselection; weighted lower semicontinuity follows coefficient convergence on each fixed core. None of these operations requires a bounded inverse for the dense range.

### 3.4 The signed hard boundary identity

Split each even power into its two signed one-sided powers solely for measure bookkeeping, and put
\[
\Lambda_j(dx,du)=\sum_iq_j\psi_{i,j}(x)\mu_j(dx)\delta_{p_{i,j}}(du).
\]
Radial integration gives
\[
\Lambda_j(1)=n-\varepsilon E_{\mu_j}|x|^2,\qquad
\Lambda_j(|x|^2)=(n+2)E_{\mu_j}|x|^2-\varepsilon E_{\mu_j}|x|^4.
\]
Hence the positive measures are tight. For smooth compact \(g(x)\),
\[
\int g\,d\Lambda_j
=\int(ng+x\cdot\nabla g-\varepsilon |x|^2g)d\mu_j
\longrightarrow \int_{\partial C}g\,h_C(\nu_C)\rho\,d\mathcal H^{n-1}.
\]
As in the actual LSX contact argument, any compact set with slack at least \(s>0\) has mass bounded by \(C N_jq_j(1-s/2)^{q_j}\to0\). All joint limits therefore lie on contact pairs. The position marginal is absolutely continuous relative to boundary area, and the normal is unique there almost everywhere. Thus
\[
\Lambda_j\rightharpoonup
h_C(\nu_C(x))\rho(x)d\mathcal H^{n-1}(x)\delta_{\nu_C(x)}(du).
\]
This step uses positivity before introducing the signed continuous multiplier
\(b(u)=\log(h_L(u)/h_K(u))\).

Subselect \(m_j\to m\), with \(|m+\ell'|\le C_*\delta\) by (3.2). Adjunction passes locally by (3.5)–(3.6). Its complementary target layer is bounded by
\[
C_*\|\nabla g\|_\infty\,\mu_j(\mathbb R^n\setminus C_s)^{1/2},
\qquad C_s=\{x\in C:\operatorname{dist}(x,\partial C)\ge s\}.
\]
First let \(j\to\infty\), then \(s\downarrow0\). This is zero, since \(\partial C\) has zero volume. The dense-test error is at most \(\eta_j\|g\|_2\). The resulting exact identity is
\[
\boxed{\ \int_C W\cdot\nabla g\,d\mu
=-\int_{\partial C}g\,b(\nu_C)h_C(\nu_C)\rho\,d\mathcal H^{n-1}
-m\int_Cg\,d\mu.\ }                                                   \tag{3.8}
\]
Here \(m\), not zero, is the hard mean score. Taking a cutoff equal to one on \(C\) also verifies \(m=-\int_{\partial C}b h_C\rho\,dS\). No arbitrary direction-dependent test was inserted into radial integration.

## 4. Construction B: direct hard variational fields and a precise spectral obstruction

This construction starts with the hard body and its boundary load, without a soft sequence. It explains which part a simple Neumann inverse pays and which it does not.

For any symmetric \(C\) between fixed balls and density (3.4), define
\[
\mathcal L(g)=-\int_{\partial C}g\,b(\nu)h_C(\nu)\rho\,dS-m\int_Cg\,d\mu,
\quad m=-\int_{\partial C}b h_C\rho\,dS.
\]
It annihilates constants. On the mean-zero Euclidean \(H^1(C,\mu)\) space, the form \(\int|\nabla g|^2d\mu\) is coercive with constant depending only on the ball bounds and the bounded Gaussian weight. The usual convex-domain Poincaré bound follows, for example, from the diameter bound and comparison of the weight with uniform volume.

The boundary load has a uniform dual bound. Since \(x\cdot\nu\ge r\), weighted divergence gives
\[
r\int_{\partial C}g^2\rho\,dS
\le\int_C\{(n-\varepsilon|x|^2)g^2+2g\,x\cdot\nabla g\}\,d\mu
\le C_*(\|g\|_2^2+\|\nabla g\|_2^2).
\]
The boundary area is uniformly bounded. Cauchy–Schwarz, this trace estimate and Poincaré give
\[
|\mathcal L(g)|\le C_*\|b\|_\infty\|\nabla g\|_2.
\]
Riesz representation therefore constructs a unique mean-zero \(u\in H^1(C,\mu)\) and \(W_N=\nabla_xu\) with
\[
\int_CW_N\cdot\nabla g\,d\mu=\mathcal L(g),\qquad
\|W_N\|_2\le C_*\|b\|_\infty.                                         \tag{4.1}
\]
This pays an actual hard inverse and the full flux, with no facet constants. It does not pay the small tensor derivative energy.

There is a concrete compatibility failure already for the unregularized hard target (\(\varepsilon=0\), also allowed in the direct variational construction). For uniform measure on the unit ball take \(b(\nu)=\kappa\nu_1\nu_2\), so \(m=0\). The Neumann solution is
\[
u=-\kappa x_1x_2/2,\qquad W_N=-\kappa(x_2,x_1,0,\ldots,0)/2.
\]
Its divergence is zero and its normal component is \(-b\). The ball's moment Hessian is radial, \(a(z)I+d(z)zz^T\), and is not constant: a constant positive Hessian would have an unbounded gradient image. Thus \(D_zW_N=(D_xW_N)\tau\) is not symmetric at suitable points. It violates one of (3.6). These slopes can occur at an interior Wulff time: for sufficiently small \(\kappa\), the smooth functions \(e^{-tb}\) and \(e^{(1-t)b}\) are positive strictly convex support functions, and their interpolated bound at that time is one. The example concerns actual admissible local geometry, not arbitrary incompatible boundary data. It does not show that no tensor-compatible solution exists; Construction A provides one.

The more tempting moment spectral form has an independent boundary problem. In one dimension,
\[
d\mu=dx/2\ \text{on }[-1,1],\quad
\varphi(z)=2\log\cosh(z/2)+\log4,\quad
x=\tanh(z/2),\quad \tau(x)=(1-x^2)/2.
\]
For a nonzero dilation slope \(b\), the required load is
\[
\mathcal L(g)=b\int g\,d\mu-\tfrac b2\{g(1)+g(-1)\},\qquad W=-bx.
\]
The equation \(W=\tau f'\) forces \(f=b\log(1-x^2)+\text{constant}\), and on \([-a,a]\)
\[
\int\tau(f')^2\,d\mu
=b^2\left[\log\frac{1+a}{1-a}-2a\right]\longrightarrow\infty.          \tag{4.2}
\]
Equivalently, an even logarithmic boundary cutoff with value one at the endpoints, zero for \(1-|x|\ge a_0\), and profile
\[
g_\eta(x)=\min\!\left(1,\,
\frac{\log(a_0/(1-|x|))_+}{\log(a_0/\eta)}\right)
\]
has \(L^2\) norm tending to zero and moment Dirichlet energy \(O(1/\log(a_0/\eta))\), while \(\mathcal L(g_\eta)\to-b\). Smooth approximations preserve these estimates. The load is not continuous on the ordinary moment-form domain. The inverse norm of a boundary-truncated formulation diverges at least as a square root of a logarithm. Tensoring with intervals gives the same issue in every dimension, including three.

This is why a direct Friedrichs inverse of the second-order hard moment operator cannot simply replace the dense completions. The fourth-order constrained formulation would have to encode \(W=P x-\operatorname{div}P\), \(P\tau=\tau P^T\), and the tensor energy together. Construction A proves nonemptiness and the deficit bound for that constrained class. Equation (4.1) alone does not.

## 5. Quantitative hard coordinates, affine normalization and the constant matrix

### 5.1 Why the exponent can be dimensional

First apply a linear map sending the John ellipsoid of the selected \(C\) to \(B\). Then
\[
B\subset \widehat C\subset\sqrt n B.
\]
The operator norms of this map and its inverse are bounded in terms of the original \(r,R,n\). The transformed Gaussian is \(Q(x)=\varepsilon|Jx|^2/2\), with \(0\le Q\le1/2\) on \(\widehat C\). Thus its normalized density is between \(e^{-1/2}/|\widehat C|\) and \(e^{1/2}/|\widehat C|\). The invariant derivative and \(R\) energies are unchanged under the source/target dual transformation; the \(W\) norm changes by a parameter-bounded factor.

This normalization is performed on the already existing hard fields. Without it, balancing \(\exp(C(r,R)L)\) against \(\exp(-c(r,R)L)\) would give an aspect-ratio-dependent exponent, which would not prove the stated \(\alpha_n\) assertion.

For a normalized target \(B\subset C\subset\sqrt n B\), the source potential satisfies
\[
|\nabla\varphi|\le\sqrt n,\qquad
0<\tau\le2nI,\qquad
c_n|z|-C_n\le\varphi(z)\le C_n+\sqrt n|z|.             \tag{5.1}
\]
The cap is Klartag's hard-target theorem. A possible directional coercivity coefficient before reducing it is
\[
c_n^{(0)}=
\frac{e^{-1/2}}{\kappa_n n^{n/2}}\int_{B}|x_1|dx>0.
\]
Indeed the supporting planes at \(z,-z\), integrated against the normalized source, give
\(\varphi(y)-\varphi(0)\ge\int|x\cdot y|d\mu-n\).
The identity \(E[z\cdot\nabla\varphi]=n\) is justified first using any preliminary coercive bound from slopes in an inner ball. Normalization of \(\int e^{-\varphi}\) and the upper Lipschitz bound then bound \(\varphi(0)\) by dimensional constants.

The equation \(\det\tau=Z e^{-\varphi+Q(\nabla\varphi)}\), the cap and (5.1) give
\[
\tau\ge c_n e^{-C_nL}I,\quad e^{-\varphi}\ge c_ne^{-C_nL}
\quad\hbox{on }B_L,\qquad
\nu(B_L^c)\le C_n(1+L)^{n-1}e^{-c_nL}.                \tag{5.2}
\]
All constants in these exponents are dimensional; the bounded Gaussian on the target is sufficient, even after linear transformations.

Here is one fully dimensional choice behind (1.2). Write
\(I_n(c)=\int_{\mathbb R^n}e^{-c|z|}dz=n!\kappa_n/c^n\), take \(c_0=c_n^{(0)}\), and put
\[
h_*=\min\!\left\{1,\,
\frac{e^{-1/2}\kappa_n e^{-\sqrt n}}
{e^n I_n(c_0)(2n)^{\,n-1}}\right\},\quad
r_n=(2n)^{-1/2},\quad R_n=\sqrt{n/h_*},
\]
\[
c_1=\frac{e^{-1/2}}{\kappa_nR_n^n}
          \int_{r_nB}|x_1|dx,\qquad
a_n=10(n+1)(R_n+1),\qquad
b_n=\min\{1,c_1/(8n)\}.                               \tag{5.2a}
\]
Indeed \(\varphi(0)\le\log(e^nI_n(c_0))\) before the \(H\) transformation, so \(\tau\ge h_*I\) on \(B_1\), and \(h_*I\le H\le2nI\). In the final frame the body lies between \(r_nB,R_nB\), and its coercivity coefficient is at least \(c_1\). The squared derivative estimate grows at most as \(e^{2R_nL}\) before replacing a ball by the cube's enclosing ball. The displayed \(a_n\) absorbs that replacement and all polynomial powers of \(L\) in (5.3)–(5.4). The displayed \(b_n\) absorbs the tail polynomial, its square root and its cap \(1/n\) power. Enlarging multiplicative dimensional constants handles \(L\ge2\). These formulas are intentionally very wasteful.

### 5.2 Core estimates and symmetrization

From (3.7), \(\mathscr D(P)\ge\lambda_{\min}(\tau)\lambda_{\max}(\tau)^{-2}|D_zP|^2\), and (5.2),
\[
\|D_zP\|_{L^2(B_L)}\le C_*e^{C_nL}\sqrt\delta.
\]
Set \(A=\fint_{B_1}P\). Poincaré and (3.6) give
\[
|A|\le C_*,\qquad
\|P-A\|_{L^2(B_L)}+
\|W-A\nabla\varphi\|_{L^2(B_L)}
\le C_*(1+L)^{n/2+1}e^{C_nL}\sqrt\delta.              \tag{5.3}
\]
To verify the bound on \(A\), (5.2) on \(B_1\) makes \(\nabla\varphi\) uniformly strongly monotone there; its image contains a dimensional ball, and the Hessian upper bound controls the Jacobian. Thus \(\int_{B_1}\nabla\varphi\nabla\varphi^Tdz\ge c_nI\). This and the global \(W\) bound control \(A\). Comparing averages on \(B_1\) and \(B_L\) pays the displayed polynomial factor.

Put \(H=\fint_{B_1}\tau\). Its eigenvalues lie in a dimensional compact interval. From \(P\tau=\tau P^T\),
\[
|AH-HA^T|\le C_*\sqrt\delta.
\]
In the constant dual frame \(x'=H^{-1/2}x\), replace \(H^{-1/2}AH^{1/2}\) by its symmetric part \(S\). This changes it by \(C_*\sqrt\delta\). The change of frame has dimensional condition number. The target still lies between dimensional balls, (5.1)–(5.2) hold with new dimensional constants, and
\[
|S|\le C_*,\qquad
\|S\tau-\tau S\|_{L^2(B_L)}
+\|W-S\nabla\varphi\|_{L^2(B_L)}
\le C_*e^{a_nL}\sqrt\delta.                          \tag{5.4}
\]
Increase \(a_n\ge1\) to absorb polynomial factors, transformed balls, and the cubes used below. This describes a choice of \(a_n\) using only the cap, determinant, Poincaré and dimensional frame bounds above; there is no PDE convergence modulus in it.

Decrease \(b_n\in(0,1]\) so that the source tail, its square root, and its \(1/n\) power are all bounded by \(C_ne^{-b_nL}\) in this final frame. For example a sufficiently small dimensional multiple of the coercivity constant in (5.1), divided by \(n\), works. From (5.4), the global \(W\) bound and the tail,
\[
\int_C|W-Sx|\,d\mu
\le C_*\left(e^{a_nL}\sqrt\delta+e^{-b_nL}\right).       \tag{5.5}
\]
The tail of \(Sx\) is harmless because \(C\) and \(S\) are bounded. This explicitly pays the passage from a core estimate to all target positions.

### 5.3 Clusters and the trace

Diagonalize \(S\). Merge consecutive eigenvalues whenever their gap is smaller than \(\gamma>0\). There are at most \(n\) clusters; each has diameter at most \((n-1)\gamma\), and distinct clusters have all eigenvalue gaps at least \(\gamma\). Let \(E_i\) be their orthogonal sums, and let \(A_\gamma\) equal a chosen eigenvalue \(a_i\) on \(E_i\). Then
\[
\|S-A_\gamma\|\le n\gamma,\quad |a_i|\le C_*,
\qquad
\|\Pi_i\tau\Pi_j\|_{L^2(B_L)}
\le C_*\gamma^{-1}e^{a_nL}\sqrt\delta\quad(i\ne j).     \tag{5.6}
\]
The last estimate is entrywise division of \([S,\tau]\) by the actual spectral gaps. There is no division by a within-cluster gap.

Set \(e=\delta^{\theta_n}\) and
\[
L=\frac{\log(1/\delta)}{8(a_n+b_n+1)},\qquad \gamma=e.
\]
For sufficiently small deficit \(L\ge2\). Equation (1.2) gives
\[
e^{a_nL}\sqrt\delta\le\delta^{3/8}\le e^2,\qquad
e^{-b_nL}=e.
\]
Consequently
\[
\int_C|W-A_\gamma x|d\mu\le C_*e.                    \tag{5.7}
\]
Test (3.8) against one fixed nonnegative smooth function supported in an inner dimensional ball. Weighted integration by parts for \(A_\gamma x\) has bulk coefficient
\(-\operatorname{tr}A_\gamma+(A_\gamma x)\cdot\nabla Q\).
The latter Gaussian term is \(O_*(\delta)\). It follows that
\[
|\operatorname{tr}A_\gamma-m|\le C_*e,\qquad
|\operatorname{tr}A_\gamma+\ell'|\le C_*e.             \tag{5.8}
\]
Subtracting this bulk identity from (3.8), for arbitrary smooth compact \(g\), gives
\[
\left|\int_{\partial C}g\,
\{A_\gamma x\cdot\nu+b(\nu)h_C(\nu)\}\rho\,dS\right|
\le C_*e(\|g\|_\infty+\|\nabla g\|_\infty).           \tag{5.9}
\]
The nonzero chord slope and Gaussian term have both been retained.

## 6. Paying the normal-test interface on arbitrary convex boundaries

The following lemma is independent of moment coordinates.

**Radial BV flux lemma.** Suppose \(r_1B\subset C\subset R_1B\), \(F(x,u)\) is bounded and Lipschitz on a fixed neighborhood of \(\partial C\times S^{n-1}\), and \(w\) is a boundary weight bounded above and below by positive constants. If
\[
\left|\int_{\partial C}g(x)F(x,\nu_C(x))w(x)dS(x)\right|
\le\eta(\|g\|_\infty+\|\nabla g\|_\infty)
\]
for all compact smooth \(g\), then
\[
\int_{\partial C}|F(x,\nu_C(x))|dS(x)\le C\eta^{1/4}                 \tag{6.1}
\]
for \(0<\eta\le1\). Constants depend only on the indicated bounds, dimension and the Lipschitz bound of \(F\). No derivative of the normal map is assumed.

**Proof.** Let \(p=p_C=h_{C^\circ}\) be the gauge restricted to the sphere. It is bounded above and below and is uniformly Lipschitz. Its spherical distributional Hessian satisfies
\(D_S^2p+pI\ge0\). The total trace of this positive matrix measure is
\((n-1)\int_Sp\), since the spherical Laplacian integrates to zero. Hence \(D_S^2p\) has uniformly bounded total variation.

Write \(X(\theta)=\theta/p(\theta)\). This radial parameterization is uniformly bi-Lipschitz onto \(\partial C\), and almost everywhere
\[
N(\theta)=\nu_C(X(\theta))
=\frac{p(\theta)\theta+\nabla_Sp(\theta)}
       {|p(\theta)\theta+\nabla_Sp(\theta)|}.
\]
The denominator is at least \(\min p>0\). Thus \(N\) is a uniformly bounded BV function on the sphere. One can justify the chain rule directly by smoothing support functions in spherical charts or by rotation convolution: the positive Hessian-measure bound controls the derivatives of the smooth approximants, and lower semicontinuity gives the assertion. The radial area Jacobian
\[
J(\theta)=p(\theta)^{-n}|\nabla p(\theta)|
\]
is bounded above and below.

Therefore \(f(\theta)=F(X(\theta),N(\theta))\) has uniformly bounded BV norm and supremum. A finite chart partition and convolution at scale \(s\) give smooth \(f_s\) with
\[
\|f_s\|_\infty\le C,\quad \operatorname{Lip}(f_s)\le C/s,\quad
\int_S|f-f_s|\le Cs.
\]
The \(L^1\) estimate follows by integrating the derivative along translations for smooth approximants and passing to BV limits; the Lipschitz estimate is the \(L^1\) norm of the differentiated convolution kernel. These constants depend on the fixed sphere charts, not on facets.

Take \(g_s(x)=\chi(|x|)f_s(x/|x|)\), where \(\chi\) is a fixed compact smooth cutoff equal to one on \([r_1,R_1]\) and vanishing near zero. Then \(g_s(X(\theta))=f_s(\theta)\), and its test norm is at most \(C/s\). The area-Jacobian and weight bounds imply
\[
\int_{\partial C}F^2w\,dS
\le\left|\int_{\partial C}Fg_sw\,dS\right|+Cs
\le C(\eta/s+s).
\]
Choose \(s=\sqrt\eta\) and apply Cauchy–Schwarz on the uniformly bounded boundary area. This proves (6.1). Facet edges and nonsmooth contacts cause no loss beyond the BV bound. \(\square\)

Apply the lemma to
\[
F(x,u)=A_\gamma x\cdot u+b(u)h_C(u),\qquad w=\rho.
\]
The transformed endpoint supports are uniformly positive and Lipschitz, so \(b\) has a uniform \(C_*\) Lipschitz bound; \(h_C\) does too. Equations (5.9) and (6.1) give
\[
\int_{\partial C}|A_\gamma x\cdot\nu+b(\nu)h_C(\nu)|dS
\le C_*e^{1/4}.                                       \tag{6.2}
\]
This is the actual quantitative normal information needed later. It is derived by testing a controlled approximation to the residual, not by treating \(\nu(x)\) as Lipschitz.

We will also use
\[
d_{\rm BL}(S_C,S_Q)\le C_*d_H(C,Q)^{1/2}.               \tag{6.3}
\]
This is exactly Hug–Schneider (1.2). Here is an independent verification in the ball-bounded setting. For the two homogeneous gauges \(p,q\), Hausdorff error \(\zeta\) gives \(\|p-q\|_\infty\le C\zeta\) on a fixed annulus. With a cutoff equal to one on a smaller annulus, integration by parts and the positive Hessian measures give
\[
\int\chi|\nabla p-\nabla q|^2
=-\int(p-q)\{\chi\Delta(p-q)+\nabla\chi\cdot\nabla(p-q)\}
\le C\zeta.
\]
Each Laplacian measure has bounded mass there, by convexity and bounded gradients. Smooth approximation justifies the identity. Homogeneity transfers the estimate to the sphere. The normal and radial area-Jacobian formulas above are Lipschitz functions of \(p,\nabla p\) on their bounded range with positive denominator. Thus their \(L^1\) differences are \(O(\sqrt\zeta)\); testing a bounded Lipschitz function of the normal proves (6.3). This also clarifies why no total-variation convergence of the spherical measures is asserted.

## 7. Constructing one global product body

Use the orthogonal block coordinates of \(A_\gamma\), and take a cube \(Q_L=[-L,L]^n\) in the corresponding orthonormal basis. The definition of \(a_n\) in (5.4) includes replacement of \(B_L\) by \(B_{\sqrt n L}\).

For each block let
\[
F_i(z_i)=\fint_{[-L,L]^{n-\dim E_i}}
\Pi_i\nabla\varphi(z_i,z_{-i})\,dz_{-i},\qquad F=(F_1,\ldots,F_m).
\]
When there is one block, the transverse average is interpreted as the identity. Each \(F_i\) is a gradient of an averaged convex function, is Lipschitz with dimensional bound from the hard cap, and is odd: use the global evenness of \(\varphi\) and the symmetric averaging domain.

Poincaré only in the transverse variables, followed by integration in \(z_i\), yields
\[
\|\nabla\varphi-F\|_{L^2(Q_L)}
\le C_nL\left(\sum_{i\ne j}\|\Pi_i\tau\Pi_j\|_2^2\right)^{1/2}
\le C_*L\gamma^{-1}e^{a_nL}\sqrt\delta
\le C_*Le.                                             \tag{7.1}
\]
There is no restriction of an \(L^2\) Hessian to a coordinate line in this argument.

Both functions in (7.1) have uniformly bounded Lipschitz constants. If a Lipschitz function of bound \(M\) has maximum \(s\) on a cube, a ball of radius \(s/(2M)\), intersected with that cube, has volume at least a dimensional multiple of \((s/M)^n\), and its values are at least \(s/2\). This gives the usual \(L^2\)-to-sup estimate with exponent \(2/(n+2)\), including points on the cube boundary. Consequently
\[
\|\nabla\varphi-F\|_{L^\infty(Q_L)}
\le C_*(Le)^{2/(n+2)}
\le C_* e^{1/(n+2)}.                                   \tag{7.2}
\]
The last weakening uses \(L\le C_ne^{-1/2}\) for sufficiently small deficit, where here \(e=\delta^{\theta_n}\); the constant is dimensional.

Define relative convex bodies
\[
D_i=\operatorname{conv}\overline{F_i([-L,L]^{\dim E_i})},\qquad
D=\sum_iD_i.
\]
The Cartesian product identity
\(\operatorname{conv}\prod_i X_i=\prod_i\operatorname{conv}X_i\)
follows by taking products of the finite convex-combination coefficients. Thus (7.2) implies
\[
d_H\!\left(D,\operatorname{conv}\nabla\varphi(Q_L)\right)
\le C_* e^{1/(n+2)}.                                    \tag{7.3}
\]
All these sets are bounded and symmetric.

It remains to cover the part of \(C\) outside the core image. Let
\(C^{\rm core}=\operatorname{conv}\overline{\nabla\varphi(Q_L)}\subset C\).
The hard density is bounded below on \(C\), and
\[
|C\setminus C^{\rm core}|
\le C_*\mu(C\setminus\nabla\varphi(Q_L))
=C_*\nu(\mathbb R^n\setminus Q_L)\le C_ne^{-c_nL}.
\]
The gradient image of \(B_1\) contains a dimensional ball, so \(C^{\rm core}\) has a uniform inner ball. If a convex body between fixed balls has a point with support excess \(s\) above a contained convex body, joining that point to the inner \((n-1)\)-disk through zero creates a cap of volume at least \(c_ns^n\). Applying this here gives
\[
d_H(C,C^{\rm core})\le C_ne^{-b_nL}\le C_ne.
\]
Combine with (7.3) and weaken the exponent once more:
\[
\boxed{\ d_H(C,D)\le C_*e^{1/(2(n+2))}=:\zeta.\ }       \tag{7.4}
\]
For small deficit \(D\) contains a fixed inner ball and lies in a fixed outer ball. Hence each \(D_i\) has nonempty relative interior and contains zero in it. This is a **single** compatible product body. Neither approximate equality of mixed Hessians at one point nor a collection of separately fitted slices was used.

By (6.3),
\[
d_{\rm BL}(S_C,S_D)\le C_*\sqrt\zeta.                   \tag{7.5}
\]
The boundary of a product has, up to boundary area zero, exactly one boundary factor. Therefore \(S_D\) is supported on
\(U=\bigcup_i(E_i\cap S^{n-1})\).
The function \(\operatorname{dist}(u,U)\) is bounded Lipschitz, so
\[
\int\operatorname{dist}(u,U)dS_C(u)\le C_*\sqrt\zeta.   \tag{7.6}
\]
This step transports normal mass near the block union; it does not assert that any approximating facet lies exactly in a subspace.

## 8. Both original endpoints and the final power

Construct
\[
K^\sharp=e^{tA_\gamma}D=\sum_i e^{ta_i}D_i,\qquad
L^\sharp=e^{-(1-t)A_\gamma}D=\sum_i e^{-(1-t)a_i}D_i.    \tag{8.1}
\]
This pair belongs to \(\mathcal E\), with factors \(e^{ta_i}D_i\) and dilation ratios \(e^{-a_i}\). Its ball bounds depend only on the original fixed parameters, because \(|a_i|\le C_*\). These auxiliary bounds are a conclusion of the construction, not an imposed restriction on the comparison class.

### 8.1 Boundary slope and support errors

For \(S_C\)-almost every normal \(u\), the full Wulff bound contacts:
\[
h_C(u)=h_K(u)^{1-t}h_L(u)^t,\quad
h_K(u)=h_C(u)e^{-tb(u)},\quad h_L(u)=h_C(u)e^{(1-t)b(u)}.              \tag{8.2}
\]
To see contact, at a regular boundary point compactness of the sphere supplies an active constraint; its normal must be the unique normal there. Thus (8.2) holds regardless of inactive directions.

Choose a nearest block sphere to \(u\), say \(E_i\cap S^{n-1}\), and put \(d(u)=\operatorname{dist}(u,U)\). For its regular boundary position \(x\),
\[
|(A_\gamma x)\cdot u-a_i h_C(u)|\le C_*d(u).
\]
Indeed \(A_\gamma\) is scalar on that block and \(x\) is bounded. Dividing by \(h_C\ge c_n\), then using (6.2) and (7.6), gives
\[
\int|b(u)+a_i|\,dS_C(u)\le C_*(e^{1/4}+\sqrt\zeta).                  \tag{8.3}
\]
The nearest-block selection is only measurable bookkeeping; it is never used as a Lipschitz test.

The support formula for the actual product dilation gives
\[
|h_{K^\sharp}(u)-e^{ta_i}h_C(u)|\le C_*(d(u)+\zeta).
\]
The terms from the other blocks are bounded by their projection lengths, at most \(C_*d(u)\); the remaining difference uses (7.4). The analogous estimate holds for \(L^\sharp\).
The exponential is Lipschitz on the bounded range of slopes. Equations (8.2)–(8.3) therefore yield
\[
\int |h_K-h_{K^\sharp}|dS_C+
\int |h_L-h_{L^\sharp}|dS_C
\le C_*(e^{1/4}+\sqrt\zeta+\zeta)
\le C_*e^{1/(4(n+2))}=:\omega.                        \tag{8.4}
\]

Each absolute support difference in (8.4) is itself uniformly bounded and Lipschitz on the sphere. Apply (7.5) to transfer (8.4) from \(S_C\) to \(S_D\), at an additional cost \(C_*\sqrt\zeta\le\omega\). No discontinuous nearest-block test is transferred.

For a block diagonal positive map \(T\) with multiplier \(s_i\) on \(E_i\), the product boundary change-of-variables formula is
\[
dS_{TD}(u)=\frac{\det T}{s_i}\,dS_D(u)\quad(u\in E_i\cap S^{n-1}).   \tag{8.5}
\]
It follows either from the tangential Jacobian \(\det T\,|T^{-T}u|\), or directly by scaling the one boundary factor and all other interior factors. These coefficients are uniformly bounded above and below for the maps in (8.1). Thus
\[
\left|V_1(K^\sharp,K)-|K^\sharp|\right|
+\left|V_1(L^\sharp,L)-|L^\sharp|\right|\le C_*\omega,                \tag{8.6}
\]
where \(V_1(A,B)=n^{-1}\int h_B\,dS_A\).

### 8.2 Endpoint volumes and centering

Hausdorff closeness and an inner ball give
\(|\log|D|-\log|C||\le C_*\zeta\).
Equations (5.8), \(\log|C|=\ell(t)+O_*(\delta)\), and (8.1) imply
\[
|\log|K^\sharp|-\log|K||+
|\log|L^\sharp|-\log|L||\le C_*(\zeta+e+\delta)\le C_*\omega.          \tag{8.7}
\]
In particular the volume chord slope has supplied the determinant of the two comparison maps. Merely setting \(m=0\) would fail here for endpoints of different volume.

For completeness, the following classical mixed-volume interface pays the final distance. If symmetric \(A,B\) lie between fixed positive balls and
\[
|V_1(A,B)-|A||+||B|-|A||\le s,
\]
then
\[
d_H(A,B)\le C s^{1/(2n)}.                              \tag{8.8}
\]
Apply Figalli–Maggi–Pratelli with finite-perimeter set \(E=A\) and Wulff shape \(B\). Its anisotropic perimeter is \(nV_1(A,B)\). Ordinary Minkowski ensures the normalized deficit is nonnegative; the displayed hypotheses and positive volume bounds make it \(O(s)\). The theorem gives
\[
|A\mathbin\triangle(x+aB)|\le C\sqrt s,\qquad
a^n|B|=|A|,\quad a=1+O(s),
\]
for some translation \(x\), or a sequence approaching the infimum.

The optimal translation can be removed for symmetric convex bodies. The overlap \(f(x)=|A\cap(x+aB)|\) is even, and \(f^{1/n}\) is concave on its support: Minkowski interpolation of two intersections is contained in the intersection at the interpolated translation. Hence \(f(0)\ge f(x)\). Thus
\(|A\triangle aB|\le C\sqrt s\), and changing \(a\) to one costs \(O(s)\).
Finally a support excess \(h_A(u)-h_B(u)=\eta>0\) creates a cone cap inside \(A\setminus B\) of volume at least
\(\kappa_{n-1}r_1^{n-1}\eta^n/(nR_1^{n-1})\), by joining an exposed point to the inner disk perpendicular to \(u\). Interchange the bodies for the other sign. This proves (8.8), with all constants paid and no smoothness condition.

Apply (8.8) to (8.6)–(8.7) for each endpoint:
\[
\max\{d_H(K,K^\sharp),d_H(L,L^\sharp)\}
\le C_*\omega^{1/(2n)}
\le C_*e^{1/(8n(n+2))}
=C_*\delta^{1/\alpha_n}.                              \tag{8.9}
\]
Undo the two constant linear transformations; their operator norms are bounded in terms of the original parameters. They preserve membership in the complementary-block class, allowing oblique subspaces. This proves (1.1) for small positive deficit.

For a larger deficit use the uniformly bounded distance to the fixed comparison pair \((rB,rB)\), and reduce the constant in (1.1). If \(\delta=0\), repeat the construction with an arbitrary positive upper budget \(d\downarrow0\), taking \(\varepsilon=d\). Every estimate above used only \(\delta\le d\). Equation (8.9) gives \(d_{\mathcal E}=0\), sufficient for (1.1), without invoking closedness or qualitative equality. The construction began directly with arbitrary bodies and direction exhaustion, so no facet-dependent approximation exponent remains. \(\square\)

## 9. Self-audit, countermodels and scope of the candidate

The proof contains four points that require particular attention in independent review.

1. **Finite defect is not equality compactness.** The limit fields need not be constant. Rellich compactness is applied to locally bounded \(H^1\) fields; weak derivatives and lower semicontinuity retain a nonzero budget. The \(R\) square gives the local \(W\) derivative bound. The final rate is obtained only after the hard limit. No effective \(q\)-dependent regularity constant is carried into it.
2. **Normal tests are paid by BV.** The radial gauge has a bounded Hessian measure. The residual is bounded Lipschitz in position and normal, so its radial composition has a uniform BV bound even on facets. Its smooth approximations are admissible position tests. A general arbitrary bounded measurable normal test would not satisfy this argument and is not claimed.
3. **The product is global and unique within the construction.** Transverse averages, product of their image convex hulls, and a source-tail/cap estimate build one \(D\). There is no claim that every local nearly commuting Hessian automatically has a nearby global product image.
4. **Endpoints need both first mixed volume and volume.** The contact identity supplies endpoint supports on \(S_C\); surface-area continuity transfers bounded Lipschitz absolute support errors to \(S_D\); exact product area scaling reaches each comparison endpoint. The trace/mean-score calculation pays its determinant. Classical Minkowski stability then compares each original endpoint. Small intermediate-body error alone would not suffice.

Exact diagnostics include hard uniform-box moment fields, nonzero-mean dilation flux, oblique constant-frame covariance, independent polynomial adjunctions, positive derivative energies, scalar spectral boundary divergence, the ball Neumann incompatibility, product averaging and block surface-Jacobian formulas, and rational cap volumes/rate inequalities. They test signs, domains and degeneracies but do not prove the analytic compactness or BV arguments.

The classical cut-corner and I44 hexagon examples are compatible with this very weak power; no sharp cubic result is claimed. The direct spectral obstruction (4.2), the Neumann compatibility example, and the danger of an aspect-ratio-dependent exponent are **not** counterexamples to H49 and are not separate nominated findings. The planar result and I48's reduction are untouched. No centered nonsymmetric statement is established here.

## 10. Evidence and handoff

The source directory freezes the exact current brief (including the historical I46 brief), prior briefs/reports/parent results, the relevant selected pinned files, current primary responses and extracted passages, and immutable prior seals. It deliberately does not recursively duplicate old archives. The four shared ledgers and the current task orchestration record are marked mutable observations. Prior immutable artifact sets are checked in place against their unchanged seals.

Run from the project root:

~~~sh
python frontier/experiments/i49_hard_moment_quantitative_stability/check.py
python frontier/experiments/i49_hard_moment_quantitative_stability/verify.py
~~~

Both are read-only and disable bytecode. The verifier checks the exact I49 seal, input identities, response/derived-text bindings, read passages, selected Git blobs, whole ignored corpus, and old seals. Finite checks and hashes certify reproducibility, not analytic correctness or substantiality.

The exact diagnostic run passes **506 assertions**. It includes three nonconstant hard-box field cases with exact positive derivative energies. The evidence has **35 frozen inputs, 49 passage records, 12 selected pinned files, and 23 fresh primary responses**, all HTTP 200; 17 downloaded PDFs have reproducible text extraction. Six unchanged prior seals cover 2,253 artifact hash checks (including overlap between archives). The full inventory remains 13,223 tree entries, 749 manuscript directories and 9,340 ignored corpus files.

Two diagnostic implementation failures were retained with their original scripts: a first/third-index tensor was initially symmetrized using a three-term formula for a different index symmetry, and an algebra-only simplifier did not reduce a hyperbolic identity. Literal six-permutation symmetrization and the appropriate symbolic simplifier resolve those fixture failures. Neither changed a mathematical claim or source input. The final checker replays from the two frozen Python wheels without installing packages or writing bytecode. These corrections are disclosed in the execution notes.

**Handoff:** H49 is offered as a complete author-level candidate for a fresh independent full-proof audit, concentrating on §§3, 5–8, followed separately by an operation-level significance review. The bounded primary search does not certify priority. No shared ledger has been changed and no acceptance is presumed.
