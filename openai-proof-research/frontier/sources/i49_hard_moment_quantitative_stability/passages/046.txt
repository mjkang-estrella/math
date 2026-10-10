# I45 — independent full-proof audit of the I44 symmetric equality reduction

**Verdicts: E, C, B, and Q each PASS ORIGINAL WITHOUT REPAIRS.** These are analytic proof verdicts under the stated pinned OpenAI premises, separately from the finite diagnostics and integrity replay. No original author file is changed. The unrestricted pointwise kernel assertion K remains open in this project. Neither cubic nor quartic quantitative stability is proved. The substantial-finding count remains **6/10**.

E is the symmetric specialization of the mechanism in **Yude Liu, Qiang Sun, and Ge Xiong, *The centered logarithmic Brunn–Minkowski inequality*, arXiv:2610.10152v2, 8 October 2026**, especially (3.10)–(3.16), Lemma 3.4, and §3.3. Full credit for that mechanism belongs there; neither I44 nor this audit claims discovery or priority. The external paper is **not an assumed theorem**. Its authors explicitly call it a proposed proof and state that their independent human verification is incomplete. This audit checks the symmetric reduction only; it does not certify their nonsymmetric theorem or replace that human verification.

The verdicts apply to these exact claims:

* **E:** For every n≥2, full-dimensional origin-symmetric K,L⊂Rⁿ, and 0<λ<1, equality in logarithmic Brunn–Minkowski holds exactly when K=ΣKᵢ and L=ΣcᵢKᵢ on common nonzero complementary linear subspaces, cᵢ>0. The original subspaces need not be orthogonal.
* **C:** On an exact polytopal equality path, every true facet centroid divided by its support width is constant, with the stated scalar and vector ridge identities, including nonsimple configurations.
* **B:** The fixed-polytope facet/ridge Gamma limits, the Gaussian row correction, the full limiting logarithmic Hessian, and the normalized-score dual defect at order 1/q hold with the original order of limits.
* **Q:** The specified planar hexagons have midpoint deficit ½t³+O(t⁴) and distance comparable to t from the **entire** block equality class. In particular a uniform quadratic estimate fails, and any positive power estimate on a class containing these pairs must have exponent at least three.

The report below gives independent derivations and estimates at every new interface. Expanding details of a valid argument is not classified as a repair. No changed statement, additional hypothesis, altered limit order, or replacement mechanism is needed.

## 1. Inputs, premise boundary, and current sources

I read both complete I43/I44 reports, their original briefs, parent verification/primary-check records, I44's verifier, and the actual pinned `introduction`, `reduction`, `moment`, `identities`, `density`, `tensor`, and `variance` proofs. The accepted pin is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Its finite-slab inequality, smooth moment construction, compact adjunctions, dense even range, and retained tensor identity are premises. Their extension through changing parameters and hard boundaries is not a premise.

The complete 13,223-entry tree has 749 manuscripts; `CONTENTS.md`'s 719 count is historical. The read-only corpus contains 9,340 files, including ignored files enumerated with `rg --files --no-ignore`. The selected twelve pinned files and seven operation contracts are preserved and bound to that tree. Current raw retrievals of `reduction.tex`, `tensor.tex`, and `variance.tex` agree byte-for-byte with I44 and the immutable pin.

An early bounded search was followed by official primary retrievals. The current [LSX record](https://arxiv.org/abs/2610.10152v2) and explicit v2 PDF agree with I44. Fresh copies of the following actual papers also agree with I44's PDFs:

* [Berman–Berndtsson, Theorem 1.1 and §§2.9, 2.12](https://afst.centre-mersenne.org/item/10.5802/afst.1386.pdf): smooth entire compact-target moment potential, arbitrary convex target, prescribed positive smooth target density, barycenter criterion, translation uniqueness, and gradient image equal to the target interior.
* [Bonnet–Rubinstein, v1, Theorem 1.3, Propositions 3.3–3.4 and §3.5](https://arxiv.org/pdf/2604.09914v1): L¹ stability of probability-normalized source densities up to translations, controlled by W₁ and directional first-moment nondegeneracy.
* [Cule–Samworth, Proposition 2 and proof](https://arxiv.org/pdf/0908.4400): log-concave density convergence, in particular local uniform convergence when the limit density is positive and continuous.
* [Figalli–Jhaveri–Mooney, Theorem 1.1 and §2](https://people.math.ethz.ch/~afigalli/papers-pdf/Nonlinear-Bounds-in-Holder-Spaces-for-the-Monge-Ampere-Equation.pdf): interior C²,α control, with explicit dependence on strict-convexity modulus and Hölder right-hand side. Its proof uses normalized sections; no dimension-only Hessian bound is asserted.

I also checked Putterman's actual Lemma 2.1 for arbitrary positive Wulff bounds and Hu–Ivaki's support-derivative and C² proofs (Proposition 8.5, Theorem 8.13). LSX Lemma 2.1's normal-support reconstruction is rederived below. The parent-rejected aggregator identifier is preserved only as an objection record, not used as evidence. The earlier Lu, Böröczky–De, zonoid, and smooth uniqueness exclusions remain scope boundaries; no novelty nomination is attempted.

The complete brief and prior bytes are frozen in the I45 source directory. All four shared status ledgers are marked mutable. Historical seals are replayed without refreshing them. Search results are contextual leads; actual primary statements/proofs govern the argument.

## 2. E: normalization, equality geometry, and the two algebraic completions

### 2.1 The inherited equality reduction is valid

Write F(a)=log|W[eᵃ]| on even continuous sphere functions. For two such functions, apply the assumed symmetric inequality to their Wulff bodies and then use inclusion of the logarithmic combination in the Wulff body of the interpolated bounds. This proves concavity even when bounds are inactive.

At any boundary point of W[eᵃ] an inequality is active: otherwise compactness of the sphere gives a uniform positive slack, contradicting that the point is on the boundary. At almost every boundary point the outer normal is unique, hence the active direction is that normal. Therefore eᵃ=h on surface-area-almost every direction. Putterman's first variation applies because the difference quotients of eᵃ⁺ˢᵍ converge uniformly, and gives

\[
 DF(a)g=|W[e^a]|^{-1}\int e^a g\,dS
       =n\int g\,d\nu_{W[e^a]}.
\]

The derivative is a global upper supporting functional of the concave F. If F is affine on a segment, the same upper support contacts every point of it. Two-sided directional differentiability makes that upper support unique by testing both signs of every direction. Thus all normalized cone-volume measures coincide. Conversely, equal endpoint derivatives squeeze the endpoint difference and force affinity. An interior chord equality forces affinity on the full segment. Continuity extends the contact relation to the common measure support.

Independently dilating the endpoints to volume one preserves equality: the Wulff interpolation is multiplied by the corresponding geometric scalar. Thus throughout the normalized path C_t one has |C_t|=1 and a common normalized cone-volume measure. In particular all surface-area supports agree, since h is positive. No normal fan is inferred from this, and no exact equality of approximating bodies is used later.

### 2.2 Tensor completion and invariant norm

Use the original source conventions x=∇φ(z), τ=D²φ, M=τ⁻¹, h=D²ₓv, P=τh, B=Pτ, W=Px−div_zP, u=δ_μW. Compact support permits the source integrations without boundary terms. The tensor calculation has already integrated by parts before the pointwise frame normalization. Choose a **constant** dual map z=Tz′, x′=Tᵀx, with T=τ(z₀)⁻¹/² for evaluation at z₀. It is not a varying orthonormal frame.

For fully symmetric S=D³ₓv and C=D³_zφ, put Jᵢⱼₖ=hᵢₐCₐⱼₖ. J is symmetric in its last two slots, and Kₐₖℓ=∂_zℓPₐₖ=Sₐₖℓ+Jₖₐℓ in this frame. Let a=|J|² and b=〈J,J¹²〉. Full symmetrization is the orthogonal projection onto symmetric tensors, so

\[
 |\operatorname{Sym}J|^2=(a+2b)/3,\quad
 |J-J^{12}|^2=2(a-b),\quad
 |K|^2=|S|^2+2\langle S,J\rangle+a.
\]

Both sides of the proposed completion therefore equal
2|S|²+4〈S,J〉+a+b. This proves the identity for every last-two-symmetric J, without needing any extra relation between h and C. In particular the derivative norm controls all components of D_zP, rather than merely a symmetric projection.

The transformation rule

\[
 P'=T^TPT^{-T},\qquad
 K'_{ak\ell}=T_{ia}K_{ijm}(T^{-1})_{kj}T_{m\ell}
\]

gives the invariant contraction

\[
 \mathscr D(P)=M_{ab}\tau_{kr}M_{\ell s}K_{ak\ell}K_{brs}.
\]

The eigenvalues of this tensor-product positive form are bounded below by κ/Λ² when κI≤τ≤ΛI. Consequently the accepted retained-square identity implies

\[
 T(v)\ge\tfrac12E\mathscr D(P)
       \ge\frac{\kappa}{2\Lambda^2}E|D_zP|^2
\]

on any such compact region. The trace in T(v) is tr((DₓW)²), as in the source weighted vector Bochner identity, not tr((DₓW)ᵀDₓW). In general they differ. The new diagnostic explicitly detects the difference for a correlated Gaussian and a quartic test.

### 2.3 Exact score completion, signs, and cutoffs

For arbitrary real βᵢ let F=Σβᵢψᵢ, U=F−EF, aᵢ=Eψᵢ, dᵢ=E(uψᵢ), and γᵢ=βᵢ/q. Symmetry gives E(xU)=0. The source adjunctions and homogeneity give

\[
 E\operatorname{tr}(\tau H_i)=qa_i,\quad
 E\operatorname{tr}(BH_i)=E(W\cdot\nabla\psi_i)=d_i,
\quad E(x^TH_ix)=q(q-1)a_i,\quad
 E(x^TH_iW)=(q-1)d_i.
\]

For the only noncompact Stein step insert η_R∂ⱼψᵢ. The extra term is bounded by (4/ε)C/R times the polynomial tail E[|∇ψᵢ|1_{|x|≥R}], which tends to zero **at fixed q,ε**. No uniform-in-ε cutoff is required. The other pairings contain compact B or W.

Expanding the matrix square gives a cross term −2γᵢdᵢ and constant γᵢ²qaᵢ; expanding the vector square gives −2γᵢ(q−1)dᵢ and γᵢ²q(q−1)aᵢ. Their combined cross term is −2βᵢdᵢ and their constant is βᵢ²aᵢ, for either sign of βᵢ. Retain εI in H. The full right side of I44 (5.1) is then

\[
 Eu^2-2E(uF)+\sum_i\beta_i^2a_i
 =\|u-U\|_2^2+\sum_i\beta_i^2a_i-EU^2.
\]

Each matrix term is a squared Hilbert–Schmidt norm of Hᵢ¹/²(B−γᵢτ)M¹/²; B−γᵢτ need not be positive. Also tr(MB²)≥0. Thus all claimed signs hold and no mixed coefficient term is omitted: cross-products of distinct ψᵢ already occur inside EU² and the approximation error. The case F constant, including all zero coefficients, is covered without division.

The accepted dense even range supplies v with ||u−U||₂≤η for every fixed finite list, q,ε. Choosing η later does not assert a uniform inverse. This verifies the exact unnormalized completion and the εE|W|² term needed next.

## 3. E: the diagonal limit and local moment regularity

### 3.1 Uniform soft approximation and simultaneous time selection

Let a_t=(1−t)log h_K+t log h_L, f=log(h_L/h_K), and B₀=||f||∞. All finite outer bodies Q_m(t), including coordinate directions, have common positive inner radius and finite outer radius. The support-bound inclusions

\[
 e^{-B_0|t-s|}Q_m(t)\subset Q_m(s)\subset e^{B_0|t-s|}Q_m(t)
\]

prove continuity of their log volumes, uniformly in m. Nested dense direction sets decrease to C_t. Their log volumes decrease to zero, so Dini gives a uniform error on the closed parameter interval.

Choose ε_j↓0 first, increasing m_j with outer log-volume error ≤ε_j next, and an even q_j afterward with soft error ≤ε_j and q_j≥j(1+log(N_j+1)). Uniformity in t at this last step follows directly, not just from pointwise convergence: for fixed m, every sequence t_q→t has almost-everywhere soft convergence away from finitely many limiting facet hyperplanes, with the fixed-ε Gaussian majorant. A failed uniform bound would give a contradicting convergent subsequence of t_q. The hard Gaussian insertion changes log volume by at most ε_jR²/2. Hence |G_j(t)|≤Cε_j for G_j=log Z_j, on [0,1].

G_j is smooth and concave by the pinned variance inequality. For 1/3≤t≤2/3, chords to 0 and 1 bound |G′_j(t)|≤6Cε_j. Also

\[
 \int_{1/3}^{2/3}-G_j''(t)dt
 =G_j'(1/3)-G_j'(2/3)\le12C\epsilon_j.
\]

Some t_j in that interval has −G″_j(t_j)≤36Cε_j, and the first-derivative bound holds at this **same** t_j. Thus D_j=O(ε_j) and EF_j=−G′_j(t_j)→0 simultaneously. Subselect t_j→t_* and write C=C_{t_*}. There is no need to prescribe t_*.

For signed directions use ψ_{p,j}=(p·x/e^{a_{t_j}(p)})₊^{q_j}. The opposite term completes it to the even polynomial |p·x/e^{a_{t_j}(p)}|^{q_j}. Source smoothness and density are applied to that paired polynomial. The signed terms are used for measure bookkeeping. Individual one-sided powers need not be C∞ at zero; this causes no use of the source on an inadmissible potential.

On a fixed compact subset of int C all support ratios have a common bound ρ<1 for large j. For each fixed k their derivative sum is at most C_kN_jq_j^kρ^{q_j-k}. Its logarithm is bounded by
q_j/j+k log q_j+(q_j−k)logρ+O_k(1), which tends to −∞. This works on every compact, for every fixed derivative order, without a separate uniformity assertion on all compacts at once.

Outside C, continuity in the direction supplies a direction in the fixed dense union that strictly violates the limiting constraint. Its power diverges. For the tails choose R₀ so the coordinate widths are ≤R₀/√n. Outside a fixed ball one coordinate ratio is ≥|x|/R₀>1, giving the common bound e^{−(|x|/R₀)²} once q_j≥2. The bound is integrable against every fixed polynomial. After normalization Z_j→1,

\[
 \int (1+|x|^k)|\rho_j(x)-1_C(x)|dx\to0\quad(k\text{ fixed}).
\]

This proves all required moment convergence and W₁ convergence (couple common density mass identically and send the residual through the origin). No exchange of unproved joint limits occurs.

### 3.2 Compactness of the moment potentials: all hypotheses paid

This is an independent justification of the use of LSX Lemma 3.4, not invocation of that lemma as an axiom.

The uniform probability on C has barycenter zero, and C is any full-dimensional symmetric convex body. In Berman–Berndtsson take the globally smooth positive function g≡1/|C| on the target; boundary smoothness is not a hypothesis. Their theorem gives an entire smooth convex φ, gradient diffeomorphism onto int C, and det D²φ=|C|e^{−φ}. Integrating through the diffeomorphism gives ∫e^{−φ}=1. Positive determinant and convexity make the Hessian positive definite. Their proof constructs the potential variationally, obtains regularity on bounded sublevel domains, and establishes the global gradient-image condition; one is not extrapolating an interior PDE solution to surjectivity.

For Bonnet–Rubinstein both targets are probabilities of equal mass, centered, with finite first moments, and not supported on hyperplanes. The moment potentials are smooth on the whole space, hence essentially continuous in their definition. Put

\[
 r_*:=\inf_{|e|=1}\int_C|e\cdot x|dx>0,\qquad
 R_*\ge\int_C|x|dx>0.
\]

Positivity of r_* follows from an inner ball, or continuity in e and nondegeneracy. The theorem may use this fixed target for its constants. Its proof also controls the approximating first moments by R_*+W₁ and their directional moments below by r_*−W₁. The resulting L¹ error is O(\sqrt{d_j\log(1+R_*/d_j)/R_*}) with d_j=W₁(μ_j,μ) and a fixed constant. It tends to zero. If d_j=0 use translation uniqueness. The proof's truncated-source comparison and exponentially small truncation tail justify this conclusion without any soft-parameter Hessian assumption.

Translate φ_j accordingly. Translations preserve ∫e^{−φ_j}=1 and leave the **target-coordinate** τ_j(x) unchanged. The target is still symmetric, so the accepted even test range is unaffected. Cule–Samworth applies to the log-concave source densities converging to the positive continuous e^{−φ} on all Rⁿ. Its Proposition 2 proof yields local uniform convergence; on a compact set the limit is bounded away from zero, allowing logarithms. Convex difference quotients give

\[
 \|\nabla\varphi_j-\nabla\varphi\|_{C^0(Q)}
 \le C_n\{2\|\varphi_j-\varphi\|_{C^0(Q^+)}/s+\omega_{\nabla\varphi,Q^+}(s)\}.
\]

First j→∞, then s↓0 yields local C¹ convergence.

Fix a source ball and a larger compact neighborhood. Its limiting gradient image is compactly inside int C. C¹ convergence keeps all large-j images in a common target compact. The equation

\[
 \det D^2\varphi_j=Z_j\exp[-\varphi_j+V_j(\nabla\varphi_j)]
\]

therefore has two-sided positive determinant bounds. Bounds on every fixed derivative of V_j hold on that target compact. There is no use of the divergent global cap 4/ε_j here.

To verify the convexity/section hypothesis rather than infer it from determinant bounds alone, let D²φ≥mI on the larger ball, e_j=||∇φ_j−∇φ||∞. The tangent-plane separation satisfies

\[
 \varphi_j(w)-\varphi_j(z)-\nabla\varphi_j(z)\cdot(w-z)
 \ge\tfrac m2|w-z|^2-2e_j|w-z|.
\]

At each fixed positive separation this has a uniform positive lower bound for large j; the finitely many remaining smooth strictly convex potentials have a positive minimum on the compact pair set too. This provides a common modulus of strict convexity. It does **not** assert a uniform quadratic separation down to arbitrarily small scales at this stage.

Subtract a tangent plane at a center. Strict convexity of the limit and local uniform convergence allow fixed h,r,R>0 with

\[
 B_r\subset S_j(h/4)\subset S_j(h/2)\subset S_j(h)
 \subset S_j(2h)\Subset B_R.
\]

A common gradient bound L gives separation at least (t−s)/L between nested levels s<t. Caffarelli's interior estimates on these bounded, normalized sections give a common C¹,α bound. The right-hand sides are now uniformly C^α by composition. FJM Theorem 1.1, with the common strict-convexity modulus, gives a common local C²,α bound. The beginning of its §2 derives the power-type section modulus from normalized sections and the determinant bounds; I44 does not have to assume a uniform quadratic modulus for φ_j. This checks the potentially circular regularity step.

The determinant lower bound and Hessian upper bound now imply a positive local Hessian lower bound. Differentiating the logarithmic equation yields, for w_{j,k}=∂_kφ_j,

\[
 (D^2\varphi_j)^{-1}:D^2w_{j,k}
 =\nabla V_j(\nabla\varphi_j)\cdot\nabla w_{j,k}-w_{j,k}.
\]

Local Schauder estimates bootstrap to every fixed order. Compactness and the known C¹ limit identify every subsequential limit with φ. The inverse maps converge locally on int C by the inverse function theorem on finitely many neighborhoods of the compact preimage. Thus both source and target moment Hessians have the needed local bounds and convergence. This closes the local compactness interface.

## 4. E: bounded fields, hard boundary, and splitting

### 4.1 No unbounded constant part of P can escape

Choose the dense test error η_j≤ε_j after fixing the parameters. The exact completion implies

\[
 T(v_j)+\epsilon_jE|W_j|^2\le C\epsilon_j+\epsilon_j^2.
\]

Hence T(v_j)→0 and sup E|W_j|²<∞. Keeping only T→0 would not provide the second assertion. Local moment bounds and a positive lower bound on e^{−φ_j} convert the invariant derivative estimate to ||D_zP_j||_{L²(B_R,dz)}→0 for every R.

Let A_j be the mean of P_j on B₁. Poincaré gives ||P_j−A_j||₂→0. Since x_j=∇φ_j is uniformly bounded there, and |div P_j|≤√n|D_zP_j|,

\[
 \|W_j-A_jx_j\|_{L^2(B_1,dz)}\to0.
\]

The global μ_j bound is the same as a ν_j bound under the moment map and hence bounds this local Lebesgue norm. Moreover Q_j=∫_{B₁}x_jx_jᵀdz→Q with Q positive definite: if eᵀQe=0, continuity gives e·∇φ=0 on B₁, impossible for a nonzero e because its gradient image is open. Therefore tr(A_jQ_jA_jᵀ)≥c|A_j|² bounds A_j. After subselection A_j→A. Poincaré on B_R and comparison of averages on B₁ give P_j→A and W_j→A∇φ in local source L².

The target-coordinate conclusion requires care about composition. If Q⊂int C is compact, its inverse images for all large j lie in one fixed source compact, and detτ_j is uniformly bounded there. Changing variables gives

\[
 \int_Q|W_j(x)-Ax|^2dx
 \le C\int_{B_R}|W_j(\nabla\varphi_j(z))-A\nabla\varphi_j(z)|^2dz\to0.
\]

This uses the same moving x_j inside both terms; it does not assume composition continuity for arbitrary L² functions. Since B_j=P_jτ_j is symmetric, local convergence implies Aτ=τAᵀ almost everywhere, then everywhere by continuity of τ.

### 4.2 The joint boundary measure and the test-function issue

Define Λ_j=Σ_pq_jψ_{p,j}μ_j⊗δ_p with the signed one-sided convention. Its position marginal has the radial identities

\[
 \int d\Lambda_j=n-\epsilon_jE|x|^2,\qquad
 \int|x|^2d\Lambda_j=(n+2)E|x|^2-\epsilon_jE|x|^4.
\]

At each j, polynomial times the soft density is integrable, so expanding cutoffs justify radial integration. The bounds proved earlier give bounded mass and second moment, hence tightness and uniform integrability of first moments. In particular no mass can disappear at infinity.

For **g=g(x)** smooth and compactly supported, radial integration gives

\[
 \int g(x)d\Lambda_j(x,p)
 =\int[ng+x\cdot\nabla g-\epsilon_jg|x|^2]d\mu_j
 \to\int_{\partial C}g(x)h_C(\nu_C(x))d\mathcal H^{n-1}(x).
\]

This identity is for the position marginal. It is not asserted for a general direction-dependent g(x,p); that erroneous extension would indeed leave a gap. The next contact argument identifies the joint measure, and only then permits general joint tests.

On a compact neighborhood of any pair with p·x≤(1−δ)e^{a_{t_*}(p)}, the Λ_j mass is bounded by N_jq_j(1−δ/2)^{q_j} times a bounded factor, and tends to zero. Positivity is important here. Every joint subsequential limit therefore lies on contact pairs x∈∂C, p·x=h_C(p)=e^{a_{t_*}(p)}. At boundary-area-almost every x the unit normal is unique. The position marginal has density h_C(ν)>0 against boundary area and gives no mass to the exceptional set. This uniquely identifies the joint limit as

\[
 h_C(\nu_C(x))d\mathcal H^{n-1}(x)\,\delta_{\nu_C(x)}(dp).
\]

Consequently for arbitrary bounded continuous joint g one has the corresponding integral convergence; for first-growth tests use the uniform first-moment tail bound. In particular

\[
 F_j\mu_j=-\int f(p)d\Lambda_j(\cdot,p)
 \rightharpoonup-f(\nu_C)h_C(\nu_C)d\mathcal H^{n-1}|_{\partial C}.
\]

There is neither an antipodal factor two missing nor a direction-sign reversal: at a negative facet the negative signed direction alone has a positive one-sided power. Pairing the two powers recovers exactly the original even potential.

### 4.3 Adjunction across the boundary and zero trace

For g∈C_c∞, the test error contributes at most η_j||g||_{L²(μ_j)}, and the centering term contributes EF_j∫g dμ_j→0. On a compact interior subset, W_j→Ax in L² and ρ_j→1 locally uniformly. On the complement use

\[
 \left|\int_{\mathbb R^n\setminus C_\delta}W_j\cdot\nabla g\,d\mu_j\right|
 \le\|\nabla g\|_\infty(E|W_j|^2)^{1/2}
       \mu_j(\mathbb R^n\setminus C_\delta)^{1/2},
\]

where C_δ={x∈C:dist(x,∂C)≥δ}. Take j→∞ first and δ↓0 next; L¹ density convergence and zero volume of ∂C make this vanish. Thus adjunction yields

\[
 \int_C Ax\cdot\nabla g\,dx
 =-\int_{\partial C}g f(\nu_C)h_C(\nu_C)d\mathcal H^{n-1}.
\]

Interior tests first give tr A=0. The divergence theorem on a convex body, followed by density of smooth restrictions in C(∂C), then gives the boundary flux identity

\[
 Ax\cdot\nu_C(x)=-f(\nu_C(x))h_C(\nu_C(x))
 \quad\mathcal H^{n-1}\text{-a.e.}
\]

This is a proof of the limiting normal flux, not an assumption of Sobolev traces for W_j and not a weak-limit argument for a normalized score.

### 4.4 Linear algebra and global reconstruction

Choose τ₀=D²φ(0). From Aτ₀=τ₀Aᵀ, the matrix τ₀⁻¹/²Aτ₀¹/² is real symmetric. A is therefore diagonalizable over R, even when zero eigenvalues or repeated eigenvalues occur. Use one constant dual transformation to make A symmetric. One can multiply τ₀⁻¹/² by (detτ₀)¹/(2n), so the transformation is volume preserving; this avoids changing the normalized volume during the argument.

Now A commutes with D²φ everywhere. Relative to its distinct eigenspaces Eᵢ all mixed Hessian blocks vanish. Because the source domain is **all Rⁿ**, integrating along coordinate segments gives φ(z)=c+Σφᵢ(zᵢ), with linear terms included in φᵢ. Its gradient image is the product of the individual gradient images. Taking closures gives C=ΣCᵢ, each a bounded full-dimensional relative body; projections of the symmetric C make the factors symmetric and centered at zero. The normal support of a product is contained in the union of the factor subspaces, since the boundary pieces with at least two boundary factors have zero (n−1)-area.

For clarity, reconstruction from the surface-area support S does not require all normals to be regular. Let P=∩_{u∈S}{x:x·u≤h_K(u)}. S positively spans Rⁿ, so P is bounded, and K⊂P. On S their supports agree. Thus V₁(K,P)=|K|. Ordinary Minkowski's first inequality yields |P|≤|K|, and inclusion implies P=K. The same applies to L and C. This classical inequality needs no equality characterization here.

The common normal support now separates the constraints into the eigenspaces, giving K=ΣKᵢ, L=ΣLᵢ. For a normal u∈Eᵢ, Ax·u=λᵢh_C(u) on its supporting boundary. The flux relation gives f(u)=−λᵢ for surface-area-almost every such direction. Continuity, and the fact that distinct eigenspace spheres are disjoint compact sets, extends it to the entire common support in Eᵢ. Reconstruction within the factor gives Lᵢ=e^{−λᵢ}Kᵢ. Since tr A=Σλᵢdim Eᵢ=0, the normalized volume ratio is one, as required.

If A=0, there is one eigenspace and f=0 on the common support, so K=L after normalization. A scalar A also vanishes because tr A=0. Repeated eigenvalues merely merge factors; uniqueness of the finest decomposition is not claimed. Undoing the constant linear map permits nonorthogonal complementary primal blocks, and undoing endpoint normalization restores arbitrary positive dilation factors.

Conversely, after making complementary blocks orthogonal, block-direction constraints give one Wulff inclusion and Hölder gives the other:
Σcᵢᵗh_{Kᵢ}(uᵢ)≤(Σh_{Kᵢ}(uᵢ))¹⁻ᵗ(Σcᵢh_{Kᵢ}(uᵢ))ᵗ. The determinant product gives equality of the volumes. This completes both directions of E with the original quantifiers.

## 5. C: facet-centroid invariant and ridge compatibility

Index one unit normal uᵢ per antipodal true facet pair; hᵢ(t)=aᵢe^{bᵢt}, |P(t)|=Ce^{st}, and wᵢ=2hᵢAᵢ/|P| are fixed and positive by the inherited reduction. This exact positive-mass statement concerns a finite fixed equality path only.

Perturb uᵢ to uᵢ+ηr and its opposite to its negative, holding every width fixed. The source finite-slab inequality allows nonunit spanning vectors. Boundedness persists for small η. Away from the facet boundary the normal velocity is −r·x. Integrating the swept layer gives the volume derivative −2∫_{Fᵢ}r·x. To justify this at nonsimple vertices, remove a δ-neighborhood of the finite facet skeleton. Its contribution divided by |η| is O(the removed facet area)+o(1); overlaps near transverse fixed hyperplanes have order O(η²) after localization. Let η→0 and then δ→0. Facet boundaries have zero facet area. This proves the two-sided first variation without genericity.

For every η the deficit between 0,t,1 is nonnegative and at η=0 is zero. Its derivative is therefore zero, giving

\[
 \frac{c_i(t)}{h_i(t)}=(1-t)\frac{c_i(0)}{h_i(0)}
                       +t\frac{c_i(1)}{h_i(1)}.
\]

The fixed wᵢ cancels; equality for perturbed normals is never assumed.

For every independent n-tuple of signed normals a candidate vertex is linear in its exponential supports. Each feasibility event is an exponential polynomial with at most n+1 distinct rates. A nonzero such function has at most n real zeros: divide by its least exponential, differentiate, and use Rolle inductively. Identically zero events are retained as persistent incidences. Thus a finite partition into open strata exists, including paths entirely on nonsimple walls.

On a stratum, pulling triangulations express Jᵢ=∫_{Fᵢ}x dH^{n−1} as a homogeneous polynomial of degree n in the support vector. Unit normals fix the area-to-oriented-determinant conversion; signs are fixed on each nondegenerate simplex. Hence cᵢ/hᵢ=2Jᵢ/(wᵢCe^{st}) is a finite real exponential sum on any nonempty stratum. An affine exponential sum is constant: its second derivative and exponential independence eliminate every nonzero rate. Since the vector function was globally affine, its slope is zero on the whole interval. This proves C, including endpoints and persistent walls.

For the additional ridge balance, write all signed facets separately. In the hyperplane of facet k the ridge inequality has bound (h_ℓ−h_k cosθ)/sinθ. Its velocity is the stated d′_{kℓ}. The derivative of the centroid consists of the normal translation b_kh_ku_k plus the sum of boundary velocities times (ridge centroid−facet centroid), weighted by ridge area/A_k. Subtract the same calculation for uniform dilation at rate b_k, and use c′_k=b_kc_k. Multiplying by h_kA_k/|P| gives exactly I44 (3.7).

For n≥3, a ridge that disappears while all true facets survive collapses in its (n−2)-dimensional affine intersection, so its measure and first moment vanish. Surviving ridge measures and first moments converge by the fixed-plane section description. For n=2 the zero-dimensional ridge measure is one and cannot be argued to vanish by shrinking length. Instead a polygon with a fixed irredundant cyclic list of true normals has a fixed adjacency list; each vertex belongs to exactly two edges, and an adjacency change would require loss of a true edge. No such disappearance occurs on this equality path. Thus the original continuity claim is valid also in dimension two, with this distinct reason. Zero-weight nonexistent ridges should be interpreted through their moment integrals rather than assigned centroids.

The scalar support derivative formula gives the spectral identity at n. The vector balance is a further necessary identity, not a maximum principle or splitting theorem by itself. All of C passes as stated.

## 6. B: hard facet/ridge limits and the exact defect scale

Fix a single symmetric polytope with irredundant representative unit normals. Limits are q→∞ through even integers at fixed ε>0, followed by ε↓0. No facet-count-uniform constant is asserted.

Slice in the signed normal coordinate x·u=±h r¹/ᑫ. Then

\[
 q\psi^ke^{-\psi}d(x\cdot u)=h r^{k+1/q-1}e^{-r}dr.
\]

For almost every point in the limiting facet plane all other constraints are strict or violated; irredundancy excludes an identical facet plane. The remaining soft weight tends to the facet indicator. For two representatives the normals are linearly independent, and coarea gives the Jacobian hᵢhⱼ/(q²sinθᵢⱼ). Each r-kernel is r¹/ᑫe^{−r} for the ψᵢψⱼ moment, giving Γ(1)²=1 in the limit.

A full-dimensional feasible subset of the two-plane intersection is a codimension-two face, hence a ridge. A transverse two-dimensional slice of its normal geometry shows that exactly two irredundant facets contain it. This remains true for polytopes with nonsimple vertices. If the intersection is feasible only in smaller dimension, its (n−2)-area is zero and contributes zero. In n=2 the affine fiber is a point; a feasible intersection of two distinct true facets is a vertex with exactly two incident facets, so the same statement, using H⁰, is valid.

Here is an explicit domination check. For a fiber x=x₀+y with x₀ perpendicular to its linear direction,
∫e^{−ε|x|²/2}dy=e^{−ε|x₀|²/2}(2π/ε)^{d/2}, uniformly bounded over offsets. With |x|² inserted it becomes the same exponential times a fixed linear polynomial in |x₀|², also uniformly bounded. The one-dimensional kernels are bounded, uniformly for q≥2, by r^{k−1}e^{−r} on (0,1) and r^{k−1+1/2}e^{−r} on [1,∞); both are integrable for k≥1. Products handle the two-fiber case. Discarding other soft factors only increases these bounds. This proves dominated convergence for bounded continuous tests and the stated |x|² test. Z_{q,ε}→Z_ε>0 supplies normalization. Thus (4.1), including nonsimple cases, follows.

For the diagonal cancellation derive the row sum independently. Put aᵢ=Eψᵢ and R₂=E|x|². Radial integration first gives qEΣψⱼ=n−εR₂. Applied to xψᵢ it gives

\[
 qE(\psi_i\sum_j\psi_j)=(n+q)a_i-\epsilon E(\psi_i|x|^2).
\]

Subtract the product of expectations to obtain
ΣⱼCov(ψᵢ,ψⱼ)=aᵢ−(ε/q)Cov(ψᵢ,|x|²). Therefore

\[
 \sum_jD_{q,ij}=\frac\epsilon q\operatorname{Cov}(\psi_i,|x|^2).
\]

The sign and coefficient of the Gaussian correction are essential. Off-diagonal limits are q²D_{ij}→wᵢ^εwⱼ^ε−κᵢⱼ^ε. The row limits εrᵢ^ε determine the diagonal, giving I44's H_ε. Letting ε↓0 yields row sums zero and

\[
 b^TH_Pb=\sum_{i<j}\kappa_{ij}(b_i-b_j)^2
             -n\sum_iw_i(b_i-\bar b)^2,
 \quad\bar b=n^{-1}\sum_iw_ib_i.
\]

The identity Σ_{i<j}wᵢwⱼ(bᵢ−bⱼ)²=nΣwᵢ(bᵢ−b̄)² explains the normalization. Support first variations give off-diagonal logarithmic Hessian entries κᵢⱼ−wᵢwⱼ and homogeneity gives row sums zero, identifying H_P with −D²_zlog|P(eᶻ)|. Hu–Ivaki's actual C² proof covers the irredundant domain across walls. No differentiation of a pointwise soft-volume limit is used.

For b≠0, B_ε=Σwᵢ^εbᵢ²>0. Since qEψᵢ²→wᵢ^ε while all distinct cross-products are O(q⁻²), qVar(Σbᵢψᵢ)→B_ε. The centered normalized score has signed-measure total variation O(q⁻¹/²) and its squared measure converges to Σbᵢ²βᵢ^ε/B_ε. Its unit L² mass is on the actual boundary; there is no nonzero bulk limit.

With A_q=diag(aᵢ), C_q=Cov(ψ), D_q=A_q−C_q, direct matrix multiplication gives

\[
 C_qA_q^{-1}C_q=A_q-2D_q+D_qA_q^{-1}D_q,
\quad
 d_q=\frac{b^T(D_q-D_qA_q^{-1}D_q)b}{b^TC_qb}.
\]

A_q⁻¹=O(q), D_q=O(q⁻²), so the second numerator term is O(q⁻³), while the denominator is B_ε/q+o(q⁻¹). Hence qd_q→bᵀH_εb/B_ε, and the subsequent ε limit is exactly I44 (4.6). In particular d_q→0 for **every** nonzero slope, including strict directions. The zero slope has no defined normalized score and is excluded as in I44. This is a method obstruction at leading normalized order, not a counterexample to E or K.

## 7. Q: the full planar equality-class distance

Take P_δ(s) with widths (eˢ,e⁻ˢ,2−δ), δ=t, K_t=P_t(−t), L_t=P_t(t). For all sufficiently small positive t and |s|≤t, |eˢ−e⁻ˢ|<2−t<eˢ+e⁻ˢ, so all six facets are true. Their fixed cyclic normals give a common planar fan. On each cone between adjacent normals, support is a fixed positive linear combination of the two corresponding widths. Hölder applied to that combination proves that the body formed from the three midpoint facet widths satisfies every interpolated support constraint. The facet constraints prove the reverse inclusion. Therefore the **full** Wulff midpoint is P_t(0), not merely a finite-slab outer approximation.

The removed-corner triangle formula gives |P_δ(s)|=4−(2cosh s−2+δ)². Thus

\[
 \Delta_{1/2}(K_t,L_t)
 =\log\frac{4-t^2}{4-(t+2\cosh t-2)^2}
 =\tfrac12t^3+\tfrac14t^4+O(t^5).
\]

The stronger displayed expansion is only a diagnostic refinement of the original O(t⁴) statement. Both endpoints are O(t) from the square, giving the upper distance bound by the equality pair consisting of that square twice.

For the lower bound the planar block class has only two types: a homothetic pair of arbitrary symmetric bodies, or two parallelograms with common side directions and independent factor lengths. This enumeration follows from the dimensions of complementary subspaces, independently of the newly audited E; it also agrees with the known planar equality theorem.

For any homothetic comparison pair, the determinant of its two coordinate-support vectors is zero. For our pair it is e⁻²ᵗ−e²ᵗ=−4t+O(t³). If the comparison pair is within a fixed small Hausdorff distance, its four supports are bounded, and the determinant difference is at most a fixed constant times that distance. Hence distance≥ct. A comparison pair outside that neighborhood has a fixed positive distance, which is already ≥ct for small t. No bound is imposed on the comparison bodies beforehand.

For parallelograms it suffices to bound the distance from either endpoint to **every** centered parallelogram, a larger comparison class than the actual paired one. If Q_j→[−1,1]² are parallelograms, write Q_j={±a_j±b_j} by their vertices. The vectors a_j,b_j are bounded because they are half vertex sums/differences. Every subsequential limit represents the square. It is nondegenerate, and uniqueness of the two edge directions of the square forces those limiting vectors to be its two coordinate half-edges, up to signs and interchange. Thus the corresponding vertex normal cones contain the three fixed interior first-quadrant vectors
v=(1,½), w=(½,1), v+w=(3/2,3/2) for all sufficiently close Q. Consequently h_Q(v)+h_Q(w)−h_Q(v+w)=0. This argument includes rotations and shears.

For the hexagon H with widths a,b,c, these supports are (a+c)/2, (b+c)/2, and 3c/2. Their defect is (a+b−c)/2∼t/2. Support-function Lipschitz control yields

\[
 d_H(H,Q)\ge\frac{a+b-c}{2(\sqrt5+3\sqrt2/2)}.
\]

Parallelograms outside a fixed neighborhood of the square have distance from H bounded below independently of t; they also satisfy an order-t lower bound. Taking the infimum over all homothetic pairs and all allowed parallelogram pairs proves d_𝓔(K_t,L_t)≍t, with no restriction on the sizes or orientations of the comparison bodies.

Thus Δ/d_𝓔²→0 and more generally Δ/d_𝓔^α→0 for α<3. This proves an obstruction, not the existence of a bound at exponent three (or any finite exponent). Compactness after E yields only a qualitative modulus. Q passes independently of any unresolved quantitative regularity issues in E.

## 8. Evidence, diagnostics, and handoff

The new `check.py` passes **81 exact assertions** using independently constructed tests: general third-order tensors; a nonorthogonal constant dual transformation; complete Gaussian integration of the unnormalized identity with mixed-sign coefficients and quartic v; a matrix-square/HS-square negative control; the nonzero Gaussian row correction for correlated slabs; the exact matrix dual defect; one- and two-fiber Gamma Jacobians; nonsimple octahedron incidences; independently enumerated hexagon vertices and the normal-variation derivative of their shoelace area; rotated/sheared parallelogram support witnesses; signed boundary flux and radial marginal integrals; and the cubic family. The polynomial Gaussian tests admit integration by parts by Gaussian decay, or compact cutoffs; they are diagnostics, not a change to the compact-test source contract. The script does not merely reproduce the author's identities by substituting their printed right-hand sides.

The analytic arguments in §§2–7, not those finite tests, establish compactness, convergence of measures, and universal quantifiers. Source and report hashes establish provenance, not mathematical truth. The original I44 verifier and its unchanged I43 replay pass, with 245 and 125 sealed artifacts respectively and 200 and 2,365 exact assertions. The current I44 replay reports changes to its four mutable shared ledgers; I43 retains its two historical mutable ledger drifts. These are distinct from immutable discrepancies, of which there are none. I45 freezes **386 inputs**, with no drift at this handoff, and marks all four live shared ledgers mutable. There are **13 successful fresh responses**, including three matching pinned blobs, **16 read-passage records**, seven pinned-operation contracts, and seven external applicability contracts.

Run from the project root:

```sh
python frontier/experiments/i45_logarithmic_equality_r2/check.py
python frontier/experiments/i45_logarithmic_equality_r2/verify.py
```

The sealed source directory records current responses (including retrieval failures if any), version bindings, exact read passages, selected source contracts, the complete inherited evidence, and the full brief. `verify.py` is read-only: it checks the exact artifact set, hashes, live immutable inputs, all 9,340 ignored corpus files against the complete pinned inventory, selected Git blobs, current-response hashes, read extracts, and reproducible exact diagnostics. It replays original verifiers without modifying their files or seals.

**Parent disposition:** E is technically closed by the attributed symmetric reduction under the accepted OpenAI operations; C, B, and Q pass their original claims. None is a seventh substantial finding. The unrestricted pointwise kernel K and positive finite-exponent stability remain unproved. Only the authorized I45 report/source/experiment paths were written; no staging, commits, publication, shared/prior edits, or further agents were used.
