# I68 — independent contribution and prior-art audit of C66

**Verdict: TECHNICAL ONLY for the full original C66.** The completed I67 report states **PASS ORIGINAL WITHOUT REPAIRS**; its proof decision is distinguished from this contribution decision. Aggregate evidence replay separately retains **FAIL_REFERENCE_DRIFT** for a parent bookkeeping wrapper, with core checks PASS and an exact reconstruction of the historical bytes (Section 6). This is not a KNOWN verdict: no inspected primary theorem literally gives the periodic, defocusing, open-set statement. Nor is it a GAP verdict. The reduction below reaches that statement using the pinned source's actual torus evolution and degree operations, finite-regularity composition, logarithmic amplitude normalization, and classical phase modulation. It does not assume C66's stable graph or its conclusion. The author report and its seals are unchanged. The alternative argument here is a contribution-reduction certificate, not a repair inserted into the author's proof.

The most relevant additional prior art is Nguyen–Zaag's treatment of precisely a power divided by a logarithm in a heat equation. Its amplitude correction, small-amplitude split, and polynomial decay budgets precede C66. Its heat estimates do **not** transfer to Schrödinger evolution. The latter input comes from the stipulated torus source. A second decisive observation is that a nonlinear phase slice removes the neutral direction before constructing the graph. Consequently no new quantitative torus spectral-transfer theorem, and not even C66's special-column estimate, is necessary for the conclusion.

All statements **and proof operations** in `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are true premises here. No upstream truth audit is made. Eight accepted findings remain R006, R008, R009, R010, R011, R012, R013, R014; this child neither changes their count nor evaluates I65.

## 1. Frozen scope and the exact assertion

The [current review brief](../sources/i68_logarithmic_blowup_novelty/current-review-brief.txt) includes the full original assignment and all supplied objections. The separate [original full brief](../sources/i68_logarithmic_blowup_novelty/original-full-brief.txt) is byte-identical to I66's original archive. [References](../sources/i68_logarithmic_blowup_novelty/references.json) bind the complete author report, verifier, seal and old evidence by SHA-256 rather than recursive copying. The four current mutable ledgers are separately captured. Historical I07/I36/I37 and I52/I54/I57/I58 outcomes remain binding context: a complete and useful consequence can still be technical. I56's fixed-dimensional entropy reduction supplies another explicit instance of the same standard.

C66 asserts existence of a sufficiently large **odd** p≥201, k=⌈3p/4⌉, a source profile Q and frequency b, and κ*>0, such that for **every real** |κ|≤κ* there is a nonempty open subset of H^k(T¹²;C) whose solutions to

\[
 i u_t+\Delta u=|u|^{p-1}u\left(1+\frac{\kappa}{\log(2+|u|^2)}\right)
 \tag{C}
\]

blow up at a finite T. With a=1/(p−1), σ=log(1/(T−t)), S=log(1/T), s=σ−S, L=e^{σ/2}, a suitable center and a **constant limiting phase** satisfy

\[
 (T-t)^a((T-t)/T)^{-ib}e^{-i\theta}
 u(t,x_*+\sqrt{T-t}\,y)
 =c_\kappa(\sigma)(Q_\sigma+v),\quad
 c_\kappa=(1+\kappa/(2a\sigma))^{-a},\quad
 Q_\sigma=\chi(y/L)Q,
 \quad\|v\|_{Y_L}=O(\sigma^{-1}).
 \tag{1}
\]

In particular the normalized center amplitude tends to |Q(0)|>0. The physical solution has the stated C H^k and C¹ H^{k−2} regularity until T. Constants depend on the fixed p and profile. This is neither arbitrary κ, arbitrary p, a general metric/potential perturbation theorem, nor an asymptotic expansion identifying the first coefficient of v.

The spaces are exactly the source's Y=Ḣ^{6−a}∩Ḣ^k and

\[
 \|f\|_{Y_L}^2=(2\pi L)^{12}\sum_m
 \big[(L^{-2}+|m/L|^2)^{6-a}+|m/L|^{2k}\big]|f_m|^2.
 \tag{2}
\]

A constant z has norm (2π)^6 L^a|z|. Q is nonvanishing with symbol tail ⟨y⟩^{−2a}, and is not assumed L². No unregularized torus norm is substituted below.

## 2. Actual antecedent operations and their limits

**Pinned torus manuscript B.** `profiles.tex`, `profile:inner`, `profile:amplitude`, `profile:exterior-pressure` supply the inner barrier and exterior smallness used below. `linear.tex`, `lin:spatial`, `lin:k-choice`, `linear:decay`, and `linear:torus` provide the uniform algebra/localization, actual stable semigroup decay, and expanding-torus step contraction. `nonlinear.tex`, `nl:residual-formula`, `nl:step`, `nl:forward`, `nl:coordinates`, `nl:graph`, `nl:parameter-expansion`, and `nl:degree-map` provide cutoff forcing, full slab estimates, forward/backward graph construction, strong parameter continuity and the physical open-set argument. These complete operation interfaces were read, not just the main theorem. Source main and spectral-classification statements were also read; the stipulated spectral proof was not re-audited. Immutable paths, Git blobs and exact passage ranges are in [passages.json](../sources/i68_logarithmic_blowup_novelty/passages.json).

**Buck–Carballeira–Gómez-Serrano–Shi.** The current v1 treats radial whole-space pure powers at (d,p)=(3,27),(4,9),(5,7). Proposition 4.8 and its complete proof prescribe stable data, cancel all nonstable components by a backward integral, and obtain exponential decay. Its finite-dimensional localization selects compactly supported data. It does not identify all unstable modes as symmetries, prove the present open set, or absorb a logarithmic perturbation with those exponential weights. This is an antecedent for the graph operation, explicitly acknowledged by B itself. [Primary text, §4.3](https://arxiv.org/html/2609.23685v1).

**Li.** The current v2 treats focusing mass-supercritical, energy-subcritical pure powers. Theorem 1.4 uses mode stability; §6.3 computes the symmetry directions and solves the initial-data matching equation by Brouwer. Theorem 1.5 adds the energy-space setting. The full §6.3 proof differentiates the smooth reference, controls the perturbed datum continuously, and matches the number of symmetry parameters to the spectral codimension. Its scaling-symmetry step cannot be copied into (C). B's exact physical change of variables, retaining the σ-dependent coefficient, is the applicable operation. [Primary text](https://arxiv.org/html/2304.02078v2).

**Cao-Labora–Gómez-Serrano–Shi–Staffilani.** Current v1, Theorem 1.1, equations (1.20)–(1.27), and §3.7 were inspected. The periodic result is d=8, p=3, hydrodynamic implosion with spatial scale (T−t)^{1/r}, r>2, and finite codimension. The damped density profile includes a positive exterior term. Its cutoff and unstable-mode selection precede C66, but it neither has the same scaling/norm nor supplies an open H^k set for (C). [Primary text](https://arxiv.org/html/2410.04532v1).

**Donninger–Wallauch.** Current v1, assumptions (1.5)–(1.7), Lemma 3.2, and the complete §4 modulation, correction and time-selection arguments were read. Its complex radial 3D focusing wave equation is genuinely equation-robust. The perturbation growth q<p makes its similarity forcing exponentially small. For κ≠0, r^p/log(2+r²) divided by r^q diverges for every q<p. Its theorem therefore cannot be cited as covering (C). Nevertheless §2.2 and §4.1 already separate a convergent phase from the remaining perturbation; §4.2 cancels the positive mode backwards, and §4.3 selects physical blowup time continuously. The phase-slice reduction below is a discrete implementation of this modulation operation, not an application of its wave theorem. [Primary text](https://arxiv.org/html/2006.04600v1).

**Nguyen–Zaag: strongest logarithmic methodological antecedent.** Current v4, equation (3), includes h(u)=μ|u|^{p−1}u/log^γ(2+u²) for every γ>0, hence γ=1. Theorems 1–2 concern a real heat equation, Sobolev-subcritical powers and an open W^{1,∞} neighborhood. Equation (12) multiplies the profile by φ(s)/K_p. Appendix A.1 splits exponentially small amplitudes from the logarithmic region; A.2 gives φ/K_p=(1+η_γ)^{−1/(p−1)} with η_1∼μ(p−1)/(2s). Appendix B.1 explicitly cancels the leading logarithmic correction; C.1 proves the resulting profile-error bounds. Proposition 3 and the ensuing proof use different polynomial component budgets and degree. These actual calculations, including the remainder proofs, are more relevant than a generic robustness slogan. The heat kernel, Gaussian norm and √s core are not imported into C66. [Primary v4](https://arxiv.org/html/1406.5233v4).

The ODE proof cited by Nguyen–Zaag was followed to Nguyen, current v4 of 1404.4018, Appendix A, Lemmas A.1–A.3. Dividing the amplitude ODE by φᵖ makes φ¹⁻ᵖ solve a scalar linear equation, with correction η(s)=∫ₛ^∞eˢ⁻ᵗg(t)dt. Its complete proof was read. That paper’s PDE hypotheses require γ>1; the elementary ODE operation survives at γ=1, which the later construction explicitly treats. The related 1410.4079v1, Appendix A, repeats the amplitude formula and verifies cancellation in the linear coefficient. These are methodological antecedents, not stronger Schrödinger theorems. [Earlier ODE proof](https://arxiv.org/html/1404.4018v4), [later companion](https://arxiv.org/html/1410.4079v1).

**Other controls on overclaiming.** Hamza–Saidi's current v1 allows logarithmic wave perturbations with γ>1 in a subconformal real wave problem; it is not the γ=1 endpoint or a Schrödinger theorem. [Primary](https://arxiv.org/html/1311.7479v1). Le Coz–Martel–Raphaël's current v1 treats focusing mass-critical NLS plus a strictly lower power; Proposition 3's full construction solves profile corrections with spectral solvability parameters and controls the tail remainder. It demonstrates that nonhomogeneous NLS blowup and asymptotic profile correction are established subjects, but its minimal-mass threshold, exponentially localized Q, and changed blowup law do not imply C66. [Primary](https://arxiv.org/html/1406.6002v1). Bento–Silva's current v2, Theorem 2.1 and its integral-graph proof, permit general nonautonomous growth rates. Its hypotheses include an invariant dichotomy, a bounded time-dependent generator and f(t,0)=0; these cannot simply be asserted for C66's raw forced equation on varying tori. I use the explicit recursions below instead. [Primary](https://arxiv.org/html/1007.5039v2).

## 3. Full-scope technical reduction

This section is independent of the truth of I66's claimed graph theorem. It uses B plus explicit estimates. The elementary scalar normalization is the same one as C66, because the leading slowly varying coefficient determines it. The pressure estimate and neutral-mode handling are different and provide useful tests of whether the claimed bridge is indispensable.

### 3.1 Pay k<p directly from the source barriers

B's inner construction has h_b>.999, r_b²<11, b<.335, and h_b≤A≤.5^a<1. Its actual amplitude formula therefore gives throughout the inner ball

\[
 \frac{w(r)}r=(6-2a)A(r)^{-2}\int_0^1 A(rt)^2t^{11}\,dt
 \ge\frac{6-2a}{12}(.999)^2.
\]

For 0<a≤1/1000,

\[
 V=b+r^2/16-w^2/4
 \le .335+11\left[\frac1{16}-\frac14
 \left(\frac{6-2/1000}{12}(.999)^2\right)^2\right]
 <.34.
 \tag{3}
\]

The last strict inequality is rational arithmetic, also checked independently in diagnostics. At a maximum of A in the interior, −ΔA+PA=VA gives P≤V. If the maximum is at the boundary, P=h_b^{1/a} is uniformly small for sufficiently small a, by the source's uniform boundary gap. Its exterior-pressure operation makes P small for r≥r_b. Thus ||P||∞≤17/50 follows without a new limiting-profile argument. This is an extraction of the lower proof operations, not of the weaker printed P≤1 alone.

Now choose an odd p sufficiently large that a=1/(p−1) obeys all source restrictions and (3); p≥1001 is a harmless additional sufficient threshold, not an assertion that p=1001 is source-admissible. With k=⌈3p/4⌉,

\[
 k-(7-2a+.68p)\ge .07p-7+2a>0,
 \qquad k+3\le .75p+4<p.
\]

This pays B's exact condition k>max{8,7−2a+2p||P||∞}. It preserves C66's existential p and exact k, with no uniform-in-p estimates. The pressure optimization is technical, not a separate finding.

### 3.2 A uniform scalar estimate pays the expanding-domain tail

Let N(z)=|z|^{p−1}z and F(V)=iΔV−(D/2+a)V+ibV−iN(V). The exact substitution U=c_κ(σ)V gives V_s=F(V)+H_σ(V), where

\[
 H_\sigma(z)=-\frac{c'}c z
 -i\frac{\kappa}{1+\kappa/(2a\sigma)}
 \left[\frac1{\ell_\sigma(z)}-\frac1{2a\sigma}\right]N(z),
 \quad \ell_\sigma(z)=\log(2+e^{2a\sigma}c^2|z|^2),
 \quad\frac{c'}c=\frac{\kappa}{2\sigma^2(1+\kappa/(2a\sigma))}.
 \tag{4}
\]

For each fixed disk, all real derivatives of H_σ through order k+3 are O(|κ|σ^{−2}). Here is the actual estimate rather than a core-only expansion. For r=|z|≥e^{−aσ/2}, ℓ≥aσ−C, |ℓ−2aσ|≤C(1+|log r|), and j derivatives of ℓ are bounded by C_j r^{−j}. Differentiating the product in (4) yields C_m|κ|σ^{−2}r^{p−m}(1+|log r|). Since m≤k+3<p, this is bounded. For r<e^{−aσ/2}, bounded Euler derivatives of 1/log(2+q²), q=e^{aσ}cr, bound the nonlinear part by C_m|κ|r^{p−m}, exponentially small in σ; the linear part is separately O(|κ|σ⁻²). The maps are smooth at zero for every fixed σ. Also H_σ(0)=0. This is the same small/large amplitude mechanism as the logarithmic antecedent, with the finite number of derivatives needed here made explicit.

For completeness, passage from this scalar estimate to (2) does not use an expanding-volume L² bound. Use periodized Littlewood–Paley kernels with uniform L¹ norms, frequencies 2^j≥L^{−1}, and the bottom block containing zero. Telescope H(S_{j+1}f)−H(S_j f). Its coefficient is an averaged DH; m=k+1 derivatives are bounded by C_R h 2^{mj}, where h bounds the C^{k+3} norm of H and ||f||∞≤C_R. The projection to output frequency 2^ℓ is bounded in L² by C_R h 2^{−m(ℓ−j)_+}||Δ_j f||₂. Weighted summation is bounded for both s=6−a and s=k because 0<s<m. The lowest block has its initial weight L^{−s}, and separately

\[
 L^{-(6-a)}\|H(f)\|_2\le hL^{-(6-a)}\|f\|_2.
\]

Thus ||H(f)||_{Y_L}≤C_R h||f||_{Y_L}. For differences, use (f−g)∫DH(g+t(f−g))dt, split off DH(0), and apply the same calculation to DH−DH(0), together with B's algebra estimate. An extension by a fixed disk cutoff and smooth Fourier approximation justify the computation. All constants are independent of L≥1; in particular the constant mode is retained. B supplies the uniform bound for Q_σ. Consequently H_σ(Q_σ+v) and its local Lipschitz constant are O(|κ|σ^{−2}) on a fixed perturbation ball. This standard finite-regularity composition argument is additional to B's polynomial algebra, but does not require a new weighted resolvent or a new tail estimate for Q.

### 3.3 Slab maps and an exact phase slice

Take B's fixed long step M, σ_n=S+nM, L_n=e^{σ_n/2}. Abbreviate Q_{σ_n}, E_{L_n}, π_{L_n}, P_{L_n} by Q_n,E_n,π_n,P_n. Their real symmetry columns have eigenvalues 0, twelve copies of 1/2, and 1. Let π_n^0 be the phase row and π_n^+ the other rows. B gives π_nE_n=I, uniform boundedness, stable contraction 1/8, and

\[
 e_n=\pi_{n+1}\mathcal F_n-e^{M\Lambda}\pi_n\longrightarrow0
\]

uniformly after increasing S. No rate is assigned to this operator.

The source's fixed-slab Duhamel/Gronwall proof applies to (4), with

\[
 v_{n+1}=\mathcal F_n v_n+h_n(v_n),\qquad
 \|h_n(0)\|\le C_M f_n,\quad
 \operatorname{Lip}_{\|v\|\le d}h_n\le C_M(d+f_n),
 \quad f_n=|\kappa|\sigma_n^{-2}+e^{-(1+a/2)\sigma_n}.
 \tag{5}
\]

The residual exponent is exactly B's L_n^{−2−a}. The proof is contraction on finitely many uniform short subslabs, followed by the source difference estimate. There is no finite-speed or whole-space-to-torus substitution.

Rather than putting the phase coordinate into a backward sum, work on the **nonlinear phase slice**. For z with π_n^0 z=0 define

\[
 W_n(z)=Q_{n+1}+\mathcal F_nz+h_n(z),\qquad
 \pi_{n+1}^0(e^{-i\beta_n(z)}W_n(z)-Q_{n+1})=0.
 \tag{6}
\]

At z=0 and f_n=0 the derivative of the scalar left side with respect to β is −π_{n+1}^0(iQ_{n+1})=−1. At small z,f_n it remains uniformly separated from zero, since Q_n and π_n are uniformly bounded. The one-dimensional implicit equation therefore defines a unique small real β_n, continuously in scale and locally Lipschitz in z. Taylor expansion in this scalar, with the same bounds for differences, gives

\[
 \beta_n(z)=\pi_{n+1}^0\mathcal F_nz+O_M(f_n+\|z\|^2)
           =[e_nz]_0+O_M(f_n+\|z\|^2).
 \tag{7}
\]

Set J_n=I−iQ_nπ_n^0. The sliced map is

\[
 z_{n+1}=J_{n+1}\mathcal F_nz_n+r_n(z_n),\quad
 \|r_n(0)\|\le C_Mf_n,\quad
 \operatorname{Lip}_{\|z\|\le d}r_n\le C_M(d+f_n).
 \tag{8}
\]

Indeed expand e^{−iβ}(Q'+Fz+h)−Q': its linear correction is −iQ'π^0Fz, while the remaining terms are O(f_n+||z||²), with the asserted difference estimate. This derivation uses no arbitrary-input quantitative defect bound and no unproved normal-form resolvent.

Crucially, both F+H_σ and the actual normalized slab flow are **exactly gauge equivariant**. Hence if V_n=e^{iα_n}(Q_n+z_n), its next value is e^{iα_n}W_n(z_n); equations (6)–(8) yield the exact reconstruction α_{n+1}=α_n+β_n(z_n). The sliced dynamics do not depend on α_n. This is why a potentially nonsummable e_nα_n term never appears. It implements the earlier complex-wave phase-modulation operation with B's torus coordinates.

### 3.4 Only hyperbolic graph coordinates remain

Write z_n=w_n+E_n^+u_n, with π_nw_n=0. As π_n^+iQ_n=0 and (I−P_n)iQ_n=0, (8) gives precisely

\[
 w_{n+1}=A_nw_n+B_n^+u_n+(I-P_{n+1})r_n(z_n),
\]
\[
 u_{n+1}=D_+u_n+[e_nz_n]_++\pi_{n+1}^+r_n(z_n),
 \quad D_+=\operatorname{diag}(e^{M/2},\ldots,e^{M/2},e^M).
 \tag{9}
\]

Prescribe w_0 and use B's forward equation and the backward positive-coordinate sum

\[
 u_n=-\sum_{j=n}^{\infty}D_+^{n-j-1}
 \big([e_jz_j]_++\pi_{j+1}^+r_j(z_j)\big)
 \tag{10}
\]

in the single weighted norm sup_n σ_n²(||w_n||+K|u_n|). This is a Banach space on the sequence of source subspaces, not a claim that the source π_n commute with the evolution. The elementary kernel bound is

\[
 \sigma_n^2\sum_{j\ge n}e^{-M(j-n+1)/2}\sigma_j^{-2}
 \le\frac{e^{-M/2}}{1-e^{-M/2}}.
 \tag{11}
\]

For the forward terms, (σ_{n+1}/σ_n)²≤2 once S is large. Choose K so that 2(1/8+C_M/K)<1/2; then enlarge S so that C_{M,K}sup||e_n|| is small. On a sequence ball of radius δ, ||z_n||≤Cδσ_n^{−2}; (8) makes the nonlinear Lipschitz cost at most C_{M,K}(δ/S²+|κ|/S²+o(1)). The zero-input forcing has weighted norm O_{M,K}(|κ|+S²e^{−cS}), c=1+a/2. Choose δ small, S large and κ* small, and impose S²||w_0||≤c_1δ with a sufficiently small fixed c_1. These choices make the entire forward/backward map a strict contraction of the ball. Consecutive backward sums telescope to (9). Thus there is a continuous positive-coordinate graph \(\widetilde G_{S,\kappa}\), with

\[
 |\widetilde G_{S,\kappa}(w_0)|
 \le C\left(\|w_0\|+\frac{|\kappa|}{S^2}+e^{-cS}\right),
 \qquad \|z_n\|=O(\sigma_n^{-2}).
 \tag{12}
\]

Equation (7) now gives β_n=O(σ_n^{−2}). Consequently α_n converges, with

\[
 |\alpha_\infty-\alpha_n|\le C\sum_{j\ge n}\sigma_j^{-2}
 \le C\left(\frac1{M\sigma_n}+\frac1{\sigma_n^2}\right).
 \tag{13}
\]

This is the entire neutral loss. No sum Σe_j/σ_j is used. The source finite-slab estimates extend the bound to every similarity time: interpolate α between its endpoint values, whose differences are O(σ_n^{−2}), and apply (5) and gauge equivariance to the shape. Rotating by the limiting constant phase gives
\(e^{-i\alpha_\infty}V=Q_\sigma+v\) with ||v||_{Y_L}=O(σ^{−1}), because multiplication by a constant phase is isometric and Q_σ is uniformly bounded in (2).

Joint strong continuity in S, κ and w_0 follows from B's finite-slab continuity, the scalar slice equation, and iteration of the uniformly contracting sequence map. Each fixed-coordinate tail in (10) is geometric and uniform on compact S ranges; the phase tail (13) is uniformly summable. No operator-norm continuity in Schrödinger time is required.

### 3.5 Physical parameters give an open set, not only finite codimension

Set T_0=e^{−S_0} and use the author's smooth physical reference
\(u_{\mathrm{ref},\kappa}=T_0^{-a}c_\kappa(S_0)\chi(x)Q(x/\sqrt{T_0})\).
For d'=(θ_0,ζ,β), take T=T_0e^β, x*=√T_0 ζ, S=S_0−β. The exact starting field is

\[
 v_0=e^{-i\theta_0}T^ac_\kappa(S)^{-1}
 u_{\mathrm{in}}(x_*+\sqrt T\,y)-Q_S.
\]

B's parameter-expansion proof applies with the extra scalar c_κ(S_0)/c_κ(S). Formula (4) bounds its variation by O(|κ||β|/S_0²). Thus, uniformly for |d'|≤ρ≤1,

\[
 v_0=E_LCd'+r,\quad Cd'=(-\theta_0+b\beta,\zeta,\beta),
 \quad\|r\|\le C(\rho^2+e^{-S_0/2}\rho+|\kappa|\rho/S_0^2+\varepsilon_{\rm data}),
 \tag{14}
\]

where ε_data=C(T_0)||u_in−u_ref,κ||_{H^k}. This differentiates only the smooth reference. The perturbation datum is handled by bounded, strongly continuous translations and dilation.

Use the 14-dimensional degree map

\[
 \Phi(d')=\big(\pi_L^0v_0,
 \pi_L^+v_0-\widetilde G_{S,\kappa}((I-P_L)v_0)\big).
 \tag{15}
\]

At a zero the initial field already belongs to the phase slice, and its positive coordinates lie on (12). Exact normalization π_LE_L=I gives (I−P_L)v_0=(I−P_L)r throughout the parameter ball. Hence

\[
 |\Phi-Cd'|\le C(\rho^2+e^{-S_0/2}\rho+|\kappa|\rho/S_0^2+
 \varepsilon_{\rm data}+|\kappa|/S_0^2+e^{-cS_0}).
 \tag{16}
\]

To check compatibility explicitly, choose a small d>0 and ρ=d/S_0. First take d so small that Cd²<c_1δ/4. Next enlarge S_0 for the graph, for exponentially small terms, and for the errors in (16) divided by ρ. Reduce κ* for the graph forcing and the remaining boundary errors. Finally choose a **positive** H^k radius so that both S_0²ε_data<c_1δ/4 and Cε_data≪ρ. Equation (14) then puts every stable argument in the graph domain S²||w_0||≤c_1δ, including interior points. Equation (16) is smaller than the smallest singular value of C times ρ on the boundary. B's straight-line degree homotopy supplies a zero for every datum in that physical open ball.

Reconstruct the actual normalized solution with α_0=0. Its limiting phase is absorbed by θ=θ_0+α_∞, giving exactly (1). The changes of variables have been derived for each T separately; no scaling symmetry of the nonhomogeneous equation is invoked. Finite-slab equivalence to physical H^k and the finite-regularity composition estimate give local well-posedness and uniqueness, and continuation for every t<T. Finally Q(0)≠0, c_κ→1, and (2)'s uniform L∞ embedding give the center limit and rule out continuous H^k extension. This completes the full-scope reduction.

## 4. What remains attributable to C66

The profile, its spectrum, stable torus contraction, norm, cutoff residual and physical degree mechanism belong to B. The basic forward/backward stable graph belongs to classical Lyapunov–Perron theory and is explicitly present in B and Buck et al. Symmetry matching has the inspected Li antecedent. Scalar renormalization of a logarithmically perturbed blowup profile and adjusted polynomial component budgets have the inspected Nguyen–Zaag antecedent. Finite-regularity composition is the usual Littlewood–Paley/Moser operation; its verification in the exact norm is necessary but technical. The general asymptotic-correction method is not new; the inspected NLS double-power construction also uses it.

C66's worthwhile work is checking their compatibility in this particular defocusing periodic setting. The all-input bound (4), rather than a compact-profile expansion, is a useful formulation. But its proof is the existing small-amplitude split plus differentiation with m<p, and the source gives enough freedom to arrange m<p. The phase difficulty is real for an unchanged exponential graph, yet disappears under exact gauge modulation before the standard graph is built. The altered parameter radius is then ordinary source degree bookkeeping. None requires a new spectrum, a new dispersive estimate, a new torus transfer rate, or a new tail-preserving resolvent. At the established project standard, the combined construction remains a technical equation extension.

The strongest argument for SUBSTANTIAL is that (C) changes the constitutive law at asymptotically the same power and is not a theorem-level corollary of any single cited paper. That statement is correct, but insufficient here: Section 3 gives the concrete noncircular reduction through the paid lower operations, including phase, cutoff, k, domain norm and open physical set. New exact wording and a new parameter family do not by themselves meet the nonroutine gate. No worldwide-priority conclusion follows in either direction.

## 5. Correctness boundaries and unresolved objections

This is a contribution audit, not I67's full original-proof decision. Section 3 was derived while that review was pending. Before handoff, the separately authored I67 report was observed to state **PASS ORIGINAL WITHOUT REPAIRS** for the full original C66. Its earlier [observed snapshot](../sources/i68_logarithmic_blowup_novelty/i67-observed-report.md) and [timestamp/hash record](../sources/i68_logarithmic_blowup_novelty/i67-observation.json) are preserved. The subsequent [dependency update](../sources/i68_logarithmic_blowup_novelty/dependency-update.txt), completed [I67 report](i67-logarithmic-blowup-r2.md), peer verifier and parent drift audit were read and separately hash-bound. The peer verifier reproduces core PASS, 3,108 exact and 117 decimal assertions, with its intentional aggregate FAIL_REFERENCE_DRIFT retained. That proof approval does not alter this contribution verdict. The alternative phase-slice proof is not retroactively substituted for any line of the author report.

The original phase-column claim has the right source interface: B linearizes at χQ, with potential χ^{p−1}DN(Q). Gauge differentiation therefore makes iQ_σ an approximate linear solution with the same cutoff residual, yielding the special Duhamel bound. This does **not** produce a rate on all e_n. I found no material new correctness objection in the interfaces examined for contribution; full original correctness remains I67's responsibility.

Construction II remains a **compact approximate-orbit construction**, not a second complete PDE proof. The identity AQ=−iN(Q)/a makes the leading forcing phase-orthogonal and gives q_1=−κQ/2; it is not an unavoidable logarithmic phase resonance. Its global weighted-resolvent and nonlinear-tail estimates remain unpaid. Section 3 uses neither, and their absence is not a gap in Construction I. Similarly, A's broad variable-metric wave target remains rejected only in its stated broad scope (positive cone curvature, not a new positive-sectional-curvature assertion), and B's fractal endpoint remains open at the unsupplied p-threshold and spatial-measure/tree interface. They contribute no additional finding.

## 6. Evidence, reproducibility and search limits

The complete tree has 13,223 entries and 749 manuscripts. All 9,340 ignored cached corpus files were enumerated with `rg --files --no-ignore`; their pinned Git blobs are verified by the unchanged I66 verifier. New corpus searches use the full fixed corpus domain and preserve line **multisets**, including multiplicity, in [searches.json](../sources/i68_logarithmic_blowup_novelty/searches.json). Title and mechanism searches are discovery aids, not a claim to have semantically read every manuscript. Relevant B operations and the specified primary interfaces were read in full; other primary papers were read at the exact comparison interfaces stated above, not represented as fully audited proofs.

Current unversioned arXiv pages were independently retrieved. They identify Buck v1, Li v2, Cao-Labora et al. v1, Donninger–Wallauch v1, Nguyen–Zaag v4, Hamza–Saidi v1, Bento–Silva v2 and Le Coz–Martel–Raphaël v1; the two additional heat companions are 1404.4018v4 and 1410.4079v1. The version passages are bound in [current-versions.json](../sources/i68_logarithmic_blowup_novelty/current-versions.json). Initially retrieved Nguyen v1 and Bento v1 are retained and superseded by the current versions. Three new pinned raw responses for B's profiles, linear evolution and nonlinear proof match the immutable Git blobs. Old Donninger–Wallauch v2 404 and institutional-mirror 502 remain retained through their original response hashes; no content is attributed to failures. Response headers, times, exact bytes, version passages and text extraction replays are in [primary evidence](../sources/i68_logarithmic_blowup_novelty/primary/).

The bounded web search covered logarithmic and nonhomogeneous NLS blowup, robust wave perturbations, strongly perturbed heat blowup and nonautonomous graph methods, using the [recorded queries and limits](../sources/i68_logarithmic_blowup_novelty/web-search-scope.json). It distinguishes u log|u|², spatially inhomogeneous coefficients, lower-power perturbations, log-log blowup rates and a logarithmic multiplier of a supercritical power. Search results from nonprimary sites were leads only. No exact printed theorem was found among the inspected sources; that is neither proof of absence nor evidence of priority. No MathDB score or priority claim is made.

The fresh read-only I66 replay is **evidence PASS**: 147 sealed artifacts, 26 input snapshots, 59 pins, 9,340 corpus files, 30 passages, 14 primary requests with 12 successes, 12 extraction replays, five original raw-pin comparisons and 1,991 author diagnostic assertions. Its four author-era ledger drifts are informational; no seal was refreshed. The immutable author report and verifier remain hash-bound.

**Preserved reference drift.** I68 froze `frontier/experiments/i66-parent-verification.json` earlier than I67: 1,438 bytes / `edef80f176d606e4078813c3b8e162f4c4fa194678e4597405e4076eb505e1bc`. The current wrapper is 2,132 bytes / `36aa2d02db24c2bc75e2ce52341705bc712aa88f69f947100d5d3662f06007d6`. Removing only its subsequently added top-level `parent_reading` field and serializing with the original two-space indentation reproduces I68’s frozen bytes and hash **exactly**. The [I68 forensic record](../sources/i68_logarithmic_blowup_novelty/reference-drift.json) preserves this explanation and the current snapshot. I67’s later baseline already included that field: the [parent audit](../experiments/i67-parent-reference-drift-audit.json) reverses only `30-147,151-201` to `30-201` and exactly reconstructs its 2,124-byte hash. Both reconstructions are checked in memory by the verifier. All mathematical/verifier-result fields are unchanged. Neither reference is refreshed, removed, or reclassified as a fifth mutable ledger. Thus **I68 aggregate evidence status is FAIL_REFERENCE_DRIFT with exit 1; core evidence checks are PASS**. The parent reading description is not a mathematical premise of this review.

The 2,171 independent finite assertions in the [diagnostics](../experiments/i68_logarithmic_blowup_novelty/diagnostics.py) check the rational pressure bound, finite admissible-k margins, polynomial convolution budgets, exact gauge slicing in a finite model, a forced nonautonomous stable/positive toy recurrence with slowly vanishing coordinate error, phase-tail scaling, and illustrative whole-ball degree budgets. They do not sample the unknown profile, certify a PDE estimate, or infer convergence from a numerical plateau. The analytic reduction is the argument in Section 3.

Run the [read-only verifier](../experiments/i68_logarithmic_blowup_novelty/verify.py) from the project root:

```bash
python frontier/experiments/i68_logarithmic_blowup_novelty/verify.py
```

It verifies hashes, original evidence replay, the fixed-domain line multisets, primary response and extraction bindings, actual source passage hashes, the new artifact seal and fresh independent diagnostics. It never downloads, rewrites evidence, refreshes an old seal or treats mutable ledger drift as proof failure. It preserves the explained parent-wrapper mismatch as FAIL_REFERENCE_DRIFT and exits 1 after completing the other checks. Its separate core PASS is provenance and finite reproducibility only. **Recommendation to the parent: retain C66 as one technical consequence alongside I67’s observed original-proof approval; do not count its normalization, pressure bound, graph or parameter variants as separate substantial findings.** No staging, commit, publication, shared-path edit or agent spawning was performed.
