# I340 — proofs of the paid partials and the remaining estimate

Date: 2026-10-13. Verdict: **UNRESOLVED**. All references H refer to `preprints/Hard-sphere-fluctuations-on-the-regular-Boltzmann-lifespan-September-23-2026/build` at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Upstream theorem truth is stipulated; the deductions below are separate arguments. They have not undergone a fresh independent proof gate.

## 1. The exact problem

Position and velocity belong to R³, sphere diameter is ε, and μ=ε⁻². The law is exactly

\[
 P_\varepsilon(N,dZ_N)=\mathcal Z_\varepsilon^{-1}
 \frac{\mu^N}{N!}\mathbf1_{\{|x_i-x_j|>\varepsilon\}}
 \prod_{i=1}^N f_0(z_i)\,dz_i,
\]

including N=0. Here f₀ is a smooth nonnegative probability density, and for some β>0 its Gaussian Bol norm and that of ∇ₓf₀ at exponent 2β are finite. The Bol norm is the sum, over a∈Z³, of the local supremum on |x−a|≤1 of e^{2β|v|²}|g(x,v)|. Fix **any supplied** finite [0,T] with a nonnegative classical nonlinear Boltzmann solution f and sup_{t,x,v}e^{2β|v|²}f_t(x,v)<∞. No shortening of T, equilibrium, periodic replacement, or small-data condition is introduced.

Let Xᵋ_t(φ)=μ⁻¹ᐟ²[Σ_iφ(z_i(t))−EΣ_iφ(z_i(t))] for the true deterministic elastic flow. Write \(\widehat X\) for the source's pasted flow, centered by its **own** exact expectation. The requested conclusion is convergence of each fixed finite vector of Xᵋ coordinates in D([0,T],Rᵐ), J1, to the continuous version of H's Gaussian field. H `thm:main` supplies only FDD convergence. Its introduction explicitly excludes a tightness assertion.

The collision convention is B(g,ω)=[g·ω]₊ with ordinary sphere area; v′=v−(g·ω)ω and v*′=v*+(g·ω)ω. Put

\[
 A_t\phi=v\cdot\nabla_x\phi+\int Bf_t(x,v_*)\Delta\phi\,dv_*d\omega,
 \qquad C_t(\phi,\psi)=\tfrac12\int B f_t f_{t,*}\Delta\phi\Delta\psi\,dx\,dv\,dv_*d\omega.
\]

The joint target covariance is exactly

\[
 K_{\phi,\psi}(t,s)=\int f_0U(0,t)\phi\,U(0,s)\psi
 +\int_0^{t\wedge s}C_r(U(r,t)\phi,U(r,s)\psi)\,dr.\tag{1}
\]

Its initial term is Poisson covariance, with no fixed-particle-number subtraction.

## 2. Continuous Gaussian coordinates — independently verified parent support

H §02 `lem:target-propagator`, `prop:gaussian-target`, `eq:target-source-bound`, and `eq:target-field-bound` give the backward field and the weak identity

\[
 \zeta_t(\phi)=\zeta_0(\phi)+\int_0^t\zeta_r(A_r\phi)\,dr+W_t(\phi).\tag{2}
\]

For φ∈C_c^∞ choose 0<a<b<β. The source's K estimate and compact support give sup_r||A_rφ||_a<∞. Continuity of r↦A_rφ in E_a^0 and the mean-square field construction make the integrand strongly measurable in L²(Ω); a jointly measurable representative exists. The uniform field bound gives E∫₀ᵀ|ζ_r(A_rφ)|²dr<∞. Its indefinite integral consequently has continuous paths almost surely, with modulus at most |t−s|¹ᐟ² times the finite random L² norm.

The source-bound on C gives E|W_t(φ)−W_s(φ)|²≤C|t−s|. Gaussian fourth moments give E|W_t−W_s|⁴≤3C²|t−s|². Kolmogorov yields a continuous modification of W. Equation (2) then defines a continuous modification of ζ(φ): for every fixed t the new coordinate equals the old coordinate almost surely. For a finite list, take the intersection of the finitely many probability-one events. Thus **all** joint covariances remain (1). This proves coordinate continuity, not samplewise membership of a Banach dual.

Credit: this is the parent's supplied argument in `frontier/iterations/i340-parent-path-transfer.md`, checked against the actual §02 statements and proof. The operations are standard Bochner measurability, Tonelli, and Gaussian Kolmogorov continuity.

## 3. Uniform exact-centering transfer — independently verified parent support

H §05 `prop:cutoff` gives the global event Eᵋ of any true/pasted discrepancy on [0,T], with P(Eᵋ)≤Cε^{1+η}; η=1/20 is allowed. H §02 `eq:initial-N-moments` gives uniformly bounded fixed moments of N/μ. For every bounded b, the *simultaneous* pathwise bound is

\[
 \sup_{t\le T}|S_t^\varepsilon(b)-\widehat S_t^\varepsilon(b)|
 \le2\|b\|_\infty N\mathbf1_{E^\varepsilon}.
\]

For integer p>(1+η)/η,

\[
 \sup_t\frac{|ES_t- E\widehat S_t|}{\sqrt\mu}
 \le C_p\varepsilon^{-1+(1+\eta)(1-1/p)}\longrightarrow0.\tag{3}
\]

With η=1/20, p=22 gives exponent 1/440>0. On the complement of Eᵋ the uncentered paths coincide for all t. Equation (3) implies

\[
 \|X^\varepsilon(b)-\widehat X^\varepsilon(b)\|_\infty
 \longrightarrow0\quad\hbox{in probability}.\tag{4}
\]

This holds for any fixed finite coordinate vector. The identity time change bounds the J1 distance by the supremum distance. Therefore any proved pasted functional limit transfers to the true flow. This does **not** transfer fourth moments of the instantaneous true fluctuations: the crude fourth-power bound on Eᵋ need not vanish or stay bounded. Credit: parent support and H §08 `lem:center-transfer`, with the uniform-in-time extension justified by the displayed simultaneous inequality.

## 4. Uniform deterministic-time moments: a derived bound, not a uniform-record assumption

For every fixed bounded compact smooth b and fixed integer k≥2,

\[
 \sup_{\varepsilon\le\varepsilon_0}\sup_{t\le T}
 E|\widehat X_t^\varepsilon(b)|^{2k}<\infty.\tag{5}
\]

Here is why the constants can be uniform in t. Use t as an **unmarked final endpoint**, rather than retaining an increasing list of observations. Its slab index has only L possibilities. H §03 `eq:dhm-partial-slab` and §04 `lem:stopped-variation` explicitly allow a partial final slab with unchanged upper majorants. For each h≤2k choose the same complexity cutoff K for all these finitely many prefixes. The high-complexity estimate in §04 is bounded by

\[
 C_{h,m}\varepsilon^{-C_*h-C_m+c_*K/2},
\]

with no observation pulses in this use. Take K large enough to absorb multiplication by μ^{h−1}. The variation remainder e^{−cΛ_L} is superpolynomial; earlier prefix cutoffs are larger. At bounded complexity, the §06 Jacobian and fresh-label calculation does not use continuity or asymptotic convergence of endpoint tests. Enlarge every partial-slab time domain to its full slab, **in merger coordinates**, and integrate the translation of each component using one birth's spatial L¹ bound and all other births' spatial supremum. This is precisely the displacement-independent argument in `lem:sharp-summability`. It bounds the resulting absolute measures by

\[
 C_K(1+n)^{d_K}(C\tau\sqrt L)^n\mu^{1-h},\qquad \tau=T/L.
\]

Use the fixed L with Cτ√L<1. The physical-link radii, dummy losses, and powers in this bound depend on h,K,L and the kinetic envelopes, not t. The no-extra-contact lemma is **not needed** for this absolute bound. We have thus derived sup_t||c_{h,t}ᵋ||TV≤C_hμ^{1−h} on the same pasted flow.

The factorial-to-ordinary identity in H §07 `eq:limit-factorial-ordinary`, now with the endpoint test b, gives |κ_j(Σb)|≤C_{j,b}μ. Centering removes κ₁; each term in the centered 2k-th moment is a product of at most k cumulants of order at least two. Dividing by μᵏ proves (5). In particular the fourth moment equals κ₄/μ²+3κ₂²/μ² and is uniformly bounded. This argument derives only a fixed-test endpoint bound; it does not turn arbitrary fixed-record constants into shrinking-window estimates.

## 5. A proved functional partial: fixed indefinite integrals

For any fixed finite compact smooth tests b₁,…,b_q,

\[
 Y_t^\varepsilon(b_j):=\int_0^t X_r^\varepsilon(b_j)\,dr
 \quad\Longrightarrow\quad
 Y_t(b_j):=\int_0^t\zeta_r(b_j)\,dr
 \quad\hbox{in }C([0,T],\mathbb R^q).\tag{6}
\]

This is a **weaker partial**, not the requested theorem. There is no ε-dependent averaging, but taking an indefinite integral loses microscopic path information.

First prove (6) for the pasted process. By (5) and Tonelli, E∫₀ᵀ|\widehat X_r(b)|⁴dr≤C. Hölder gives, simultaneously for every s,t,

\[
 |\widehat Y_t(b)-\widehat Y_s(b)|
 \le |t-s|^{3/4}\left(\int_0^T|\widehat X_r(b)|^4dr\right)^{1/4}.\tag{7}
\]

The random Hölder constants are tight by Markov; Y₀=0. Arzelà–Ascoli therefore gives tightness in C.

For identification, a finite linear combination of integrated coordinates is ∫Σ_j a_j(r)\widehat X_r(b_j)dr, where the a_j are bounded step functions. Expand each fixed power, use Fubini, and apply dominated convergence on [0,T]^p. H §07 `prop:cumulant-clt` gives convergence of all mixed centered moments at each fixed finite list of times, by polarization. The dominating bound follows from Hölder and (5), using a sufficiently high **fixed** moment. Thus the integrated linear combination's moments converge to those of ∫Σ_j a_j(r)ζ_r(b_j)dr. That variable is Gaussian as an L² limit of jointly Gaussian Riemann sums. Gaussian moment determinacy gives scalar convergence and Cramér–Wold gives the integrated FDD limits. Tightness identifies the unique continuous process law. Its covariance is ∫₀ᵗ∫₀ˢK_{b_i,b_j}(r,q)drdq. Finally (4) gives sup_t|Y_t−\widehat Y_t|≤T||X−\widehat X||∞→0 in probability, proving (6) for the true flow.

This deduction uses fixed-time moment convergence only inside a dominated **integral**. It makes no sampling approximation uniform in ε and is not a claim that FDD convergence alone implies (6).

## 6. What the retained trees pay for increments

A further bound can be paid, but has an unpaid remainder. Fix φ∈C_c^∞. There is a deterministic rᵋ→0, independent of s,t, such that, with δ=t−s,

\[
 E|\widehat X_t^\varepsilon(\phi)-\widehat X_s^\varepsilon(\phi)|^4
 \le C\{(\delta+r^\varepsilon)^2+
            \mu^{-1}(\delta+r^\varepsilon)\}.\tag{8}
\]

No rate for rᵋ is asserted. The following explains both the uniformity and the loss.

Retain the two endpoint phase points at s,t on each of at most four designated labels, always using final time T. The record number is fixed (two pulses), and these same designated lines continue to zero. For the absolute estimates, pulse placement merely selects which of finitely many straight segments carries each pulse. Dropping this selection and summing at most a fixed polynomial in n bounds all pulse placements independently of their time values. Record multipliers here are bounded by fixed powers of 2||φ||∞; no record Gaussian weight is needed. The coarse complexity sum, variation error, and low-complexity majorant consequently have uniform constants for these moving two pulses. This is an argument from §04's kernels and factorial counts, not an extra uniform-time statement attributed to `thm:sharp-cumulants`.

In a connected global tree with trivial initial blocks every contact is a dynamic merger. On a designated line let H=φ(z(t))−φ(z(s)). With D=||v·∇ₓφ||∞ and B=||φ||∞,

\[
 |H|\le D\delta+2B\sum_{\substack{a\text{ scattering}\text{incident to the line}}}
                          \mathbf1_{\{t_a\in(s,t]\}}.\tag{9}
\]

All other endpoint powers are bounded. For one selected merger in a slab with a_i merger times, restricting its ordered time to an interval J has volume at most

\[
 |J|\frac{\tau^{a_i-1}}{(a_i-1)!}.
\]

Indeed, at fixed selected time the volumes before and after it are one binomial term in the sum τ^{a_i−1}/(a_i−1)!. Relative to τ^{a_i}/a_i! this costs at most a_i|J|/τ. The flux and energy-bin bounds in §06 are independent of the time values. Selecting incident vertices and segments only adds fixed polynomial factors. Summing slabs uses Σ_i|(s,t]∩slab_i|=δ. Thus every connected tree term tested against a product H₁^{k₁}…H_h^{k_h}, Σk_i≤4, gains δ, while its original μ^{1−h} normalization and summable atom base remain intact.

The other retained diagrams have normalized absolute mass tending to zero uniformly in these pulse positions. Physical initial links give O(ε); initial artificial tails can be assigned any fixed power after K; cycle disappearance uses the observation-independent geometric first-redundant-contact indicator in §06 lines 618–639. At fixed graph size its dominating bound and pointwise vanishing do not involve evaluation of the pulse tests; remove all pulse-selection restrictions for this upper bound. Then remove size tails by the same summable majorant, and choose the high-complexity/variation accuracy before normalization. This proves the existence of a common rᵋ→0 for h≤4. It does not quantify it.

Consequently the increment sum S has |κ_j(S)|≤C_jμ(δ+rᵋ) for j=2,4, by the factorial-to-ordinary formula. Centering and the fourth-moment identity prove (8). This establishes a uniform mesoscopic estimate with a remainder, not microscopic closure.

## 7. Exact transport/current reduction

For either flow and each φ put b_φ=v·∇ₓφ and let Q_tᵋ(φ) be the sum over accepted physical collisions up to t of

\[
 \phi(x_i,v_i^+)+\phi(x_j,v_j^+)
 -\phi(x_i,v_i^-)-\phi(x_j,v_j^-).
\]

The two positions remain distinct at finite ε. Replacing both by one collision position is not used. Define the centered current M_tᵋ=μ⁻¹ᐟ²(Q_tᵋ−EQ_tᵋ). Pathwise telescoping and exact expectation subtraction yield

\[
 X_t^\varepsilon(\phi)=X_0^\varepsilon(\phi)
        +Y_t^\varepsilon(b_\phi)+M_t^\varepsilon(\phi).\tag{10}
\]

The signed Q_t is integrable: telescoping bounds its absolute value by N(2||φ||∞+T||b_φ||∞). The pasted total number of accepted collisions is also at most L(Γ+1)N, since each slab's collision graph has excess at most Γ in every component. The true flow has finitely many collisions almost surely. No unsigned true collision-count moment is assumed. At restarts neither phase points nor records jump, so (10) concatenates exactly across slab interfaces.

Equation (6) pays the drift. Initial vectors are tight by H. Thus C-tightness of the vector of centered collision currents would pay the remaining path limit; FDD identification would then be H's existing theorem. Conversely, the continuous drift cannot repair non-tight current oscillations. Each microscopic jump of X has size at most 4||φ||∞/√μ, but their accumulation remains uncontrolled. The current's candidate limit is ζ_t(φ)−ζ₀(φ)−∫₀ᵗζ_r(b_φ)dr; it is **not asserted to be a martingale**.

## 8. The precise unpaid operation

One sufficient closure is the following pair of estimates for the pasted X (or analogous estimates for M and its paid drift), on the one fixed pasted flow:

\[
 E|\widehat X_t-\widehat X_s|^4\le C(\delta^2+\delta/\mu),\tag{11}
\]

uniformly in ε,s,t, together with

\[
 \sup_{|t-s|\le2\alpha_\varepsilon}
 |\widehat X_t-\widehat X_s|\longrightarrow0
 \quad\text{in probability},\qquad
 \alpha_\varepsilon=\mu^{-7/3}.\tag{12}
\]

The established BGSS modified GRR argument then closes C-tightness; it is credited old machinery. The missing source adaptation is a window-localized connected estimate for collision events incident to the designated lines that proves (11), including **redundant** contacts and all normalized remainders. A genuine adjacent-disjoint-interval mixed estimate E[(M_t−M_s)²(M_u−M_t)²]≤C(u−s)² with valid boundary/microscopic closure is another possible route, also unproved here.

In H's chronological chart, a redundant contact time is a function of earlier merger parameters. Its incoming coarea integral is an indicator of an intersection, of mass at most one; there is no remaining dt. Restricting that determined time to a window cannot simply replace τ by δ. One must construct a compatible new chart/cut that localizes that event **while preserving** the connected root gain, the fresh-label denominator, and the summable bounds through every restart, or prove an adequately quantified alternative maximal estimate. §06's dominated-convergence argument supplies no such window factor.

The loss is visible even granting (12). For 2<γ<3 the fourth-moment GRR integral above α receives from (8), besides the standard bounded term, contributions bounded by constants times

\[
 (r^\varepsilon+\mu^{-1})\alpha^{2-\gamma}
 +\bigl((r^\varepsilon)^2+\mu^{-1}r^\varepsilon\bigr)
                              \alpha^{1-\gamma}.\tag{13}
\]

For γ=7/3 and α=μ⁻⁷ᐟ³, α^{1−γ}=μ^{28/9}. Qualitative rᵋ→0 gives no control of (13). A diagonal cutoff cannot be chosen freely: (12), or a replacement microscopic estimate, must hold at the same cutoff. This diagnoses why (8) is insufficient; it does not prove tightness is false.

H §05's primitive-pair lemma is also not (12). Its smallness simultaneously imposes |t₂−t₁|≤ε^{9/10} **and** a prospective fixed-edge velocity difference ≤ε^{4/5}; its gain is μ ε^{9/10+12/5}=ε^{13/10}. The complementary cutting branch pays for a high-cycle cutoff witness. This is neither the probability of arbitrary two collisions in a μ⁻⁷ᐟ³ window nor the centered current bound. A proof must cover nonprimitive chains, disconnected pairs, observation incident contacts, slab boundaries, and factorial/normalization losses, and then union over O(α⁻¹) windows. None is claimed paid here.

No counterexample within the actual prescribed gas has been found. Correctness of the partials, significance of the unproved functional upgrade, and worldwide novelty remain distinct. The partials are technical deductions from H and old continuity machinery, not a contribution to the substantial-result count.
