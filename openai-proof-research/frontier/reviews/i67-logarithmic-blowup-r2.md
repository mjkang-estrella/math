# I67 — independent full original-proof audit of C66

**C66: PASS ORIGINAL WITHOUT REPAIRS**, conditional on the stipulated truth of all statements and proof operations in `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. This is a deduction/applicability verdict on the full original [I66 report](../iterations/i66-dispersive-equation-discovery.md), not an upstream truth audit. No author artifact was changed, and no replacement norm, regularity, hypothesis, equation, or proof construction is used to obtain this verdict.

The accepted scope is existential: a sufficiently large odd `p≥201`, `k=ceil(3p/4)`, one corresponding source profile, and a positive sufficiently small `κ_*`. For every real `|κ|≤κ_*`, there is a nonempty **physical H^k-open** set of data on T¹² for the original logarithmically perturbed equation, with the normalization (5)–(6), error `O(1/σ)` in the stated `Y_L`, and center amplitude limit `|Q(0)|`. This is not a theorem for p=201 specifically, all powers, arbitrary κ, metrics, or potentials.

Separate verdicts, with equation numbers referring to I66:

- **Pressure and permissible regularity (7): PASS ORIGINAL WITHOUT REPAIRS.**
- **Uniform composition and local Lipschitz bounds (8), including homogeneous and periodic low frequencies: PASS ORIGINAL WITHOUT REPAIRS.**
- **Normalized equation and full-input nonlinearity (9)–(12): PASS ORIGINAL WITHOUT REPAIRS.**
- **Finite slab estimates and special phase column (13)–(15): PASS ORIGINAL WITHOUT REPAIRS.**
- **Anisotropic infinite graph, size and continuity (16)–(19): PASS ORIGINAL WITHOUT REPAIRS.**
- **Physical degree, graph domain and continuation (20)–(21): PASS ORIGINAL WITHOUT REPAIRS.**
- **Construction II as a compact approximate orbit, including its generator-domain and regularity assertions: PASS ORIGINAL WITHOUT REPAIRS.** Its proposed global expanding-torus extension remains **GAP**, explicitly acknowledged in the original and not used for C66.
- **Screens as used: PASS ORIGINAL WITHOUT REPAIRS.** Broad metric target A is **FALSE**; fractal endpoint target B remains **GAP/unproved and unrefuted** in this record. Neither screen supplies a positive input to C66.

No mathematical repair was needed or applied. The expanded estimates below resolve the listed objections within the author's existing argument. They are not a replacement proof conditional on new lemmas. I68 owns the separate contribution assessment. This review assigns no ninth finding, acceptance, MathDB score, worldwide priority, or significance verdict. The eight accepted findings and I65's separate work are unchanged.

## 1. Scope, immutable evidence and actual reading

The exact current review brief, including its author outcome, unresolved objections and embedded original assignment, is [frozen here](../sources/i67_logarithmic_blowup_r2/review-brief.txt). The complete original author brief is [separately frozen](../sources/i67_logarithmic_blowup_r2/original-brief.txt). The full report, verifier, original evidence files, parent replay, task record, prior reports/reviews and original seals are bound by [immutable hash references](../sources/i67_logarithmic_blowup_r2/immutable-references.json); old evidence archives were not recursively copied. The four current front-page ledgers have separate snapshots and remain informationally mutable. The latest front pages show eight accepted findings and separate I67/I68 gates.

I read the full 353-line original report and its read-only verifier. In source B I read **all** of `profiles.tex` (744 lines), `linear.tex` (608), and `nonlinear.tex` (406), plus the main theorem and the spectral classification/top-derivative interface. In particular, the review includes the actual matching construction and its uniformity for nonunique parameter selections, the energy-observation retention of escaping norm, and the original graph's strong-continuity proof. Source symbols and projections are used as written. The source's exact k-choice, not an informal large-regularity statement, is the applicable interface.

[Passage records](../sources/i67_logarithmic_blowup_r2/passages.json) bind the full essential source sections and the actual primary proof interfaces read. Buck et al.'s complete §4 graph/localization argument, Li's §6.2–6.3 graph and symmetry matching and relevant H¹ matching, Cao-Labora et al.'s cutoff/linear transfer and bootstrap/topological interfaces, and Donninger–Wallauch's perturbation estimates and neutral/positive-mode construction were inspected. Their abstracts alone were not used as exclusions. Wave/fractal source interfaces and the corresponding BHS and Du–Zhang primary operations were also checked. The garbled BHS inequality was checked against the existing immutable page image.

The complete `preprints-tree.json` contains 13,223 entries and 749 manuscripts. `rg --files --no-ignore` enumerated the 9,340-file corpus. The unchanged I66 verifier rechecks every blob against that complete inventory, all 59 selected pinned artifacts, and its original search multisets. I67 also records three explicitly bounded searches with **line multisets**, not sets or traversal-order comparisons. Those searches are reproducible coverage, not semantic reading of all manuscripts or a novelty certificate. The old truncated tree is not used.

Fresh official retrievals produced 13 successful responses: five current arXiv version pages, five corresponding versioned full texts, and the three pivotal pinned B sections. All ten freshly extracted primary texts match the existing I66 texts exactly; all three raw B files match the pinned Git blobs. Versions remain Buck v1, Li v2, Cao-Labora et al. v1, Donninger–Wallauch v1 and Du–Zhang v3. Original failed DW-v2 (404) and institutional PDF (502) requests remain preserved; the successful official v1 is the text used. I67 did not replace failed history with successful bytes.

The original verifier independently replays with evidence PASS: 147 sealed artifacts, 26 inputs, 59 pins, 9,340 corpus files, 30 passages, 14 historical requests/12 successes, 12 extraction replays, five original raw-pin comparisons and 1,991 author finite assertions. All four ledgers now differ from I66's earlier snapshot; these are allowed integration changes, not immutable drift. This evidence PASS is **not** the analytic verdict above.

**Final provenance exception:** the first I67 replay detected that `frontier/experiments/i66-parent-verification.json` changed after its hash was frozen: 2,124 bytes / `e0b7b7b6f76df127ea5bc9500ff74daeab6afa927cf4c979eba052a7e7e27c7c` became 2,132 bytes / `36aa2d02db24c2bc75e2ce52341705bc712aa88f69f947100d5d3662f06007d6`. The latter bytes match the observed Git HEAD. The old wrapper bytes were not copied and no claim about the precise edit is made. [The discrepancy and current snapshot are preserved](../sources/i67_logarithmic_blowup_r2/reference-drift.json); the initial reference is unchanged. This wrapper is not reclassified as a fifth mutable ledger. Accordingly the aggregate I67 evidence status is **FAIL_REFERENCE_DRIFT**, with a nonzero verifier exit, while all 160 other immutable references, the unchanged author evidence replay and the new diagnostics pass. This provenance failure does not invalidate the analytic audit, which derives no proof premise from the parent wrapper. No old seal was refreshed.

## 2. Pressure, matching uniformity and choice of p

The source constructs profiles for every sufficiently small real a>0. Its spectral theorem holds for all sufficiently small admissible a, and the top-derivative test only requires an integer k≥7. Thus it permits restricting to the sequence `a=1/(p−1)` with p odd tending to infinity. No prescribed continuously selected matching branch is required.

Take any parameter-convergent sequence of matched profiles with a→0. Its limit has A₀=1 in the core and decreasing positive amplitude outside. For every r>0, monotonicity and the source integral identity give

`w₀(r)=6r^(−11) A₀(r)^(−2) ∫₀ʳ A₀(t)²t¹¹dt ≥ r/2`.

Hence `V₀=b+r²/16−w₀²/4≤b<0.335`. The source gives C¹ convergence of w on the **fixed** ball of radius r_b, including its regular origin. Therefore V_a converges uniformly there. For sufficiently small a its supremum is below 0.34. The maximum of A_a on that ball is attained. At an interior maximum, including the origin, the exact amplitude equation implies `P_a=V_a+ΔA_a/A_a≤V_a`. Since P_a is an increasing function of A_a, this bounds every interior pressure value. If the maximum is at r_b, the uniform exterior pressure bound bounds that maximum instead. On all r≥r_b the source gives `P_a≤a η₀(a)r^(−2)`, tending uniformly to zero.

Uniformity over matched profiles follows by contradiction: a violating sequence has a convergent subsequence of parameters in the compact matching disk, whose limit is a matching root, and the preceding argument contradicts its violation. Weak-star pressure convergence alone would not prove the assertion; the author correctly uses uniform convergence of V and the maximum principle.

For p≥201 and k=ceil(3p/4),

`k−[7−2a+(17/25)p] ≥ (7/100)p−7+2a>0`,

and `k+3<3p/4+4<p`. Thus `B=p||P||∞≤17p/50` satisfies the actual source condition `k>max(8,7−2a+2B)`. First choose one p sufficiently large for both pressure and spectrum, then fix k. The source's all-fixed-order symbol estimates apply at this finite k; their constants may depend on that p and k. No estimate uniform along k→∞ is being imported. Replacing 17/50 by the coarse source bound 1 would fail this compatibility test, as I66 states.

## 3. Composition: leakage, fractional order, zero mode, extension

Here all derivatives of H are **real** derivatives on R². Let λ_j=2^j/L, j≥0, with a lowest block at λ₀=L⁻¹. This is just the author's dyadic telescope with a convenient indexing for non-dyadic L. Periodized cutoff kernels and differentiated kernels have uniform L¹ bounds after scaling. The uniform source embedding bounds the values of all low-pass inputs by a fixed disk depending on R.

For a telescope term `T_j=H(S_{j+1}f)−H(S_jf)`, the mean-value formula and Bernstein yield

`||T_j||₂≤C_R h||Δ_jf||₂`,

`||∇^m T_j||₂≤C_R h λ_j^m||Δ_jf||₂`, for m=k+1.

The second inequality includes derivatives on **both** the band-limited Δ_jf and its coefficient. It does not assume the coefficient is band-limited. Therefore an output projection at λ_ℓ satisfies

`||Δ_ℓ T_j||₂≤C_R h min(1,(λ_j/λ_ℓ)^m)||Δ_jf||₂`.

Multiplying by λ_ℓ^s and dividing by λ_j^s gives the two-sided kernel `2^{s(ℓ−j)}` for ℓ≤j and `2^{−(m−s)(ℓ−j)}` for ℓ≥j. Both tails are summable for **each** s=s₀,k, since 0<s<m. This explicitly includes arbitrarily high inputs leaking to low outputs. Discrete Young's inequality on ℓ² is the stated Schur/Young step, so the argument proves Sobolev rather than merely Besov-ℓ¹ control.

Treat `H(S₀f)` separately. Its L² norm is bounded by `h||S₀f||₂`; differentiating as above bounds its high output tail with starting weight L⁻ˢ. At s=k, the auxiliary lowest-block quantity `L^(−k)||f||₂` is paid by `L^(−s₀)||f||₂` because L≥1 and k>s₀. The low norm in (1) is uniformly equivalent to `dot H^{s₀}` plus `L^(−s₀)L²`. Finally `|H(f)|≤h|f|` pays this last term for the full composition, including the zero mode generated by all nonlinear interactions. In particular a constant z retains its actual norm `(2π)^6L^a|z|`. Neither a mean-zero restriction nor deletion of the constant mode is permissible or used.

For Lipschitz continuity write

`H(f)−H(g)=DH(0)(f−g)+(f−g)∫₀¹[DH(g+t(f−g))−DH(0)]dt`.

Apply the just proved composition estimate entrywise to DH−DH(0), which vanishes at zero, and then the source's uniform algebra bound. The proof for this new function needs derivatives of H through k+2; the stated k+3 allowance suffices. The constant matrix DH(0) acts directly and is not assigned the growing norm of a constant torus function. Integrating the coefficient estimates gives exactly the second inequality in (8), with constants uniform in L.

The disk-extension sentence does not allow evaluating an undefined H outside its domain: the usual fixed bounded finite-order extension from a disk, followed by a cutoff on a larger disk, preserves H(0)=0 and multiplies its derivative bounds by only a fixed constant. This is the extension operation invoked in the original argument. In the actual application H_{σ,κ} is already globally smooth and (12) holds on **any fixed** disk, so one can simply use a disk containing all low-pass values before applying that cutoff. Neither the extension nor its constants depend on L or σ. No analyticity or polynomial approximation is needed.

On R¹², start at frequency 2^J and send J→−∞. The estimate `||S_Jf||∞≤C2^{aJ}||f||Y` gives the zero low-frequency representative; moreover its defining low-frequency Sobolev energies tend to zero by absolute continuity of the Fourier integral. The same lowest-block estimate and telescope therefore converge in Y. Fourier approximation, the just established Lipschitz estimate, and Y→C₀ identify the limit with H(f). This does not demand Q∈L². The author's homogeneous statement and periodic application both pass.

## 4. Normalization and real derivatives at zeros

Let N(z)=|z|^{p−1}z. For odd p this is a real polynomial of degree p, not a holomorphic polynomial. Its real derivative obeys `DN(z)z=pN(z)` and `DN(z)(iz)=iN(z)`. With `F(U)=iΔU−(D/2+a)U+ibU−iN(U)`, the physical-to-similarity change in I66 has the correct signs. Since `dσ/ds=1`, substitution U=cV gives precisely (9)–(10). Also

`c'/c=κ/[2σ²(1+κ/(2aσ))]`,

`c^{p−1}(1+κ/ℓ)−1 = κ(1+κ/(2aσ))^(−1)[ℓ^(−1)−(2aσ)^(−1)]`.

The linear `−(c'/c)z` term must remain. These identities are exact for both signs of κ once S is large, with a fixed positive lower bound on the parenthesis. The leading scalar `1/σ` correction is thereby removed from the entire nonlinear map, rather than only along Q.

For `r≥exp(−aσ/2)` in a fixed disk, `ℓ≥aσ−C` and `|ℓ−2aσ|≤C(1+|log r|)`. A positive-order real multi-index derivative of ℓ has size at most C_j r⁻ʲ. Differentiating its reciprocal contributes at least two denominator powers, so derivatives of the reciprocal difference, after multiplication by N and Leibniz' rule, are bounded by

`C_m|κ|σ⁻² r^{p−m}(1+|log r|)`.

For m≤k+3<p the last radial factor is bounded even as r→0. For `0<r<exp(−aσ/2)`, the bounded Euler derivatives of `1/log(2+q²)`, with q=e^{aσ}cr, give instead `C_m|κ|r^{p−m}` for the nonlinear part. Its exponential smallness absorbs σ⁻². This is not the false claim that ordinary q derivatives alone are uniform after composing with e^{aσ}r. At r=0 the denominator is smooth positive and N is polynomial, so the same finite-order estimate extends there. The linear term has the stated σ⁻² bound separately.

Constants may grow with fixed p,k,a and the disk. They are uniform in sufficiently large σ and `|κ|≤1/4`. The proof does not use a nonvanishing lower bound for Q+v: perturbations may have zeros, and Q_σ vanishes outside the cutoff. The low-amplitude region is exactly what handles these points. Combining the bound with (8) and the uniformly bounded Y_L norm of Q_σ supplies global Y_L forcing and difference estimates, including the cutoff annulus and zero mode. Construction II's unpaid symbol-tail estimate is not hidden here.

## 5. Slabs and the precise phase-column identity

Fix the source M, then take large S. On each finite slab the free propagator and linear potential have bounds independent of the starting torus scale. The inherited polynomial remainder is quadratic; H_{σ,κ} is uniformly Lipschitz of size `O(|κ|σ_n⁻²)`. The author's subslab contraction and difference Gronwall argument therefore yields (13)–(14), including the forcing-created `|κ|σ_n⁻²+d_n` term in the Lipschitz constant of h_n. It would be incorrect to estimate this constant using only the initial norm d.

For the phase estimate let `R_n(s)=∂_sQ_σ−F(Q_σ)` on the expanding torus. In terms of the source's displayed nonlinear cutoff defect 𝓡_s, **R_n=−i𝓡_s**. Hence `||R_n(s)||≤C_Md_n`. Gauge covariance gives

`[∂_s−DF(Q_σ)](iQ_σ)=iR_n(s)`.

The derivative DF(Q_σ) is exactly the source torus linearized generator, with cutoff potential `χ^{p−1}𝓥`, not DF(Q), and not the linearization of the κ-modified equation. This distinction is necessary: the modified derivative is already accounted for in h_n. Duhamel gives

`𝓕_n(iQ_{σ_n})−iQ_{σ_{n+1}} = −∫₀ᴹ 𝓕_n(M,t)iR_n(t)dt = O_M(d_n)`.

At both endpoints `π_nE_n⁰=e₀`, `π_{n+1}E_{n+1}⁰=e₀`, and `exp(MΛ)e₀=e₀`. Consequently

`e_nE_n⁰=π_{n+1}[𝓕_nE_n⁰−E_{n+1}⁰]`,

`(I−P_{n+1})𝓕_nE_n⁰=(I−P_{n+1})[𝓕_nE_n⁰−E_{n+1}⁰]`.

The uniform endpoint projection bounds prove both estimates actually used in the graph. No uncontrolled `π_{n+1}−π_n`, no rate for the full e_n, and no derivative of a spectral projection enters. Equation (15) passes with the original source propagator and cutoff.

## 6. Infinite contraction and continuity at varying S

Use precisely the author's norm (17). If X and X̃ belong to its δ-ball and D is their distance, boundedness of E_n gives

`||v_n||≤Cδ/σ_n`, `||v_n−ṽ_n||≤CD/σ_n`.

Substituting the actual size of these states into (14) gives

`||h_n(v_n)−h_n(ṽ_n)||≤C_M[δ/σ_n²+|κ|/σ_n³+d_n/σ_n]D`.

This state-dependent factor is crucial. A fixed small Lipschitz constant times σ_n⁻¹ would not be summable in the neutral coordinate. Here the quadratic term is summable even when both factors are phase components.

The stable forward update uses output weight σ_{n+1}². Its linear stable/positive cost is bounded by `(σ_{n+1}/σ_n)²(1/8+C_M/K)≤2(1/8+C_M/K)`. The positive backward sum has the factor `D_+^{n−j−1}` with its correct extra inverse step; its norm is at most `exp(−M(j−n+1)/2)`. The neutral sum has no geometric factor, and its bound is

`σ_n Σ_{j≥n}σ_j⁻²≤1/M+1/σ_n≤1/M+1/S`.

These estimates give exactly the separate positive σ² and phase σ weights in (17). The linear e_j input from w_j and E_j⁺u_j⁺ is O(εD/σ_j²), paid by small ε after K is fixed. Its phase input is O(d_jD/(Kσ_j)) by (15). Both the neutral backward sum and the stable forward update of that phase column have weighted bounds tending to zero as S→∞. A sum `Σ||e_j||/σ_j` is never required. Mere e_j→0 would not suffice for such a sum.

The full output norm is a sum of the three weighted components, so all coordinate costs must be **added**, not just maximized. The author's budget leaves room for that: first make the forward cost below 1/2 by K; then all remaining linear costs below 1/8 by S/ε; then all nonlinear costs below 1/8 by δ and S. Thus the total is strictly below one. The prescribed zeroth stable value is fixed in the contraction differences and contributes S²||w₀|| to the image of zero. The forcing contributes `C(|κ|+S²e^{−(1+a/2)S})`. A sufficiently small κ_* and the original graph-domain bound put the image and fixed point inside the δ-ball.

The sequence space is complete because each ker π_n is closed and the weighted product is a Banach space. Absolute convergence of both backward sums follows from the estimates above. Subtracting consecutive sums recovers the exact coordinate recurrence; the forward recurrence already lands in ker π_{n+1}. The unique fixed point therefore supplies actual consecutive nonlinear slab solutions. Dividing its bound by the phase weight KS gives (19); the stronger positive component bound also follows. Between-step bounds yield the asserted O(σ⁻¹) error for all times.

For parameter continuity one does not need continuity of the infinite map in operator norm. After physical-torus dilation, finite-index propagators and projections are strongly continuous for continuously varying inputs. H_{σ,κ} has the same finite-slab continuity by its smooth formula and local composition bounds. On a compact S-range, all iterates remain in the same uniform weighted ball. At a **fixed output index**, tails of the neutral sum are uniformly bounded by CΣ_{j≥J}σ_j⁻² plus an exponential tail; they tend to zero. Positive tails are smaller. Induction gives coordinatewise continuity of each iterate. Uniform contraction makes the iterates converge uniformly at index zero. Thus G_{S,κ}(w₀) is jointly continuous, exactly what degree requires. Uniform continuity of the whole sequence in an infinite weighted norm is neither asserted nor needed.

## 7. Physical parameters, all interior graph arguments, and local uniqueness

Changing T is not an equation symmetry for κ≠0. The author redoes the exact similarity transformation with `σ=log(1/(T−t))`, so no nonexistent symmetry is invoked. At the initial time S=S₀−β, the only added scalar in the reference expansion is `c(S₀)/c(S₀−β)`. Its β derivative at zero has **positive** sign `c'(S₀)/c(S₀)`, with size O(|κ|/S₀²). The inherited leading spectral map is thus unchanged: `Cd'=(-θ+bβ,ζ,β)`. C is invertible independently of S₀ and κ.

The source's two parameter derivatives apply only to the smooth reference and retain its tail order. Nearby physical H^k data are translated and rescaled by strongly continuous bounded operators on the compact parameter ball. They are not differentiated. Thus (20) has the stated uniform remainder and data factor C(T₀).

At the current scale, the exact identities `π_LE_L=I` and `(I−P_L)E_L=0` remove the full linear parameter term from the stable graph argument, including for varying L. Combining (19) and (20) gives (21). For ρ=d/S₀, its error divided by ρ is bounded by a fixed constant times

`d + S₀ exp(−S₀/2) + |κ|/S₀ + S₀² ε_data/d + |κ|/d + S₀² exp(−cS₀)/d`.

For **every** point of the closed parameter ball the stable-domain quantity has the independent bound

`S²||w₀||≤C[d² + S₀ exp(−S₀/2)d + |κ|d/S₀ + S₀² ε_data]`.

These two budgets are simultaneously payable in the author's order: choose d small for the quadratic terms and graph radius; choose S₀ large for the exponential terms and all slab/normalization thresholds; reduce κ_* relative to d and the graph forcing budget; choose a strictly positive H^k data radius for ε_data. The second bound verifies the domain throughout the ball, not just on its boundary. These are existential choices; the absence of an explicit numerical source M or p creates no circularity.

The straight-line homotopy to C has no boundary zero and has nonzero degree. Each datum in that open ball consequently admits θ,ζ,β placing v₀ on the graph. No continuity or uniqueness of the selected parameters is required by the theorem. The physical nonlinearity is smooth on C, including zero, and locally Lipschitz on H^k because k>6 and the finite-order composition argument applies on bounded amplitude disks. Duhamel supplies local H^k existence and uniqueness. Every finite similarity slab corresponds to a finite physical interval before T, with equivalent norms after dilation; uniqueness glues them. The equation then gives C¹ time regularity in H^{k−2}. Finally Y_L→L∞, c→1, χ(0)=1 and Q(0)≠0 imply the exact stated center limit. H^k→C⁰ excludes extension through T. This closes all of C66 within its original quantifiers.

## 8. Construction II: valid compact expansion, unpaid global extension

Cutoff approximation puts Q in the **generator domain**, not merely Y: its omitted tail has norm O(R⁻ᵃ), the drift-cutoff commutator has that same vanishing order, and Laplacian commutators have two more powers of decay. The polynomial potential is bounded on Y. Closedness of A therefore justifies the real homogeneity identity

`AQ=−i(p−1)N(Q)=−iN(Q)/a`.

Differentiating `πS(t)=exp(tΛ)π` on the domain gives π₀A=0. Thus π₀(iN(Q))=0. The leading forcing is **not** a phase resonance. With q₁=−κQ/2, `Aq₁−iκN(Q)/(2a)=0` as claimed.

The source's exponential stable semigroup gives `R_st h=−∫₀∞S(t)hdt`. Finite semigroup integrals lie in D(A) with A-image `S(t)h−h`; closedness passes to infinity. The positive symmetry coordinates have inverse Λ_+⁻¹. Together these define the bounded inverse on the closed complement ker π₀. No inverse on the phase line is claimed.

Every term in H₂ belongs to Y: q₁ has Q's tail, while N(Q)log|Q|² and its derivatives have order `r^(−2−2a)` times a log. The two-sided nonvanishing profile bounds control those log derivatives globally. Their dyadic Y tails are summable. This proves q₂∈D(A)⊂Y; it does not prove a symbol bound for q₂. Locally A is an elliptic real two-component system with smooth coefficients and bounded drift on compact balls. Local Sobolev bootstrapping gives q₂∈C∞ locally. On each fixed ball Q has a positive minimum modulus, so the Taylor expansion is legitimate there for sufficiently large σ.

Writing h₀=π₀H₂, γ=−h₀, and ϑ=−γ/σ, the σ⁻² residual coefficient is

`−q₁+γ iQ−Aq₂−g₂=H₂+γ iQ−(H₂−h₀ iQ)=0`.

In particular ϑ'=γ/σ²; reversing that sign would fail. The regularizing 2 in the logarithm is exponentially small on each compact ball. Higher fixed C^j remainders are O_{R,j}(σ⁻³), with thresholds/constants allowed to depend on the ball and j. This establishes exactly the original compact approximation.

A bounded inverse on Y gives no quantitative expanding-cutoff tail or pointwise comparison q₂/Q at infinity. A weighted resolvent preserving the log-symbol class and the associated global nonlinear remainder are still missing. The claim that Construction II itself proves C66 would therefore be **GAP**. The author does not make that claim, and Construction I uses neither missing estimate.

## 9. Screens and antecedent applicability

For A, the source wave theorem is Euclidean with every ε>0, and its physical predecessor proof explicitly uses straight-ray backflow, the discriminant identity and a fixed polynomial slice Jacobian. Its fixed-setup compactness lemma does not extend this geometric setup to arbitrary metrics. The metric necessary condition in [BHS, printed p.404 and §4C](https://msp.org/apde/2020/13-2/apde-v13-n2-p03-p.pdf) becomes `p≥2(3·3+1)/(3·3−3)=10/3`. Thus the asserted broad p=3 target fails. The positive curvature here is the cone-curvature distinction in §4C; no new assertion about positive sectional curvature of a metric, or arbitrarily small prescribed metric neighborhoods, is inferred. The broad rejection also follows from the stipulated wave source's explicit metric discussion.

For B, the source measure condition is n-growth only for radii r≥1. An α-growth scaled graph with α=n−1/10 satisfies that weaker condition; the source's D=1 tube moment follows with a fixed enlargement of its growth constant. Using only the resulting weak estimate produces distribution mass N^n before returning by N^(−α), hence the extra factor `N^{(n−α)/p}`. Since

`s_α−s_n=n(n−α)/[2(n+1)]`,

this use attains the proposed short-time exponent only if `p≥2(n+1)/n`. “Some p>2” does not supply this. Separately the common-tree localized dual estimate uses both `m_{J,Q}≤r^n` and a kernel integrated against spatial Lebesgue measure. The tree's abstract mass deficit survives, but its analytic spatial input has not been replaced. Du–Zhang v3, Theorem 2.2 and its full local-constancy/pigeonholing proof, retains a power loss. These are method obstructions, not a counterexample to B. No endpoint theorem or divergence-set improvement is being certified.

For C66 the primary comparison is bounded and accurate. [Buck et al., v1, Proposition 4.8](https://arxiv.org/html/2609.23685v1) owns an exponential Lyapunov–Perron graph and finite-dimensional compact-support correction for pure-power radial whole-space dynamics. [Li, v2, §6.3](https://arxiv.org/html/2304.02078v2) explicitly matches phase, translation and scaling coordinates through a Brouwer map under mode stability; the H¹ proof repeats this after localization. [Cao-Labora et al., v1](https://arxiv.org/html/2410.04532v1) works with periodic damped hydrodynamic profiles, r>2 scaling and a finite-codimension unstable-mode selection in dimension eight. These actual lower operations prevent crediting the generic graph/cutoff/degree ideas to I66. They are not invoked as proof of the new interfaces audited above.

[Donninger–Wallauch, v1](https://arxiv.org/html/2006.04600v1), Assumption 1.1 and Lemma 3.2, imposes a fixed q<p and obtains a positive exponential similarity exponent. Its phase-modulation and positive-mode correction are genuine robustness antecedents. For every q<p, however, `r^{p−q}/log(2+r²)→∞`, so its growth hypothesis does not directly cover I66's perturbation. Neither that nonapplicability nor absence of an exact statement proves substantiality. Whether its operations combine with the pinned source to make C66 technical is I68's separate question. The prior geometric-avoidance, standard-map and fixed-dimensional entropy technical verdicts remain in force; proof correctness alone does not raise the count.

## 10. Independent diagnostics, reproducibility and handoff

The new [diagnostic program](../experiments/i67_logarithmic_blowup_r2/diagnostics.py) is independent of the author's program and uses only the Python standard library. It reproduces **3,108 exact rational assertions** and **117 decimal assertions at precision 180**. Its tests include real directional derivatives of complex N (radial versus phase directions), the compact correction sign, high-frequency convolution creating a nonzero mean, exact backward-index/integral-tail budgets, an illustrative summed graph contraction budget, and all interior radii in an illustrative degree-domain budget. The latter finite examples do not identify the unknown PDE constants.

Decimal directional jets test every coefficient through order 154 for the actual p=201 algebraic formula at both κ signs and at core, transition, tiny-amplitude and zero inputs. Selected derivative records are retained; direct and normalized coefficient formulas agree at the recorded precision. The same code tests the next nonlinear Taylor coefficient at order p+2: its growth illustrates why an arbitrary-high-regularity uniform claim would be invalid. None of these finite samples asserts p=201 is a spectrally admissible source profile or proves a universal composition/PDE estimate. The universal arguments are Sections 2–8 above.

Run the [read-only verifier](../experiments/i67_logarithmic_blowup_r2/verify.py) from the project root:

```bash
python frontier/experiments/i67_logarithmic_blowup_r2/verify.py
```

It checks I67's immutable references and seal, both exact briefs, four frozen ledgers with permitted live drift, actual source passage bytes, pinned Git blobs, the complete inherited corpus check, I67 search line multisets, all fresh response and extraction bytes, and independent diagnostic reproduction. It invokes the unchanged read-only I66 verifier; it does not fetch, write caches, refresh seals, or modify verification outputs. The result reports core checks PASS and the preserved parent-wrapper **FAIL_REFERENCE_DRIFT** separately, then exits 1 for that immutable-reference discrepancy. It does not silently bless the changed wrapper or stop before testing the remaining evidence. Evidence reproduction is separate from this original-proof PASS and from I68's contribution decision.

All work is confined to the assigned I67 report/source/experiment paths. No shared status/count change, author edit, staging, commit, publication, or agent spawning was performed. The handoff is full-scope original-proof PASS for C66, with Construction II's global extension and fractal target B still unpaid exactly as stated by the author.
