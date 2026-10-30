# Independent full RF proof review, round 1

**Verdict: PASS_FULL_RF. No required mathematical repair.**

This verdict concerns the complete frozen RF statement, not a positive-field law, an ideal-gas substitute, a selected spin, or a subsequence. It is an independent mathematical review, not a contribution verdict, campaign acceptance, formal proof certificate, or publication authorization. The campaign count is unchanged by this report.

The exact reviewed author directory is `fresh-analytic-discovery-r19`. Bindings:

- Sealed manifest: `bde061c4eea5499343cfd07b623efe2079b858b19faa90f031e719702ec4902b`.
- Candidate: `9ea51c98f9f50c7e614c754070b21ba8fc0e558df506363ccbbcaa453962ca80`.
- Original scope: `e40f0169ee9c301474c7f255ea129e311f001990786c338862e884dddf756e8f`.

The full candidate I read already contained the explicit Fourier-radius optimization and has exactly the final sealed candidate hash. Thus there is no unreviewed changed proof paragraph hidden by the seal. I separately read the final audit note, receipts, screening note, and author diagnostic code. The detailed read extent is in `reading.md`.

## 1. Full scope retained

For each fixed half-integer S≥1/2, the model is the nearest-neighbor quantum ferromagnet on the even cubic torus of side L≥4, with unordered-bond energy S²−S_x·S_y. The physical probability measure is the zero-field Gibbs trace, including all magnetic multiplicities. The observable is D=SL³−J, with J the total-spin label. The centering is exactly the nonzero-mode ideal occupation sum μ, not a presumed interacting expectation. The scale is a=β/L².

The proof applies to every sequence β→∞ and β^.501≤L≤β^.51. It proves weak convergence of a(D−μ) and convergence of its Laplace transforms at every λ≥0 to the centered independent exponential series with coefficients (4π²S|k|²)⁻¹, indexed by all nonzero k∈Z³. Its variance is positive and its third cumulant is nonzero. Constants may depend on fixed S and bounded auxiliary λ ranges. No uniform-in-S assertion is used or obtained.

## 2. Actual classical inputs

The load-bearing spin estimates are in [Correggi–Giuliani–Seiringer, arXiv:1312.7873v2](https://arxiv.org/abs/1312.7873v2), whose relevant proof bodies I read. The HP formula (3.2), local projected inequality (4.11), entropy argument (4.21)–(4.23), Casimir comparison (5.5), rough trace estimate from Lemma 5.3, interaction inequality (5.27), and local pair-density calculation (6.2)–(6.11) have the interfaces stated in the candidate. In particular, the pair calculation sums local bond squares and never divides by E. It applies on the torus at E=0. The positive-energy open-box density theorem is **not** being imported as a torus theorem.

Adding periodic bonds adds nonnegative spin operators. The Casimir deficit lower bound survives. The trace upper bound survives by eigenvalue min-max; no operator-monotonicity claim for exp is needed. The open-cube side condition L≥√(βS/2) holds eventually throughout the window for each fixed S, since L/√β≥β^.001. The other fixed-S lower-temperature condition of CGS Lemma 5.3 also holds eventually. Multiplying its free-energy bound by βL³ gives precisely the rough log-trace order L³β⁻³ᐟ²(log β)⁵ᐟ² used here.

The family 271 thermodynamic results are not required premises of this proof. Their stipulated truth cannot replace the new finite-volume estimates, and no such replacement occurs. The independent contribution gate must assess the campaign eligibility and significance of a proof whose principal analytic inputs are classical.

## 3. Periodic pair process and the S=1/2 diagonal

For S≥1, w(x,y)=1−δ_xy/(2S) is between 1/2 and 1. Substitution ρ=wσ in CGS (6.9), and division by w at the starting vertex, gives −Aσ≤(2E/S)σ with rates A(z,z′)=w(z′). Its reversible measure is w(z), because its edge conductance is w(z)w(z′). Thus its weighted L¹ norm on σ is exactly Σρ=n(n−1). Conductances and measures are uniformly comparable to counting measure for each fixed S.

For S=1/2, ρ(x,x)=0 identically. At off-diagonal starting vertices the rates into the diagonal are zero, so deleting the diagonal gives exactly the required generator, not an approximate generator or an extra boundary condition. The extension construction in §3 gives a valid uniform Nash inequality on this graph. I checked the paths for all allowed L analytically: the A_e-to-A_f path avoids the origin when f≠−e; opposite directions can use a perpendicular coordinate; and the displayed A_e-to-B_e detour keeps the two particles distinct at every vertex. Its displacements remain distinct modulo every L≥4. Only finitely many translated bounded-length patterns occur, hence each edge has bounded congestion independently of L.

Each off-diagonal neighbor participates in at most two diagonal averages. Consequently the extension has the stated L¹ and L² bounds. The newly introduced edges are precisely those incident to a diagonal vertex, and their energies are controlled by differences among its twelve neighbors, then by the bounded-congestion paths. This proves the energy extension inequality; it is not inferred merely from finite path tests.

## 4. Nash estimate and semigroup endpoint

The six-dimensional torus Fourier split gives low-frequency mass at most Cr⁶||f||₁² and high-frequency mass at most Cr⁻² energy(f). The chosen r makes the low part at most half of ||f||₂² when r≥L⁻¹. When this chosen r is below L⁻¹, the L⁻²||f||₂² correction gives the inequality directly. Thus the exponents 8/3 and 2/3 and the finite-volume correction in (3.3) are correct.

Transferring this inequality by the preceding extension or measure comparison is valid. For the reversible semigroup, L¹ contractivity and differentiation of its L² norm produce u′≤−cu⁴ᐟ³+CL⁻²u. The exponential integrating factor gives u(t)≤Ct⁻³ up to L²; self-adjointness and semigroup composition give the 1→∞ bound of the same order, with a harmless time factor. Composition with time L² gives CL⁻⁶ for later times.

The subsolution sign is correct: Aσ+(2E/S)σ≥0 makes e^(2Et/S)P_tσ increasing pointwise. Choosing t=min(L²,S/(2E)), and t=L² when E=0, yields ||ρ||∞≤C_S(E+L⁻²)³n(n−1). No zero-energy state is omitted. For n=0,1, nonnegativity and Σρ=0 give the result directly.

## 5. Free estimates and the uniform window

The dispersion bounds c_S|k|²/L²≤ε(k)≤C_S|k|²/L² hold for the chosen representatives. The nonzero Gaussian-sum estimate, summed over the geometric-series parameter, gives μ≤CL³β⁻³ᐟ². The zero mode contributes (βhV)⁻¹ to the density bound, at most 1 to the βT_h energy sum, and O((βh)⁻¹) to the differentiated occupation sum. All constants remain valid for β⁻¹ᐟ²⁰≤λ≤B, h=λ/L².

Independently recomputing the endpoint powers gives:

| Quantity | Worst relevant power of β |
|---|---:|
| M=L³β⁻³ᐟ² | lower .003; upper .03 |
| E₀L², omitting its positive logarithmic factor | lower .005 |
| r | upper −1.451 |
| Vr² | upper −1.372 |
| βVr² | upper −.372 |
| (βh)⁻¹ | upper .07 |
| βVE₀⁵h⁻² | upper −.18 |
| βh₀D₀ | upper −.02 |
| βh₀μ | upper −.04 |

All powers required to vanish are strictly negative; fixed powers of log β do not change that conclusion. In particular the cutoff tail exp(−cM(log β)⁵ᐟ²) is smaller than every fixed inverse power of β. The window's lower endpoint also makes a=β/L²→0 for every permitted sequence.

## 6. Upper partition comparison and noncommuting compression

For E₀=AL³β⁻⁵ᐟ²(log β)⁵ᐟ², positivity of hN and commutation of H,N justify the tail estimate for the spectral cutoff of H+hN. Taking A sufficiently large absorbs the rough trace exponent at β/2. A simultaneous eigenbasis on the retained range satisfies E≤E₀ and n≤E₀/h, so the pair bound and CGS interaction inequality give β〈K〉≤CβVE₀⁵h⁻². The replacement of E₀+L⁻² by 2E₀ is justified by the positive .005 power above.

The Peierls–Bogoliubov direction is correct: using the interacting truncated Gibbs state as trial state for the compressed free operator gives log Z_H≤log Z_T+β〈K〉_H. The compression need not commute with T. Its free variational supremum ranges over density matrices supported in the cutoff space, a subset of all Fock density matrices. Their compressed energy equals their T_h energy, hence the compressed partition function is at most F(h). The cutoff space is finite dimensional and contains the aligned N=0 state. Adding the small absolute tail and using F(h)≥1 gives the required absolute logarithmic upper comparison.

## 7. Lower comparison, entropy, and covariance

The hard projection P onto n_x≤1 lies inside the physical spin space for every S≥1/2. Its free expectation satisfies q≥1−Vr² by the factorial-moment inequality and Wick's rule. Off-site Gaussian occupations are at most 2r². CGS's projected bond calculation plus PhNP≤hN therefore gives the stated trial energy upper bound for Γ=Pe^(−βT_h)P/(qF).

The entropy proof uses equality of nonzero spectra of Pe^(−βT_h)P and e^(−βT_h/2)Pe^(−βT_h/2), followed by operator monotonicity of log on the latter inequality. This yields (5.7) with exactly the cancellation of A₁/q. Neither cyclicity nor positivity is misused to commute P with T_h.

For (5.8), T_he^(−βT_h) is a positive trace-class operator, so it can multiply the positive operator inequality for 1−P inside a trace. Differentiating the normalized expectation at fixed h gives E[T_hB]=E[T_h]E[B]−∂_βE[B]. Since E[n_x(n_x−1)]=2r² and −∂_βr=V⁻¹Σ(ε+h)m(1+m), summing half the identity over x gives exactly Vr²A₁+2rA₂ after multiplying by β. The β dependence chosen for h later is immaterial to this fixed-parameter identity.

The three residual terms vanish uniformly: βVr², Vr²A₁, and rA₂ have respective upper powers −.372, −1.342, and −1.381. Together with log q→0, the variational bound completes the absolute, two-sided log Z(h)−log F(h)=o(1).

## 8. Highest-weight trace and exact zero-mode removal

The SU(2) character identity is exact. On a spin-J multiplet, N runs from D through D+2J in integer steps. Its geometric sum produces (1−e⁻ᵝʰ)Z(h)=Q(h)−R(h), with the exponent βh(2J+1) in R. Q is a scalar highest-weight trace here, distinct from the cutoff projection in §5.

The separate H-only cutoff is essential and valid. The Casimir estimate bounds D≤D₀=CL²E₀ on low energies, with D₀/V→0; hence J≥SV/2 eventually. At h≥h₀ the character remainder there is exponentially small by βh(2J+1)≥cβ^1.451. The omitted high-energy highest-weight sum is at most the full physical trace tail, because physical multiplicities are at least one. Since Q(h)≥1, these are relative errors. Consequently Q(h)/F_exc(h)→1 uniformly on the field interval.

At h₀, βh₀D₀≤Cβ⁻.02(log β)⁵ᐟ²→0, so the H cutoff also proves Q(h₀)/Q(0)→1. The ideal shift satisfies log F_exc(0)−log F_exc(h₀)≤βh₀μ→0. Thus Q(0)/F_exc(0)→1 without inserting an interacting mean.

Restoring multiplicities is also relative: on low energies (2J+1)/(2SV+1)=1−2D/(2SV+1)=1+o(1), and on the complement both normalized sums have the same absolute tail bound. Q(h)≥1 converts it to a relative comparison uniformly for h≥0. This proves (6.10). Its relative form survives multiplication by exp(λaμ), even though aμ can diverge. A total-variation error alone would not have sufficed; none is substituted here.

## 9. Changing-mode ideal limit and weak convergence

The centered geometric log transform has f(0)=f′(0)=0 and second derivative a²e^(a(c+λ))/(e^(a(c+λ))−1)². The inequality 2sinh(u/2)≥u yields its summable domination λ²/(2c²). For fixed k the rescaled dispersion tends to 4π²S|k|², and all finite-volume dispersions dominate c_S|k|². Extending summands by zero outside the representative cube makes dominated convergence legitimate on the fixed countable index set. This is the credited geometric-to-exponential operation in [Chatterjee–Diaconis, arXiv:1306.3625v2](https://arxiv.org/abs/1306.3625v2); I read its full 1<α<2 proof and checked the candidate's changing-spectrum version directly.

The exponential series converges in L² because Σ|k|⁻⁴<∞ in three dimensions. Bounded partial Laplace transforms at 2λ give uniform integrability at λ and identify the limiting product. The same product therefore is the limiting physical Laplace transform at every λ≥0.

The proof does not misapply a nonnegative-variable Laplace continuity theorem. Exponential tilting at 1 produces probability laws whose mgfs converge on an open interval about zero. The mgf continuity argument is justified by exponential tail bounds at ±1/2, tightness, and uniqueness on that interval. After weak convergence of the tilted laws, convergence of their e^y integrals to the limit's integral gives uniform integrability: truncating by min(e^y,R) and using e^y1_{e^y>2R}≤2(e^y−R)_+ proves it explicitly. Untilting therefore gives weak convergence of the original centered laws despite their drifting lower supports.

Finally the limiting variance Σc_k⁻² is positive. The log mgf is analytic near zero, and its third cumulant 2Σc_k⁻³ is positive and finite. This proves non-Gaussianity with the stated normalization and with independent modes indexed by both k and −k; no extraneous factor of two is introduced.

## 10. Disposition

Every mathematical vulnerability listed in the review brief is addressed above. I found no repair needed for the sealed full RF proof. This is a mathematical PASS for the actual full statement. The originality of the absolute finite-volume comparison and SU(2) normalization, the prior-developed-family exclusion, and whether classical rather than pinned dependencies satisfy the campaign's contribution rules remain matters for the separate contribution gate. This review does not decide them or increment the count.
