# i07 arithmetic — complex factor-count twists: explicit main terms and the remaining prime bridge

2026-10-08. Premise: **all** applicable theorems in `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are true. R006 and R008 are accepted. No upstream truth audit is attempted.

**Outcome: no additional substantial finding is claimed. The accepted count remains TWO, with EIGHT still required.** Three distinct candidates were screened. The most promising genuinely additional target is a root-of-unity refinement of R008. Its scalar main term and a truncated-divisor comparison can be calculated rigorously, but the required marked prime-extraction estimate is not proved. Two tempting alternatives are already standard transfers from stronger lower-level corpus interfaces. They are recorded to prevent rediscovery and count inflation.

This report is the assigned arithmetic-lane deliverable, not completion of the parent's ten-finding objective. No agents, commits, staging, shared-index edits, other-project writes, or external messages were used. Writes are confined to this file and `frontier/{sources,experiments}/i07_arithmetic/`.

## 1. Ranked screen and why the first candidate was selected

1. **Complex factor-count twists at prime predecessors.** For fixed integer m≥3, seek joint independence of Ω(p−1) modulo m and the PD(1) factor partition, in each fixed reduced progression. The Fourier modes z^Ω, z^m=1, z≠1, require new estimates. R008 handles z=−1 only. Below I prove the exact covariance/stripping identities and an arbitrary-precision **main-term-subtracted ordinary-integer** comparison, then identify what fails when passing to the prime statistic. Status: promising but unclosed; no count.
2. **Squarefree quartic values at prime arguments.** This looked like a new prime-normalization bridge from family 020. Reading the entire relevant appendix changed the assessment: `prop:cyclotomic-central` already contains the extension below the input scale, the exact enlarged first cell, and the check that its arithmetic proof needs only q²>x and exclusion of fixed bad primes. The general quartic machinery is unchanged. Standard prime sieving then gives a prime-input density. A complete transfer is recorded in §8, but the needed mechanism is already present in the accepted source. Status: correct prospective routine corollary, not a substantial finding.
3. **Two independent full PD partitions for consecutive integers.** Family 012's title says “joint Dickman,” but `eq:distribution-characters` and its subsequent finite Fourier inversion already give independence of **all fixed finite bin-count vectors**, not merely the two largest factors. Refining the mesh gives the full ranked-partition conclusion by standard approximation. Status: already covered at the lower interface; no new bridge, no count.

These are distinct arithmetic routes, not three reformulations of parity. Within candidate 1 I tried, in order: direct Liouville substitution; ordinary-integer main-term subtraction; fixed-modulus additive decomposition; centered Bombieri–Vinogradov plus a complex sieve; and scalar recentering of the marked endpoint. The first is false, the next two have the proved scope below, and the last two leave explicit missing work. The parked cubic reservoir is not relabeled or reopened without its missing norm-minus-one correlation.

## 2. Source contracts and reproducible inputs

All fetched corpus files use immutable **raw GitHub** URLs. [The retrieval manifest](../sources/i07_arithmetic/retrieval-manifest.json) records full paths, URLs, SHA-256 hashes, Git blob hashes, and byte counts. Each blob is checked against the complete `sources/preprints-tree.json`, with `truncated=false`. [The input snapshot](../sources/i07_arithmetic/input-snapshot.json) hashes the rules, pin, complete tree, catalogue, frontier status, R006/R008, their full arithmetic proofs, and relevant reviews. The catalogue was read by selected family sections, never dumped whole.

Prefixes below denote the matching directory under `preprints/`:

- D: `The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/build/`.
- S: `Weighted-Dilation-Graphs-Smooth-Shifted-Primes-and-Totient-Fibers-September-24-2026/build/`.
- E: `Prime-Predecessors-with-an-Even-Number-of-Prime-Factors-September-17-2026/build/`.
- P: `Primitive-roots-for-every-admissible-integer-base-October-4-2026/build/`.
- O: `Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/build/`.
- J: `The-joint-Dickman-law-for-consecutive-integers-September-24-2026/build/`.
- Q: `Squarefree-values-of-quartics-and-power-free-values-of-polynomials-September-24-2026/build/`.
- Z: `The-Quasi-Riemann-Hypothesis-September-30-2026/build/`.

The relevant exact interfaces are:

**D §3 `thm:type-II`, `det:cauchy-square`.** Fix δ,C,D*>0 and damping q∈(0,1); H_m,H_n≥x^δ, H_mH_n≍x. The printed predecessor factor satisfies |F|≤1 and F(ph)=F(h) on the inert bands. The first coefficient is the prime-minus-positive-rough proxy with Mellin phase |v|≤(log x)^C; the second is rough-supported and bounded by (log x)^C. Sufficiently large fixed K, independent of later band exponents, gives error ≪x(log x)^−D*. The proof removes F outside a scalar Cauchy square. P §8 `lem:marked-coefficient-transfer` gives the character/Mellin coefficient interface used in R006/R008. We keep the original scalar coefficients; we do not twist their discrepancy by z^Ω.

**D §6 `thm:two-sided`, `cor:centered-core`.** Fix d≥1, ε>0 and distinct numerical prime slots whose lower endpoints are ≥x^ε and whose upper-endpoint product is ≤x^(1−ε). The first core is exactly W(n)(Σ_ℓ1_{ℓ|n}−C_x), C_x=Σ_ℓ1/ℓ. The second satisfies G(n)=G(n_*) and |G(n)|≤L^C τ(n_*)^C. There are Θ(log L) active groups of harmonic masses in a fixed positive compact interval, small scales exp(L^.27)–exp(L^.36), big scales exp(L^.39)–exp(L^.46); big groups are full prime intervals. The theorem gives every prescribed L^−A for its specified **centered** correlation, uniformly over these groups and slots. It is not a theorem for arbitrary multiplicative twists.

**S §2 `cor:transference-pairing`.** Under `thm:transference`'s parameter choices, the first physical vector is independent of marks at each position, has supremum ≤exp(O(√L)), and both vector norms are ≤X^(1/2)L^C3. The residual pairing is ≪XL^(−E+2C3). Position dependence is permitted. D's `prop:graph-transfer`/`prop:ideal-family` and stripping/multiplier equations specify the resulting comparisons. This pairing controls their combined residual, not each individual comparison.

**D §6 `lem:divisor-model`.** On every positive integer dyad, the marked first weight has a divisor model H₀(n)=Σ_{d'|n}A_d', supported on d'≤exp(O(L^.47)), with Σ|A_d'|/d'≤L^C8. For every fixed N the squared model error is ≪_N R L^−N on n≍R. All prime divisors of d' lie in the active/inert bands; the bounded tuple test requires no regularity. The crucial coefficient bound is a fixed power of L, not an absolute constant.

**D §6 `cor:low-main-term`, `cor:sparse-bound`, `cor:long-prime-saving`, `cor:constant-high`.** The low-time cancellation in the unsigned proof works because its main term depends on ℓ only through 1/ℓ. The high-time tuple argument retains a long prime and uses a coefficient-independent sparse Gram estimate. The separate constant-term high-time argument uses an unweighted logarithmic-phase estimate. Neither theorem states the needed main-term-subtracted complex comparison.

**Z `paper.tex`, `thm:main`.** Every finite-order Hecke L-function over Q(√−3), and every Dirichlet L-function including ζ, has no zero in Re s>7/8; the principal pole at 1 is allowed. This removes zeros, not ζ's pole or the branch singularity of ζ(s)^z. Thus it cannot make the main term in §4 vanish.

**O `introduction.tex`, `thm:elliott`.** For fixed multiplicative f₁,f₂ bounded by one, if one is uniformly nonpretentious against each fixed Dirichlet character times n^it for |t|≤N, the ordinary two-shift integer mean tends to zero. Its qualitative rate is unspecified. `thm:q-affine` gives a fixed positive log saving for two Liouville factors on fixed nonproportional affine forms. Neither permits replacing a factor by a prime indicator or Λ, nor automatically treats an x-dependent marked/slot family at prime normalization. Its quantitative and qualitative centering interfaces were also inspected; the limitation is not inferred only from the title.

**E.** Its sign is the active-band sign in `sh:sign`; the long prime and complementary factor have no active-group prime. Full z^Ω does not have that property. R008 already explained this limitation for λ. The complex inverse phase below is an additional bookkeeping distinction, not a reason to assert an arbitrary-f theorem.

**Families 023 and 029.** The cubic-Gauss-sum first moment and its dispersion concern prime ideals/Gauss weights, not a shifted norm-minus-one rough reservoir. The primitive-root splitting estimates concern Kummer splitting, not Ω(p−1) modes. R006's factorization reservoir and R008's parity independence do not furnish their joint cubic moment. The i06 gap RP/MT/CR remains unchanged.

Exact local source-label ranges and their hashes are in [source-locators.json](../sources/i07_arithmetic/source-locators.json). Manifests identify sources, not independent proof validation.

## 3. Exact new target and a sufficient interior statement

For p≥3, V(p) is the ranked normalized logarithmic factor partition of p−1, counted with multiplicity. Let N(x)=π(2x)−π(x). For fixed M≥1, (b,M)=1, integer m≥3, k≥1 and continuous H on [0,1]^k, the desired assertion is

\[
 \frac1{\pi(X;M,b)}\sum_{\substack{3\le p\le X\\p\equiv b\pmod M}}
  1_{\Omega(p-1)\equiv a\pmod m}H(V(p))
 \longrightarrow \frac1m\,\mathbb EH(\mathrm{PD}(1)),
 \qquad a\in\mathbb Z/m\mathbb Z. \tag{T, UNPROVED}
\]

All parameters are fixed before X→∞. No rate or growing-modulus conclusion is proposed. Finite Fourier inversion reduces T to cancellation of each nontrivial z^Ω mode. If z=−1, R008 already gives that mode; it supplies no other nontrivial root.

For fixed d≥1 and the interior slots of D, put F_x(n)=Σ_ℓ1_{ℓ|n}. A sufficient analytic bridge is

\[
 \sum_{\substack{p\equiv b\pmod M}}
 \Phi((p-1)/x)z^{\Omega(p-1)}F_x(p-1)=o(x/\log x)
 \tag{I_z, UNPROVED}
\]

for every smooth compactly supported Φ and every fixed nontrivial m-th root z. This has to hold at every large real x, for the fixed slot data, with the order of auxiliary limits needed for extraction.

**Conditional implication, proved.** I_z for every nonempty interior tuple implies the corresponding H-weighted mode cancellation, and hence T. Associate the complex signed factorial measures with weights z^Ω; their total variations are dominated by the unsigned R006 factorial measures because |z^Ω|=1. Multiplication by the usual size-biased factors transfers interior convergence to zero. Unsigned GEM tightness exhausts the interior, with expected unseen mass tending to 2^−d. Already d=1 gives zero total signed mass, so a d=0 analytic theorem is unnecessary. Sorting finitely many size-biased draws approximates each ranked coordinate within the unseen mass. Uniform continuity and domination finish the passage. This is the probability argument of R008 with complex finite measures; it is a **routine conditional transfer**, not new evidence for I_z.

## 4. Why direct replacement of Liouville is false

Write f_z(n)=z^Ω(n), |z|=1. For Re s>1,

\[
 \sum_{n\ge1}\frac{f_z(n)}{n^s}
   =\zeta(s)^zG_z(s),\qquad
 G_z(s)=\prod_q\frac{(1-q^{-s})^z}{1-zq^{-s}}. \tag{4.1}
\]

The logarithm of each local factor is O_z(q^−2Re s), so G_z is analytic and nonzero near 1. Choose the branches by continuation from real s>1. Classical Selberg–Delange gives, for fixed z≠−1,1 on the unit circle,

\[
 \sum_{n\le R} f_z(n)
  =R(\log R)^{z-1}
       \left(\frac{G_z(1)}{\Gamma(z)}+O_z((\log R)^{-1})\right).
 \tag{4.2}
\]

Both G_z(1) and 1/Γ(z) are nonzero. Its absolute size is therefore asymptotic to a positive constant times R(log R)^(Re z−1). In particular the zero-main-term assertion ≪_A R(log R)^−A **fails already for modulus one** when A>1−Re z. This is an asymptotic proof, not a numerical experiment.

For z=exp(2πi/3) the exponent is −3/2; for z=i it is −1; for a primitive m-th root closest to 1 it is −(1−cos(2π/m)). A fixed positive logarithmic saving is not arbitrary accuracy after the marked-weight losses.

The exceptional value z=−1 is structural: the coefficients of every algebraic-log term contain 1/Γ(−1−j)=0. That is why the Liouville proof can use zero-main-term BV/SW. For a nonreal root, ζ's fractional pole cannot be removed by a zero-free region. This does **not** disprove T or the exact fully marked LC analogue; it disproves the specific replacement of the ordinary-integer zero-main-term input.

The primary input is de la Bretèche–Tenenbaum, *Remarks on the Selberg–Delange method*, [arXiv:2010.12929v8](https://arxiv.org/pdf/2010.12929v8), Theorem 1.2 and (1.10), PDF p.3. To check applicability: take ρ=z, r=1 and any σ∈(1/2,1); f_z belongs to their F(r,σ), and f_z(q)−ρ=0 at every prime. Their arbitrary A thus gives as many terms as needed. The actual current history lists v8, 24 June 2025; the PDF notes corrections to the published version. The retained page was rendered and visually checked.

## 5. The algebra survives, with an inverse phase

### 5.1 One-sided determinant covariance

For a selected product a of K inert primes and mn−1=ah,

\[
 f_z(mn-1)F_0(mn-1)=z^Kf_z(h)F_0(h). \tag{5.1}
\]

This holds even when a selected prime divides h. Here F₀ is the original invariant bounded factor. After selected-square deletion, the dyadic sum is z^KΣ_h f_z(h)F₀(h)q^ω(h)T(h), with T exactly the original scalar inner sum. Cauchy discards the outside unit-modulus factor. The expanded square is literally `det:cauchy-square`. Thus R008's CT reduction extends to these **constant-on-primes completely multiplicative** twists, retaining the original α,β, character restrictions, and parameter order. This does not assert it for arbitrary f.

### 5.2 Shared/free labels

For a comparison pattern ν, put c_ν=Σ_g|C_g|. The source has Ω(D_R)=Js−c_ν and Ω(D_C)=c_ν, counting repeated labels with multiplicity. Therefore

\[
 f_z(D_Rw)=z^{Js}z^{-c_\nu}f_z(w). \tag{5.2}
\]

**The factor is z^−cν, not z^cν.** They coincide for z=−1 and generally differ for complex roots. It is constant on the pattern, so the fixed-position first-vector condition and the R006 harmonic unit mixing survive. Keep the original ideal kernels; do not multiply them by new phases and claim their norm is unchanged. Only after transference and full dyad/Mellin reassembly does the scalar residual take the form

\[
 \frac1{\varphi(M)}\left(R_z+
       \sum_{\nu\ne0}z^{-c_\nu}C_{\nu,z}\right)=O_A(L^{-A}).
 \tag{5.3}
\]

This is an identity plus the accepted residual estimate. It leaves all comparison main terms. Neither cancellation of their absolute norms nor a conclusion about R_z follows from (5.3) alone.

For the high-time tuple step, isolating a long numerical prime contributes the constant z rather than −1; the residual coefficient remains bounded and the sparse Gram kernel remains the same. This explains why the long-prime phase itself is not the new obstruction. It does **not** dispose of the low-time main terms or the high-time behavior of a newly subtracted model.

## 6. A proved replacement: arbitrary-precision scalar main-term subtraction

Here is the strongest completed analytic statement in this report. It is a standard Selberg–Delange application arranged for the corpus divisor model, and is **not** proposed as a substantial finding.

Fix a nonreal unit root z, ε>0, B,C>0, and ψ∈C_c^∞((0,∞)). Let L=log x. Let Y lie between x and x². Take the D interior long tuples with d fixed, ℓ≤x^(1−ε), and Σ_ℓ1/ℓ=O(1). Let

\[
 H_0(n)=\sum_{a\mid n}A_a,\quad
 a\le\exp(C L^{.47}),\quad
 \sum_a|A_a|/a\le L^C,
\]

with a supported on primes outside the long slots. Suppose H_marks has D's arbitrarily accurate dyadic L² approximation by H₀. Define

\[
 T_z(Y,t)=\frac1Y\sum_w\psi(w/Y)(w/Y)^{it}
      f_z(w)F_x(w)H_{\rm marks}(w),\qquad |t|\le L^B.
\]

For each A>0 there is a **fixed** truncation length N, depending on A,B,C,ε,z,ψ, such that

\[
 T_z(Y,t)=z^d\sum_{\boldsymbol\ell}\frac1\ell
       \sum_a\frac{A_af_z(a)}a\,
       \mathcal M_{z,N}(Y/(\ell a),t)+O(L^{-A})
 \tag{6.1}
\]

uniformly over these data. The explicit model is as follows. Let a_j(z) be the coefficients in the cumulative Selberg–Delange expansion

\[
 A_{z,N}(v)=v\sum_{j=0}^{N-1}a_j(z)(\log v)^{z-1-j},
 \qquad a_0(z)=G_z(1)/\Gamma(z),
\]

and set

\[
 \mathcal M_{z,N}(R,t)
 =\int_0^\infty\psi(u)u^{it} A_{z,N}'(Ru)\,du. \tag{6.2}
\]

The derivative is literal:

\[
 A_{z,N}'(v)=\sum_{j<N}a_j(z)
 \{(\log v)^{z-1-j}+(z-1-j)(\log v)^{z-2-j}\}.
\]

This definition avoids silently suppressing derivative or cutoff terms. All powers use the real positive logarithm at sufficiently large x.

**Proof.** By complete multiplicativity, on w=ℓan the twist separates as z^d f_z(a)f_z(n), without a coprimality condition between n and ℓa. Long primes are outside the mark support, so first putting w=ℓv preserves H_marks(v). Cauchy and D's dyadic L² model error, followed by Σ1/ℓ=O(1), replace H_marks by H₀ with arbitrary prescribed normalized log saving. The resulting inner sum is exactly

\[
 \frac1{\ell a}\left\{\frac1R\sum_n f_z(n)\psi(n/R)(n/R)^{it}\right\},
 \qquad R=Y/(\ell a)\ge x^{\epsilon-o(1)}.
\]

Theorem 1.2 cited above, with arbitrarily large fixed accuracy, supplies a cumulative expansion with remainder ≪v(log v)^−K after enough terms. Stieltjes partial summation with ψ(v/R)(v/R)^it has total variation O_ψ(1+|t|); its support stays in a fixed positive dyad. Thus its normalized error is O(L^(B−K)), uniformly for the displayed scales. Choose K>A+B+C+2 and the expansion length accordingly. Summing the errors with Σ|A_a|/a≤L^C proves (6.1). Integration by parts gives (6.2). □

Even without marks (A₁=1), the leading term is

\[
 \frac{z^dG_z(1)}{\Gamma(z)}\widehat\psi(1+it)
   \sum_{\boldsymbol\ell}\frac{(\log(Y/\ell))^{z-1}}\ell.
 \tag{6.3}
\]

At t=0, Y=x, and fixed logarithmic slot intervals, harmonic prime summation gives

\[
 \frac{z^dG_z(1)}{\Gamma(z)}\Bigl(\int\psi\Bigr)
 L^{z-1}\int_{\mathrm{slots}}
       (1-t_1-\cdots-t_d)^{z-1}\prod_{j=1}^d\frac{dt_j}{t_j}
 +o(L^{\Re z-1}). \tag{6.4}
\]

The repeated-prime exclusions contribute o(1) to the integral calculation; the slots lie in a fixed compact interior simplex. For sufficiently narrow nonempty slots the complex integral is nonzero by continuity, since its integrand at the central point is nonzero and its arguments then lie in an open half-plane. This supplies a genuine asymptotic obstruction to treating every long-tuple scalar mean as arbitrarily small.

D's unsigned centering C_x=Σ1/ℓ does not cancel (6.3): the factor (1−Σt_j)^(z−1) depends on the total slot mass. Subtracting just one scalar leading mean also leaves the subsequent terms of (6.1), whose number must increase with the precision demanded by extraction. With marks, the coefficients include f_z(a), and logarithms of a enter all derivatives. A fixed one-line centering is insufficient.

### Fixed rational-frequency decomposition: an exact additional identity

For fixed k≥1 and h∈Z, let c_r(h) be the Ramanujan sum. The principal-character contribution to the Dirichlet series of f_z(n)e(hn/k) is

\[
 \zeta(s)^zG_z(s)B_{z;k,h}(s),\qquad
 B_{z;k,h}(s)=\sum_{g\mid k}\frac{f_z(g)}{g^s}
 \frac{c_{k/g}(h)}{\varphi(k/g)}
 \prod_{q\mid k/g}(1-zq^{-s}). \tag{6.5}
\]

To prove this, partition n by g=gcd(n,k), put n=gv, and expand the additive character on the units modulo k/g in Dirichlet characters. The principal coefficient is c_{k/g}(h)/φ(k/g); the principal Euler series deletes precisely the factors with q|k/g. The other terms are the nonprincipal character series with their exact finite Fourier coefficients. No gcd(g,v)=1 is imposed.

If a unit u multiplies h, c_r(hu)=c_r(h) for every r|k, so the principal model is invariant under the unit dilations ℓa used in D. This repairs a potential mistaken claim that these dilations create new principal residue characters. It still does not make the principal term zero. Applying fixed-character Selberg–Delange and fixed-modulus PNT gives the analogue of (6.1) for each **fixed** k, with (6.5) inserted in the coefficients. No uniform claim over k≤L^C is inferred from this fixed-k statement.

## 7. Remaining gap after the pivots

The next task is not merely to prove ordinary BV for f_z. The correct ordinary discrepancy is

\[
 \Delta_z(R;q,a)=\sum_{n\le R,\ n\equiv a(q)}f_z(n)
 -\frac1{\varphi(q)}\sum_{n\le R,(n,q)=1}f_z(n),\quad(a,q)=1.
 \tag{7.1}
\]

Granville–Shao, [arXiv:1706.05710v1](https://arxiv.org/pdf/1706.05710v1), Theorem 1.1(b), provides a framework: for f in their class C, a Siegel–Walfisz criterion for Δ plus BV for f restricted to primes implies BV for f. Here f_z is completely multiplicative, |Λ_fz(q^j)|=log q, and its prime restriction is z1_P. Thus prime BV is classical; the remaining SW verification concerns a **centered** discrepancy. Even granting the appropriate centered BV uniformly, its main term remains. The q=1 counterexample to zero-main BV cannot be repaired by citing that theorem.

A complete proof of I_z by this route must supply all of the following together:

1. Uniform additive/multiplicative main-term expansions at D's logarithmic moduli and low Mellin times, with the actual mark models, rather than only the fixed-modulus statement (6.5).
2. A subtraction represented by admissible physical vectors, whose main-term contributions to the **entire** residual (5.3) are calculated or canceled. An expansion for a comparison endpoint alone cannot just be removed from a physical correlation: its coefficient depends on the pattern, slot product, divisor product, and Mellin variable.
3. A high-frequency bound for this subtracted model. D's unweighted `cor:constant-high` does not apply to a new f_z-weighted constant or to fractional-log main terms. The unchanged long-prime estimate controls the retained tuple part; it does not supply this additional model estimate.
4. A compatible presieve with the nonzero principal progression means, and sufficient uniform error to survive the fixed L^C costs in the active-set and factorization expansion. Writing 1±Re f_z and 1±Im f_z makes positive sequences, but does not give them the scalar density model of R008 without proving the new remainder and main-term formulas.

A convenient precise **sufficient** completion contract is the following. For each fixed extraction depth h, inert array, and resulting j, carry D's positive proxy expansion through with the original α,β. For every retained active set P and all coefficient cores G_P produced by that expansion, prove

\[
 \sum_{u+1\equiv b(M)}\Phi(u/x)f_z(u)\mathcal W(u)F_x(u)
           W_1(u)W_1(u+1)G_P(u+1)
   =\mathfrak M_{z,P}(x)+O_A(xL^{-A}), \tag{CM, UNPROVED}
\]

uniformly after the fixed log-power costs, where the explicitly evaluated main terms, **with the actual expansion coefficients**, and the presieved main term have combined size o(x/L). Individual arbitrary-log cancellation is not demanded. CM must use the actual original kernels and account for the factors z^−cν. Its proof would complete composite subtraction; the accepted unsigned deweighting then completes I_z in the order x→∞, number of arrays→∞, depth→∞.

CM is not asserted or hidden as an assumption in a claimed theorem. In particular, I have not proved that the sum of its prospective main terms is small. The explicit scalar expansion (6.1) advances the diagnosis but does not establish CM. The available power saving from a nonreal z does not automatically dominate unspecified fixed positive log losses; nor can one choose the approximation depth after seeing x while invoking a fixed-depth theorem.

Two further shortcuts were screened and rejected. O's qualitative integer Elliott theorem has neither the prime weight nor the required rate/triangular-array uniformity. Also, (−1)^ω(n) differs from λ(n) only through prime-square valuations and can be treated by finite-valuation truncation plus a square tail at prime arguments; that is a routine R008 consequence, not the missing higher-order Fourier modes of Ω or ω.

## 8. Completed but demoted alternative: quartic squarefree values at primes

For clarity, this is the exact mathematical transfer found while screening candidate 2. It is not counted.

**Proposition QP (routine under Q's full lower-level contracts).** Let f∈Z[T] be a fixed irreducible quartic. Let

\[
 r_f^*(q^2)=\#\{a\bmod q^2:(a,q)=1,\ f(a)\equiv0\pmod{q^2}\}.
\]

If r_f^*(q²)<φ(q²) for every prime q, then

\[
 \#\{p\le X:f(p)\text{ squarefree}\}
 \sim \pi(X)\prod_q\left(1-\frac{r_f^*(q^2)}{\varphi(q^2)}\right)>0.
 \tag{QP}
\]

The factor uses **unit roots divided by φ(q²)**; the integer-input product ρ_f(q²)/q² is wrong here. For f(T)=T⁴+1 it is ∏_{q≡1 (8)}(1−4/[q(q−1)]).

**Tail input, with the generalization made explicit.** For a fixed primitive quartic with positive leading coefficient, Q `prop:large-prime-tail` gives x^(1−δ) for q>x. Its worked-example `prop:cyclotomic-central` treats q≥x^(1−10^−6) for T⁴+1. That proof's enlarged-cell argument uses the general quartic Hilbert/curve alternatives, not the later special Q(ζ₈) factorization or Pell argument. It repeats `lem:balanced-factorization` using only absence of fixed bad primes and q²>x, valid for **any** fixed primitive irreducible quartic. Its fixed parameters are

ε₀=1/10⁶, η₋=1−ε₀, η₊=3001/3000, b₋=2999/1500, b₊=2+2ε₀,

t*=1/2, w=24809/100000, m=74427/100000,

u=76819/1200000, v=313933/1000000, τ=1/50000.

The upper radical bounds are (4729,5097,6899)/100000 and δ₁=76819/1200000. The lattice and fiber gaps are exactly 1941/100000 and 15319/120000. Thus the same proof extends the general quartic tail to q≥x^(1−ε₀). Taking the minimum with Q's upper-range saving, and absorbing O(log x) dyads, gives

\[
 \#\{x<n\le2x:\exists q\ge x^{1-\epsilon_0},\ q^2\mid f(n)\}
   \ll_f x^{1-\delta_f}. \tag{8.1}
\]

Q's single global quintic-value exceptional set has size O_f(x^1/5), already harmless. No new continuity assertion or numerical search is needed: the source prints this exact enlarged cell and its arithmetic checks. For nonprimitive f, first remove its fixed content; q above x^(1−ε₀) eventually does not divide it. Sign is immaterial. Keep the original local conditions at the finitely many content primes.

**Prime transfer.** Fix Y beyond the bad primes, then x→∞. For Y<q≤x^1/4, each of the at most four root classes modulo q² is a unit class (q outside the prime divisors of f(0)); Brun–Titchmarsh bounds the number of input primes by

\[
 \ll \frac{x}{\log x}\sum_{q>Y}\frac1{q(q-1)}
 \ll \frac{x}{Y\log x}.
\]

For x^1/4<q<x^(1−ε₀), count all integer inputs:

\[
 \sum_q O_f(x/q^2+1)
 \ll_f x^{3/4}+x^{1-\epsilon_0}=o(x/\log x).
\]

The remaining q are covered by (8.1). Fixed-prime exclusions q≤Y are a finite union of reduced classes modulo ∏_{q≤Y}q². Fixed-modulus PNT therefore gives the finite Euler product times N(x), with o(N(x)) error. Sandwich by the preceding tail, let x→∞ and then Y→∞. The product converges positively since r_f^*(q²)≤4 outside a finite set and all factors are positive. Dyadic summation gives QP. □

The transfer answers a natural stronger-looking prime-input question, but its only potentially new step is already laid out in the companion's lower-level proof. Given the user's instruction to compare against **all** applicable corpus sources, I recommend **not counting QP**. Adding R008 parity/PD weights to the finite-prime sieve would be another routine consequence, not another finding.

Primary checks: Helfgott [arXiv:1112.3820v1](https://arxiv.org/pdf/1112.3820v1), Main Theorem, PDF p.1, gives the cubic squarefree prime-input density with unit local factors. Reuss [arXiv:1307.2802v1](https://arxiv.org/pdf/1307.2802v1), Theorem 1, PDF p.2, concerns exponent d−1, so quartics there are **cube-free**, not squarefree. The corresponding published paper is BLMS 47 (2015), 270–284, DOI 10.1112/blms/bdu116. These establish nearby prior art and the correct normalization; no absence-of-search priority argument is made.

## 9. Demoted alternative: full joint PD is already encoded by J

For fixed J≥2, J uses bins (x^(r/J),x^((r+1)/J)], 1≤r<J, and arbitrary unit phases for their counts, with multiplicity. `eq:distribution-characters` states the product limit for any two independently chosen phase vectors. The subsequent displayed Fourier inversion modulo J+1 is injective on all possible bin-count vectors and explicitly states factorization for every pair of fixed functions of those vectors.

Approximating each ranked factor mass above a fixed cutoff by its bin endpoint gives an error at most 1/J per coordinate. Every omitted factor has normalized size at most 1/J; coordinatewise approximation requires no bound on their number. On n∈[εx,x], log n/log x→1 uniformly; the initial εx integers have mass at most ε. Classical single-integer PD identifies each marginal. First x→∞, then J→∞ and ε→0 yields two independent PD(1) ranked partitions. This is fully encoded by the existing finite-bin statement and standard weak convergence, not a new independence estimate. A theorem about λ labels jointly with both partitions would require another argument; it is not claimed here.

## 10. Literature limits, significance, and reproducibility

The bounded primary-source screen included the current corrected Selberg–Delange manuscript, Granville–Shao's centered BV theorem, Helfgott's cubic theorem, Reuss's prime-input power-free theorem, and the Kyoto proceedings article *Distributions of additive functions on shifted primes*. Its [displayed mod-one example](https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/2092-22.pdf), printed p.194, assumes prime values tending to zero and a small variance tail; it cannot be applied to the constant prime increment defining Ω. [Hildebrand's 1989 paper](https://doi.org/10.1112/plms/s3-59.2.209) was identified through its publisher's primary abstract, but the full PDF returned HTTP 403. Its abstract advertises a **partial** Halász analogue; no unchecked full theorem is used. A Pasten primary PDF retrieval also returned 403 and is not counted as read.

The named prime-input squarefree-value problem is meaningful, and [MathDB's indexed entry 360489](https://mathdb.com/p/360489/squarefree-values-of-polynomials-at-primes) identifies it, but that entry's displayed integer local factor is unsuitable for prime inputs. This report uses the primary unit-root normalization instead. No importance score was observed or invented. The complex-twist target is a concrete refinement of prime-shift multiplicative cancellation; I have not verified a separate named high-significance conjecture exactly identical to T. Neither search absence nor mathematical plausibility certifies worldwide priority.

Reproduce retrieval and checks from the repository root:

```sh
python3 frontier/experiments/i07_arithmetic/retrieve.py
python3 frontier/experiments/i07_arithmetic/literature.py
python3 frontier/experiments/i07_arithmetic/check.py
python3 frontier/experiments/i07_arithmetic/record.py
```

`check.py` checks the cyclotomic exponent identities and the enlarged quartic cell in exact rational arithmetic. It does not sample prime counts or claim asymptotic validation. `record.py` checks retained bytes against the pinned tree and manifests, records exact source-label ranges, checks input changes, and hashes the report and artifacts. The PDF page used for Theorem 1.2 was rendered and visually inspected; mathematical reading used the retained primary PDF/text, not a search snippet.

**Handoff.** There is no result here to promote toward the ten substantial findings. The best further arithmetic task is CM with explicit principal modes and extraction bookkeeping, rather than another scalar Hecke/BV estimate or another complex-sign substitution. The strongest completed additional formula is (6.1), whose standard analytic origin and restricted scope are explicit. QP and the full consecutive-integer PD transfer should be kept as deduplicating notes, not counted breakthroughs.
