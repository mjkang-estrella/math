# I117 — Original I114 audit and unequal-temperature bosonic entropy stability

**Terminal disposition: original I114 analytic claims PASS at their original scopes, without statement repairs. Target B remains unproved and unrefuted. No substantial finding nominated; eight remain accepted.** This is an independent AI proof/disposition audit and a continuation, not human review or formal certification. In particular, the original report never asserted Target B. Its failure to solve B is preserved.

The new results are: an exact fixed-bath factorization with an explicit deficit transfer; uniqueness of the centered optimizer at the full finite-energy, internally entangled input scope; and two rare-tail constructions satisfying **both** the fixed entropy and fixed energy cap. They rule out a uniform strict thermal-relative-entropy contraction improvement and deficit-to-weighted-balance or deficit-to-ordinary-balance moduli, even qualitatively. An entropy-preserving rotation also forces any possible power exponent to be at most 1/2. They do **not** refute Target B, which permits smaller exponents. The factorization and uniqueness are technical consequences of accepted EPnI and the independently reconstructed linear-qEPI equality mechanism. The tail constructions are technical obstructions, not a ninth finding.

## 1. Premises, originals, and source scope

All theorems and lower operations in `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated. No upstream truth audit, contradiction synthesis, or ex-falso deduction is performed. External literature is identified separately and is not stipulated by association. Basic spectral calculus, entropy concavity, relative-entropy data processing, strong subadditivity, finite-dimensional entropy continuity, and Weyl characteristic-function uniqueness are used in their ordinary mathematical senses.

The original report is frozen byte for byte at `../sources/i117_bosonic_entropy_stability/snapshots/frontier/iterations/i114-quantum-information-discovery.md`, SHA-256 `7981bd6832a249ad5e4d7f59e02fe3622215ea175f7ebb26ee11713060ceb8db`. The inherited seal is SHA-256 `f4850563e1ca604d248e0cf8956aed950aadb2ab6977c3237b53e15897540764`. No original report, source, experiment, ledger, or parent result was edited. The original statement was audited before the continuation below. No children were created.

AGENTS.md, upstream identity, the catalogue, and the four current ledgers were read at the relevant entries and frozen. The long ledgers are not represented as wholly semantically read. I39 concerns Haldane disorder, SK entropy/waiting times, and PEPS interfaces, not all quantum information. I07 already screened GAD strong converse and conditional EPnI. I110/I111 add no entropy stability theorem. No I112/I113 working output is a dependency; incidental mentions in the four permitted ledger snapshots are not bindings to those outputs.

Pinned source identities, exact read ranges, and passage hashes are in `read-manifest.json` and `passages.json`. Their URLs identify the actual pinned originals; inherited `search-domain.json` identifies both original bytes/Git blobs and text views. The relevant operations are EP §§1–5; US fields, encoders, recursion and phase-sensitive compilation; AD arbitrary-partner branch/ensemble arguments; PR conditioning-to-threshold and root-support constructions; ZK represented-class operational obstruction and channel completion. The complete tree, not truncated `sources/tree.json`, is used.

Primary literature inspected:

* Li, **Equality in the Bosonic Quantum Entropy Power Inequality**, [2609.40061v1](https://arxiv.org/html/2609.40061v1), §§3.1–3.4, Appendix A.4 and finite-energy characterization. The current abstract page still identifies v1. The fresh v1 text agrees with the inherited text. The instrument/equality mechanism is attributed to Li. Below its needed operations are proved, rather than importing its theorem by fiat.
* De Palma–Trevisan, **The conditional Entropy Power Inequality for bosonic quantum systems**, [1706.00440v2](https://arxiv.org/html/1706.00440v2), dated 4 January 2018, §§3–6 through the end of Theorem 6.1 and Appendix B. It assumes finite input energy, finite memory entropy, and conditional independence. Section 5 uses Gaussian extremality/complementary channels to obtain heat asymptotics. Section 5 below gives a self-contained alternative for the particular linear inequality needed here, using an explicit heterodyne heat-channel representation. Thus no unproved external equality theorem enters the new uniqueness deduction.
* Cuesta, [1902.05298v1](https://arxiv.org/html/1902.05298v1), Theorem 9 and quantitative proof: approximate **product** outputs, all finite moments, explicit second/fourth-moment constants, and Hilbert–Schmidt state distance. The current abstract lists v1. It is not a finite-energy-only trace-distance theorem. No use is made of its claimed constants or of density of Schwartz states as a uniform-moment argument. Its displayed scalar inequality preceding Eq. (41) has an incorrect factor `1/2` (take opposite nonzero complex numbers); this is a literal external-proof defect, not a disproof of its theorem and not a defect in I114, which did not import that proof as certified.
* Fang, [2609.14621v2](https://arxiv.org/html/2609.14621v2), revised 6 October 2026: Theorems 1, 3, 4, the complete sandwiched-norm/information-radius reduction, and Appendix A. The current abstract continues to list v2. This is an external author-theorem comparison, not a stipulated theorem or a complete independent certification of every cited Rényi theorem.

The named significance interface remains the [entropy photon-number conjecture / constrained minimum output entropy problem](https://qiqc-op.com/problem/op_ba39e7a80122b256/). An inherited observed problem-page record is evidence of that connection, not a ranking or priority certificate. Searches and full-domain lexical replay do not prove absence of prior work.

## 2. Independent verdict on ORIGINAL B114

**(1) PASS; (4), including domains and gap, PASS.** For a finite-energy positive trace-one operator, all four products with a single ladder operator are trace class: for example `aρ=(a√ρ)√ρ`, with both factors Hilbert–Schmidt. Creation costs one additional photon. Their Hilbert–Schmidt extensions satisfy

\[
 \|a_j\rho\|_2^2=\operatorname{Tr}(N_j\rho^2)\le\operatorname{Tr}(N_j\rho),
 \qquad \|\rho a_j\|_2^2=\operatorname{Tr}((N_j+1)\rho^2)\le\operatorname{Tr}((N_j+1)\rho).
\]

These are positive-form traces, not cyclic permutations of undefined unbounded products. One proves them with bounded number cutoffs and takes the Hilbert–Schmidt limit. Positivity `ρ²≤ρ` bounds each sum.

In number-basis vectorization, right multiplication by `a` is creation on the second factor. Thus `D_j|ρ⟩=|R_j⟩` and `E_j|ρ⟩=|R_j†⟩`, including the order of the two terms. Both lists are needed; using only D would leave an infinite-dimensional kernel. The finite-mode squeezing transformation in I114 is a genuine unitary canonical transformation. One domain-level construction uses the Schrödinger representation: the real hyperbolic coordinate transformation and its inverse transpose on momenta are implemented by the associated unitary change of variables on L². Schwartz vectors are a core for the transformed oscillator forms. On that core the displayed cosh/sinh formulas hold; closure identifies the forms on the full space. This also identifies the exponential convention in I114: with `U=exp[θ(ab−a†b†)]`, `U†aU=a coshθ−b†sinhθ`. Hence

\[
 \sum_j(D_j^*D_j+E_j^*E_j)=(2r+1)U^*N_{2n}U
\]

as closed forms. Its gap above its unique vacuum is exactly `2r+1`; it is not inferred merely from commutators or a formal recurrence. The normalized vacuum has coefficients `(1−q²)^{n/2}q^{|p|}` on `|p,p⟩`, `q=r/(r+1)`. The finite-energy estimates above put `|ρ⟩` in this form domain. Projection gives `(2r+1)||ρ−cτ_r||₂²≤2Σ||R_j||₂²`. Finally `Tr τ_r²=(2r+1)^{-n}` and `||τ_r||∞=(r+1)^{-n}` give precisely `0≤c≤C_{r,n}`. No bounded inverse of ρ was used.

**(2) PASS.** For `P=1_{N≤K}`, `d_K=binom(K+n,n)` and `qσ=Tr σ(1−P)`, pure-state diagonalization gives `||σ−PσP||₁=√(4qσ−3qσ²)≤2√qσ`; convexity proves the mixed-state inequality. Then

\[
 \|\rho-c\tau_r\|_1\le\sqrt{d_K}\,t+
 2\sqrt{E/(K+1)}+2c\sqrt{nr/(K+1)}.
\]

The absolute trace `|1−c|` is bounded by this same expression. Adding it gives exactly (2), including the factors two and four. Applying a rank estimate directly to the uncompressed infinite operator would be invalid; I114 did not do that.

**(3) PASS, including t=0.** The cube `{0,…,K}^n` contains the total-number simplex, so `d_K≤(K+1)^n`. With `K+1=ceil(t^{-2/(n+1)})`, the rank term is at most `2^{1+n/2}t^{1/(n+1)}` and the tail term has exactly the other displayed coefficients. At zero the Hilbert–Schmidt identity gives `ρ=cτ_r`, and normalization fixes c. At large t the independent trace-distance cap is two.

**(5), metric duality and centered test density, PASS.** In the eigenbasis of faithful ρ the coordinate weight is

\[
 w_{lr}=h(r)\ell(rp_l,(r+1)p_r)\le h(r)(2r+1)/2.
\]

Its diagonal value is exactly `p_l`, since `h(r)ℓ(r,r+1)=1`. Therefore orthogonal projection off I is subtraction of the ρ-mean, and is contractive. The source actually admits finite eigenblocks centered by the full identity; I114's finite-block approximation is also in that space because its ρ-mean is zero. For `Z_M=Z−[TrρZ/TrρP_M]P_M`, with P_M containing Z's support, the squared F-norm of `I−P_M` is `Trρ(I−P_M)→0`; coefficients converge, so `Z_M→Z−TrρZ I` in F. Trace-class R gives convergence of its pairings, and centering gives `q(I)=0`. Thus

\[
 |\operatorname{Tr}R_j^*Z|\le\|q_j\|_{F,*}\sqrt{h(r)(2r+1)/2}\,\|Z\|_2.
\]

Finite eigenblock matrices are Hilbert–Schmidt dense. Taking the dual norm proves (5). There is no assertion that every finite-energy state has finite Q; this restriction matters, and the new sequence in §4 has finite but divergent Q.

**Regularized-minimizer rate and undoing displacement: PASS at the exact original scope.** The source defines `A_*²=Σw_iQ_i²`, `M_*²=Σw_i|μ_i|²` and proves `A_*²+M_*²≤2Cζ/ε` with fixed positive w_i, fixed auxiliary parameters, and uniformly bounded input energies. Displacement reduces energy, preserves spectrum and the F norm, and converts the centered ladder defect to R. Thus (3),(5) give `O(ζ^{1/[2(n+1)]})` for each centered input. If `D(α)=e^{iHα}`, purification and the spectral inequality `|e^{ix}−1|≤|x|` give

\[
 \|D(\alpha)\tau_rD(\alpha)^*-\tau_r\|_1
 \le2\sqrt{\operatorname{Tr}\tau_rH_\alpha^2}
 =2\sqrt{2r+1}\,|\alpha|.
\]

The generator has finite second moment on that purification. Since the means are `O(√ζ)`, undoing displacement preserves the asserted weaker exponent for `ζ≤1`. The input seventh moments used by the source are properties of its constructed Gibbs states, not assumptions on Target B's arbitrary inputs. Neither the rate nor the Hessian inequality applies to arbitrary nonnegative-deficit states. In fact the direct weighted-Q transfer proposed as a possible bridge is false, as §4 proves.

## 3. Independent verdict on ORIGINAL Q114, doubling, counterexamples and S

**Q114 (6) and (7): PASS without repairs.** The heterodyne Fourier transform contributes `exp(−|w|²/4)` at `w/√2` and the prepared `τ_{1/2}` contributes `exp(−|w|²)`, so the total is exactly `χρ(w/√2)exp(−5|w|²/4)`. This is `T_{1/2,2}`. The inverse quadratic form at vacuum is `(3/2)^m exp(|z|²)`, finite for every z. Cauchy–Schwarz with `π_z^{-1/2}|0⟩` proves the stated positive vacuum minorant. Integrating its coefficient gives `G=3^{-m}2^{-N}`; it has no kernel but no positive uniform lower bound.

For an ancillary positive operator, the heterodyne operator-valued measure on the reference is positive, and its tensor product with each positive prepared kernel is positive. Integrating proves complete positivity on every finite ancillary dimension. These normal trace-bounded maps extend to trace class and separable references by finite-rank compression and trace-norm continuity. The branch-0 channel is

\[
 \Psi_0(X)=\Lambda_0((I-G)^{-1/2}X(I-G)^{-1/2});
\]

the inverse here is bounded, with norm at most `(1−3^{-m})^{-1/2}`, and the effect identity proves trace preservation. This is distinct from the unbounded G inverse later compressed.

Both branch probabilities are positive: p₁>0 by injectivity, p₀≥1−3^{-m}. The filter commutes with N, so branch input energy is ≤E/p_f. Its reference marginal satisfies `ω_K=Σp_fω_K^f`; entropy concavity gives `S(ω_K^f)≤S(ω_K)/p_f`. Total output energy is finite, and positivity bounds branch output energy by the total divided by p_f. Joint entropies are bounded above by sums of marginal entropies. Thus all the ordinary mutual informations and flagged chain rules are finite. The FK marginal is identical before and after the branch processing, but the conditional K marginal need not be ω_K. Subtracting the two chain-rule bounds gives `ℓ≥p I(ξ)`, exactly with `ξ_K`.

Pinsker, obtained by a Helstrom binary measurement and classical Pinsker in nats, then gives

\[
 \|\sqrt G\,\omega\sqrt G-(\sqrt G\omega_X\sqrt G)\otimes\xi_K\|_1
 \le\sqrt{2p\ell}\le\sqrt{2\ell}.
\]

The operator `B_L=P_LG^{-1/2}` is bounded with squared norm `3^m2^L`. Multiplying by it yields the compressed product comparison with ξ_K. Both compared full states have the same X energy. Their two gentle tails cost `4√(E/(L+1))`. Partial trace controls the change `ξ_K→ω_K` by the same bound, giving exactly `2·3^m2^L√(2ℓ)+8√(E/(L+1))`. Taking the specified floor gives (7), including its coefficient 16 and its natural logarithm. At ℓ=0 take L to infinity after fixing it. These arguments work for arbitrary separable K with finite entropy, not merely a classical or bounded-dimensional reference.

**Exact doubling/noisy-correlation consequence: PASS.** With four independent inputs and memory `M=A_+B_+`, the A-group/B-group tensor factorization gives `I(A_-;B_-|M)=0`. The chain rules and commuting passive rotations give, for linear weight η,

\[
 L_\eta(A_1,B_1)+L_\eta(A_2,B_2)
 =L_\eta(A_+,B_+)+L_\eta(A_-,B_-|M)+I(C_-;E_+|C_+).
\]

Every entropy is finite because total energy is finite. Both entropy deficits on the right are nonnegative; the needed conditional linear qEPI is proved in §5, with no conditional EPnI. Set the second pair to `(τ₂,τ₂)`, whose rotated outputs are independent τ₂ states. If `σ_CJ=(id⊗Φ)ω_CE`, the other circuit ordering gives

\[
 I(C_-;J|C_+)=I(C;J)_\sigma-I(C_+;J)_{(\Phi\otimes id)\sigma}.
\]

Independence of the added C thermal from CJ is essential here. Hence Q114 controls the noisy correlations with loss at most Lη. At the original unequal thermal pair, however, `Lη=n[g(s)−ηg(r)−(1−η)g(b)]>0` while Δ=0, and the output cross covariance is nonzero. This failure is preserved. It does not become a Δ estimate merely by subtracting a scalar from an inequality whose other terms also have nonzero baselines.

**Both original counterexamples: PASS at their stated scopes.** In the equal-weight vacuum/Fock-bit example the correlation distance is one and the information is log 2. Expanding the output number gives mean `k/2+1` and variance `(5k+8)/4`. The vacuum output mean is one. The Markov/Chebyshev decision rule has average error at most `12/k+16/k²`; Fano yields loss tending to zero. The energies k/2 diverge: this disproves only an energy-cap-free information-loss modulus. In the original thermal/Fock mixture with weight c₀/k, trace distance vanishes, energy tends to nr+c₀ and entropy tends to ng(r), giving relative entropy limit h(r)c₀. Its entropy was not fixed exactly, so it was correctly not called a Target B counterexample. Section 4 strengthens this obstruction while preserving the target constraints.

**Symmetries, endpoints, compactness: PASS.** Displacements preserve the two entropies and move the optimizer; common finite-mode symplectic transformations commute with the scalar two-port mixing but generally change the fixed isotropic bath. Passive invariance does not produce a distinct isotropic thermal state. At η=0,1 arbitrary inputs provide trivial equality, so uniqueness at those endpoints is false. At E=nr entropy-energy equality forces τ_r. Finite-energy caps give compactness and entropy continuity; centeredness is closed, since the cutoff estimate on first moments in §4 tends uniformly to zero. Even with the new uniqueness result this yields only an unspecified modulus, not a power. It is not offered as a solution to B.

**High-precision synthesis S: PASS, technical at full source-operation scope.** The actual fields/encoders are defined for every L≥1, not just the source's final convenient choice L=10000J. Choose the least integer L with `72J(3/4)^L≤2^{-k}`. It is deterministically computable by rational integer arithmetic in polynomial time and is O(k+log(n+1)). The source's dimensions are `h=ceil(log₂(L+1))`, `b=nL+h`, `K=b(L+1)`. The modulus is strictly larger than `L2^{nL}`, so the power-sum argument retains all multisets and the row bound is L. There is one smaller synthesis call per level. Summing its actual qubit/slot bounds gives exactly the two O-expressions in I114.

For compilation retain the stronger recurrence already proved in the source: `e_{j+1}≤C₀e_j^{3/2}`, `ℓ_{j+1}≤5ℓ_j`. Hardcode a sufficiently fine fixed net and a rational upper bound on C₀. With `b₀=C₀²e₀<1`, induction gives `C₀²e_j≤b₀^{(3/2)^j}`. Choosing j by integer upper bounds yields `ℓ=O((1+log(1/ξ))^{log5/log(3/2)})`, and the generator only needs this length, not a search for the word. Use per-slot error `ξ=2^{-k}/[4(S+1)]` and the phase-sensitive two-word construction; each word is approximated to ξ/2. The second word acts on a zero scratch bit and keeps the scalar phase as a coherent relative phase. Fixed-symbol controlled H,T,T† and reversible lookup are exact by the source's explicit gate constructions. Address length is `O(Q+log(S+1)+log(ℓ+1))`. Ideal-prefix telescoping applies each error only to clean scratch and bounds total compilation error by ε/4. With the skeleton error ≤ε/4, clean isometry error is ≤ε/2. Tensoring a reference leaves this operator norm unchanged; the pure-vector trace bound and partial trace give full diamond error ≤ε.

The quantifiers are **one polynomial-time skeleton generator, for every U some U-dependent Boolean truth table**. Oracle synthesis, storage and truth-table generation are not polynomially bounded. Coherent supplied labels add their bit length to resources and preserve the same blockwise norm proof. Ordinary channel composition alone would not check these requirements; the actual lower operations do. No efficient description of an arbitrary U was inferred.

**Contribution comparisons: PASS at the scopes actually asserted.** B114 uses a thermal oscillator gap plus energy truncation; Q114 uses Li's explicit instrument plus compressed inversion; both are technical. S is paid by the full accepted encoder and commutator-recursion operations. AD already handles arbitrary finite-dimensional CPTP partners and entangled signal inputs; its partner may still require capacity regularization. Fang v2's sandwiched CP-map multiplicativity is stronger and covers all Rényi orders and arbitrary entangled codes in the screened unassisted problem. This external exact duplicate is not inferred from ordinary Holevo additivity. ZK already includes tensor powers, its admitted completed/countable public-record protocols, conditioning at every positive success probability, and the 2m+1-dimensional absorbing-flag completion; the full Choi matrix can have a product flag corner even though another corner certifies entanglement. PR's full transfer gives δ^{1+1/β} from conditioning error O(τ^β); β=1/4 gives δ⁵, and its root construction gives β=1/2 only with κ_μ. Neither a commuting-operator result nor a distribution-uniform cubic threshold follows. G was unresolved, not disproved. None of these comparisons is a universal literature absence claim.

## 4. Route I — paying localization and small-eigenvalue costs; a fixed-entropy obstruction

Fix the original parameters n≥2, r,b>0 unequal, 0<η<1 and E>nr. Write `s=ηr+(1−η)b`, `H=ng(r)`, and

\[
 f(x)=n g\bigl(\eta g^{-1}(x/n)+(1-\eta)b\bigr),\qquad
 F(\sigma)=S(T_{\eta,b}\sigma)-f(S(\sigma)).
\]

EPnI gives F≥0 for every finite-energy σ. On the target constraint, F(ρ)=Δ. This extension allows auxiliary variations without pretending their entropies stay fixed.

### 4.1 Explicit cutoff and entropy budgets

Let P_K be the total-number cutoff, q=Trρ(1−P_K)≤E/(K+1)<1/2, and `ρ_K=P_KρP_K/(1−q)`. Then

\[
 \|\rho-\rho_K\|_1\le2\sqrt q+q,
 \quad \operatorname{Tr}\rho_KN\le E/(1-q),
 \quad |S(\rho)-S(\rho_K)|\le B_E(q),
\]

where

\[
 B_E(q)=h_2(q)+qn g(E/(nq))+qn g(E/[n(1-q)]).
\]

To prove the entropy bound, pinch into P_K and its complement. Recording the binary measurement changes entropy by a number in [0,h₂(q)] (the isometry recording its outcome has binary environment; subadditivity/Araki–Lieb give the upper bound). The pinched entropy is `h₂(q)+(1−q)S(ρ_K)+qS(ρ_Q)`. Bound the two conditional entropies by their thermal energy bounds; taking the absolute difference proves B_E. The zero-q values are continuous limits.

For clarity an explicit entropy continuity budget can be obtained without small-eigenvalue assumptions. If two states have energy ≤F₀ and half trace distance d≤1/8, set `M=ceil(F₀/d²)` and `D=binom(M+n,n)`. Both cutoff tails are ≤d². Their normalized compressed states have half distance at most `2d/(1−d²)≤3d`; this follows by compressing their difference and bounding the difference of their normalization traces by 2d. Finite-dimensional entropy continuity, followed by the preceding two tail bounds, gives

\[
 \omega_{F_0}(d)=3d\log D+h_2(3d)+2B_{F_0}(d^2)
\]

as an upper bound on the entropy difference. Here use the bound with actual compressed distance x≤3d, `x log D+h₂(x)`, increasing for x≤3/8; D=1 is harmless. Each term of B is increasing on the relevant q range or bounded by its displayed endpoint using the perspective concavity of g. Thus `ω_{F₀}(d)=O_{n,F₀}(d log(1/d))`. F₀=0 means both states are vacuum and is separate. This derives the output continuity cost used next, rather than assuming a hidden uniform Hessian bound.

Smooth inside P_K by `σ=(1−θ)ρ_K+θP_K/d_K`, θ=K^{-2}, K≥2. Its eigenvalue floor on that block is `m=θ/d_K`, its energy is ≤E/(1−q)+1/K, and its distance from ρ_K is ≤2θ. Its entropy changes by at most `h₂(θ)+θlog d_K`. Channel contraction and the preceding modulus, with a fixed enlarged output energy cap, give

\[
 0\le F(\sigma)\le\Delta+C_{n,E,r,b,\eta}\,K^{-1/2}\log(K+1).
 \tag{L1}
\]

For sufficiently large K the input entropies stay in a fixed compact interval about H>0, where f', f'' are bounded. The finitely many excluded K are irrelevant to this route. The input cutoff entropy error is smaller, O(log K/K); the output coherence/continuity error is the larger term in L1.

Centering is also paid. Since a_j lowers total number, `a_j−P_Ka_jP_K=a_j(1−P_K)`. Hilbert–Schmidt Cauchy–Schwarz gives

\[
 \sum_j|\operatorname{Tr}\rho a_j(1-P_K)|^2
 \le q\sum_j\operatorname{Tr}\rho a_ja_j^*=q(E+n).
\]

For centered ρ this bounds the squared mean of ρ_K by `q(E+n)/(1−q)²`; the diagonal smoothing has zero mean. Displacing σ by its own mean reduces its energy and leaves F unchanged. These auxiliary states are used only to test a route, never substituted for the original input in Target B.

For a traceless Hermitian block matrix A with `||A||₂=1`, two-sided positivity of `σ+tA` is guaranteed only for `|t|≤m/2`. At such points the input entropy Hessian has absolute value at most `2/m`. The output BKM quadratic form is no greater than the input one by differentiating relative-entropy data processing on this finite input block. Output logarithms are legitimate: `σ+tA≥(m/2)|0⟩⟨0|` implies

\[
 T(\sigma+tA)\ge(m/2)\tau_{(1-\eta)b},
 \quad -\log T(\sigma+tA)\le C+|\log(m/2)|+h((1-\eta)b)N
\]

as forms. Finite input blocks have all moments, and the thermal channel sends them to exponentially decaying output number tails; equivalently the characteristic polynomial times Gaussian gives this property. Resolvent differentiation, dominated by these logarithmic/energy bounds and the input BKM bound, justifies the entropy derivatives. Also `|DS(A)|≤√d_K |log(m/2)|`. Consequently along the allowed segment

\[
 |D^2F(A,A)|\le H_K:={2(1+\sup|f'|)\over m}
 +\sup|f''|\,d_K\log^2(m/2).
\]

Global F≥0 and Taylor's theorem give the actual boundary-aware estimate

\[
 |DF_\sigma(A)|\le\inf_{0<t\le m/2}
 \{F(\sigma)/t+H_Kt/2\}.\tag{L2}
\]

The square-root choice requires `F(σ)≤H_Km²/8`. In the present budget, `m≈K^{-(n+2)}` while L1 only bounds the excess by `Δ+O(K^{-1/2}log K)`. The uniform bound L1 does not meet that requirement at increasing K; the endpoint t=m/2 instead costs `2F(σ)/m+H_Km/4`. Thus this localization calculation supplies **no** vanishing gradient bound. This is an obstruction to this budget, not a proof that every actual cutoff realizes its worst error. A trace-ball constraint would additionally have a normal functional; dropping it is unjustified. A fourth-moment penalty on original ρ is unavailable. No infinite-dimensional Łojasiewicz assertion is used.

### 4.2 Exact entropy repair of rare Fock tails

The following construction disproves the strongest natural missing transfer on **the original constraint set**. Choose any `0<c<E−nr`. For integers k tending to infinity let p=c/k, `v_k=|k,0,…,0⟩`, and define

\[
 \rho_k(x)=(1-p)\tau_x+p|v_k\rangle\langle v_k|.
\]

For every sufficiently large k there is `x_k∈(r/2,r)` such that

\[
 S(\rho_k(x_k))=ng(r),\quad
 r-x_k=O(\log k/k),\quad
 \operatorname{Tr}\rho_k(x_k)N<E.
 \tag{T1}
\]

Here is an exact entropy formula, avoiding any numerical root assertion. Put `a=(1-p)t_k(x)`, `t_k(x)=(x+1)^{-n}(x/(x+1))^k`, and

\[
 J(a,p)=(a+p)h_2\bigl(p/(a+p)\bigr)
 =a\log(1+p/a)+p\log(1+a/p).
\]

The classical label distinguishing the two components is ambiguous only at v_k. The entropy chain rule for their diagonal laws gives

\[
 S(\rho_k(x))=(1-p)ng(x)+h_2(p)-J(a,p).\tag{T2}
\]

At x=r, `J≤a[1+log(1+p/a)]` is exponentially small times O(k), whereas `h₂(p)−p ng(r)>0` eventually. At x=r/2, the upper mixture bound `(1-p)ng(r/2)+h₂(p)` is less than ng(r) eventually. Continuity in x (also direct from T2) and the intermediate value theorem give x_k. From concavity and the upper mixture entropy bound at that root,

\[
 0\le ng(r)-ng(x_k)\le h_2(p),
\]

so `r−x_k≤h₂(p)/(n h(r))`. The exact energy is `(1-p)nx_k+c<nr+c<E`. These states are faithful, centered, have no finite-support restriction, and satisfy every target hypothesis. Their use as counterexamples to a proposed universal transfer needs no entanglement: a diagonal subfamily already suffices.

They converge in trace norm to τ_r, because thermal states are trace-continuous in x on `[r/2,r]` by domination by a summable geometric law and p→0. Their energies tend to nr+c, not nr. The entropy identity gives

\[
 D(\rho_k\|\tau_r)\longrightarrow h(r)c>0.\tag{T3}
\]

The outputs converge in trace norm to τ_s with uniformly bounded energy, so their entropies converge and `Δ_k→0`. More explicitly mixture concavity/upper mixing entropy and
`S(T|v_k⟩⟨v_k|)≤n g((ηk+(1−η)nb)/n)` give `0≤Δ_k=O(log k/k)`. This is an upper bound, not a lower asymptotic and not a power-bound counterexample.

For the centered weighted defect Q at the **fixed parameter r**, one matrix entry already diverges. Let u=v_k−e₁ and v=v_k. Its squared contribution to the Hilbert dual norm is

\[
 {k[(r+1)P_v-rP_u]^2\over
 h(r)\ell(rP_u,(r+1)P_v)}
 ={k[(r+1)P_v-rP_u]\over h(r)}
 \log{(r+1)P_v\over rP_u},\tag{T4}
\]

where `P_v=p+(1-p)t_k(x_k)` and `P_u=(1-p)t_{k-1}(x_k)`. The test `|u⟩⟨v|` is centered, so restriction to centered tests changes nothing. On `[r/2,r]` the thermal probabilities decay uniformly exponentially, and x_k→r. Thus

\[
 (r+1)P_v-rP_u=(r+1)c/k+O(e^{-a_0k}),
 \quad \log{(r+1)P_v\over rP_u}=k h(x_k)+O(\log k),
\]

and T4 divided by k tends to `(r+1)c`. In particular `Q(ρ_k)^2≥((r+1)c/2)k` eventually. For each fixed k its full dual sum is finite: away from finitely many edges incident to v_k, probabilities are a common multiple of the thermal law at x_k, so the sum is a convergent geometric first-moment sum; the exceptional edges have positive finite probabilities. Each state even has all moments, but those moments have no common cap (`Trρ_kN²≥ck`).

Consequently **no** function m(d)→0 can bound Q(ρ) by m(Δ) on the original target set. In particular the direct proposed `Q≤CΔ^β` bridge is false for every β>0. Likewise no bound `D(ρ||τ_r)≤m(Δ)` holds there. Ordinary Hilbert–Schmidt R is a different defect; T4 alone says nothing against a transfer to that weaker defect. The next, separate construction closes that loophole. Neither construction contradicts the original B114 theorem.

### 4.3 Entropy-preserving rotation: ordinary balance obstruction and exponent ceiling

Keep `0<c<E−nr`. Write `p₀=(r+1)^{-n}`, `p_k=p₀(r/(r+1))^k`, `d_k=p₀−p_k`. For sufficiently large k≥2 let U_k be a real rotation in the span of vacuum and v_k, identity elsewhere, with

\[
 \sin^2\theta_k={c\over k d_k},\qquad
 \widehat\rho_k=U_k\tau_rU_k^*.
\]

Its diagonal differs from τ_r only by subtracting c/k at vacuum and adding c/k at v_k. Its only new off-diagonal pair has magnitude `d_k sinθ_k cosθ_k`. Consequently the state is faithful, centered (no new matrix entry connects number states differing by one photon in one mode), and

\[
 S(\widehat\rho_k)=ng(r),\quad
 \operatorname{Tr}\widehat\rho_kN=nr+c<E,\quad
 \|\widehat\rho_k-\tau_r\|_1=2\sqrt{cd_k/k}.
 \tag{T5}
\]

The entropy equality is exact unitary invariance. The trace norm is the sum of the two absolute eigenvalues of the traceless 2×2 difference, namely `d_k|sinθ_k|`. Thus these are actual original-scope states, not approximately corrected inputs.

For the ordinary balance residual at fixed r, its `(v_k−e₁,0)` entry is `(r+1)√k (widehatρ_k)_{v_k,0}`: the corresponding entry of ρa is zero. Therefore

\[
 \sum_j\|R_j(\widehat\rho_k)\|_2^2
 \ge(r+1)^2\bigl(cd_k-c^2/k\bigr)
 \longrightarrow(r+1)^2cp_0>0.\tag{T6}
\]

All these products are defined by finite energy as in the original audit. This proves failure of any vanishing deficit-to-ordinary-balance modulus once the deficit convergence below is checked. It does not contradict B114: that is a sufficient bound on trace distance in terms of R, not a converse, and R is not trace-continuous on an energy cap.

Here the deficit has a sharper elementary upper bound. Let `p=c/k`, and let the global phase twirl be the average of `exp(iϕN)`. It removes the sole new off-diagonal pair and leaves the diagonal state
`barρ_k=τ_r+p(|v_k⟩⟨v_k|−|0⟩⟨0|)`. The thermal attenuator commutes with this twirl. Entropy concavity therefore gives `S(T widehatρ_k)≤S(T barρ_k)`. For large k, p<p₀ and
`σ_k=(τ_r−p|0⟩⟨0|)/(1−p)` is a state. We have `barρ_k=(1−p)σ_k+p|v_k⟩⟨v_k|` and `τ_r=(1−p)σ_k+p|0⟩⟨0|`. Apply the upper mixture entropy bound to the first identity after T and entropy concavity to the second. Subtracting yields

\[
 0\le\widehat\Delta_k
 \le h_2(p)+p\{S(T|v_k\rangle\langle v_k|)-S(T|0\rangle\langle0|)\}
 \le h_2(c/k)+{cn\over k}g\left({\eta k+(1-\eta)nb\over n}\right)
 =O(\log k/k).\tag{T7}
\]

All mixture entropies are finite by their explicit energies. The global twirl can be obtained by finite convex averages and energy-entropy continuity, so no differential entropy is involved. The lower bound is stipulated EPnI applied to the original fixed-entropy state. Uniqueness in §5 also makes these deficits strictly positive, since the centered states are not τ_r.

Equations T5 and T7 show that **no Target B estimate can hold with α>1/2**, for any of its fixed allowed parameter choices: the ratio of distance to Δ^α is bounded below by a constant times `k^{α−1/2}/(log k)^α`, which diverges. They leave all `0<α≤1/2` open. They also give `D(widehatρ_k||τ_r)=h(r)c` exactly. The construction is a technical energy-preserving-budget test using an entropy-preserving two-level unitary, not a full counterexample to B and not a substantial nomination.

## 5. Route II — exact baseline subtraction, factorization, and uniqueness

### 5.1 Thermal and correlated reference identities

For any original target input with e=TrρN, thermal relative entropy gives the exact identities

\[
 D_{\rm in}=h(r)(e-nr),\qquad
 D_{\rm out}=\eta h(s)(e-nr)-\Delta,
 \qquad \Delta=c_*D_{\rm in}-D_{\rm out},
 \quad c_*={\eta h(s)\over h(r)}\in(0,1).\tag{R1}
\]

The energy relation uses the independent centered thermal bath; arbitrary internal input entanglement is allowed. Positivity of D gives e≥nr. To check c_*<1, `s>ηr`, h is decreasing, and strict concavity of log gives `η log(1+1/(ηr))<log(1+1/r)`. EPnI is exactly the sharp contraction `Dout≤c_*Din` on this entropy slice. The rare-tail sequence gives `Dout/Din→c_*`, so a uniform strict coefficient smaller than c_* is impossible **even centered with fixed entropy and fixed energy cap**. This is the actual thermal-relative-entropy obstruction; subtracting the unequal-temperature scalar baseline alone does not fix it.

For the full beam-splitter output Ω and the correlated Gaussian reference `Γ=U_η(τ_r⊗τ_b)U_η*`, unitary invariance gives `D(Ω||Γ)=Din`. Its marginals are τ_s and `τ_t`, `t=(1−η)r+ηb`. The logarithm of Γ is a quadratic Hamiltonian with a cross term proportional to `h(r)−h(b)`; it is not the sum of marginal logarithms. Define `K=logΓ−log(τ_s⊗τ_t)`. All its expectations are finite because its cross ladder terms are bounded in quadratic-form expectation by total energy. Direct expansion gives

\[
 D(\Omega\|\Gamma)=D(\Omega_C\|\tau_s)+D(\Omega_E\|\tau_t)
 +I(C;E)_\Omega-\operatorname{Tr}\Omega K.\tag{R2}
\]

At Γ, `TrΓK=I(C;E)_Γ=n[g(s)+g(t)−g(r)−g(b)]`. Subtracting that baseline in R2 yields the exact remainder

\[
 D_{\rm in}=D_C+D_E+(I_\Omega-I_\Gamma)-\operatorname{Tr}(\Omega-\Gamma)K.
\]

Neither of the last two terms has a favorable sign separately. In particular it is not a sum of nonnegative deficits that Δ controls. This is the correlated-reference calculation, with its full missing term retained. No product-output assumption is imposed on unequal-temperature extremizers.

### 5.2 Exact transfer to an equal-temperature channel on the SAME input

**Proposition F117.** Set

\[
 u={\eta+\min\{1,s/r\}\over2},\qquad t=\eta/u,
 \qquad c={s-ur\over1-u}.
\]

Then `η<u<1`, `0<t<1`, c>0, and

\[
 T_{\eta,b}=T_{u,c}\circ T_{t,r}.\tag{F1}
\]

For every target input, with `δ=S(T_{t,r}ρ)−ng(r)≥0`,

\[
 0\le\delta\le\Delta/\kappa,
 \qquad \kappa={u\,h(uM+(1-u)c)\over h(r)}>0,
 \quad M={tE+(1-t)nr\over n}.\tag{F2}
\]

**Proof.** The scalar channel characteristic formula proves composition: the signal coefficient is ut=η and the added photon number is `u(1−t)r+(1−u)c=s−ηr=(1−η)b`. The vacuum half-photon contributions also agree because the attenuations multiply. Thus this is equality of channels on arbitrary inputs, not just Gaussian states. EP gives δ≥0. If `x=g^{-1}(S(T_{t,r}ρ)/n)`, energy and entropy-energy bounds give r≤x≤M. Apply EP to the second factor:

\[
 \Delta\ge n[g(ux+(1-u)c)-g(s)].
\]

The derivative of the right-hand thermal entropy as a function of input entropy is `u h(ux+(1−u)c)/h(x)`, bounded below on [r,M] by κ. Integrating from r to x proves F2. All states retain finite energies. ∎

This does not choose a new physical bath for the target or replace ρ by a nearby state. The original fixed channel is exactly decomposed, and the same ρ is the first input. It does not by itself establish a stability theorem at equal temperature; in particular it is **not** a replacement of Target B by an asserted solved special case. It explains why the positive original Li baseline can be bypassed by a different circuit, rather than incorrectly bounded in the original circuit.

### 5.3 The external linear-qEPI operation, proved at the needed scope

Here is a proof of the needed conditional **linear** qEPI for arbitrary finite-energy bosonic A,B and finite-entropy memory M with `I(A;B|M)=0`. It reconstructs De Palma–Trevisan's integral-information argument; the heat asymptotic is established explicitly, so the external theorem is not an additional stipulated premise.

Let `N_v` be additive Gaussian displacement noise adding v photons per mode, and write `H_X(v)=S(X|M)_{(N_v⊗id)ρ}`. Finite energy bounds S(X); finite S(M) bounds joint entropy. Noise increments equal the conditional mutual information with their classical Gaussian displacement label Z, since displacements leave the conditional entropies of the labelled branches unchanged:

\[
 H_X(v+w)-H_X(v)=I(X;Z|M)\ge0.
\]

Increasing v is an additional channel on X; data processing makes each fixed-w increment decrease. Hence H_X is concave. At v=0 it is continuous: strong continuity of displacements gives trace convergence; lower semicontinuity of joint entropy gives the lower limit, and lower semicontinuity of `D(ρ_XM||τ_a⊗ρ_M)` together with exact energy `e+nv` gives the upper limit through the identity
`S(X|M)=h(a)e+nlog(a+1)−D(ρ_XM||τ_a⊗ρ_M)`. This also proves continuity at all finite v. Concavity gives local absolute continuity and finite derivatives almost everywhere away from zero; continuity at zero makes the improper derivative integral recover the increment there as well.

For the large-v asymptotic, for v>1 the channel has the explicit heterodyne representation

\[
 N_v(\rho)=\int Q_\rho(z)D(z)\tau_{v-1}D(z)^*\,d^{2n}z.
\]

Indeed the heterodyne transform contributes `e^{-|w|²/2}` and `τ_{v-1}` contributes `e^{-(v-1/2)|w|²}`, giving `χρ(w)e^{-v|w|²}`. Positivity of the kernels proves the ancillary version. If the input has energy e, output entropy is between `ng(v−1)` by concavity and `ng(v+e/n)` by its energy. In the joint output, Y and M are independent given the classical heterodyne label Z. Data processing from the classical Z to its conditional M state gives

\[
 I(Y;M)\le I(Y;Z)=S(Y)-ng(v-1).
\]

Continuous classical registers can be interpreted through relative-entropy integrals or finite measurable partitions followed by monotone refinement; the displayed Holevo quantity is finite by the preceding entropy bounds. Therefore

\[
 ng(v-1)\le H_Y(v)\le ng(v+e/n),
 \qquad H_Y(v)=n\log v+n+o(1).
\]

For the Stam step, jointly displace A by √η Z and B by √(1−η) Z, so the retained output is displaced by Z. Conditional independence holds in every labelled branch. The chain identity gives

\[
 I(AB;Z|M)=I(A;Z|M)+I(B;Z|M)
 -I(A;B|M)+I(A;B|MZ)
 \le I(A;Z|M)+I(B;Z|M).
\]

Output data processing and the noise-increment identity imply
`H_C(w)−H_C(0)≤H_A(ηw)−H_A(0)+H_B((1−η)w)−H_B(0)`. Now evolve A and B by independent noise N_v; conditional independence persists by conditional-mutual-information data processing, and C evolves by N_v. Taking right derivatives, or difference quotients at common differentiability points, shows that
`H_C(v)−ηH_A(v)−(1−η)H_B(v)` is nonincreasing. Its large-v limit is zero by the asymptotic just proved. Its value at zero is therefore nonnegative, proving the required inequality. This proof uses no finite fourth moment and includes arbitrary quantum M under the displayed finiteness assumptions. The unconditional case is M trivial.

### 5.4 Full uniqueness, and its precise quantitative limit

**Theorem U117 (technical uniqueness).** For fixed finite n≥1, r,b>0, 0<η<1, a finite-energy input with `S(ρ)=ng(r)` has `S(T_{η,b}ρ)=ng(s)` if and only if it is a displacement of τ_r. In particular a centered exact optimizer is τ_r. No energy cap beyond finiteness, faithfulness, mode-product hypothesis, or higher moment is required. This includes the original unequal-temperature parameters.

**Proof.** F1–F2 imply `S(T_{t,r}ρ)=ng(r)`; thus the linear deficit for `(ρ,τ_r)` is zero. Apply the exact doubling identity with auxiliary `(τ₂,τ₂)`. The preceding conditional linear qEPI makes its remainders nonnegative, so the noisy mutual-information loss is zero. Q114, whose instrument proof was independently checked above, makes `(id⊗Φ)ω_CE` a product. Weyl characteristic functions remove Φ exactly: its multiplier `exp(−5|w|²/4)` is never zero and its argument rescaling is onto. Thus ω_CE itself is a product. This exact cancellation asserts no quantitative inverse bound.

Because one input is known thermal, no external Darmois–Skitovich theorem is needed to finish. In complex Weyl coordinates, put a=√t, d=√(1−t), R=r+1/2. Product outputs give, for all x,y∈Cⁿ (take output arguments x/a and −y/d),

\[
 \chi_\rho(x+y)=\chi_\rho(x)\chi_\rho(y)
                     e^{-2R\operatorname{Re}(x\cdot\bar y)}.
\]

Consequently `φ(x)=e^{R|x|²}χρ(x)` is continuous, φ(0)=1, and φ(x+y)=φ(x)φ(y). It has no zeros: split any x into sufficiently many equal small increments. Also φ(−x)=conjugate φ(x) and φ(x)φ(−x)=1, so it takes values on the unit circle. On a neighborhood of zero choose its continuous argument; additivity there makes that argument real-linear (first on rational multiples and sums, then by continuity), and subdivision extends this to all x. Hence φ(x)=exp(iℓ(x)) for a real linear functional ℓ. This is exactly a displacement phase; finite first moments identify it with the input mean. Thus ρ is a displaced τ_r by Weyl uniqueness. Conversely displacement covariance and thermal mixing prove equality. ∎

There is also an explicit, but incomplete for B, quantitative consequence. Let Ψ=T_{t,r}, let ω be its two-port output from `(ρ,τ_r)`, and σ=(id⊗Φ)ω. Equations F2 and the doubling identity give Q114's bound for

\[
 \|\sigma-\sigma_C\otimes\sigma_J\|_1
 \le\inf_{L\ge0}\left\{2\,3^n2^L\sqrt{2\Delta/\kappa}
                +8\sqrt{(E+nr)/(L+1)}\right\},
\]

capped at two. This compares the correct **intermediate** equal-temperature circuit, not the correlated original unequal-temperature circuit. To derive a power bound on ρ one still needs a quantitative reversal and stability of its characteristic equation with all tails controlled. The displayed inverse-filter method gives a logarithmic cost. Cuesta's fourth-moment constants cannot be made uniform by our cutoff, and the rare-tail sequence rules out the weighted-Q and strict relative-entropy shortcuts. No unknown compactness modulus, Gaussian-only result, or nearby auxiliary state is substituted for B.

## 6. Contribution assessment and terminal obligations

U117 proves uniqueness, a consequence not asserted in the pinned EPnI introduction, but its full-scope proof reduces to scalar channel composition, EPnI, Li's explicit doubling/instrument operations, conditional linear qEPI, and an elementary thermal characteristic equation. The linear operation was independently reconstructed rather than stipulated. This is a concrete technical reduction, not a substantial new mechanism. F117's explicit constant is useful bookkeeping, not a separate finding. T1–T7 pay the original entropy and energy constraints and falsify both weighted and ordinary deficit-to-balance transfers, as well as a strict relative-entropy contraction gap. T5–T7 also exclude exponents above 1/2. They remain technical obstructions and do not refute B.

The original report's failures remain failures: no original entropy-to-defect transfer; no control of original unequal-temperature Lη by Δ; no quantitative removal of the noisy reference supplied by injectivity; no finite-energy fourth-moment bound; no distribution-uniform cubic game rate. The new work improves the first diagnosis from “unpaid” to **false** for both its weighted-Q and ordinary Hilbert–Schmidt-R formulations, and establishes exact optimizer uniqueness. It leaves open a transfer to a suitably weaker, bounded-test defect or an argument that uses additional nonnegative doubling remainders to obtain a power rate. No exponent α_n>0 or valid countersequence violating every such exponent has been proved.

The complete Target B, with the original fixed n,E,r,b,η, centered arbitrary internally entangled inputs and the fixed independent thermal bath, is therefore **UNPROVED AND UNREFUTED in this investigation**. All proved new claims above have complete analytic arguments; finite diagnostics below are separate evidence. No nomination is forced.

## 7. Evidence inventory and replay boundary

`seal.json` binds the exact owned report/source/experiment file and directory inventory. `inherited.json` binds the original I114 seal and each immutable original-package artifact. The inherited verifier then checks all 10,373 original blob positions (9,340 reused I14 originals, 776 PDF views, 257 other byte views), their Git identities against all 13,223 complete-tree entries, exact original lexical multisets (98 topic and 143 stability occurrences), source passages and HTML conversions. I117 adds an exact lexical expression and full occurrence records, fresh primary responses, current-version records, and exact new passage hashes. No recursive corpus copy or PDF re-extraction occurred. Line numbers are UTF-8 replacement-decoded Python `splitlines()`; LF counts are recorded separately; passage text uses LF joins without an appended newline.

The verifier first checks its complete immutable inventory and references, source/view/original bindings and passages, and only then runs the inherited and I117 finite diagnostics. It blocks writes, process launches and network through a Python audit hook and disables bytecode. It has no download, repair, reseal or source-rewrite operation. The only live paths allowed to drift are the four specified ledgers, whose frozen snapshots never drift. The preseal mode validates before the single final seal is written; default replay requires that seal. Acquisition/output failures and failed mathematical routes are retained in `failure-log.json`; no failed attempt is relabelled a success.

Preseal validation passed with all 10,373 original positions and 627,365,628 original bytes, the inherited 98/143 lexical occurrences, eight I117 route occurrences, 27 read sources and 34 exact passages, five new HTML views, and 85 new exact finite diagnostic cases. The inherited sealed replay also passed. The validation record preserves that first run's inventory count before the record itself was added; the final seal includes the record and binds 37 files besides the seal in eight owned directories. All four permitted live ledgers had drifted from the snapshots; no immutable-reference mismatch occurred.

Run from `/home/mj-kang/Documents/Dev/math/openai-proof-research`:

```bash
python -B frontier/experiments/i117_bosonic_entropy_stability/verify.py
```

Provenance replay and exact finite diagnostics do not establish universal operator truths, contribution significance, worldwide priority, human review, or formal proof certification.
