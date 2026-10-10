# I120 — Original I117 audit and finite-energy trace stability

**Disposition: ORIGINAL I117 PASS without repairs at every claimed analytic scope. Original I114's no-repair pass and technical disposition are retained. Target B remains unproved and unrefuted. No ninth finding is nominated.** Eight substantial findings remain accepted.

The new paid bridge is a trace-distance estimate on the original constraint set, with an explicit **iterated-logarithmic**, not power, modulus. It quantitatively finishes the bounded-Weyl-test version of I117's noisy equal-temperature circuit. A separate direct entropy-growth route gives an exact positive Stieltjes remainder and a finite-energy short-time comparison, but lacks a coercive trace remainder. A centered, entropy-repaired displaced-tail family tests that route: its deficit is asymptotic to a positive constant times `p log(1/p)`, and its trace distance is of order `sqrt(p)`. It does not defeat any exponent at most one half.

This is an independent AI analytic audit followed by author-level new proofs, not human review or formal certification. All pinned OpenAI theorems **and lower operations** are accepted. No upstream truth audit or contradiction argument is used. External primary texts are comparisons and identified proof inputs only where their operations are reconstructed below. No children, shared edits, staging, commits, or publication were performed.

## 1. Original bindings, scope, and reading

The ORIGINAL I117 report has SHA-256 `e2c61edf86103f7d59295dad3e08a3a8a2cef9dd1f058d831cf5f37722238ff6`; its seal has SHA-256 `1b443f3b148bc01bd2df57678a330f199ceb688ae8389959f51421aee5ba9523`. The ORIGINAL I114 report and seal remain respectively `7981bd6832a249ad5e4d7f59e02fe3622215ea175f7ebb26ee11713060ceb8db` and `f4850563e1ca604d248e0cf8956aed950aadb2ab6977c3237b53e15897540764`. These live immutable originals, all their owned artifacts, and their original-source bindings are checked by the new replay. The verdicts in §2 refer to those bytes, before the new work in §§3–4; no revised I117 statement is being passed.

AGENTS.md, upstream identity, the relevant catalogue entries and four ledgers were read. The long historical ledgers are frozen for provenance, not represented as fully semantically read. Their current entries retain eight accepted findings and explicitly assign this branch without a nomination. I39's actual scope and I07/I110/I111 exclusions remain as recorded in I114/I117; no I112/I113 working output is a dependency. The complete 13,223-entry preprint tree and 10,373-original-position mapping are inherited, not replaced by the truncated root tree. Exact source passages, URLs, line conventions and source hashes are in `../sources/i120_thermal_trace_stability/read-manifest.json` and `passages.json`.

The analytic comparisons use these primary operations:

* [Pinned EPnI, §§1, 3–5](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-entropy-photon-number-inequality-September-24-2026/build/sections): energy/entropy continuity; arbitrary internally entangled independent-port inequality; the actual Gibbs-minimizer, metric, generator and stationarity restrictions. Its recurrence closure does not itself give arbitrary-input stability.
* [Li, 2609.40061v1, §§3.1–3.4 and Appendix A.4](https://arxiv.org/html/2609.40061v1): exact different-pair doubling, all three nonnegative remainders, the explicit thermal erasure instrument, changed reference marginals, and exact removal of noise. These are the operative comparison, not merely the equality theorem's title.
* [De Palma–Trevisan, 1706.00440v2, §§3–6](https://arxiv.org/html/1706.00440v2): integral conditional information, shared-noise Stam inequality and heat integration at finite input energy and finite memory entropy. The needed linear case, including its asymptotic, is independently checked in §2.5.
* [Cuesta, 1902.05298v1, Theorem 9 and its proof through Appendix V](https://arxiv.org/html/1902.05298v1): phase-space functional equations, a growing ball, Parseval and frequency tails are already lower proof operations. Its local differentiated error uses fourth absolute moments. Section 3 below instead uses the known thermal second port to obtain a scalar dyadic recurrence, without taking derivatives of an approximate independence error. We do not import Cuesta's theorem or constants. The erroneous scalar factor before its Eq. (41), already noted in I117, is retained as a literal external-proof defect, not used to dismiss all its valid operations.

Fresh web opens confirmed access to these three versioned external pages. No new PDF download or extraction was needed. Reused immutable text views, rather than search snippets, supply the passages actually compared. A supplementary log-Sobolev search was exploratory only; no classical result from it is asserted to cover quantum states. The named significance remains the [entropy photon-number / constrained minimum-output-entropy problem](https://qiqc-op.com/problem/op_ba39e7a80122b256/), with the inherited observed page record. No ranking, worldwide priority, or full semantic corpus search is claimed.

Throughout, `g(x)=(x+1)log(x+1)-x log x`, `h(x)=log(1+1/x)`, `N=sum a_j* a_j`, and `tau_x=(x+1)^(-n)exp(-h(x)N)`. Entropies are in nats; trace norms are unhalved. Target B keeps fixed finite `n>=2`, `E>nr`, `r,b>0`, `r!=b`, `0<eta<1`, arbitrary centered n-mode inputs with `S(rho)=ng(r)` and `Tr rho N<=E`, and the fixed independent isotropic bath `tau_b`. Write `s=eta r+(1-eta)b` and `Delta=S(T_eta,b rho)-ng(s)`.

## 2. Independent audit of ORIGINAL I117

### 2.1 Cutoff, smoothing, entropy and centering; L1–L2

**PASS without repairs.** Put `q=Tr rho(1-P_K)` and `rho_K=P_K rho P_K/(1-q)`. Gentle compression and normalization cost `2sqrt(q)+q`; commutation of `P_K` with N gives energy at most `E/(1-q)`. Pinching has entropy increase `d_pin` in `[0,h_2(q)]`, so, exactly,

`S(rho)-S(rho_K)=h_2(q)-d_pin+q[S(rho_Q)-S(rho_K)]`.

The two conditional thermal energy bounds yield precisely the displayed `B_E(q)`. This bounds both signs; a continuity statement alone would not pay this budget. At q=0 the terms use their continuous limits. On `q<=1/2`, each energy perspective used to replace a tail by an upper endpoint is increasing: for example the derivative of `q g(c/q)` is `log(1+c/q)>0`; the derivative of `q g(c/(1-q))` is positive. This justifies the endpoint substitutions in the original modulus.

For states of energy at most F and half trace distance d, the chosen `M=ceil(F/d^2)` makes both tails at most `d^2`. Their normalized compressions have half distance at most `2d/(1-d^2)<=3d`. The finite-dimensional estimate `x log D+h_2(x)` is increasing for `x<=3/8`, `D>=1`. Two pinching errors then give exactly `omega_F(d)`. For F>0, `log binom(M+n,n)=O_n(log(1/d))`; thus its declared order is correct. F=0 is the separate vacuum case. There is no uniform input Hessian hidden in this argument.

Smoothing by `theta=K^-2` has block floor `m=theta/d_K`, energy addition at most `theta K=1/K`, and entropy cost at most `h_2(theta)+theta log d_K`. Output trace contraction with the preceding modulus costs `O(K^-1/2 log K)`, while input entropy truncation costs only `O(log K/K)`. On a fixed neighborhood of `H=ng(r)>0`, f' and f'' are bounded. This proves the original L1, including its nonnegativity from EPnI and its dependence only on fixed parameters.

The centering identity also passes. Since `a_j-P_K a_j P_K=a_j(1-P_K)`, Cauchy–Schwarz applied to `(a_j* sqrt(rho))` and `(1-P_K)sqrt(rho)` gives

`sum_j |Tr rho a_j(1-P_K)|^2 <= q(Tr rho N+n)`.

After division by `(1-q)^2`, this is the original mean bound; diagonal smoothing has zero mean. Displacement reduces energy by the squared mean and preserves both entropies. This does not substitute a centered approximation for the original rho in B.

For a Hermitian traceless A with `||A||_2=1`, its operator norm is at most one, hence the admitted two-sided interval is indeed `|t|<=m/2`. The input entropy Hessian is bounded by `2/m`. On the finite input block, differentiation of relative-entropy data processing bounds the output BKM form by that input form. The vacuum minorant `T(sigma+tA)>=(m/2)tau_(1-eta)b` supplies the stated logarithmic form bound; finite input blocks give polynomial times Gaussian characteristic functions and exponentially decaying number tails. Resolvent differentiation is therefore legitimate. Cauchy–Schwarz gives `|DS(A)|<=sqrt(d_K)|log(m/2)|`. The original H_K and Taylor estimate L2 follow.

Minimizing `F/t+H_K t/2` unconstrained uses `t=sqrt(2F/H_K)`, admissible exactly when `F<=H_K m^2/8`. Here `m` is of order `K^(-n-2)`, and `H_K m^2` is of that same order, up to a smaller logarithmic correction. L1's supplied error is much larger. The original conclusion is correctly a failure of this **budget**, not a counterexample to all localization arguments. No small-eigenvalue or boundary term was dropped.

### 2.2 Entropy-repaired Fock tails T1–T4

**T1, T2, T3, T4 and every stated obstruction: PASS without repairs.** With `p=c/k`, the only ambiguous component label is at `v_k`. The exact ambiguity is

`J(a,p)=(a+p)log(a+p)-a log a-p log p`,

which gives T2. Uniformly on `[r/2,r]`, the thermal probability at v_k is bounded by a geometric sequence; `J<=a[1+log(1+p/a)]` is exponentially small times O(k). The sign at x=r is positive eventually, and the upper mixture bound at r/2 is strictly below H. The intermediate-value root is actual, not a numerical approximation. The upper mixing inequality at the root yields `H-ng(x_k)<=h_2(p)`, whence `r-x_k<=h_2(p)/(n h(r))`. The energy is `(1-p)nx_k+c<nr+c<E` and tends to `nr+c`. Centering, faithfulness and exact entropy all hold.

Thermal trace continuity plus p→0 gives convergence to tau_r. The thermal relative-entropy identity then proves T3, while the output mixing bound and its energy entropy bound give `0<=Delta_k=O(log k/k)`. No lower asymptotic for this deficit was asserted.

For the edge `(u,v)=(v_k-e_1,v_k)`, the logarithmic-mean identity gives exactly T4, with its numerator sign matched to the logarithm. The numerator before multiplication by k is `(r+1)c/k+O(exp(-a_0 k))`; the logarithm is `k h(x_k)+O(log k)`. Thus the displayed contribution divided by k tends to `(r+1)c`. The off-diagonal test is centered. All other nonexceptional edges form a geometric first-moment sum, so Q is finite at each k but diverges along the sequence. This is a counterexample to every vanishing weighted-Q or input-relative-entropy transfer on the original constraint set. It says nothing against trace stability, and is not a proof about ordinary R.

### 2.3 Entropy-preserving rotation T5–T7 and exponent ceiling

**T5, T6, T7 and `alpha<=1/2`: PASS without repairs.** The two eigenvalues of the difference in the rotated block are `+-d_k sin(theta_k)`. Its trace norm is therefore `2sqrt(c d_k/k)`; its energy increase is exactly c. For k>=2 the only off-diagonal entries do not connect neighboring number states, so every annihilator mean is zero. Entropy is unchanged by the unitary, and strict positivity is preserved.

The `(v_k-e_1,0)` entry of rho a is zero, whereas that of a rho is `sqrt(k)rho_(v_k,0)`. Squaring gives precisely `(r+1)^2(c d_k-c^2/k)`. Thus ordinary R stays away from zero. The phase twirl removes just the new coherence, and its covariance with T plus entropy concavity makes the output entropy no smaller. Subtracting the two mixture entropy inequalities for the common state `(tau_r-p|0><0|)/(1-p)` proves T7, including the vacuum subtraction before it is discarded. Every state used in these inequalities has finite energy. Finite twirls converge with a common energy cap, justifying entropy convergence.

Together, `d_k->p_0>0` and `Delta_hat<=C log k/k` exclude every `alpha>1/2`. Even without strict positivity, a zero deficit at a nonthermal state would already contradict such a bound; U117 additionally establishes positivity. No exponent in `(0,1/2]` is excluded. The exact relative entropy `h(r)c` and failure of ordinary-R transfer are consistent with B114's one-way sufficient estimate.

### 2.4 R1–R2 and F1–F2

**R1 and R2: PASS without repairs.** Entropy is fixed and output energy is `eta e+(1-eta)nb`, giving `D_in=h(r)(e-nr)` and `D_out=eta h(s)(e-nr)-Delta`. Strict scalar log concavity and `s>eta r` give `0<c_*<1`. T1–T3 have a strictly positive limiting D_in, so their ratio really tends to c_* and refutes a uniformly smaller coefficient on the same constraints.

For R2, `log Gamma` is the conjugate of two thermal logarithms and hence is quadratic, including its cross term. Every cross expectation is finite by quadratic-form Cauchy–Schwarz and the total-energy bound. Expanding the three relative entropies gives the stated identity, with the minus sign before `Tr Omega K`. At Gamma the expectation equals its mutual information. Subtracting the reference leaves both the mutual-information difference and the cross-Hamiltonian expectation difference; neither can be erased as nonnegative.

**F1 and F2, arbitrary internally entangled input scope: PASS without repairs.** `s/r>eta`, so `eta<u<min(1,s/r)`; hence `0<t=eta/u<1` and `c=(s-ur)/(1-u)>0`. The Weyl signal factor is ut=eta and the added photon noise is `u(1-t)r+(1-u)c=(1-eta)b`. The half-photon contribution also agrees. This proves equality of channels, rather than agreement only on Gaussian states.

For any target input, EPnI and the energy bound put `x=g^-1(S(T_t,r rho)/n)` in `[r,M]`. Differentiation in input entropy gives `u h(ux+(1-u)c)/h(x)`, bounded below by the displayed positive kappa. Integration proves F2. M is finite and greater than r for E>nr. For an arbitrary finite-energy input in U117 one may take its actual energy or any larger cap. Displacements do not invalidate the energy formula because the bath is centered. The original bath is never freely changed: the physical channel is exactly factored, with rho itself at the first input.

### 2.5 Conditional linear qEPI, including the infinite-dimensional steps

**PASS without repairs.** Here are explicit checks of the potential analytical failure points. All marginal and joint quantum entropies involving finitely many finite-energy modes and finite-entropy M are finite, by subadditivity and Araki–Lieb. Conditional entropy can consequently be subtracted without an infinity-minus-infinity convention.

For a continuous displacement label Z, use the classical-quantum direct integral. Its information is a relative-entropy integral, not an expression containing the differential entropy of Z. With Z independent of M,

`I(X;Z|M)=S(XM)_average-integral S(XM)_z`,

since the M marginal of every branch agrees. Gaussian averaging has finite average energy. Each branch has the same joint entropy, while the averaged state has finite entropy. The formula is finite and follows by expanding the relative entropy to the average; unbounded logarithms are obtained by monotone spectral truncations of their positive parts. Equivalently, increasing finite measurable partitions converge to the classical-quantum relative entropy, and the finite conditional entropy expressions converge to the integrals. Conditional independence in a labelled branch is not assumed for a coarse partition: its limiting integral is the quantity that vanishes.

The heat increment is thus the stated nonnegative information. Adding independent heat to X is a local channel and diminishes this same fixed-w increment. The midpoint inequality follows by comparing consecutive equal increments; continuity makes midpoint concavity ordinary concavity. At zero, heat is trace-norm continuous even with a separable reference, by strong continuity on finite-rank approximants and trace contraction. Joint entropy lower semicontinuity supplies one direction. For any fixed a>0,

`S(X|M)=h(a) e+n log(a+1)-D(rho_XM || tau_a tensor rho_M)`

and the exact energy increase nv plus relative-entropy lower semicontinuity supply the other. The reference marginal does not move. No continuity of an unbounded energy functional on the whole energy cap was used; along this heat path its value is known exactly.

A finite concave continuous function is locally absolutely continuous on `(0,infinity)`. Since the heat entropy is increasing, its derivative is nonnegative almost everywhere. For `0<epsilon<T`, the fundamental theorem holds on `[epsilon,T]`. Monotone convergence of its derivative integral and continuity at zero extend the identity to `[0,T]`. Linear combinations of these functions therefore admit the improper derivative integration used in I117. This checks the endpoint rather than treating almost-everywhere differentiability alone as sufficient.

For v>1, the heterodyne channel representation has characteristic multiplier `exp(-v|w|^2)`: the measurement contributes `exp(-|w|^2/2)` and the prepared `tau_(v-1)` contributes `exp(-(v-1/2)|w|^2)`. In its ancillary form the conditional M states are obtained from the positive operator-valued heterodyne density. Given Z, Y and M are a product. Classical-to-quantum data processing implies

`I(Y;M)<=I(Y;Z)=S(Y)-ng(v-1)`.

The right-hand side is finite since Y has energy `e+nv`; the equality follows from the finite Holevo integral. Subtracting from S(Y) gives the conditional lower bound `ng(v-1)`, while the upper bound is `ng(v+e/n)`. Their difference from `n log v+n` tends to zero. This proves exactly the needed heat asymptotic, without Gaussian extremality or extra moments.

For shared noise, the chain identity is

`I(AB;Z|M)=I(A;Z|M)+I(B;Z|M)-I(A;B|M)_average+I(A;B|MZ)`.

The last term is zero in the labelled branches. The negative term is evaluated in the averaged state and may be nonzero; it has the favorable sign. Data processing to C gives the finite-increment Stam inequality. Independent heat on A and B preserves their zero conditional mutual information and evolves C by the same heat time. At common differentiability points this gives `H_C'<=t H_A'+(1-t)H_B'`. The weighted difference is therefore nonincreasing, and its limit is zero. Integration back to zero proves the conditional linear qEPI used by doubling. This argument covers arbitrary quantum M with finite entropy and arbitrary internal entanglement in either port.

### 2.6 U117, noisy consequence, and original I114 disposition

**Full U117 and its explicit noisy consequence: PASS without repairs.** F117 reduces a zero physical deficit to zero linear deficit for `(rho,tau_r)`. The different-pair doubling identity with `(tau_2,tau_2)` has three nonnegative terms by §2.5, the explicit A-group/B-group conditional independence, and strong subadditivity. Its information-loss term is zero. The Q114 erasure instrument then makes `(id tensor Phi)omega_CE` a product at the stated separable-reference scope.

In this step the branch reference marginal is the filtered one. The positive filter has eigenvalues `3^-n 2^-N`; compression, Pinsker, two gentle tails and the final reference-marginal correction are exactly what prove Q114. The branch-zero inverse is bounded, whereas the branch-one inverse is used only on a fixed number cutoff. Finite branch entropies follow from their conditional energy bounds and from entropy concavity on the reference. None of these checks requires a classical memory or finite reference dimension.

At equality, Weyl cancellation removes Phi because its multiplier is nonzero and its argument map is onto. For `a=sqrt(t)`, `d=sqrt(1-t)`, output arguments `(x/a,-y/d)` give

`chi_rho(x+y)=chi_rho(x)chi_rho(y) exp(-2(r+1/2)Re(x conjugate(y)))`.

The function `exp((r+1/2)|x|^2)chi_rho(x)` is a continuous multiplicative character, has no zeros by subdivision, and has modulus one by conjugate symmetry. A local continuous argument is additive; rational approximation and subdivision extend it to a real linear functional on all real phase space. It is exactly a displacement phase. Finite first moments identify that displacement with the mean. Conversely displaced thermals attain equality by channel covariance. This proves the full finite-energy uniqueness, including uncentered inputs, with no Darmois–Skitovich theorem assumed.

At nonzero deficit, doubling and F2 give the exact Q114 bound with loss at most `Delta/kappa` and C energy at most `E+nr`. Its constants, infimum over L, and cap at two pass. It controls the noisy **intermediate** equal-temperature output, not the original correlated unequal-temperature output. Injectivity was used only for equality; no quantitative inverse was asserted.

**Original I114 no-repair pass retained.** In particular B114's closed squeezing form has gap `2r+1`, both annihilator lists are required, and finite energy puts the vectorized state in their form domains. Its trace-normalization/cutoff constants, centered thermal metric duality and undoing of displacement apply at their original scopes. The source stationarity controls only its constructed minimizers. Q114 and its two scoped counterexamples, symmetry/endpoints, and synthesis S retain the original pass and technical disposition. S already follows from the source's all-L encoders, one-call recursion, commutator refinement, phase-sensitive lookup and clean-isometry-to-diamond comparison with a target-dependent truth table. Nothing in this audit promotes it or the AD/PR/ZK screens to a new finding.

**U117 contribution: technical.** Its complete reduction is scalar channel composition and EPnI, followed by reconstructed conditional linear qEPI, Li's exact doubling and instrument operations, and the known-thermal characteristic equation. The pinned EPnI title's failure to mention uniqueness is irrelevant to this assessment. The reduction works at the full arbitrary-input scope; it is not a Gaussian-only reduction. T1–T7 are genuine constraint-respecting technical obstructions. Their original failure conclusions remain intact.

## 3. Route I — bounded Weyl tests, paid frequency tails, and an explicit modulus

This route completes a quantitative bridge beyond the original noisy correlation statement. It does not turn Q or ordinary R into a small-deficit quantity.

### 3.1 A general noisy-product-to-input lemma

Fix finite n>=1, r>0, `0<t<1`, and a centered input rho with energy at most E. No entropy constraint is needed in this lemma. Let

`omega=U_t(rho tensor tau_r)U_t*`, `sigma=(id tensor Phi)omega`, `Phi=T_(1/2),2`,

and suppose `||sigma-sigma_C tensor sigma_J||_1<=epsilon`, `0<epsilon<=exp(-4)`. Define explicit constants

\[
 R=r+\tfrac12,\quad B=2E+n+R,\quad
 A=\frac5{8(1-t)}+\frac{R(1-2t)^2}{4t(1-t)},\quad D=4(A+1),\quad J=8(E+nr)+8n,
\]
\[
 H_0^2=JD+\frac{2^{n+3}(n+3)!}{n!D^n}
                  \left(\frac BD+\frac12\right)^2,
 \qquad H_1=2^{n/2}H_0+2\sqrt E+2\sqrt{nr},
 \qquad \gamma=\frac1{2(n+1)}.
\]

**Lemma W120 (author-proved technical):**

\[
 \|\rho-\tau_r\|_1\le
 \min\{2,H_1[\log(1/\epsilon)]^{-\gamma}\}. \tag{W1}
\]

There is no finite-support, faithfulness, fourth-moment, Gaussian-input or mode-product assumption.

**Bounded-test defect.** Use complex Weyl operators `D(z)` with `chi_tau_r(z)=exp(-R|z|^2)`. In sigma test C at `u=z/(2sqrt(t))` and J at `sqrt(2)v=-z/sqrt(2(1-t))`. A product of Weyl operators has norm one, so its expectation defect is at most epsilon. Removing the **scalar** noise multiplier at these finite test arguments costs `exp(5|v|^2/2)`, not a global channel inverse. The remaining thermal second-port factor in the joint characteristic function is

`exp(-R(1-2t)^2 |z|^2/[4t(1-t)])`.

The product-marginal thermal factor differs from this by `exp(-R|z|^2/2)`. Therefore, for every z,

\[
 |\chi_\rho(z)-\chi_\rho(z/2)^2e^{-R|z|^2/2}|
 \le\epsilon e^{A|z|^2}. \tag{W2}
\]

All amplification as the test radius grows is displayed in A.

**Centering and dyadic propagation.** Write `D(z)=exp(iH_z)`. The annihilator in direction z, divided by |z|, is one normalized mode, whose number expectation is at most E. The elementary vector inequality for its creation and annihilation parts gives `Tr rho H_z^2<=(4E+2n)|z|^2`. Centering makes `Tr rho H_z=0`. Integrating the scalar bound `|exp(ix)-1-ix|<=x^2/2` against its spectral measure gives

`|chi_rho(z)-1|<=(2E+n)|z|^2`.

Also `|1-exp(-R|z|^2)|<=R|z|^2`. For `d(z)=|chi_rho(z)-exp(-R|z|^2)|`, W2 and `|chi_rho|<=1` yield

`d(z)<=2d(z/2)+epsilon exp(A|z|^2)`.

After m iterations this is at most `B|z|^2/2^m+(2^m-1)epsilon exp(A|z|^2)`. Choose the integer m with `epsilon^-1/2<=2^m<2epsilon^-1/2`. For every radius Q and every `|z|<=Q`,

\[
 d(z)\le(BQ^2+2)e^{AQ^2}\sqrt\epsilon. \tag{W3}
\]

Only a second moment and bounded tests enter; no derivative of W2 is taken. At zero epsilon one may instead send m to infinity at fixed z, recovering exact centered uniqueness directly.

**Frequency tails at finite energy.** In the convention here Weyl Plancherel is

`||X||_2^2=pi^-n integral |chi_X(z)|^2 dz`.

For completeness, in the Schrödinger representation the characteristic function at real displacement (q,p) is the ordinary Fourier transform in the midpoint variable of the kernel `K(x-q/2,x+q/2)`. Ordinary Fourier Plancherel and the unit-Jacobian midpoint/difference change of variables give `integral |chi_X(q,p)|^2 dq dp/(2pi)^n=integral |K(x,y)|^2 dx dy`. Since `(q,p)=sqrt(2)(Re z,Im z)` up to a harmless rotation, this is the displayed normalization. Finite-rank Schwartz kernels are dense in Hilbert–Schmidt space, proving the identity for all Hilbert–Schmidt X.

For a finite-energy state nu, the four single-ladder products are Hilbert–Schmidt, with `||a_j nu||_2^2<=Tr nu N_j` and `||nu a_j||_2^2<=Tr nu(N_j+1)`. Consequently

\[
 \pi^{-n}\int |z|^2|\chi_\nu(z)|^2 dz
 =\sum_j\|[a_j,\nu]\|_2^2\le4\operatorname{Tr}\nu N+2n. \tag{W4}
\]

To justify the unbounded commutator identity, first take `P_K nu P_K`. Its characteristic function is Schwartz and cyclicity gives `chi_[a_j,nu](z)=-z_j chi_nu(z)`. Its left/right ladder products converge in Hilbert–Schmidt norm: use `a P_K=P_(K-1)a`, `P_K a=a P_(K+1)`, and the Hilbert–Schmidt convergence of two-sided cutoffs on a nu and nu a. Closedness of multiplication by z_j in L2 passes the equality to the limit. This proof never asserts finite fourth moment.

Apply W4 to rho and tau_r and use the factor-two square inequality. The frequency tail of their difference outside radius Q is bounded by `J/Q^2`. The ball's normalized volume is `Q^(2n)/n!`. Combining with W3 gives, for every Q>0,

\[
 \|\rho-\tau_r\|_2^2
 \le\frac{Q^{2n}}{n!}(BQ^2+2)^2\epsilon e^{2AQ^2}
          +\frac J{Q^2}. \tag{W5}
\]

Let `lambda=log(1/epsilon)>=4`, `Q^2=lambda/D`. Then `epsilon exp(2AQ^2)<=exp(-lambda/2)`, and `BQ^2+2<=(B/D+1/2)lambda`. The elementary series bound `exp(lambda/2)>=(lambda/2)^(n+3)/(n+3)!` gives exactly `||rho-tau_r||_2^2<=H_0^2/lambda`.

**Number tails and trace norm.** For every integer K>=0, gentle compression and the energy cap give

\[
 \|\rho-\tau_r\|_1\le\sqrt{\binom{K+n}{n}}\,
                       \|\rho-\tau_r\|_2
       +\frac{2(\sqrt E+\sqrt{nr})}{\sqrt{K+1}}. \tag{W6}
\]

Take `K+1=ceil(lambda^(1/(n+1)))`. The rank is at most `(K+1)^n`, and `K+1<=2lambda^(1/(n+1))`. Substitution proves W1 with the displayed H_1. Both growing cutoffs, both tails, the frequency amplification, the dyadic iteration and their constants have now been paid. ∎

### 3.2 The original constraint set: an explicit iterated-logarithmic theorem

Use F117's **same input** parameters u,t,c,kappa; use t in W120. Set

\[
 K_0=4\,3^n+16\sqrt{(E+nr)\log2},\qquad
 z_0=\max\{e^{16},K_0^4\},\qquad \gamma=1/[2(n+1)].
\]

**Theorem M120 (author-proved technical).** Under every original hypothesis of B, if `0<Delta/kappa<=exp(-z_0)`, then

\[
 \boxed{\quad\|\rho-\tau_r\|_1
 \le 4^\gamma H_1\,[\log\log(\kappa/\Delta)]^{-\gamma}.\quad} \tag{M1}
\]

At Delta=0 the distance is zero. For other deficits the bound two applies. An often more usable explicit bound is W1 with any upper bound `epsilon<=exp(-4)` obtained from

\[
 \epsilon\le\inf_{L\ge0}
 \left\{2\,3^n2^L\sqrt{2\Delta/\kappa}
              +8\sqrt{(E+nr)/(L+1)}\right\}. \tag{M2}
\]

**Proof.** F2 and doubling give M2 by the already audited instrument estimate. For `d=Delta/kappa<1` and `z=log(1/d)`, Q114's explicit choice yields

`epsilon<=2sqrt(2)3^n exp(-z/4)+16sqrt((E+nr)log2/z)<=K_0/sqrt(z)`.

The last inequality uses `sqrt(z)exp(-z/4)<=sqrt(2)` for z>0. We may use the larger upper bound `epsilon_0=K_0/sqrt(z)` in W120. When `z>=z_0`, `log(1/epsilon_0)>=log(z)/4>=4`. W1 proves M1. At zero use U117 or W2 with arbitrarily small epsilon. No assertion that actual noisy correlation equals its upper bound is needed. ∎

The first logarithm is lost in the inverse-filter/energy budget; the second is lost in the bounded-frequency removal of Gaussian noise and in the recurrence. M1 is **not** B with a small exponent. It is an explicit full-scope modulus, and therefore stronger than merely citing compactness, but remains asymptotically weaker than every positive power of Delta.

### 3.3 Additional nonnegative doubling remainder and why it does not close a power

The plus-pair remainder was not needed for M1. It gives another actual quantitative restriction. Put `r_+=(r+2)/2`, `A_+=Phi rho`, `B_+=tau_(r_+)`, and `x=g^-1(S(A_+)/n)`. Let

`V=max{r_+,(E/2+n)/n}` and `x_min=g^-1([ng(r)+ng(2)]/(2n))>0`.

Unconditional linear qEPI gives `x>=x_min`; energy gives `x<=V`, and `x_min<=r_+<=V`. On `[0,V]`, `-g''(x)>=1/[V(V+1)]` (interpreted by a limit at zero). Strong concavity therefore gives

\[
 L_t(A_+,B_+)\ge
 \frac{nt(1-t)}{2V(V+1)}(x-r_+)^2.
\]

This remainder is at most `delta<=Delta/kappa`. Since h decreases,

\[
 |S(\Phi\rho)-ng(r_+)|
 \le n h(x_{\min})
       \sqrt{\frac{2V(V+1)\Delta}{\kappa nt(1-t)}}. \tag{M3}
\]

This is a square-root constraint on a smoothed entropy at the same input, derived from an additional nonnegative remainder. It supplies no control of the unsmoothed energy excess: the original rare-tail families keep a positive excess while this smoothed entropy difference tends to zero. We have not proved an inequality converting M3 and the conditional remainder into a polynomial-in-cutoff trace budget. Treating M3 alone as a trace-distance estimate would require a new argument.

## 4. Route II — direct entropy-growth coercivity and a constraint-respecting tail test

This route works with the equal-temperature semigroup on the same rho. It does not use bounded inversion of a Gaussian channel. It identifies the exact coercive quantity, pays a short-time trace comparison, and tests a potential no-power construction quantitatively.

### 4.1 An exact positive entropy-growth measure, without unjustified derivatives

Let `P_v=T_(exp(-v)),r`, `D_v=D(P_v rho||tau_r)`, and `F(v)=exp(v)D_v`, for any finite-energy rho. Conditional linear qEPI with trivial memory implies, for every finite-energy state sigma and `0<q<1`,

\[
 J_q(\sigma):=S(T_{q,r}\sigma)-qS(\sigma)-(1-q)ng(r)
             =qD(\sigma\|\tau_r)-D(T_{q,r}\sigma\|\tau_r)\ge0. \tag{D1}
\]

The equality is the exact energy identity, so no unequal-temperature baseline was omitted. Thus F is nonincreasing. It is continuous: semigroup trace continuity, its exact continuous energy, and energy-constrained entropy continuity suffice. It defines a nonnegative atomless Stieltjes measure `mu_rho=-dF` on compact time intervals. For `T=-log t`,

\[
 J_t(\rho)=e^{-T}\mu_\rho([0,T]). \tag{D2}
\]

On the original entropy slice J_t is precisely the transferred entropy deficit delta. More generally, for any partition `0=v_0<...<v_m=T`, telescoping gives the exact positive sum

\[
 J_t(\rho)=\sum_{i=1}^m e^{-(T-v_i)}
      J_{e^{-(v_i-v_{i-1})}}(P_{v_{i-1}}\rho). \tag{D3}
\]

This proves a fully scoped integral remainder without assuming differentiability of entropy for arbitrary finite-energy inputs. On smooth finite-moment faithful trajectories, the familiar density, when justified, is `e^v(I_r-D_v)` where `I_r=-D_v'`. The source's generator pairing is proved at its special regularized states; it is not an automatic proof of that differentiability on our entire state set.

Even on states where the production identity is justified, the centered formula is `I_r=h(r)Q^2`. The remainder is **`h(r)Q^2-D_v`**, not `h(r)Q^2`. Discarding the subtraction would repeat a disproved shortcut. The energy cap bounds D_v, but integrating that bound leaves a fixed positive term; it does not make Q small as delta tends to zero.

### 4.2 Paid short-time trace comparison and the missing coercivity

For every input of energy at most E,

\[
 \|P_v\rho-\rho\|_1
 \le2\arccos(e^{-v/2})\sqrt{(2r+1)E+nr}
 \le\pi\sqrt{((2r+1)E+nr)v}. \tag{D4}
\]

To prove this, purify rho and tau_r, and implement the beam splitter by `exp(-i theta G)`, `theta=arccos(exp(-v/2))`, `G=i sum(a_j* b_j-a_j b_j*)`. Its squared expectation in the product input is

`Tr (rho tensor tau_r)G^2=(2r+1)Tr rho N+nr`.

Indeed anomalous bath second moments vanish, and the two normal bath moments are r and r+1 times the mode Kronecker delta. This uses only second moments even if rho is internally entangled. The joint purification lies in the form domain of G squared. Spectral calculus gives a vector displacement at most `theta sqrt(<G^2>)`, the pure-state trace bound costs two, and partial trace contracts. Finally `theta<= (pi/2)sin(theta)` and `sin^2(theta)=1-exp(-v)<=v`. This proves D4 on the full energy cap.

One sufficient quantitative obligation is now concrete. If for centered finite-energy states sigma with energy at most E one could prove a uniform production remainder

`I_r(sigma)-D(sigma||tau_r)>=c ||sigma-tau_r||_1^p`,

with a legitimate measure/integrated formulation for nonsmooth states, D2–D4 would yield a power. In fact, put `d=||rho-tau_r||_1`, `C_E=pi sqrt((2r+1)E+nr)`, and `h=min(T,d^2/(4C_E^2))`. Centering and the energy cap persist under P_v. D4 gives distance at least d/2 on `[0,h]`. The proposed measure bound would imply

`delta>=exp(-T)c h(d/2)^p`,

and hence a bound with exponent `1/(p+2)`, with constants depending only on the fixed parameters. This is a **conditional reduction with a precisely unpaid premise**, not a theorem claiming that production coercivity holds. It does not demand vanishing Q or R, nor a strict multiplicative improvement `D_out<ct D_in`.

A naive convexity route to that premise fails. J_q is nonnegative and vanishes on every displaced tau_r. For opposite nonzero displacements, their midpoint is centered and not a thermal state: its characteristic function has a nonconstant cosine factor. The equality mechanism in §2.6 applies to any zero J_q with the known bath, without an entropy-slice assumption, and forces a displaced tau_r. Thus this midpoint has strictly positive J_q although both endpoints have zero J_q. J_q is not convex on the state space. A globally nonnegative Hessian difference cannot be assumed.

On a finite-number block with spectral floor m, the exact entropy Hessian difference along a traceless A is `q B_sigma(A,A)-B_Tsigma(TA,TA)`. Data processing gives only `B_Tsigma<=B_sigma`, which does not give a sign after multiplying the input by q<1. A thermal-line Taylor argument must retain the negative portions outside a small neighborhood. The original cutoffs make `m=K^-2/binom(K+n,n)`; local derivative costs at least `1/m=K^2 binom(K+n,n)`, and logarithmic gradients can cost `sqrt(binomial(K+n,n))|log m|`. There is no cutoff-independent spectral neighborhood. These are the actual small-eigenvalue and integration obligations, not a missing appeal to compactness.

### 4.3 A different exact-constraint no-power test: separated displaced thermal tails

Choose `0<c<E-nr`. For `0<p<1/2`, let a_p be the real first-mode displacement with

`|a_p|^2=c/[p(1-p)]`.

For x in `[r/2,r]` define

\[
 \rho(p,x)=(1-p)D(-pa_p)\tau_xD(-pa_p)^*
       +pD((1-p)a_p)\tau_xD((1-p)a_p)^*. \tag{D5}
\]

Its mean is exactly zero and its energy is exactly `nx+c`. It is faithful and is not restricted to finite Fock support. Write `chi_in(p,x)` for the Holevo information of this binary ensemble, so

`S(rho(p,x))=ng(x)+chi_in(p,x)`.

The means of its heterodyne outcomes differ by a_p; the variance of the first real coordinate is `(x+1)/2`. A threshold at the midpoint of these two means has each conditional error at most `exp(-|a_p|^2/[4(x+1)])`, by the exponential Markov bound for a one-dimensional Gaussian. For small p, this is less than one half uniformly in x. Binary Fano and data processing therefore give

\[
 h_2(p)-h_2\!\left(e^{-c/[4(r+1)p(1-p)]}\right)
       \le\chi_{\rm in}(p,x)\le h_2(p). \tag{D6}
\]

The identical calculation after the **original physical channel** has component temperature `s_x=eta x+(1-eta)b` and mean separation `sqrt(eta)a_p`. Hence its Holevo information satisfies

\[
 h_2(p)-h_2\!\left(e^{-\eta c/[4(s+1)p(1-p)]}\right)
       \le\chi_{\rm out}(p,x)\le h_2(p). \tag{D7}
\]

For fixed p the entropy is continuous in x by the common finite-energy bound. At x=r the Holevo information is strictly positive: otherwise both distinct displaced components equal their mixture by relative-entropy positivity. At x=r/2, the upper bound `ng(r/2)+h_2(p)` is below H for small p. There is therefore an actual `x_p in (r/2,r)` with **exact** entropy H. The resulting rho_p obeys every Target B hypothesis and has energy `<nr+c<E`.

Let `h_p=h_2(p)`. The error terms in D6–D7 are `o(h_p^m)` for every fixed positive m, since `h_2(exp(-a/p))=O(p^-1 exp(-a/p))` for a>0. Taylor's theorem on `[r/2,r]`, using `|g''|<=1/[(r/2)(r/2+1)]`, gives

\[
 r-x_p=\frac{h_p}{n h(r)}+O(h_p^2),\qquad
 \Delta_p=(1-c_*)h_p+O(h_p^2),\quad
 c_*=\frac{\eta h(s)}{h(r)}<1. \tag{D8}
\]

All constants here depend only on the fixed n,r,b,eta,c. The second Taylor remainder is bounded on `[eta r/2+(1-eta)b,s]`, whose left endpoint is positive. Thus D8 is a two-sided asymptotic, not merely an upper bound. In particular `Delta_p` is bounded above and below by positive fixed multiples of `p log(1/p)` eventually.

The trace distance has order sqrt(p). For the upper bound, changing the rare component costs at most 2p. Moving the main thermal by `beta=-pa_p` costs at most `2sqrt(2r+1)|beta|`. Also the thermal family is trace-Lipschitz on `[r/2,r]`: differentiation of its diagonal probabilities gives

`||d tau_x/dx||_1=E_tau_x |N-nx|/[x(x+1)]<=2n/(x+1)<=2n`.

Integration and D8 prove `||rho_p-tau_r||_1=O(sqrt(p))`. For a lower bound, test the first-mode Weyl operator at z=i. Its thermal characteristic function is real, whereas

`Im chi_rho_p(i)=exp(-(x_p+1/2))[-(1-p)sin(2p|a_p|)+p sin(2(1-p)|a_p|)]`.

The second summand has magnitude at most p and the first is `-2sqrt(cp)+O(p^(3/2))`. Since `x_p->r`, the absolute expectation difference is at least a positive fixed multiple of sqrt(p) for small p. The operator norm is one, so

\[
 \|\rho_p-\tau_r\|_1=\Theta(\sqrt p),\qquad
 \Delta_p=\Theta(p\log(1/p)). \tag{D9}
\]

This fully paid centering/entropy/energy construction is a **failed no-power candidate**. For `alpha<1/2`, the ratio `||rho_p-tau_r||_1/Delta_p^alpha` tends to zero; it also tends to zero at alpha=1/2. It only duplicates the already known exclusion of alpha>1/2. Making the displaced rare component travel to distance of order p^-1/2 does not make its binary mixing entropy disappear. The positive coefficient `1-c_*` in D8 is the exact unequal-temperature baseline subtraction that the proposed counterexample must overcome. No conclusion about all other possible sequences follows from this calculation.

## 5. Contribution assessment and terminal quantitative obligation

All original I117 audited claims pass without repairs. U117 remains a full-scope technical consequence of the accepted and reconstructed operations, and original I114 remains proof-passed and technical. The new M120 conclusion controls the **original input's trace distance** under every original hypothesis. Its proof uses the original instrument bound, a known-thermal specialization of the characteristic functional equation, elementary dyadic iteration, Hilbert–Schmidt Fourier tails, and a number cutoff. This is more than tuning a Q114 cutoff constant: it supplies the previously missing finite-energy quantitative reversal to the actual input. Nevertheless, the full mechanism is a concrete combination of the existing doubling/instrument and phase-space stability operations with a fixed known Gaussian factor. It is assessed **technical**, not nominated as a substantial finding merely because its exact formula is absent from a title.

Cuesta's phase-space split and Parseval tail operation are credited at their actual scope. We have not imported its fourth-moment local estimates. Here the second input is known thermal and centering fixes the remaining character; these special facts permit W2–W3. W4 supplies a direct domain-safe version of a finite-energy frequency tail. W6 is the same elementary energy/rank mechanism as B114. None of these facts supplies a positive power of the entropy deficit.

Route II gives a different exact entropy-growth formulation and D4, and rejects an actual centered fixed-entropy fixed-energy displaced-tail proposal by its two-sided deficit asymptotic. Its remaining obligation is a trace-coercive remainder for D2/D3 (or an equivalent integrated statement) with constants uniform on the finite-energy centered set. Source generator identities only at constructed Gibbs minimizers do not pay it. In Route I the corresponding obligation is a polynomial-in-cutoff bounded-test/doubling estimate whose errors remain absorbable when both frequency and number cutoffs grow; exponential Gaussian test amplification and `2^L` inverse-filter growth currently prevent that conclusion.

Target B, with some `0<alpha_n<=1/2`, is **UNPROVED AND UNREFUTED in this investigation**. No sequence defeating every positive exponent was produced. No balance-defect shortcut, injectivity-to-bounded-inverse inference, fourth-moment assumption, finite-support substitution, Gaussian-input substitution, or compactness-as-rate claim enters the positive theorem. Eight accepted findings remain eight.

## 6. Exact inventory and replay

The new owned roots are exactly this report, `frontier/sources/i120_thermal_trace_stability/`, and `frontier/experiments/i120_thermal_trace_stability/`. The single final seal binds their exact file and directory inventory, excluding only its own hash. Original I114/I117 package inventories and seal identities are bound in `inherited.json`. Only the four permitted live ledgers may drift; every frozen snapshot is immutable.

The verifier checks all owned bytes, all inherited immutable package bytes and references, all 10,373 original Git blobs against the complete tree, their 776 PDF text-view bindings and other views, the inherited exact lexical occurrence multisets, title results, selected inventories, passage text/hashes, and deterministic HTML conversions **before** invoking any diagnostic program. It performs one combined corpus traversal for the inherited searches, without rerunning the nested corpus verifiers. New lexical results are explicitly restricted to the selected sources; they are not advertised as a new full semantic or full-domain search. No PDF extraction is performed.

The diagnostics are finite exact rational checks of the scalar noise exponents, dyadic constants, cutoff ranks, commutator energy budgets, satellite energy/centering and baseline signs, together with the inherited finite checks. They do not prove universal operator assertions or contribution significance. Acquisition/output limitations and unsuccessful mathematical approaches are retained in `failure-log.json`.

Preseal validation runs before the one seal is written. Default replay has no write, network, subprocess, bytecode, repair, source-rewrite or reseal path. Run from the research directory:

```bash
python -B frontier/experiments/i120_thermal_trace_stability/verify.py
```

The immutable preseal record contains validation counts. A successful replay certifies this scoped provenance and the deterministic diagnostics, not human review, formal proof, worldwide priority, or substantiality.
