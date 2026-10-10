> Archived exploratory draft. Some claims were corrected, rejected, or left unreviewed. Use [the final index](../README.md) and [screening decisions](../SCREENING.md) for accepted results.

# Analytic number theory: downstream research report

Date: 2026-10-08. Revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. **All upstream results are assumed true.** This is downstream research, not an upstream proof audit. No priority claim is established merely by a negative literature search.

## Ranking

1. **Prime-predecessor divisor overlap law:** two independent uniform divisors of the same random prime predecessor yield a Dirichlet law for their gcd, exclusive parts, and unused part. Their limiting arcsine marginals are dependent; the conditional divisor distributions cannot converge in probability to a deterministic arcsine law. Complete proof below; best candidate for a short note.
2. **Binary Elliott/Chowla under polynomial power-free conditioning:** arbitrary fixed admissible families of separable polynomials with irreducible degrees at most \(k+2\) can be imposed without destroying ordinary binary cancellation. Quartic squarefree constraints preserve equidistribution of the four Liouville sign pairs. Complete proof below; only a qualitative error survives.
3. **Integrable inverse-sine moments and a logarithmic endpoint:** for fixed \(0<b<1\), \(\sum_{n\le N}|\sin n|^{-b}=C_bN+O_{b,\epsilon}(N^{b+\epsilon})\). The logarithmically corrected series at exponent \(a=1\) converges exactly when its logarithmic exponent exceeds one. Proof below; classical rotation machinery newly applicable to the full integrable exponent range.

The generalized unweighted Flint–Hills threshold and simultaneous power-free densities are **already upstream**. Neither is proposed as new.

## Sources and exact contracts

Read AGENTS.md, upstream.json, assigned catalogue entries, and matching overview.tex entries. The supplied tree.json is truncated inside lean/ and does not contain the manuscripts. Retrieved the pinned root tree and preprints subtree df0564b2deaab87e07854b6344d8c2f037682e77 (13,223 entries, not truncated). Actual TeX manuscripts and companions are cached under sources/cache/number_theory/, with family/manuscript/basename in each filename.

- **P, family 011:** [Poisson–Dirichlet law for prime predecessors, introduction](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/build/sections/01-introduction.tex), label thm:main, equation eq:main-law. Uniform primes \(3\le p\le x\): ranked logarithms of prime factors of \(p-1\), with multiplicity and denominator \(\log(p-1)\), converge in every finite-dimensional distribution to PD(1). PD(1) is defined by ranking independent uniform stick fragments. Also checked 08-poisson-dirichlet.tex and companion statements; no divisor-overlap law is stated.
- **E, family 007:** [Ordinary two-point correlations, introduction](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/build/introduction.tex), labels cor:affine, thm:q-affine, eq:unp. For fixed nonproportional affine forms of positive integer slope and nonnegative integer intercept, bounded multiplicative functions have ordinary product mean zero if one original factor is uniformly nonpretentious. The quantitative Liouville bound has an absolute logarithmic exponent but constants depending on the forms. Liouville satisfies eq:unp.
- **S, family 020:** [Squarefree quartics, introduction](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Squarefree-values-of-quartics-and-power-free-values-of-polynomials-September-24-2026/build/sections/01-introduction.tex), label cor:separable-products. For fixed \(k\ge2\) and fixed separable nonzero integer polynomials \(F_i\), with irreducible degrees at most \(k+2\), simultaneous \(k\)-power-freeness has density \(\prod_p(1-|\Omega_p|/p^k)>0\), provided \(|\Omega_p|<p^k\) for all primes. Here \(\Omega_p\) is the union of root sets of the individual \(F_i\), not their product. Checked the proof in 02-sieve.tex.
- **I, family 017:** [Irrationality exponent of pi](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/build/main.tex), label thm:main: for every \(\nu>2\), eventually \(|\pi-p/q|\ge q^{-\nu}\) for all integer numerators. Thresholds are ineffective. Its [series section](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/build/sections/series.tex), label series:generalized, already proves the criterion \(a>\max(1,b)\) for \(\sum n^{-a}|\sin n|^{-b}\).

## 1. Divisor gcd/lcm Dirichlet law

### Statement

Choose \(p\) uniformly among primes \(3\le p\le x\), put \(M=p-1\), and conditionally choose \(D_1,D_2\) independently and uniformly from the **distinct positive divisors** of \(M\). Put
\[
A=\gcd(D_1,D_2),\quad B=D_1/A,\quad C=D_2/A,\quad
H=M/\operatorname{lcm}(D_1,D_2).
\]
Then, through all real \(x\to\infty\),
\[
\frac{(\log A,\log B,\log C,\log H)}{\log M}
\Longrightarrow \operatorname{Dir}(1/4,1/4,1/4,1/4). \tag{1}
\]
Thus \(U_x=\log D_1/\log M\) and \(V_x=\log D_2/\log M\) each converge to Beta\((1/2,1/2)\), whose CDF is \(2\arcsin(\sqrt t)/\pi\). Normalized gcd and lcm logarithms tend respectively to Beta\((1/4,3/4)\) and Beta\((3/4,1/4)\). The limiting \(U,V\) are uncorrelated but not independent:
\[
\mathbb E(U-\tfrac12)^2=\tfrac18,\qquad
\mathbb E[(U-\tfrac12)^2(V-\tfrac12)^2]=\tfrac7{384},
\]
\[
\operatorname{Cov}((U-\tfrac12)^2,(V-\tfrac12)^2)=\tfrac1{384}. \tag{2}
\]
These are averaged laws over primes; the number of divisors sampled is fixed.

### Complete proof

**Repeated prime factors.** Write
\[
R(n)=\sum_{q^e\parallel n,\ e\ge2}e\log q,\qquad
d(n)=\prod_{q^e\parallel n}q^{\lfloor e/2\rfloor}.
\]
Then \(d(n)^2\mid n\) and \(\log d(n)\ge R(n)/3\). For fixed \(0<\eta<1\), among \(\sqrt x\le n\le x\), \(R(n)>\eta\log n\) implies a square divisor \(d^2\mid n\) with \(d>x^{\eta/6}\). Their number is at most
\[
\sum_{x^{\eta/6}<d\le\sqrt x}\lfloor x/d^2\rfloor
\ll_\eta x^{1-\eta/6}.
\]
Primes with \(p-1<\sqrt x\) have negligible proportion too. Since \(\pi(x)\asymp x/\log x\),
\[
R(p-1)/\log(p-1)\longrightarrow0
\quad\hbox{in probability over primes}. \tag{3}
\]
No prime-distribution estimate for growing moduli is used.

**All-factor marking.** Give each prime-factor occurrence of \(M\) mass \(\log q/\log M\) and an independent uniform color in \(\{1,2,3,4\}\). For the first \(K\) ranked atoms, convergence of colored masses follows from P by averaging over finitely many color choices. If \(T_{x,K}\) is the omitted mass, then
\[
\lim_{x\to\infty}\mathbb E T_{x,K}
=1-\sum_{j\le K}\mathbb E L_j\longrightarrow0
\quad(K\to\infty).
\]
Here \(\sum_jL_j=1\) almost surely by stick breaking. Uniform continuity of tests on the compact simplex and Markov's inequality justify discarding tails. The full colored mass vector therefore converges to the colored PD(1) vector. This explicitly handles the passage from finite-dimensional convergence to a statistic involving every factor.

**Identify the law.** More generally, color PD atoms with probabilities \(\alpha_i>0\), \(\sum_i\alpha_i=1\). Independent marks permit use of unsorted uniform stick fragments. The totals solve
\[
Z\overset d=Ue_J+(1-U)Z',
\]
where \(U\) is uniform, \(\Pr(J=i)=\alpha_i\), and \(Z'\) is an independent copy. Dirichlet\((\alpha)\) solves this equation: normalize independent Gamma\((\alpha_i,1)\) variables with sum \(S\). Their sum is Gamma\((1,1)\), independent of the normalized vector. Adding an independent Gamma\((1,1)\) variable \(T\) to coordinate \(i\) gives Dirichlet\((\alpha+e_i)\); \(T/(S+T)\) is uniform and independent of the original normalized vector. The new density is \(z_i/\alpha_i\) times the old density. Mixing with probabilities \(\alpha_i\) recovers the old density because \(\sum_i z_i=1\). The Gamma facts follow by changing variables to the sum and normalized coordinates.

Uniqueness follows by coupling two iterations with the same \(U,J\): expected \(\ell^1\) distance contracts by \(1/2\) at every step. The simplex is bounded. Thus the colored law is Dirichlet\((\alpha)\), here with all \(\alpha_i=1/4\).

**Actual uniform divisors.** Given \(M=\prod q^e\), each divisor exponent is uniform on \(\{0,\ldots,e\}\), independently across primes. For \(e=1\), the two divisor exponents give the four equiprobable states corresponding to \(A,B,C,H\). Couple these with the colors above. At repeated primes use any coupling with the independently colored occurrences. The discrepancy is supported on repeated-prime mass, so its \(\ell^1\) norm is at most \(2R(M)/\log M\). Equation (3) proves (1).

**Moments and a stronger-law obstruction.** For \(Z\sim\operatorname{Dir}(1/4)^4\),
\[
\mathbb E\prod_iZ_i^{m_i}=\frac{\prod_i(1/4)_{m_i}}{(1)_{\sum_i m_i}}.
\]
Expand \(U=Z_1+Z_2,V=Z_1+Z_3\) to obtain (2) and \(\mathbb E[(U-1/2)(V-1/2)]=0\). Boundedness transfers all moments from the finite models.

Define the conditional divisor variance
\[
Q_p=\frac1{\tau(p-1)}\sum_{d\mid p-1}
\left(\frac{\log d}{\log(p-1)}-\frac12\right)^2.
\]
Conditional independence gives \(\mathbb E Q_p\to1/8\), \(\mathbb E Q_p^2\to7/384\), and therefore \(\operatorname{Var}(Q_p)\to1/384\). The conditional divisor measures cannot converge in probability over primes to the deterministic arcsine measure: that would force their bounded continuous second-moment statistic to converge in probability to \(1/8\), with vanishing variance.

### Novelty status

The probability mechanism is classical: Hirth's [1997 GEM/PD and arcsine paper](https://doi.org/10.1017/S0963548396002805) links PD and divisor laws. Leung's [Dirichlet factorization theorem](https://arxiv.org/html/2206.14728v3), Theorems 1.1 and 7.1, covers ordinary integers and appropriate multiplicative weights, not directly the shifted-prime indicator. [Bharadwaj–Rodgers](https://arxiv.org/abs/2402.11884) supplies PD transfer at level one, including a conditional shifted-prime route. The candidate contribution is the ordinary prime-predecessor specialization and explicit gcd/lcm overlap law, including failure of conditional concentration. Searches found no identical unconditional arithmetic statement, but Hirth and older divisor-process literature need fuller checking before claiming priority.

## 2. Binary cancellation on polynomial power-free sets

### Statement

Fix \(k\ge2\) and \(F_1,\ldots,F_r\) satisfying S. Ignore finitely many integer zeros and put
\[
w(n)=\prod_i1_{\{F_i(n)\text{ is }k\text{-power-free}\}},
\qquad c=\prod_p(1-|\Omega_p|/p^k)>0.
\]
Let \(L_j(n)=a_jn+b_j\), with fixed integers \(a_j\ge1,b_j\ge0\), \(a_1b_2-a_2b_1\ne0\). If \(f_1,f_2\) are multiplicative and bounded in modulus by one, and an original factor satisfies
\[
\inf_{|t|\le X}\sum_{p\le X}
\frac{1-\Re(f_j(p)\overline{\chi(p)p^{it}})}p\to\infty
\quad\text{for every fixed Dirichlet character }\chi,
\]
then
\[
\sum_{n\le N}w(n)f_1(L_1(n))f_2(L_2(n))=o(N). \tag{4}
\]
For every sign pair \(\epsilon_1,\epsilon_2\in\{-1,1\}\),
\[
\#\{n\le N:w(n)=1,\lambda(L_j(n))=\epsilon_j,\ j=1,2\}
=\tfrac c4N+o(N). \tag{5}
\]
No coprimality between polynomials and forms is required. Family sizes, coefficients, \(k\), and forms are fixed.

### Complete proof and loss of rate

For fixed \(Y\), impose just the conditions at primes \(p\le Y\), giving a periodic majorant \(w_Y\) of period \(Q_Y=\prod_{p\le Y}p^k\) and mean \(c_Y=\prod_{p\le Y}(1-|\Omega_p|/p^k)\). From S and \(w_Y\ge w\),
\[
\lim_{N\to\infty}N^{-1}\sum_{n\le N}|w_Y(n)-w(n)|
=c_Y-c,\qquad c_Y\downarrow c. \tag{6}
\]
For \(a\in\{1,\ldots,Q_Y\}\), write \(n=Q_Ym+a\). Transformed forms have determinant \(Q_Y(a_1b_2-a_2b_1)\ne0\), positive slopes, and nonnegative intercepts. E applies to the same original functions. The initial \(m=0\) term costs at most one. Summing over finitely many allowed residues proves cancellation with \(w_Y\). Boundedness and (6) give
\[
\limsup_{N\to\infty}N^{-1}
\left|\sum_{n\le N}w(n)f_1(L_1(n))f_2(L_2(n))\right|\le c_Y-c.
\]
Send \(Y\to\infty\), proving (4). With a factor identically one the argument gives one-point Liouville cancellation, using any auxiliary nonproportional form. Expand the sign indicator as
\[
\tfrac14(1+\epsilon_1\lambda(L_1(n)))(1+\epsilon_2\lambda(L_2(n))).
\]
Its constant term has mean \(c\), and the other three terms vanish, proving (5).

**Uniformity:** first \(N\to\infty\) with \(Y\) fixed, then \(Y\to\infty\). Taking \(Y=Y(N)\) requires uniform control of E's constants for coefficients involving \(Q_Y\), plus a quantitative (6). Neither is asserted. Even for Liouville the conclusion is \(o(N)\), not a logarithmic saving.

For example, for every sign pair,
\[
\#\{n\le N:n^4+1\text{ squarefree},
\lambda(n)=\epsilon_1,\lambda(n+1)=\epsilon_2\}
\sim\tfrac N4\prod_{p\equiv1\pmod8}(1-4/p^2).
\]
Indeed \(t^4+1=\Phi_8(t)\) is irreducible, has no roots modulo 4, and has four simple roots modulo an odd prime exactly when \(p\equiv1\pmod8\). Hensel lifting gives the displayed factors. The squarefree density alone appears upstream; the sign-conditioned result is the deduction.

### Novelty status

Periodic approximation is standard. Desjardins's [squarefree–Liouville sieve](https://arxiv.org/html/1610.07440), Theorem 2.9 and Corollaries 2.10/2.12, is a direct precedent, including homogeneous two-variable applications. The new-to-project result is the ordinary **one-variable** combination of assumed binary Elliott and the assumed quartic/power-free range. Do not claim a new abstract sieve method. Fuller comparison with conditional one-variable squarefree–Chowla results remains necessary for priority; the explicit quartic sign distribution was not located in the bounded search.

## 3. Integrable inverse-sine averages and logarithmic boundary

For fixed \(0<b<1\) and every \(\epsilon>0\), I implies
\[
\sum_{n\le N}|\sin n|^{-b}
=C_bN+O_{b,\epsilon}(N^{b+\epsilon}),\quad
C_b=\frac{\Gamma((1-b)/2)}{\sqrt\pi\,\Gamma(1-b/2)}. \tag{7}
\]
Hence, for fixed real \(c\), \(\sum_{n\ge2}1/[n(\log n)^c|\sin n|^b]\) converges iff \(c>1\). At \(c=1\), partial sums equal \(C_b\log\log N+O_b(1)\). More generally, subtracting \(C_b\sum_{2\le n\le N}1/[n(\log n)^c]\) leaves a convergent sequence.

**Proof.** Put \(\alpha=1/\pi\). Inverting rational approximants in I gives \(\|n\alpha\|\ge c_\eta n^{-1-\eta}\) for every \(\eta>0\). Continued-fraction denominators satisfy \(q_{j+1}\ll_\eta q_j^{1+\eta}\), hence \(a_{j+1}\ll_\eta q_j^\eta\). Every block of \(q_j\) consecutive rotation points has interval counting discrepancy \(O(1)\): compare to the shifted rational grid, with displacement at most \(1/q_{j+1}\le1/q_j\). Greedy continued-fraction decomposition uses at most \(\sum_{q_j\le N}a_{j+1}=O_\eta(N^\eta\log N)\) blocks. Thus unnormalized interval discrepancy is \(O_\delta(N^\delta)\) for every \(\delta>0\).

Cap \(f(t)=|\sin(\pi t)|^{-b}\) at \(f(r_N)\), with \(r_N=c_\eta N^{-1-\eta}/2\). This changes none of the sampled values. Capped variation is \(O_b(r_N^{-b})\); the integral changes by \(O_b(r_N^{1-b})\). The bounded-variation discrepancy inequality bounds the error by
\[
O_{b,\delta,\eta}(N^\delta r_N^{-b}+Nr_N^{1-b}).
\]
Choose \(\delta+b\eta<\epsilon\), proving (7), with its elementary beta integral \(C_b\). Choose \(\epsilon<1-b\); partial summation of the error converges against \(1/[n(\log n)^c]\) for every fixed \(c\), since the tail is bounded by a constant times \(\int^\infty t^{b+\epsilon-2}(\log t)^{|c|+1}\,dt<\infty\). The logarithmic integral proves the weighted conclusions.

**Novelty and endpoints:** rotation machinery is classical; see primary work on [singular rotation sums](https://people.math.harvard.edu/~knill/birkhoffsum/papers/birkhoffsum.pdf) and [reciprocals of fractional parts](https://arxiv.org/abs/1511.06862). The new input supplies the full integrable exponent range at \(1/\pi\). No claim is made at \(b=1\), or about logarithmic corrections on \(a=b>1\). Exponent two supplies neither bounded partial quotients nor a prescribed logarithmic Diophantine bound. Constants inherit ineffective thresholds. The separate project proposal rotation.md concerns Sobolev cohomology, not (7).

## Broad screen and rejected alternatives

- **003:** the cached 7/8 manuscript's thm:main gives its zero-free region, while cor:nonresidues-square-roots already states polylogarithmic least quadratic nonresidues and deterministic polynomial-time modular square roots. These are duplicates. Explicit-formula applications must retain conductor dependence.
- **011:** the smooth-shifted-prime/totient and even-prime-factor companions do not state proposal 1. PD does not supply independence of recursively sampled Pratt-tree generations.
- **012:** thm:main in the joint Dickman introduction gives the joint largest-factor law; cor:comparison already gives ordering density \(1/2\). Max/min/product pushforwards are valid but less substantive. It does not supply three consecutive independent laws or full factor partitions for both integers.
- **017:** the generalized power threshold is explicitly series:generalized; bounded partial quotients and nonintegrable logarithmic endpoints are not consequences.
- **020:** simultaneous squarefree values are already cor:separable-products, used as input above.
- **021:** thm:main in the Jacobsthal introduction actually gives \(h(k)\ll k^2/(\log\log(3k))^2\). Avoidance of one arbitrary residue per prime is a CRT reformulation, not a new theorem. Multiple forbidden residues per prime do not follow.
- **024:** thm:main in build/source/statements.tex already gives \(V(cx)/V(x)\to c\). Inverse-sequence and fixed-dilation moment consequences are standard regular variation. No moving-scale interval theorem or continuity of the phase coefficient follows automatically.
- **029:** thm:primitive-root gives only \(\gg_a x/(\log x)^2\) primes per dyad. It implies neither positive prime density nor divergent reciprocal sum: reciprocal dyadic lower bounds sum like \(\sum j^{-2}\). The simultaneous prime-base companion already states its four-input conditional result.

All those manuscript theorem statements and available companion statements were inspected from the pinned cache. For 1–3, open work is priority verification and quantitative strengthening, not an unfilled implication in the stated proofs. In particular: no rate for (1), growing-parameter uniformity for (4), or nonintegrable logarithmic endpoint for (7).

## Reproducible validation

Run: python openai-proof-research/experiments/number_theory.py. Exact rational Dirichlet moments verify (2). A smallest-prime-factor sieve computes conditional divisor moments without Monte Carlo (floating point only for logarithms). At \(x=10^6\), over 78,497 primes:

- Mean conditional variance: 0.11491235; limit 0.125.
- Mean squared conditional variance: 0.01545020; limit \(7/384=0.01822917\ldots\).
- Mean normalized log gcd: 0.25600443; limit 0.25.
- At \(b=1/2\), inverse-sine averages for \(N=10^4,10^5,10^6\): 1.75009753, 1.65758248, 1.66763472; \(C_{1/2}=1.66925368\ldots\).

Finite-cutoff errors are visible; no rate is inferred. These computations check moment algebra and provide diagnostics, not proofs of convergence. The finite-sieve transfer needs no numerical verification. No files were staged or committed.
