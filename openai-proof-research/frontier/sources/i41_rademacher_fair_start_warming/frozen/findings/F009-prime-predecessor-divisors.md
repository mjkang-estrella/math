# F009 — Divisor gcd/lcm Dirichlet law

Status: **proved prime-predecessor specialization of classical multi-divisor laws; independently reviewed and accepted**. The arithmetic specialization uses the accepted upstream result; no new general probability law or literature-priority claim.

### Exact input

P is [The Poisson–Dirichlet law for prime predecessors, `thm:main`, `eq:main-law`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/build/sections/01-introduction.tex): for uniformly weighted primes 3≤p≤x, the ranked logarithms of all prime factors of p−1, with multiplicity and normalized by log(p−1), converge in every fixed finite dimension to PD(1). The limit is ranked independent uniform stick breaking, has total mass 1, and applies through all real x→∞.

### Statement

Choose \(p\) uniformly among primes \(3\le p\le x\), put \(M=p-1\), and conditionally choose \(D_1,D_2\) independently and uniformly **with replacement** from the set of **distinct positive divisors** of \(M\). Put
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
Here \(\sum_jL_j=1\) almost surely by stick breaking. Uniform continuity of tests on the compact subprobability simplex {z_i≥0, Σz_i≤1} (or on [0,1]⁴) and Markov's inequality justify discarding tails. The full colored mass vector therefore converges to the colored PD(1) vector. This explicitly handles the passage from finite-dimensional convergence to a statistic involving every factor.

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

### Novelty status and closer prior work

The correct description is a **prime-predecessor specialization of classical
multi-divisor Dirichlet laws**, including gcd/lcm marginals and a conditional
variance obstruction. In particular, the dependence of the arcsine marginals
and the coloring mechanism are not new general phenomena.

- [Hirth, *From GEM back to Dirichlet via Hoppe’s Urn* (1997)](https://doi.org/10.1017/S0963548396002842) explicitly gives the classical GEM/PD-to-Dirichlet relationship.
- [De la Bretèche–Tenenbaum (2016), Theorem 1.1](https://tenenb.perso.math.cnrs.fr/PPP/proc-arith.pdf) gives the 2^r-coordinate Dirichlet law for r divisors of an ordinary uniform integer, including exactly the quarter-parameter joint marginal law at r=2.
- [Bareikis–Mačiulis (2012), Theorem 2.1](https://www.impan.pl/shop/en/publication/transaction/download/product/82360) gives an earlier quarter-parameter second-CDF-moment integral.
- [Leung, Theorem 7.1 and Example 7.5](https://arxiv.org/html/2206.14728v3) covers ordinary-integer weighted factorizations, including the overlap factorization M=ABCH with gcd(B,C)=1. The shifted-prime indicator is not multiplicative.
- [Bharadwaj–Rodgers v3, Theorem 6 and Conjecture 4](https://arxiv.org/html/2402.11884v3) gives a conditional level-one route to shifted-prime PD. The accepted OpenAI input supplies the unconditional premise within this project.

No identical arithmetic specialization was found in the bounded check, but
that is not proof of priority. There is no rate, growing-number-of-divisors
statement, independence of recursive factorization generations, or
concentration at a deterministic conditional measure.

### Validation and an independent moment check

[Independent review](../reviews/divisor_law-r1.md) accepted the mathematics
after checking the source normalization, repeated-prime tail, finite-to-full
PD convergence, Gamma coupling, moments and nonconcentration. Replacement
sampling, the truncated-test domain and the closer prior work are clarified
here. The parent independently checked all these deductions.

A second calculation checks the fourth moment without the multivariate
expansion. If S₂=ΣL_j² for PD(1) masses, uniform stick breaking gives
S₂=U²+(1−U)²S₂′ in distribution. Thus E S₂=1/2 and
E S₂²=1/5+2(1/30)(1/2)+(1/5)E S₂²=7/24. Conditional divisor variance
in the limit is S₂/4, recovering mean 1/8 and second moment 7/384.

`python openai-proof-research/experiments/number_theory.py` passed exact
rational moment calculations. Its sieve over 78,497 primes through 10⁶
gave mean conditional variance 0.11491235 (limit 0.125), mean squared
variance 0.01545020 (limit 0.01822917…), and mean normalized log-gcd
0.25600443 (limit 0.25). Finite-size bias is visible; these observations
are diagnostics, not a proof or an error-rate estimate. No proof-assistant
verification is claimed.
