# Full ordinary source candidate: normalized totient deficiency

Target: Belbachir–Ranjan–Singh, arXiv:2610.36260v1, Section 6 and Question 9.4 (PDF p18). Put S(n)=sum_{p|n}(p-1), Delta(n)=phi(n)-1-S(n), R(n)=Delta(n)/phi(n), including phi(1)=1 and S(1)=0. For EVERY epsilon>0,

lim_{X→∞} (1/floor X) sum_{1≤n≤X}|R(n)-1|=0,
lim_{X→∞} #{n≤X: |R(n)-1|>epsilon}/floor X=0.

Thus the limiting empirical distribution is the unit point mass at 1. The same conclusions hold on composite integers, and after omitting the family 2p, since the omitted sets have density zero and the full nonnegative error sum is o(X). This determines the limiting distribution and the source's predicted convergence in mean; no exact finite-X law, rate, fluctuation law or multiplicity Questions 9.1–9.3 is claimed.

## Complete classical-adaptation bridge

All ingredients below are classical and proved here. No novelty follows from the source having posed the question. The complete bridge, rather than its length, is the substantive-novelty concern for root.

1. For every integer m≥1, phi(m)≥sqrt(m/2). Indeed phi(m)^2/m is the product over p^a||m of p^(a-2)(p-1)^2. Every odd-prime factor is at least 1; the factor at 2 is at least 1/2. Empty products give m=1. Consequently A(Y)=sum_{m≤Y}1/phi(m)≤2sqrt(2Y), and sum_{m≥1}1/(m phi(m)) converges by comparison with sqrt(2) sum m^(-3/2).

2. pi(Y)/Y→0. For a fixed finite prime set P, primes outside P lie in residue classes coprime to Q=product P. Counting these classes gives limsup pi(Y)/Y≤phi(Q)/Q=product_{p in P}(1-1/p). These products tend to zero: the inverse product over primes≤z expands into a nonnegative sum over integers with prime factors≤z, hence is at least sum_{n≤z}1/n→∞. This argument uses neither PNT nor an unproved prime-distribution conjecture.

3. Decompose each pair (n,p|n) uniquely as n=p^a m, a≥1, (p,m)=1. Euler multiplicativity gives

(p-1)/phi(n)=1/[p^(a-1) phi(m)].

Let T_a(X) be the sum of these terms over p,m with p^a m≤X and (p,m)=1. All terms are nonnegative; every rearrangement below is a finite sum or a monotone nonnegative bound. Then sum_{n≤X} S(n)/phi(n)=sum_{a≥1}T_a(X).

For a=1, dropping coprimality gives

T_1(X)/X ≤ sum_{m≤X} [1/(m phi(m))] [pi(X/m)/(X/m)].

For every fixed m the bracketed prime ratio tends to zero by step 2, is bounded by 1, and its coefficient is summable by step 1. Explicitly, choose M so that the coefficient tail is below epsilon/2, then choose X large enough that the finite sum m≤M is below epsilon/2. Thus T_1(X)=o(X). This handles ALL cofactors, not just bounded cofactors or squarefree integers.

For a≥2, again drop coprimality and use step 1:

sum_{a≥2}T_a(X)
 ≤ sum_{p,a≥2} p^(-(a-1)) A(X/p^a)
 ≤ 2sqrt(2X) sum_p sum_{a≥2} p^(1-3a/2)
 = 2sqrt(2X) sum_p p^(-2)/(1-p^(-3/2))
 < 6sqrt X.

For the last inequality use 1/(1-p^(-3/2))<2 and sum_p p^(-2)≤sum_{n≥2}n^(-2)<1, so the constant is at most 4sqrt2<6. The extension to all p,a only increases the sum. This uniformly handles arbitrary prime powers and all exponents, rather than assuming the repeated-prime terms negligible.

4. Since R(n)<1 for all n, its absolute error is exactly (1+S(n))/phi(n). Step 1 bounds the sum of the 1/phi(n) terms by 2sqrt(2X); step 3 gives o(X) for the S terms. Divide by floor X to obtain the asserted L1 convergence. Markov's elementary counting bound gives the epsilon-density conclusion. For t<1, #{n≤X:R(n)≤t}/floor X tends to zero by the same bound (use any smaller positive threshold than 1-t); for t≥1 it is identically 1. In particular this gives weak convergence to delta_1. Primes supply R(p)=-1/(p-1)→0, so ordinary pointwise convergence to 1 is FALSE and is not asserted.

## Scope and eligibility

This is a full ordinary proof for the limiting-distribution/mean interpretation of the literal source question. There is no residual universal mathematical quantifier in that claim. The exact distribution at each finite cutoff and the source's unrelated multiplicity questions remain outside it. The proof is a complete elementary classical adaptation, so eligibility as a substantive new outcome is HOLD, with no acceptance or credit requested. Bounded search has not established new-to-literature status. Root alone decides whether this is excluded as routine or warrants review. Numerical checks below are diagnostics, never the proof.
