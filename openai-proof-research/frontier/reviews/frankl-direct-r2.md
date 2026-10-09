# Frankl round 2: applying the sharp cube-information theorem directly to \(U=1_{\mathcal F}(X)\)

Date: 2026-10-08. Premise: theorems of the pinned `openai/math` revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are accepted as true. The prior scout (`frontier/scouts/discrete.md`) was read for scope only. Its coding obstructions are neither repeated nor re-audited here.

## Classification (read first)

**No new case of Frankl's conjecture and no improved frequency bound was obtained. The route is parked for lack of a viable intermediate-noise lower bound; it has not been disproved as a general proof strategy.**

**Parent review corrections.** Theorem R below is restricted to `0 < alpha <= 1/2`, the range its scalar proof covers. Candidate (C) is vacuous: at both `rho=0` and `rho=1`, information equals the accepted bound, so its supremum is zero for every family. The near-miss construction establishes continuity, not a required discontinuity or an impossibility theorem. Finite census conclusions concern only tested dimensions and noise values. These corrections supersede the scout's original terminal summary.

The route asks whether "union-closed with every coordinate frequency below 1/2" forces \(I(1_{\mathcal F}(X);Y)\) above the accepted sharp bound at some noise level \(\rho\). Proved here:

1. **Small noise correlation (\(\rho\to0\)).** For every union-closed family with density at most one half and all \(p_i\le1/2\), including any hypothetical counterexample, the ratio \(I/\text{bound}\) tends to at most \(t(\alpha)/r_m^2\le1\). The inequality is strict for \(\alpha<1/2\), and the bound does not depend on the dimension (Theorem R). The proof uses only Reimer's average-set-size theorem (2003). So the order-\(\rho^2\) content of the route is the level-one inequality, which, under the Frankl-failure sign condition, is strictly weaker than Reimer's theorem. This confirms the parent's suspicion, quantitatively.
2. **Noise correlation near 1 (\(\rho\to1\)).** Every Boolean \(f\) with mean \(\alpha\notin\{0,1/2,1\}\) is strictly below the bound for \(\rho\) close enough to 1 (Lemma N). Karpas already rules out \(\alpha\ge1/2\) for counterexamples, so no violation can occur near \(\rho=1\) either.
3. **Finite noise.** Union closure used at finite noise yields only **upper** bounds on noise stability and \(\chi^2\)-information (Proposition D). Those bounds point the same way as the accepted theorem, so they cannot combine with it to give a contradiction. In 22,016,312 (family, \(\rho\)) pairs (all union-closed families with ground set exactly \([n]\), \(n\le5\)), the closure bound was never stronger than the sharp bound.
4. **Robustness.** An explicit union-closed family \(G_n\) has ground set \([n]\). Each of \(n-1\) elements lies in exactly \((|G_n|+1)/2\) members, which is one member short of a frequency below 1/2. This family approaches the sharp bound within \(O(n2^{-n})\), uniformly in \(\rho\) (Proposition G). Any valid lemma "closure plus frequency hypothesis implies a violation" must therefore fail if the frequency hypothesis is relaxed by \(1/(2|\mathcal F|)\).

Exhaustive evidence (floating point, not proof) adds two findings:

- At \(n=4\), the most informative union-closed family of each weight is as informative as the most informative Boolean function of that weight.
- At \(n=5\), the maximum over union-closed families of each weight is attained by an **up-set**, and up-sets satisfy Frankl trivially. Families near the frequency threshold with \(\alpha<1/2\) sit well below the bound, and their best ratio decreases with \(n\).

None of the proved statements above is claimed to be new to the literature. They are retained as diagnostics of this unsuccessful attempt. No novelty ranking is offered.

## 1. Literature benchmarks (abstract-level check, not a certified survey of best bounds)

- Frankl target: [MathDB 355601](https://mathdb.com/p/355601/the-union-closed-sets-conjecture), with `importance: celebrated` as recorded by the prior scout.
- Unconditional constant \((3-\sqrt5)/2\approx0.38197\): Alweiss–Huang–Sellke, [arXiv:2211.11731](https://arxiv.org/abs/2211.11731) (one one-variable inequality checked by computer); Sawin, [arXiv:2211.11504](https://arxiv.org/abs/2211.11504); and Chase–Lovett, all building on Gilmer, [arXiv:2211.09055](https://arxiv.org/abs/2211.09055) (constant 0.01). Sawin and Yu/Cambie raised this to ≈0.38234; those papers were not separately retrieved here.
- J. Liu, [arXiv:2306.08824](https://arxiv.org/abs/2306.08824) (v1, 15 June 2023): ≈0.38271. The abstract says this rests on "numerically verified hypotheses".
- Y. Jiang, [arXiv:2609.08291](https://arxiv.org/abs/2609.08291) (8 Sept 2026): announces a **computer-assisted** bound of 0.38288525. Only the abstract page was read. Its verification was not checked.
- Large families: Karpas, [arXiv:1708.01434](https://arxiv.org/abs/1708.01434), proves Frankl whenever \(|\mathcal F|\ge(1/2-c)2^n\). Hence any counterexample has \(\alpha=|\mathcal F|/2^n<1/2-c\).
- Reimer, *An average set size theorem*, Combin. Probab. Comput. 12 (2003) 89–93: union-closed \(\mathcal F\) has average member size at least \(\tfrac12\log_2|\mathcal F|\). This is used below as an accepted published theorem.
- Related variants (not targets): Das–Wu, [arXiv:2412.03862](https://arxiv.org/abs/2412.03862), on the k-th most frequent element; Wang, [arXiv:2609.25101](https://arxiv.org/abs/2609.25101), disproving a weighted union-set conjecture; the entropy–KL strengthening, already false by Ellis (prior scout).

Nothing in this report approaches these constants. They are recorded so that no derived quantity is mistaken for an improvement.

## 2. Accepted input, as stated in the source

From `frontier/sources/discrete/binary__main.tex` (family 119, pinned), Theorem `main:soft`: for \(u:\Omega_n\to[-1,1]\) and \(-1\le\rho\le1\),
\(I(T_\rho u)\le\psi(|\rho|\psi^{-1}(I(u)))\), where \(H(r)\) is the natural-log entropy of a sign of mean \(r\), \(\psi=\log2-H\), and \(I(u)=H(\mathbb E u)-\mathbb E H(u)\).

Corollary `main:ck`: for Boolean \(f\) with mean \(m\) and \(r_m=\psi^{-1}(H(m))\),
\(I(f(X);Y)\le\psi(|\rho|r_m)\le\psi(|\rho|)\).

The input is uniform on the cube in every case. The Hellinger companion (`hellinger__main.tex`, `thm:main`) states \(\sqrt{1-m^2}-\mathbb E\sqrt{1-(T_\rho f)^2}\le1-\sqrt{1-\rho^2}\). The mean-dependent production theorem (`upgrade:production`) was located. It is not needed, because only the integrated corollary is applied.

Below, "CK" means the refined right side \(\psi(\rho r_m)\), with \(0\le\rho\le1\) (negative \(\rho\) is symmetric).

## 3. Setup and the exact decomposition

Identify \(A\subseteq[n]\) with \(x\in\{0,1\}^n\). Let \(f=1_{\mathcal F}\), \(\alpha=|\mathcal F|/2^n\), \(g=2f-1\), \(m=2\alpha-1\). Let \(X\) be uniform, \(U=f(X)\), and let \(Y\) be \(X\) with each bit flipped independently with probability \(\varepsilon=(1-\rho)/2\). Write \(p_i=|\{A\in\mathcal F:i\in A\}|/|\mathcal F|\).

**Lemma 1 (exact decomposition).** \(Y\) is uniform, and
\[
P_1(y):=\Pr(Y=y\mid U=1)=\frac{T_\rho f(y)}{\alpha2^n},\qquad
P_0(y)=\frac{1-T_\rho f(y)}{(1-\alpha)2^n},
\]
\[
I(U;Y)=\alpha D(P_1\Vert\mathrm{unif})+(1-\alpha)D(P_0\Vert\mathrm{unif}),\qquad
D(P_1\Vert\mathrm{unif})=\frac{\operatorname{Ent}(T_\rho f)}{\alpha},
\]
where \(\operatorname{Ent}(h)=\mathbb E h\log h-\mathbb Eh\log\mathbb Eh\).

*Proof.* Bayes' rule with the symmetric kernel, together with \(I(U;Y)=\sum_u\Pr(U=u)D(P_{Y\mid u}\Vert P_Y)\) and \(P_Y=\mathrm{unif}\). ∎

\(P_1\) is the law of a uniformly random member of \(\mathcal F\) passed through \(\mathrm{BSC}_\varepsilon^{\otimes n}\). This identity uses no closure. Closure must enter through the structure of \(T_\rho f\), and the next sections show where it can and cannot enter.

Fourier normalization: \(\chi_i(x)=2x_i-1\). Then \(\mathbb E[g\chi_i]=2\alpha(2p_i-1)\), so the level-one weight of \(g\) is
\[
W_1(g)=4\alpha^2\sum_i(1-2p_i)^2.\tag{3.1}
\]

## 4. Theorem R: as \(\rho\to0\), Reimer's theorem dominates the route

**Theorem R (proved).** Let \(\mathcal F\subseteq2^{[n]}\) be union-closed with \(0<\alpha\le1/2\) and every \(p_i\le1/2\). Then
\[
\lim_{\rho\to0}\frac{I(U;Y)}{\psi(\rho r_m)}
=\frac{\alpha\sum_i(1-2p_i)^2}{(1-\alpha)r_m^2}
\le\frac{t(\alpha)}{r_m^2}\le1,\qquad
t(\alpha):=\frac{\alpha\log_2(1/\alpha)}{1-\alpha}.
\]
The last inequality is strict for \(0<\alpha<1/2\). In particular, a hypothetical counterexample (which has \(\alpha<1/2\) by Karpas) cannot violate the sharp bound as \(\rho\to0\), and its limiting ratio is at most \(t(\alpha)/r_m^2<1\). This bound is independent of \(n\).

*Proof.*

*Step 1: expansion.* Write \(T_\rho g-m=\sum_{S\ne\varnothing}\rho^{|S|}\hat g(S)\chi_S\). Then \(\mathbb E(T_\rho g-m)^2=\rho^2W_1+O(\rho^4)\). The cubic term has no \(\rho^3\) contribution, because \(\mathbb E\chi_i\chi_j\chi_k=0\) for all \(i,j,k\). Taylor expansion of \(\psi\) at \(|m|<1\), with \(\psi''(m)=1/(1-m^2)\), gives
\(I=\mathbb E\psi(T_\rho g)-\psi(m)=\rho^2W_1/(2(1-m^2))+O(\rho^4)\).
Also \(\psi(\rho r)=\rho^2r^2/2+O(\rho^4)\). With (3.1) and \(1-m^2=4\alpha(1-\alpha)\), the limit is as displayed.

*Step 2: Reimer.* \(\sum_ip_i\) is the average member size, which is at least \(\tfrac12\log_2|\mathcal F|=\tfrac12(n+\log_2\alpha)\). Hence \(\sum_i(1-2p_i)\le\log_2(1/\alpha)\). Since each \(1-2p_i\in[0,1]\), \(\sum(1-2p_i)^2\le\sum(1-2p_i)\le\log_2(1/\alpha)\).

*Step 3: the scalar inequality \(t(\alpha)\le r_m^2\) on \((0,1/2]\).*

- First, \(t\le1\). Let \(q(\alpha)=1-\alpha-\alpha\log_2(1/\alpha)\). Then \(q(1/2)=0\), and \(q'(\alpha)=-1+(1+\ln\alpha)/\ln2\) is increasing with \(q'(1/2)<0\). So \(q\) decreases on \((0,1/2]\), and \(q\ge0\).
- Second, \(\psi(r)/r^2=\sum_{k\ge1}r^{2k-2}/(2k(2k-1))\) is increasing on \([0,1]\), with value \(\ln2\) at \(r=1\). So \(\psi(\sqrt t)\le t\ln2=\alpha\ln(1/\alpha)/(1-\alpha)\).
- Third, put \(G(\alpha)=(1-\alpha)^2\ln\frac1{1-\alpha}-\alpha^2\ln\frac1\alpha\). Then \(G(0^+)=G(1/2)=0\) and \(G'(\alpha)=1-2h(\alpha)\), where \(h\) is natural binary entropy, increasing on \([0,1/2]\) from 0 to \(\ln2>1/2\). So \(G\) increases and then decreases, giving \(G>0\) on \((0,1/2)\). Dividing \(G\ge0\) by \(1-\alpha\) and rearranging gives \(\alpha\ln(1/\alpha)/(1-\alpha)\le h(\alpha)\), strictly for \(\alpha<1/2\).
- Hence \(\psi(\sqrt t)\le h(\alpha)=H(m)=\psi(r_m)\). Since \(\psi\) is increasing, \(\sqrt t\le r_m\), strictly for \(\alpha<1/2\). ∎

Numerical cross-check: \(\min_{(0,1/2]}[(1-\alpha)r_m^2/\alpha-\log_2(1/\alpha)]=0\), attained at \(\alpha=1/2\) (`frankl_r2_exhaustive.results.json`, key `levelOneMinusReimer_min`).

The Hellinger companion has the analogous order-\(\rho^2\) content \(W_1\le(1-m^2)^{3/2}\). Under the same hypotheses, Reimer gives the stronger inequality whenever \(2(1-\alpha)^{3/2}\ge\sqrt\alpha\log_2(1/\alpha)\). This was checked on a grid of \(2\times10^5\) points on \((0,1/2]\), with minimum 0 at \(1/2\). That is a numerical check only, not a proof.

**Novelty and scope.** The \(\rho^2\) term is the sharp-constant level-one (Chang/Talagrand-type) inequality, \(W_1(f)\lesssim2\alpha^2\ln(1/\alpha)\) as \(\alpha\to0\). For small \(\alpha\), the refined bound agrees to relative order \(r_m^2\) with the classical tensorized strong data-processing bound \(I(U;Y)\le\rho^2H(U)\), because \(\psi(\rho r)\le\rho^2\psi(r)\). Theorem R is a two-line combination of known facts and is **not an advance**. Its role is to show that the route has no content at small noise correlation that Reimer (2003) lacks.

Inverting the same comparison gives no new frequency bound. Assume all \(p_i\le c<1/2\):

- Reimer gives \(n(1-2c)\le\log_2(1/\alpha)\).
- The level-one route gives only \(n(1-2c)^2\le(1-\alpha)r_m^2/\alpha\), which is weaker by Step 3.

## 5. Lemma N: as \(\rho\to1\), every non-balanced Boolean function is strictly below the bound

**Lemma N (proved).** Let \(f\) be Boolean on \(\{0,1\}^n\) with mean \(\alpha\notin\{0,1/2,1\}\). Then there is \(\rho_0<1\), depending on \(f\), such that \(I(f(X);Y)<\psi(\rho r_m)\) for all \(\rho\in(\rho_0,1)\).

*Proof.* Let \(\beta>0\) be the fraction of points with a neighbor of the other value. At such a point,
\(|T_\rho g|\le1-2\varepsilon(1-\varepsilon)^{n-1}\). Since \(H(1-2\delta)=h(\delta)\ge\delta\ln(1/\delta)\),
\[
H(m)-I=\mathbb EH(T_\rho g)\ge\beta\,\varepsilon(1-\varepsilon)^{n-1}\ln\frac1{\varepsilon(1-\varepsilon)^{n-1}}.
\]
This is superlinear in \(\varepsilon\). On the other side, \(r_m<1\) because \(m\ne0\). Convexity of \(\psi\) gives
\[
H(m)-\psi(\rho r_m)=\psi(r_m)-\psi(\rho r_m)\le2\varepsilon\,r_m\operatorname{atanh}(r_m),
\]
which is linear in \(\varepsilon\). ∎

A counterexample has \(\alpha<1/2\), so a violation can only occur at intermediate \(\rho\), bounded away from both ends. At the lower end the margin is dimension-free (Theorem R). At the upper end the margin depends on \(n\).

## 6. Proposition D: finite-noise closure gives only upper bounds

**Proposition D (proved).** Let \(\mathcal F\) be union-closed, \(0\le s\le1\), and let \((X,X')\) be uniform with coordinatewise correlation \(s\). Then
\[
\operatorname{Stab}_s(f):=\Pr(f(X)=f(X')=1)\le\mu_{(3-s)/4}(\mathcal F),
\]
where \(\mu_p\) is the product-Bernoulli(\(p\)) measure. Consequently
\[
I(U;Y)\le\log\Bigl(1+\frac{\mu_{(3-\rho^2)/4}(\mathcal F)-\alpha^2}{\alpha(1-\alpha)}\Bigr).
\]

*Proof.*

- Closure gives \(f(x)f(x')\le f(x\vee x')\). The coordinates of \(X\vee X'\) are independent, with \(\Pr(0)=\Pr(X_i=X'_i=0)=(1+s)/4\).
- \(\mathbb E(T_\rho f)^2=\operatorname{Stab}_{\rho^2}(f)\).
- A direct computation gives \(\sum_u\Pr(u)\chi^2(P_{Y\mid u}\Vert\mathrm{unif})=(\operatorname{Stab}_{\rho^2}f-\alpha^2)/(\alpha(1-\alpha))\).
- \(D\le\log(1+\chi^2)\) holds termwise.
- Concavity of \(\log\) finishes the proof. ∎

**The direction obstruction.** The defining constraint of union closure forbids the pattern \(f(x)=f(x')=1,\ f(x\vee x')=0\). Integrated against any coupling, it bounds joint membership from **above**, and therefore information from above. Frankl failure adds only sign information:
\[
\tfrac{d}{dp}\mu_p(\mathcal F)\big|_{1/2}=2\sum_i\mathbb E[f\chi_i]=2\alpha\sum_i(2p_i-1)<0.
\]
By (3.1), this caps the level-one weight rather than forcing it up. The accepted theorem is also an upper bound. A contradiction therefore needs a *lower* bound on \(I(1_{\mathcal F}(X);Y)\), and none of closure, the sign condition, or the decomposition of Lemma 1 supplies one.

A generic lower bound is marginal subadditivity, \(I\ge\alpha\sum_iD(\mathrm{Bern}(\tfrac12+\rho(p_i-\tfrac12))\Vert\mathrm{Bern}(\tfrac12))+\dots\). It vanishes as the deficits \(1/2-p_i\) shrink, and a counterexample may have deficits of order \(1/|\mathcal F|\).

Empirically, the bound of Proposition D was **never** below CK in any of the 22,016,312 (family, \(\rho\)) pairs tested (\(n\le5\), ground set exactly \([n]\), eight values of \(\rho\)). The inequality \(\operatorname{Stab}\le\mu\) itself held with maximum value of \(\operatorname{Stab}-\mu\) equal to \(-2.45\times10^{-3}\). On the tested instances this bound is weaker than the accepted theorem. Its upper-bound direction alone does not supply the lower bound sought for a contradiction.

## 7. Vacuous candidate inequality and a near-miss continuity calculation

**Candidate (C).** For union-closed \(\mathcal F\) with \(\bigcup\mathcal F=[n]\) and \(\max_ip_i\le\tfrac12+\delta\), we would have \(\sup_\rho[I(U;Y)-\psi(\rho r_m)]\ge-\eta(\delta)\), with \(\eta(\delta)\to0\) as \(\delta\to0\). This is the kind of robust "threshold forces near-saturation" statement the route would need before pushing strictly below the threshold.

**Proposition G (proved, for integers n >= 2).** Let \(G_n=\{A\subseteq[n]:1\notin A\}\cup\{[n]\}\). Then:

- \(G_n\) is union-closed, \(\bigcup G_n=[n]\), and \(|G_n|=2^{n-1}+1\).
- Every \(i\ge2\) lies in exactly \(2^{n-2}+1=(|G_n|+1)/2\) members. This is the least integer above \(|G_n|/2\), so \(\max p_i-\tfrac12=1/(2|G_n|)\), the smallest excess possible at this size.
- For all \(0\le\rho\le1\),
\[
0\le\psi(\rho r_{m_n})-I_{G_n}(\rho)\le4^{1-n}\ln2+h_{\rm nat}(2^{-n})=O(n2^{-n}).
\]

*Proof.*

- Closure: sets avoiding 1 are closed under union, and union with \([n]\) gives \([n]\). The counts are immediate.
- Bound: the dictator \(g_\ast=2\cdot1\{x_1=0\}-1\) has \(I=\psi(\rho)\) (directly, or by the equality case of the accepted theorem). Also \(\mathbb E|g_n-g_\ast|=2^{1-n}\) and \(T_\rho\) is an \(L^1\) contraction.
- Use \(|H(a)-H(b)|\le\phi(|a-b|/2)\) with \(\phi(t)=h_{\rm nat}(\min\{t,1/2\})\), the standard binary-entropy continuity bound; \(\phi\) is concave and nondecreasing, so Jensen applies. This gives \(|\mathbb EH(T_\rho g_n)-\mathbb EH(T_\rho g_\ast)|\le h(2^{-n})\).
- \(\ln2-H(m_n)=\psi(m_n)\le m_n^2\ln2\) with \(m_n=2^{1-n}\).
- Finally, \(\psi(\rho r_{m_n})\le\psi(\rho)\), and \(\psi(\rho)-I_{G_n}=\psi(m_n)+[\mathbb EH(T_\rho g_n)-\mathbb EH(T_\rho g_\ast)]\). The lower bound 0 is the accepted theorem. ∎

Exact symmetric computation (`frankl_r2_nearmiss.results.json`, key `Gn`) gives \(\text{gap}\cdot2^n/n\le0.13\) for \(n\le40\) at every tested \(\rho\). For example, at \(n=40\) the gap is \(5.0\times10^{-13}\) at \(\rho=0.5\) and \(2.3\times10^{-12}\) at \(\rho=0.9\).

**Correction: Candidate (C) is vacuous for every family.** At correlation zero both sides of the accepted inequality are zero; at correlation one both equal the entropy of the membership indicator. The accepted upper bound therefore makes the supremum of `I - CK` exactly zero, even without closure or frequency assumptions. Taking the supremum over the open interval would still give zero by endpoint continuity. The near-miss example neither falsifies (C) nor shows that any future lower-bound lemma must jump discontinuously. A continuous function can change sign through zero. What Proposition G actually establishes is uniform convergence to saturation for this explicit sequence, whose density lies above one half and hence outside Karpas's possible-counterexample range.

\(G_n\) has \(\alpha>1/2\), which is inside Karpas's range. For the counterexample range \(\alpha<1/2\), the evidence points the other way. The best nondegenerate near-threshold families (\(\max p_i\le\tfrac12+\tfrac1{2|\mathcal F|}\), \(|\mathcal F|\ge3\), \(\bigcup\mathcal F=[n]\), \(\alpha<1/2\)) are the codimension analogues \(2^{[n-k]}\cup\{[n]\}\). Their ratios \(I/\mathrm{CK}\) increase toward, and stay below, those of the codimension-\(k\) subcube indicator:

| \(\rho\) | 0.1 | 0.3 | 0.5 | 0.7 | 0.9 | 0.99 |
|---|---|---|---|---|---|---|
| subcube, \(k=2\) (\(\alpha=1/4\)) | 0.752 | 0.765 | 0.790 | 0.831 | 0.902 | 0.975 |
| subcube, \(k=3\) | 0.658 | 0.669 | 0.695 | 0.745 | 0.849 | 0.966 |
| best near-threshold, \(n=5\) (\(\{A\subseteq[3]\}\cup\{[5]\}\)) | 0.533 | 0.556 | 0.609 | 0.698 | 0.843 | 0.966 |
| best **exactly tight** (\(e=0\)), \(n=5\), \(|\mathcal F|\ge3\) | 0.013 | 0.107 | 0.266 | 0.469 | 0.738 | 0.948 |

Here \(e=2\max_id_i-|\mathcal F|\), and Frankl holds exactly when \(e\ge0\). The exactly tight maximizer is the block family \(\{\varnothing,\{1\},\{2,..,5\},[5]\}\).

## 8. Exhaustive census and the extremal structure (evidence only)

`frankl_r2_exhaustive.mjs` enumerates every union-closed family on \([n]\), \(n\le5\). It processes sets in increasing integer order and forces \(S\cup T\). The total counts are 4, 14, 122, 4960, 2,771,104; the ground-set-exact counts are 2, 8, 90, 4542, 2,747,402. For each family it computes \(I\), CK, the Hellinger loss, and Proposition D at eight values of \(\rho\).

- **No violations:** \(\max(I-\mathrm{CK})=5.6\times10^{-17}\), which is rounding error. This is a consistency check of the accepted theorem, not new information.
- **Closure is information-neutral at the top.** At \(n=4\), for every weight \(1\le|\mathcal F|\le15\) and every tested \(\rho\), the largest \(I/\mathrm{CK}\) among union-closed families equals that among **all** 65,534 nonconstant Boolean functions. At \(n=5\), for all 31 weights, an **up-set** attains the union-closed maximum, with largest excess \(4.6\times10^{-14}\). Up-sets are union-closed and have every \(p_i\ge1/2\) (Harris–Kleitman), so they satisfy Frankl trivially. The information-richest union-closed families are therefore the ones furthest from counterexamples, not the reverse.
- **The near-threshold range is information-poor and getting poorer.** For \(e\le1\) with \(\alpha<1/2\), the maximum ratio at \(\rho=0.5\) falls from 0.790 (\(n=2\)) through 0.695 and 0.656 to 0.643 (\(n=5\)). These figures include the trivial one-member families.

These are finite floating-point observations. They do not show that a counterexample would be information-poor; nothing finite can.

## 9. What was not done, and why the route should be dropped

- Higher-order coefficients (\(\rho^4\) and beyond) were not bounded in closed form. They mix \(W_2\), the products \(\hat g(i)\hat g(j)\hat g(\{i,j\})\), and \(W_1^2\). No closure-based lower bound on them was found, and the particular use of closure in Proposition D supplies an upper bound.
- The upper-bound direction of Proposition D, Theorem R at \(\rho\to0\), Lemma N at \(\rho\to1\), leave the following unaddressed possibility. A proof by this route would need an **intermediate-\(\rho\), dimension-sensitive lower bound on the information of union-closed families that exploits more than the estimates derived here.** No mechanism for such a bound was identified, and the finite census does not establish its impossibility.
- Recommendation: retire the direct CK/Hellinger route to Frankl. Any future information-theoretic attempt should work with the uniform measure on \(\mathcal F\) itself, as the Gilmer-type entropy methods do (current record about 0.3829, computer-assisted, per §1). This is a research prioritization decision, not a theorem that cube-uniform information functionals cannot prove Frankl.

## Files and reproduction

- `frontier/experiments/frankl_r2_exhaustive.mjs` produces `frankl_r2_exhaustive.results.json` (about 1 minute with `node`).
- `frontier/experiments/frankl_r2_nearmiss.mjs` produces `frankl_r2_nearmiss.results.json` (\(G_n\) exact symmetric gaps, subcube ratios, \(n=5\) union-closed versus up-set comparison, near-threshold maximizers).
- No sources were downloaded. Literature claims rest on the arXiv abstract pages linked in §1, and the theorem statements quoted in §2 were read from the cached pinned TeX files.
