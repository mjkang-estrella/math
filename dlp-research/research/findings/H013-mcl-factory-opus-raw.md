# H013 multiplicative-character learning proposal — unverified raw report

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h013-learning-information-factory-opus-20261008-r1`.
Provider acpRegistry_factory_droid, model claude-opus-5-5. Completed substantive
report, no pending children; distinct from earlier Fable missing-output failures.
No edits or experiments. Root does NOT authorize the proposed multi-curve FFT
sweep or accept runtime/exponent/ceiling claims without independent review.
Complex character evaluation, sampling tails, primitive-root/coset setup and
actual predictor construction require explicit accounting.

**Verified gain: NONE.** One new mechanism survives as a speculative card: H013-MCL, below. I'm not offering more cards because the other ideas I worked through either duplicate existing records or fail on paper. That is a real result, not padding.

The idea I would otherwise have led with, phase estimation against a known frequency using shifted and doubled target views, is already in the records as H004's R2 bridge (see `H004-compact-algebra-disposition.md`). I don't propose it again.

I worked read-only. I made no edits, ran no experiments, launched no subagents and did not read any other H013 proposal. Outside the repository I checked two sources: the Beullens–Beyne–Udovenko–Vitto abstract (ePrint 2019/1357), and a search result confirming Cheon's paper (J. Cryptology 2010) and its Brown–Gallant reference.

## Why the space is narrow

A public coordinate predictor $f$ can feed into ECDLP work through exact self-reducibility only via the computable affine maps $R \mapsto [u]R + [t]G$. On functions of the scalar, these maps act as the affine group $\mathrm{Aff}(\mathbb Z_q)$. Every subgroup of that group either contains all translations or fixes a point. So, by my derivation, there are three exploitable kinds of exact structure:

1. **Additive characters $e(bk/q)$.** These are H003, H004's R2 bridge and the parity work, already closed for bounded-degree features by the Weil-type bounds.
2. **Dilation-invariant classes.** This is A3, which needs exact class labels and was closed for the listed constructions.
3. **Multiplicative characters of the discrete log, $\chi(\log_G R)$, possibly about a shifted center.** The records do not cover this kind. The Weil and Kohel–Shparlinski bounds used so far say nothing about it, because Gauss sums make $\chi$'s additive spectrum flat. That gap is where the card comes from.

## Card H013-MCL: predict a multiplicative character of the log, then search one coset

**Operation.** Choose $m \mid q-1$ and a character $\chi:\mathbb Z_q^\*\to\mu_m$, computed as $c^{(q-1)/m} \bmod q$. Define
$$c_\chi(f)=\mathbb E_{n\in\mathbb Z_q^\*}\, f([n]G)\,\overline{\chi(n)}.$$

- **Exact identity:** for $Q=[k]G$ with $k\neq 0$, $\mathbb E_c\, f([c]Q)\,\overline{\chi(c)}=\chi(k)\,c_\chi(f)$, because $c\mapsto ck$ is a bijection.
- **Calibration:** estimate $c_\chi$ on $G$ itself (the case $k=1$). This needs no labels.
- **Target estimate:** estimate $\chi(k)c_\chi$ from pairwise-independent samples $c_i=r+is$. Each point $[c_i]Q=[r]Q+i[s]Q$ costs one addition. Take $\chi(k)$ as the nearest $m$-th root of unity.
- **Coset search:** then $k=k_0\lambda^i$, where $\lambda$ generates $U=\ker\chi$ and $h=|U|=(q-1)/m$. Run BSGS over $i$: baby steps $[\lambda^a]G$ use a fixed-base comb, and giant steps $[\lambda^{-bB}k_0^{-1}]Q$ use a comb built for $Q$.
- **Recovery and verification:** a match gives $k=k_0\lambda^{a+bB}$; verify $[k]G=Q$. If the class estimate was wrong, the full sweep fails, which is detected, and we re-estimate with fresh samples or try the next most likely class.
- **Negation:** when $-1\in U$, x-only storage keeps the negation-map factor of $\sqrt2$.

**Complete work, in group-addition equivalents measured on the same machine.**
$$W=W_{\rm sel}+W_{\rm cal}+N_t(1+C_f+C_\chi)+2\sqrt h\,(\lceil\log_2 q\rceil/w+1)+\text{comb tables}+W_{\rm ver}$$

- $N_t\approx \kappa\,m^2\ln(1/\delta)/(\pi^2|c_\chi|^2)$, or a sum over prime-order characters if $m$ is factored.
- $C_\chi$ is a modular exponentiation, roughly 20–30 addition-equivalents. It must be measured, not assumed.
- Memory is $\sqrt h$ points, or $O(1)$ if a rho-style walk on the coset is used instead (same per-step scalar cost).
- $W_{\rm sel}$ covers training or search, validation and model storage. There is no rank or linear-algebra cost.

**Expected gain against rho with negation ($0.886\sqrt q$).** Two conditions are needed:
- The coset step beats rho only if $m\gtrsim(2.3\log_2 q/w)^2$. The gain is then at most $\sqrt m/(2.3\log_2 q/w)$.
- The target estimate stays below the coset cost only if $|c_\chi|\gtrsim m^{5/4}q^{-1/4}\sqrt{\kappa(1+C)w/(2\pi^2\log_2 q)}$.

For example, at 256 bits with $w=8$ and a divisor $m\approx2^{20}$ of $q-1$ (not always available), the gain is about 14× provided $|c_\chi|\gtrsim2^{-38}$. A random-like predictor has $|c_\chi|\approx2^{-124}$. An exponent-level gain would need divisors of size $m=q^{\delta}$. Whether usable divisors exist depends on the curve. This is not a restriction on the secret.

**Structural facts.** These are my derivations and need independent review.

- **Exact null control.** If $f$ depends only on $x$ and $\chi(-1)=-1$ (that is, $(q-1)/m$ is odd), then $c_\chi=0$ exactly. This mirrors the existing L2 negation null.
- **Base invariance.** $c_\chi(f,[u]G)=\chi(u)\,c_\chi(f,G)$. For a predictor that ignores the base, the magnitude is a property of the curve. The random-base averaging arguments (Takhanov, Parseval) cannot remove it, unlike the additive case.
- **Unconditional ceiling I derived.** Write $S=\sum_n\chi(n)\psi(x(nG))$. Averaging $S=\chi(v)\sum_n\chi(n)F(nv)$ over $v\le V$, applying Cauchy–Schwarz, and applying the Kohel–Shparlinski bound to $x\circ[v]-x\circ[v']$ (pole degree at most $2v^2+2v'^2$) gives:
  - $|S|^2\le q^2/V+8qV^2\sqrt p$;
  - at $V\approx q^{1/6}/2$, $|c_\chi|\lesssim 2q^{-1/12}$, scaled by the Fourier $\ell^1$ norm for general $\Phi\circ x$.

  This bound does not exclude the required correlation size. Bhakta (2025) and Shparlinski–Stange study related but different sums: Dirichlet twists over the index of division polynomials. I know them only through the raw H008 Grok report and did not verify them.
- **Perfect order-2 oracle gives nothing.** A perfect $m=2$ oracle (the Legendre symbol of the log) yields chosen-shift values $\chi(k+t)$ through $[c](Q+[t]G)$. That is exactly the Legendre PRF. Beullens–Beyne–Udovenko–Vitto need $O(q\log^2 q/M^2)$ symbol evaluations for $M\le(q\log^2q)^{1/4}$ queries, so at least about $\sqrt q\log q$. Small $m$ is useless even with a perfect predictor.

**Training and certification route.** A local-to-global certificate holds. Let $\delta_S^2=\mathbb E_{u\in S,R}|f([u]R)-\chi(u)f(R)|^2$ be the equivariance defect over a multiplier set $S$, and let $\lambda_S=\max_{\eta\ne1}\mathrm{Re}\,\mathbb E_{u\in S}\eta(u)$. Then
$$|c_\chi|^2\ge\|f\|^2-\delta_S^2/(2(1-\lambda_S)).$$
With a random $S$ of size $O(\log q)$, Alon–Roichman makes $\lambda_S\le1/2$ likely. This gives a label-free training objective that costs one scalar multiplication per check.

For bounded-degree $f$ with small $u$, the Weil bound makes the defect nearly maximal, so the route only matters for non-algebraic learned $f$. Out-of-sample validity is clean: calibration and use both draw $n$ uniformly from $\mathbb Z_q^\*$, so there is no distribution shift. The single quantity that matters, $c_\chi$, is estimated on fresh samples.

**Prior art and how this differs.**
- Cheon, "Discrete Logarithm Problems with Auxiliary Inputs" (J. Cryptology 2010), and Brown–Gallant (ePrint 2004/306): known source of the coset BSGS step.
- Damgård (CRYPTO 1988) and Beullens–Beyne–Udovenko–Vitto (ToSC 2020): known source of the power-residue PRF back end.
- Akavia–Goldwasser–Safra: their method covers concentrated predicates only, and $\chi\circ\log$ is not concentrated.
- H003 A3 is the exact dual (invariants of a small subgroup), and H004's R2 bridge is the additive counterpart.
- What is new here is the information source (statistical correlation of a public predictor with $\chi\circ\log$), plus the null, base-invariance and ceiling facts above. I have not established novelty.

**Main unsupported assumption.** Some polylog-cost predictor has $|c_\chi|$ near $m^{5/4}q^{-1/4}$ for a usable $m\mid q-1$. I see no structural candidate. The natural analytic one, the division-polynomial and EDS dilation cocycle, reduces to bounded-degree characters that fall under the ceiling. My prior that this assumption holds is very low.

**Cheapest decisive falsifier.**
- **Setup.** Use frozen, pre-declared feature families: x-only, y-dependent, Legendre of $(x+c)$, integer-representation bits, EDS/φ characters, multi-view products with large multipliers, and learned models trained on separate curves. Use at least 3 ordinary prime-order curves for each $q\approx2^{12},2^{14},2^{16},2^{18}$ (within the 1M-event cap).
- **Computation.** Enumerate $F(n)=f(nG)$ exhaustively, reindex by a primitive root, and take one FFT of length $q-1$ to get every $c_\chi$. The same table also gives the additive spectrum.
- **Controls.**
  - Exact zero for odd $\chi$ on x-only features.
  - A planted $\mathrm{Re}\,\chi_0(\log R)$ control, which must return $1/2$.
  - Permuted-$F$ empirical null.
  - Table-indicator sanity check.
- **Decision.** Fit the decay exponent $\beta$ of $\max|c_\chi|$ for each fixed small character order. Reject the family if $\beta\ge0.4$ with a confidence interval that excludes $0.25$. Escalate to analytic review, not a claim, if $\beta<0.35$ on held-out curves.

## Closed or not proposed

- **Polynomial phases of the log.** By van der Corput plus Weil on $f_h(R)=f(R+hG)\bar f(R)$:
  $$|\langle F,e((an^2+bn)/q)\rangle|\le\big(1/q+\max_{h\ne0}|\widehat{f_h}(2ah)|\big)^{1/2}\lesssim q^{-1/4}.$$
  Every way to exploit it either passes through $\widehat{f_h}$, which is bounded by about $q^{-1/2}$, or needs an unknown-frequency search costing at least $\varepsilon^{-2}\approx\sqrt q$. No gain for bounded-degree features. Large-multiplier products are not covered.
- **Base-independent predictors at a designer-fixed frequency $b$.** By Parseval over generators, $\Pr_G[|\hat F_G(b)|\ge\varepsilon]\le1/((q-1)\varepsilon^2)$. This holds exactly for any $f$.
- **Table-set sanity check for R2.** A $t$-point table predictor costs about $q/t$, a time-memory tradeoff of $TM=q$. That is worse than Bernstein–Lange precomputation, so any audit pipeline must reproduce this result.
- **Unknown-frequency calibration (unreviewed side note).** Autocorrelation phase estimation on the base at shifts $2^j$ costs about $\varepsilon^{-4}\log q$, but only if one frequency dominates. It refines R2's discovery cost $S(\varepsilon)$ and is not a mechanism.
- **Dropped as duplicates or known to fail:** Bleichenbacher-style filtered bias (the same additive Fourier object), learned walk and proximity priors, searching the isogeny class or other curve models for a better predictor, and learned compression of distinguished-point tables.

**Next decisive step:** an independent review of the base-invariance, odd-null and $q^{-1/12}$ derivations, then the frozen multiplicative-spectrum audit above. Do not run any training before that audit.
