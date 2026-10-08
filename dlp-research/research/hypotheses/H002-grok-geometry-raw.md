# Unaccepted independent geometry proposals: Grok4.7

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h002-geometry-grok-20261008-r1`; status completed.
This is an initial proposal report, not accepted proof, novelty or cost evidence.
All speculative bridges and negative exclusions require scoped review.

Ordinary prime-field prime-order ECDLP, full scalar, is the target. The working reference is negation-aware Pollard rho, about \(\sqrt{\pi q/4}\) group operations, and, when many targets share a curve, generic batching \(\widetilde O(\sqrt{qU})\) or generic preprocessing of size \(q^{1/3}\) with online cost \(q^{1/3}\). The four mechanisms below are coordinate-aware collision or representation geometries. None is a signed-BSGS or delayed-canonicalization variant.

## 1. Orbit-segment vanishing circuit

- **Regime:** Single-target if the circuit is built and evaluated inside the one-shot budget. Fixed-base multi-target if the same circuit is reused. Not hidden advice: build cost is counted.
- **Mechanism:** For step \(T\), let \(F_{G,T}(X)=\prod_{j<T}(X-x([j]G))\). Then \(k=iT\pm j\) iff \(x(Q-[iT]G)\) is a root (the sign is a \(y\)-check). Expanded \(F\) plus multipoint evaluation is BSGS and ties rho at \(T\sim\sqrt q\). The proposed object is a uniform arithmetic circuit for the vanishing test \(F_{G,T}(\alpha)=0\), built from power sums \(\pi_m(T)=\sum_{j<T}x([j]G)^m\) and Newton–Girard, not from fitting coefficients.
- **Bridge:** One-shot cost \(C_{\mathrm{build}}(T)+(q/T)C_{\mathrm{eval}}(T)\). This is \(o(\sqrt q)\) only if \(C_{\mathrm{eval}}(T)<T\,q^{-1/2}\) at the \(T\) used. Polylog evaluation would allow \(T=q^{\alpha}\) with \(\alpha>1/2\) and time \(q^{1-\alpha}\mathrm{polylog}\). Reuse across \(U\) targets costs \(C_{\mathrm{build}}+U(q/T)C_{\mathrm{eval}}\), against \(\widetilde O(\sqrt{qU})\).
- **Applicability:** Any ordinary prime-order curve. No endomorphism, smoothness of \(p-1\), or short scalar.
- **Costs:** Memory is circuit size, not a \(T\)-table, if compression is real. Failed giant steps are the \((q/T)\) term. A recurrence of order \(r\) found by Berlekamp–Massey needs \(2r\) coefficients; computing those naively already costs \(\Theta(T)\) and does not beat rho. Only a uniform formula does.
- **Prior art:** Division polynomials compress torsion orbits, a different set. Lauter–Stange show elliptic-divisibility index recovery is tightly equivalent to ECDLP, so term-by-term EDS solving is not a new exponent. Miller evaluates one multiple, not the segment product. Galbraith–Gaudry treat expanded BSGS and rho as the generic reference.
- **Unsupported assumption:** A uniform circuit with \(C_{\mathrm{build}}+(q/T)C_{\mathrm{eval}}=o(\sqrt q)\). Zeta-telescoping in characteristic zero does not supply it: \(\zeta\) is not rational, and its value is essentially the discrete log.
- **Falsifier:** On a 20–28 bit prime-order curve, expand \(F\) for \(T=2^{8},2^{10},2^{12}\). If coefficient linear complexity is \(T(1-o(1))\) and symbolic search finds no rational expression in \(\bigl(x(G),y(G),x([T]G),y([T]G),\alpha\bigr)\) whose circuit beats the threshold above, the exponent claim is dead.

## 2. Fourier collision on a coordinate predicate

- **Regime:** Single-target. Multi-target only shares samples already computed; no extra asymptotic saving is claimed.
- **Mechanism:** Sample \((r_s,\eta(x([r_s]Q)))\) with a discontinuous predicate \(\eta\) (integer MSB of \(x\), or a short-interval indicator). Feed the samples to Bleichenbacher’s Fourier stage, which peels candidate bits of \(k\) when \(\eta(x([m]G))\) correlates with a character \(m\mapsto e^{2\pi i am/q}\).
- **Bridge:** Sample bias \(\beta\) needs \(S\sim\beta^{-2}\) samples. A group operation per sample beats \(\sqrt q\) only for \(\beta\gg q^{-1/4}\), i.e. some coefficient satisfies \(\bigl|\sum_{m<q}\eta(x([m]G))e^{2\pi i am/q}\bigr|\gg q^{3/4}\).
- **Applicability:** General ordinary prime-order curves. This is not scalar-MSB HNP and not nonce leakage.
- **Costs:** \(S\) curve operations, an FFT of size about \(S\), and restarts at each bit stage. Memory is the FFT buffer. No curve preprocessing.
- **Prior art:** Bleichenbacher’s FFT solves hidden-number instances with biased scalar bits. Boneh–Venkatesan is the same shape. Weil bounds give square-root cancellation for low-degree rational functions of \((x([m]G),y([m]G))\); Shparlinski-type bounds cover many complete sums. They do not automatically price this incomplete discontinuous predicate. Wagner’s \(k\)-tree does not apply: a prime-order group has no small quotient to match on.
- **Unsupported assumption:** A spike larger than \(q^{3/4}\) at a frequency the FFT can isolate. Square-root cancellation would leave \(S\gg\sqrt q\).
- **Falsifier:** On a prime-order curve with \(q\approx 2^{16}\), FFT \(\eta(x([m]G))\) and compare the largest nontrivial coefficient with \(q^{3/4}\). An \(O(q^{1/2}\log q)\) maximum kills the gain.

## 3. Dual character-sum point decomposition

- **Regime:** Single-target. Setup depends on \(p\), not on \(Q\), so a later card can amortize it. The test itself is the proposed single-target engine.
- **Mechanism:** Factor base \(\mathcal F=\{R\in E(\mathbb F_p):x(R)\in V\}\) with \(V\subset\mathbb F_p^\times\) a subgroup of size \(S\approx p^{1/m}\), \(m\ge 3\), as in Petit–Kosters–Messeng. Instead of Gröbner elimination of \(S_{m+1}(x_1,\ldots,x_m,x(R))=0\), expand \(1_V\) in the character group of \(\mathbb F_p^\times\) (length \((p-1)/S\)) and evaluate the resulting exponential sums of the Semaev polynomial.
- **Bridge:** One decomposability test costs \(\bigl((p-1)/S\bigr)^{m}\) sums if each sum is polynomial-time (point counting on an auxiliary curve, or a closed Weil sum). Walk random \(R=[a]P+[b]Q\) until one decomposes. With \(S\sim p^{1/m}\), random \(m\)-sums hit about once per \(m!\) trials only if those dual sums are sparse. Dense dual sums cost \(p^{m(1-1/m)}=p^{m-1}\), far above rho.
- **Applicability:** Needs a divisor of \(p-1\) near \(p^{1/m}\). A large prime factor of \(p-1\) removes the subgroup. A non-subgroup Petit map \(L\) needs some other short dual before the same count applies. Not a special-curve hypothesis.
- **Costs:** Dual-sum table is field-dependent preprocessing. Failed \(R\) trials dominate if the dual is dense. Memory is one sum per surviving dual character. No linear algebra if a single Amadori–Pintore–Sala relation is enough.
- **Prior art:** Petit–Kosters–Messeng define this factor base and stop at Gröbner. Amadori–Pintore–Sala reduce to one relation. McGuire–Mueller drop Gröbner for direct search and still lose to rho. Semaev’s small-\(x\) base has no short character dual. The proposed replacement is the dual-sum evaluation, not another solver for the same system.
- **Unsupported assumption:** After symmetry, only \(p^{o(1)}\) dual sums are nonzero and each is computable in \(\mathrm{poly}(m,\log p)\).
- **Falsifier:** For \(m=3\) and a prime with a suitable \(S\), compute the dual sums directly for several random targets. A positive-density set of nonzero duals restores a \(p^{\Theta(1)}\) test and kills the exponent.

## 4. Reusable factor-base matrix against generic batching

- **Regime:** Amortized multi-target only. One full scalar on a fresh curve does not beat rho at published prime-field PDP costs.
- **Mechanism:** Preprocess, for fixed \((E,G)\), a factor base and enough Semaev relations to know discrete logs of base points (Amadori–Pintore–Sala: one nontrivial relation can finish a single target once a decomposition exists). Each new \(Q\) is only a point-decomposition query. Relations are curve data, not a table of multiples of \(G\).
- **Bridge:** Cost \(R_{\mathrm{pre}}+U\,D_{\mathrm{PDP}}\). Generic online batching is \(\widetilde O(\sqrt{qU})\) (Kuhn–Struik, Fouque–Joux–Mavromati; Yun’s matching lower bound is generic-group). Generic preprocessing is about \(q^{2/3}\) work, \(q^{1/3}\) advice, then \(q^{1/3}\) online per target (Mihalcik, Bernstein–Lange, Lee–Cheon–Hong; Corrigan-Gibbs–Kogan). Algebraic amortization wins in the large-\(U\) limit only for \(D_{\mathrm{PDP}}=o(q^{1/3})\) and \(R_{\mathrm{pre}}=o(U q^{1/3})\).
- **Applicability:** Same curve and generator, many full scalars. Independent curves do not share the matrix.
- **Costs:** \(R_{\mathrm{pre}}\) includes failed decompositions, memory for the factor base, and linear algebra. Per-target failures multiply \(D_{\mathrm{PDP}}\). Using card 3’s test as the PDP is the only gain path identified here; direct search as in McGuire–Mueller is \(O(p)\)-type and loses for every practical \(U\).
- **Prior art:** The one-relation and no-Gröbner algorithms already exist and are reported slower than rho for one target. The distinction is the comparison with the generic preprocessing line \(q^{1/3}\), which those papers do not claim to cross.
- **Unsupported assumption:** A prime-field PDP below \(q^{1/3}\) after preprocessing that itself stays under the generic preprocess budget.
- **Falsifier:** Ignore relation-matrix setup and time one decomposition at the best published parameters on a synthetic prime-field curve. If that time already exceeds \(q^{1/3}\) group operations, no \(U\) saves the method.

## Ranking

1. **Fourier coordinate collision.** Cheapest decisive check, full applicability, and a concrete threshold \(q^{3/4}\).
2. **Orbit-segment circuit.** Largest one-shot upside and full applicability. The Berlekamp–Massey check is small; a positive result still has to be a uniform circuit, not an advice string.
3. **Dual character-sum PDP.** Real exponent only if the dual is sparse, and only on primes with a subgroup near \(p^{1/m}\).
4. **Reusable relation matrix.** Multi-target only, and only if a PDP from card 3 actually lands under \(q^{1/3}\).

Not carded, to avoid known walls rather than as a general impossibility claim: exact Wagner merging inside \(E(\mathbb F_p)\) (no small quotient), horizontal isogeny-path collisions (the transported relation is a tautology for the same \(k\)), and sum/difference rho steps (constant-factor search-space claims already in the Wang–Zhang line, not a new exponent).
