# Unaccepted H002 delegated report: eds-math-review

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h002-eds-math-review-20261008-r1`.
Provider/model: `claudeAgent/claude-opus-5-5`; status completed.

This report is retained for process evidence, not automatically adopted. Primary
formula checks, cost assumptions and universal claims require coordinator
qualification. In particular the EDS index1 identity is under active correction;
no experiment should rely on it before resolution. See the coordinator disposition.

I reviewed A1 only. I read Lauter–Stange 2008, Shparlinski–Stange 2012 and Bhakta–Shparlinski 2025 in full, and only the publisher's page for Bhakta 2026. I made no edits and ran no experiments; the extracted PDFs are in `/tmp/a1rev/`.

**Bottom line:** every odd-product statistic in A1 reduces exactly to one question: can a computable function of Q predict the parity (least significant bit) of k? That collapse is a theorem. Lauter–Stange already ask this question, and the specific statistics A1 needs are, in the language of the newer papers, still-unbounded character correlations at fixed shifts. No published bound rules out the bias A1 needs, but the card's cost model, its negative control and its "addition-chain offsets" all need correcting.

## Theorem-level facts (from Lauter–Stange eq. (4), Thm 6, Prop 2–4, §8)

Setup: p > 9, ordinary curve, #E = m an odd prime > 3 and m ≠ p (so not anomalous). Since m > (p−1)/2, gcd(m, p−1) = 1 holds automatically. Write W(n) = ψ_n(P), χ for the Legendre symbol, and c = χ(φ(P)).

1. **One identity carries everything.** For every integer n not divisible by m, `χ(W(n)) = χ(φ(nP)) · c^(n−1)`. This uses n²−1 ≡ n−1 (mod 2).
   - c itself is computable: it equals χ(W(p−1)·W(p−1+m)), because m⁻² mod (p−1) is odd.
2. **If c = +1, there is nothing to find.** Every product, odd or even, is a function of Q alone, so no statistic contains information about k.
   - **If c = −1:** ∏_{a∈A} s_{k+a} = (known from Q) · (−1)^{|A|(k−1)+Σa}. Products of even length are fully computable, which is stronger than "can't orient". Products of odd length equal a known value times (−1)^k.
   - The "relative window" is exactly Lauter–Stange's S(n) from Prop 4. The orientation bit is exactly the parity of the integer lift k. The EDS residue structure hides no other bit.
3. **Residue-to-parity condition.** By Lauter–Stange Prop 3, an index polynomial p_i(k) carries the bit only if t(x) = Σ e_i·p_i(x)² is non-constant mod 2.
   - Terms like W(2k+j) are fully computable from 2Q+jP, so addition-chain or CM-style offsets with an even coefficient on k add known side information, never the hidden bit.
   - The cheap identity W(k+1)W(k−1)/W(k)² = x(P) − x(Q) (Lemma 1) links only indices of the same parity. Linking indices an odd distance apart needs one φ evaluation each, costing about two EDS ladders of length ~log p.
4. **Index wraparound.** With c = −1, χ(W(n+m)) = −χ(W(n)), which matches the period-2m result (Shparlinski–Stange Lemma 3).
   - Lifts k and k+m of the same Q have opposite true statistics. So "persistent bias" only makes sense for a fixed lift, namely the minimal multiplier in [0, m).
   - Any odd statistic summed over the full 2m period is exactly 0.
   - Q + aP = O means k ≡ −a, which reveals k directly; handle that case separately.
5. **Making c = −1.**
   - For p ≡ 3 (mod 4): φ(−P) = −φ(P), so exactly one of ±P works, at no cost.
   - For p ≡ 1 (mod 4), Lauter–Stange call this "less clear". It follows from Shparlinski–Stange Cor. 7 that for large enough p, about half of all multiples uP have χ(φ(uP)) = −1, so a random u works. This is my inference; the threshold on p is not explicit. Recovering the scalar relative to uP gives k·u⁻¹, from which k follows.

## Exact correspondence with the literature (c = −1)

- **Single-term predictor χ(φ(Q))**, used to predict the parity of k: its correlation is −(1/m)·S_P(m−1).
  - S_P is the plain EDS character sum, i.e. exactly Lauter–Stange's "residue bias" question.
  - Shparlinski–Stange Cor. 7 bounds it by O(p^{11/12}(log p)^{4/3}), so the advantage is at most about p^{−1/12}. That does not rule out ε ≳ p^{−1/4}.
- **Odd predictor ∏_{a∈A} χ(φ(Q+aP)) with |A| = 3:** its correlation is ±(1/m)·Σ_{k<m} χ(W(k))χ(W(k+a))χ(W(k+b)). This is a fixed-shift three-point correlation, the m = 3 case of Bhakta–Shparlinski's V_m.
  - **Is this family already covered? No.** Bhakta–Shparlinski Thm 1.2 bounds these sums only on average over shifts in [1, H]^m, and only for large H. With N ≈ m, bound (1.4) needs roughly H > p^{5/6}.
  - Their Question 1.1, the fixed-shift o(N) bound, is stated as open even for two points.
  - So a sparse, arithmetically selected set of (a, b) is neither excluded nor known to work.
- **Bhakta 2026** (Canad. Math. Bull., 25 March 2026; I read only the publisher's page): it covers twists by multiplicative functions. (−1)^{n+1} is multiplicative, so it applies to the twisted single-term sum. Its gain is only about a log factor, so it is irrelevant at the ε ≈ p^{−1/4} scale.
- **Hard-core-bit prior art (missing from the card).** The parity of the discrete log in a prime-order group is a hard-core bit: Håstad–Näslund, and Morillo–Ràfols PKC 2009 via list decoding.
  - Their generic reduction turns an average-case advantage ε into a full discrete log in poly(log n, 1/ε) time. I did not verify the exponent of 1/ε. With cost ε^{−c}, A1 needs ε ≥ m^{−1/(2c)}; the card's m^{−1/4} assumes c = 2.
  - Shoup's generic bound does not cover φ, because φ uses coordinates.

## Prior objections, re-assessed

- **"Bias/pattern search already known":** confirmed and sharpened. Lauter–Stange §8 propose it, and Shparlinski–Stange §2 restate it. The odd-product family is Lauter–Stange Prop 3 with odd N. Novelty, if any, is limited to the particular predicate and the fixed-shift regime.
- **"Even products can't orient":** true, and stronger: they are computable from Q. That makes them unsuitable as a negative control (point 3 under "Required changes").
- **"ε⁻² presumes independence":** confirmed, and worse than stated.
  - The statistic is a deterministic function of Q, so repeated window samples are not independent votes on that instance. Averaging over a linear window adds no correlation beyond a single triple, apart from O(L²) edge terms from wraparound.
  - In Lauter–Stange Prop 2, one wrong parity bit corrupts every later halving step.
  - A sound cost model needs average-case advantage plus a randomized self-reduction. That reduction must handle wraparound, as in the Alexi–Chor–Goldreich–Schnorr / Morillo–Ràfols constructions.
- **"Finite failure ≠ universal":** agreed. Equally, a finite success does not establish an asymptotic exponent.

## Required changes / prerequisites for a bounded orientation/recovery test

1. Restate A1 as: "a computable predicate G_A(Q) = ∏χ(φ(Q+aP)) predicts the parity of the minimal multiplier with advantage ε_A(E, P)". Cite Lauter–Stange Prop 2–4, Shparlinski–Stange Cor. 7, Bhakta–Shparlinski Thm 1.2 / Question 1.1, and Morillo–Ràfols 2009.
2. Pre-test checks, which are deterministic and test the implementation, not the hypothesis:
   - c is computed and verified.
   - Identity 1 holds for all n on tiny curves.
   - Even products match their values computed from Q.
3. **Statistic:** compute ε_A = (1/m)·Σ_{k=0}^{m−1} (−1)^k G_A(kP) exactly by full enumeration, for a family A fixed in advance.
   - Use replacement negative controls: labels shuffled against the parity, or random ±1 predicates. Do not use even products.
   - Correct for multiple testing across all offsets and generators tried.
4. **Null and success thresholds:**
   - Under a random-like model |ε| ≈ m^{−1/2}, which loses to rho.
   - A1 needs |ε| ≳ m^{−1/4} times polylog, and both the sign and the choice of A must be predictable from public data. If the sign has to be learned per curve, that is a Θ(m) table, which is the card's own unsupported assumption.
   - Report how max_A |ε_A| scales with m across curves, not individual hits.
5. Recovery work should count all of: φ evaluations (two ladders each), the randomized self-reduction overhead, error correction across about log₂ m stages, the generator search, and failed runs. Compare against √(m/g0).

**Falsifier:** if |ε_A| for a predeclared A stays within a constant of m^{−1/2} across growing m and fresh curves, that family is rejected. It does not reject the broader mechanism.

**Unresolved:**
- The exact 1/ε exponent in the hard-core reductions.
- Whether φ has any low-complexity structure; Weil-type bounds fail because φ has degree about p².
- An explicit p threshold for the p ≡ 1 (mod 4) existence argument.
- Bhakta 2026's full text, which I did not read.

Sources:
- [Lauter–Stange arXiv:0803.0728](https://arxiv.org/pdf/0803.0728)
- [Shparlinski–Stange arXiv:0912.5246](https://arxiv.org/abs/0912.5246)
- [Bhakta–Shparlinski arXiv:2507.09271](https://arxiv.org/abs/2507.09271)
- [Bhakta 2026, CMB](https://www.cambridge.org/core/product/identifier/S000843952610191X/type/journal_article)
- [Morillo–Ràfols PKC 2009](https://repositori.upf.edu/items/9c4ef9c3-760c-4f43-9ea6-f40f218e794b)
- [AGS / all-bits talk summary](https://clementj01.users.greyc.fr/semalgo/2009/05/05/talk.html)
