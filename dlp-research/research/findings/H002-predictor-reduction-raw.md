# Unaccepted raw delegated review

Retained verbatim for provenance; coordinator dispositions supersede overclaims. This is not a verified ECDLP result.

# Review of L1/L2: predicting a scalar predicate and reconstructing the full scalar

## Bottom line

1. **The reconstruction theorem exists, but only with a large polynomial cost.** For a prime-order group, a stateless predictor with average advantage ε over a uniform scalar does yield a correct full ECDLP solver. The only exponent of 1/ε I could verify from a primary source is about ε⁻¹¹ (up to polylog factors). No source I verified gives a near-ε⁻² reconstruction, and any black-box reconstruction needs at least Ω(n/ε²) queries. **The missing theorem** is a reconstruction with ε^(−c)·poly(n) queries for c well below 11, ideally c ≈ 2.
2. **x-only features have exactly zero advantage on LSB and half(k).** Both predicates are odd under k → −k, and x(c·Q) = x(−c·Q). This makes Fable's L2 grammar (Legendre symbols and residues of x(c_iQ)) provably null against its own target predicates. A pipeline that reports any signal from it has a bug.
3. **Takhanov et al. cover more than the raw report says, but less than a pruning theorem would need.** Their result does cover the "multi-view" features, which removes the raw report's novelty claim (a). Its intermediate inequality also gives an unconditional limit on predictors that do not depend on the base P. It does not exclude predictors that use P, non-gradient search for a fixed P, or work on the order of 2^(n/6) to 2^(n/2).
4. **I agree with coordinator corrections 1–6** in H002-learning-cards-and-disposition.md and refine 3 and 6 below. One sentence in the disposition should be updated: the theorem hypotheses are now inspected (§3).

## 1. Verified reconstruction statements

**Håstad–Näslund, J. ACM 2004** ([author PDF](https://www.csc.kth.se/~johanh/hnrsaacm.pdf))

- **Def 4.1:** the predictor is a pptm P_x with Pr[P_x(a) = bit_i([ax]_N)] ≥ (1+ε)/2. The probability is over uniform a ∈ Z_N and the predictor's coins.
- **Thm 4.2 / 4.4:** in polynomial time, with probability at least 1/2, the reduction outputs a list containing x or a nontrivial factor of N. Thm 4.4 covers biased positions using the Schrift–Shamir advantage (Def 4.3).
- **Prime N:** there is no nontrivial factor, so the reduction must output the list. This is my direct reading of the theorem, not a separate statement in the paper.
- **Abstract:** the results "do not rely on group representation" and therefore apply to general cyclic groups.
- **ECDLP instantiation:** P_x(a) = B(a·Q).
- **Lemma 5.3:** each estimate uses m = c·λ(J)⁻¹ε⁻²K pairwise-independent queries. The total exponent of 1/ε, including the guessing of the initial information r·x and s·x, is only stated as "polynomial".

**Akavia–Goldwasser–Safra, FOCS 2003** ([PDF](https://www.cs.tau.ac.il/~safra/PapersAndTalks/hardcore.pdf))

- **§1.1.1:** segment predicates are hard-core for ECL, i.e. x·Q with Q of high order. half(k) is a basic 2-segment predicate. Section 5.1.1 shows lsb(x) = msb(x/2) for odd N.
- **Def 10 and Lemmas 2–3:** the advantage is the average over instances and the predictor's coins.
- **Footnote 4:** for a randomized predictor, take a majority over repeated calls so that the corrupted codeword is well-defined.
- **Thm 6:** heavy Fourier coefficients are found in time Õ(log N · ln²(1/δ) / τ^5.5). The Õ hides constants and polylog factors.
- **Converting τ to ε (my derivation):** the msb code's Fourier mass gives τ ≈ ε²/polylog. The resulting cost is roughly n·ε⁻¹¹ queries, and AGS's own generic choice of τ is worse.

**Exact conditions under which the reconstruction applies**

- **Advantage:** Pr over uniform k and coins that B(kP) = pred(k) must be at least ½ + ε for the fixed (E, P). For biased predicates, measure it against the majority value.
- **No loss of instances in prime order:** for any k ≠ 0, the product j·k is uniform when j is uniform. So every instance sees the same agreement, and nothing is lost to a "non-negligible fraction of instances".
- **Errors:** errors may be arbitrary, as long as the predictor is a fixed function or has independent coins. No independence of errors is assumed.
- **Queries:** queries are chosen multipliers (pairwise-independent r + js in HN, structured random samples in AGS). The predictor must be stateless and must not adapt to the history of queries.
- **What breaks the theorem:**
  - advantage that holds only for non-uniform scalars;
  - advantage measured on other curves or other bases;
  - stateful or query-detecting predictors.
- **Final step:** verify every candidate in the list by scalar multiplication.

**Not inspected:**

- **Kaliski, CRYPTO '86:** I saw it only as AGS reference [13].
- **Fischlin–Schnorr, J. Cryptol. 13:221–244:** I read the abstract only and verified no exponent from it.
- **Blum–Micali:** works in Z_p* using square roots, so it is not the right citation for elliptic curves.
- **The raw report's "O(log N/ε²) predictor calls":** no source I checked supports it. That rate is exactly the information-theoretic necessary bound, not a proven upper bound.
- **Boneh–Shparlinski (ECDH bit security):** not substituted. It concerns bits of the shared-secret coordinates, not bits of the scalar.

## 2. What advantage would justify a solver, and at what total cost

**Necessary condition (any black-box reconstruction, my derivation)**

- Use an oracle equal to the predicate XOR a fixed random noise function. Each new query point leaves at most the binary symmetric channel capacity, 1 − H(½+ε) ≈ 2.885·ε², bits of information about k.
- Fano's inequality then gives Q ≥ ((1−P_e)·n − 1) / (2.885·ε²) queries.
- Let c be the cost per query in group additions: predictor evaluation, including all views, plus forming the query point (at least 1 addition). Beating rho with the negation map, √(πN/4) ≈ 0.886·2^(n/2) additions, then requires:

$$\varepsilon \ge 0.625\sqrt{nc}\;2^{-n/4}$$

| n | ε* for c = 1 | ε* for c = 100 |
|---|---|---|
| 32 | 0.0138 | 0.138 |
| 40 | 0.0039 | 0.039 |
| 48 | 0.0011 | 0.011 |
| 64 | 7.6e-5 | 7.6e-4 |
| 256 | about 2^-60.7 | about 2^-57.4 |

**Sufficient condition (proven route, AGS)**

- Write ε = 2^(−βn). The proven cost is about 2^(11βn + o(n)), so the exponent beats rho only if β < 1/22.
- Because Õ hides constants, there is no finite-n guarantee.
- At n = 40, ignoring constants, the AGS route needs ε of roughly 0.4, which is close to a perfect predictor.

**Missing theorem**

- For 1/22 ≤ β < 1/4, there is no proven solver, and the necessary bound does not rule one out.
- The theorem needed is a reconstruction for prime-order groups from a fixed-function predictor with average advantage ε, using ε^(−c)·poly(n) queries with c < 1/(2β).

**Complete cost formula**

$$W = W_{\text{labels}} + W_{\text{train or select}} + W_{\text{certify}} + Q(n,\varepsilon)\,(c_B + c_q) + W_{\text{reconstruction}} + L\cdot W_{\text{verify}}$$

- **Certification at the threshold costs about rho:** about z²/(4ε²) labelled scalars. At ε = ε*, that is about 0.77·(z²/c)·2^(n/2) additions, so certifying a borderline predictor costs roughly as much as running rho.
- **Matched baseline:**
  - **Single target:** plain rho.
  - **Model or formula of S bits amortized over many targets:** Bernstein–Lange precomputation with matched advice and matched precomputation. Online it costs about √(nN/S) additions and precomputation about √(NT).
  - **Status of ST²:** ST² is used here only as the tradeoff that baseline achieves, not as a bound on coordinate methods.

## 3. The gradient lower bound (Takhanov et al., [arXiv 2310.01611v1](https://arxiv.org/html/2310.01611v1))

**What it covers**

- **Thm 1:** for any differentiable f_w with E‖∂f/∂w‖² ≤ d², and square loss or a 1-Lipschitz classification loss, Var over a random base A of ∇L_A is at most c·d²·ln p/√p.
- **The target:** parity only, h_a(x) = (−1)^(log_a x), with inputs uniform on G∖{1}.
- **Multi-view features:** a fixed map c_i·X followed by a network is still a differentiable f_w(X) that does not depend on the base. So the raw report's novelty claim (a) is wrong.

**A usable unconditional corollary**

- The paper's eq. (11) (Lemmas 10 and 12) holds for any fixed function g that does not depend on the base, with no limit on computation: E_A⟨h_A, g⟩² ≤ ‖g‖²·(1 + √(cp)·ln p)/(p−1).
- **Consequence 1:** for a random base, a typical base-independent predictor has correlation at most about p^(−1/4)·√(ln p), which is the same order as the rho break-even threshold.
- **Consequence 2 (union bound for L2):** for a grammar G of base-independent formulas, Pr over the base that some g ∈ G has correlation at least ε is at most |G|·(1 + √(cp)·ln p)/((p−1)·ε²).
- **What this means for L2:** a useful grammar needs about √p·ε²/ln p members, or it must contain formulas that depend on P. This holds for parity only. Extending it to half or to other segment predicates is plausible but not proven.

**What it does not cover**

- Features that depend on the base, such as X ± jP or constants derived from P. The theorem averages over the base, and in ECDLP the base is known.
- The ability to rule out a specific standard P.
- Non-gradient search for a fixed P. The paper asserts SQ hardness via Feldman et al.; I did not verify the statistical-dimension derivation.
- Exact high-precision gradient descent outside the approximate-gradient model.

**Quantitative strength:** Remark 2 (via Shamir 2018, Thm 10, which I did not inspect) implies failure at about 2^(n/6) scale. That is below rho's 2^(n/2), so this result cannot by itself show that gradient training costs more than rho.

## 4. Corrections to the raw L1/L2 cards

**L2: x-only negation null (exact)**

- For any function f of {x(c_iQ)}, E_k[f · (−1)^pred(k)] = O(1/N) when the predicate is odd (LSB or half).
- The useful part of a predictor is its odd part, (f(Q) − f(−Q))/2. That part needs the sign of y.
- Legendre(y) is invariant under negation when p ≡ 1 (mod 4), so it is useless there. It is odd when p ≡ 3 (mod 4).
- Features based only on x can only target even segment predicates, such as [N/4 ≤ k < 3N/4]. Reconstruction then yields ±k, which is resolved by verification.

**L2: other overclaims**

- **Character-sum pruning:** x(cQ) has degree about c², so Kohel–Shparlinski-type bounds become vacuous for large multipliers c_i. I did not re-verify their exact statement.
- **"S ≈ 0, so unambiguously below ST²":** this is a wrong frame. Search and selection are counted preprocessing, and §3 implies that the formula must encode P.

**Raw card 1: leakage through memorization and views**

- A test view c_i·k′ ≡ ±c_j·k (a training view) leaks a label relation. For example, half(k) = LSB(2k mod N).
- The expected leak rate is about 2m²·M_train/N. With n = 36, m = 64 and M_train = 10⁶, that is about 0.12. The raw pilot sizes (N from 2^16, up to 10⁶ samples) are therefore invalid as designed.

**Raw card 1: decision rule**

- The slope cutoff of 0.4 is the wrong threshold. Any β ≥ 1/4 already fails the black-box necessary condition.
- The rule is also not evaluable within budget. A null result with m_test = 10⁶ and z = 5 only bounds ε ≤ 0.0025. That excludes break-even for c = 1 only when n ≤ 42, and for c = 100 only when n ≤ 57.

## 5. Acceptance gate for a future finite predictor test

No training or proof infrastructure is implied. Each stage must pass before the next stage's numbers are read.

**A. Validity (all must pass)**

1. **Curves:** prime order, ordinary, j ∉ {0, 1728}. Fix the predicate exactly, with k ∈ [0, N).
2. **x-only null control:** reproduce the exact zero on an exhaustive toy group of about 2^16. Report the advantage of the predictor's odd part and the negation-pair check f(Q) vs f(−Q).
3. **Leakage:** require 2m²·M_train/N ≤ ε_claim/10, or exclude by explicit computation every test point whose ±c_i view hits a training view. An exact-lookup memorizer baseline must score below the claim.
4. **Foreign-base control:** evaluate the frozen predictor on labels log_{P′} for at least 20 random P′. Under eq. (11), parity correlation that holds across many bases without retraining signals a bug.
5. **Data splits:** use disjoint fresh scalars and seeds, with selection only on validation data. Make one pre-registered test evaluation. Use z_K = Φ⁻¹(1 − 0.01/(2K)) over all K configurations tried, plus label-shuffle controls.

**B. Measurement**

- Use m_test ≥ (z_K/(2ε_target))².
- Accept a signal only if the lower confidence bound of ε is positive and exceeds the memorizer baseline.
- State the upper confidence bound on any null result, and the n_max below which it excludes break-even.

**C. Cost**

- Count every term of W in group-addition units: labels, training or search, certification, c_B including views, c_q, reconstruction and verification.
- Convert non-group work by measured single-thread time against measured addition throughput on the same machine. Do not infer cost from FLOPS.
- Compare against rho (single target) or against matched Bernstein–Lange precomputation (amortized).

**D. Full-solver evidence (required for any solver claim)**

- At a runnable size, run an actual reconstruction (HN-style or AGS) with the frozen predictor.
- Recover k for at least 20 fresh targets and verify kP = Q for each.
- Report the success rate and the measured number of queries, compared against n/(2.885·ε²) and against measured rho at the same n.
- Sampling accuracy alone never passes this stage.

**E. Continuation only (not proof)**

- Measure ε at four or more sizes spanning at least 16 bits, each passing stage A.
- Continue only if the upper 95% bound on β is below 1/4 and the cost terms grow sub-2^(n/2).
- If β ≥ 1/22, label the outcome "requires missing theorem" and report no exponent claim.
- A failure rejects only the tested learner, grammar and parameters.

## Unresolved

- Concrete exponents for Fischlin–Schnorr and HN, and improved sparse-Fourier bounds after AGS: check these before using any cost below ε⁻¹¹.
- Near-orthogonality for half or segment predicates (needed to extend §3 beyond parity).
- The SQ-hardness claim for fixed-base program search.
- The constant c in Takhanov's Lemma 12, which is not given.
- The raw report's "Discrete-Log Clock (arXiv 2606.17399)" citation was not checked.

I made no repo edits and started no child tasks. Primary-source PDFs and text extracts were downloaded to /tmp only.
