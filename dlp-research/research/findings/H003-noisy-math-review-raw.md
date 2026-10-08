# H003 noisy recovery: raw mathematical review

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h003-noisy-math-review-opus-20261008-r1`
Provider/model: Claude Opus 5.5. Read-only, no tests or child tasks reported.
This is reviewer output, not automatically accepted; see disposition for corrections.

**Verdict: accept, with repairs.** H003 is a valid, conservative sufficient reduction. The total-work bound is Õ(ε⁻⁶): ε⁻⁶ times explicit powers of log q, provided each predictor call costs polylog(q). It is neither optimal nor a new ECDLP algorithm. I found no sign or normalisation error. Orientation can be dropped (point 3), but a guaranteed magnitude is still needed. I made no edits, ran nothing, and started no subagents.

## 1. Fourier and transport: checked, correct

- **Normalisation and inversion.** With f̂(a) = q⁻¹ Σ f(x) e(−ax/q), we get E_x f·g = Σ_a f̂(a)·conj(ĝ(a)).
- **ĝ for g(x) = (−1)^x on the canonical range [0, q).** Let z = −e(−a/q). Since q is odd, z^q = −1, so Σ z^x = 2/(1−z). This gives ĝ(a) = 2/[q(1+e(−a/q))] and ĝ(0) = 1/q. Both match the proposal.
- **L1 bound, tighter than claimed.** Write s = q − 2a, which runs over odd numbers in [−(q−2), q].
  - Then |ĝ(a)| = 1/(q·|sin(πs/2q)|) ≤ 1/|s|, by Jordan's inequality.
  - Summing gives ‖ĝ‖₁ ≤ 2 + ln q ≤ H + 2.
  - So L = 4H+4 is valid but wasteful. Using L = 2 + ln q makes the call count about 4⁶ ≈ 2¹² smaller.
- **Existence of a heavy nonzero frequency.** The argument is 2ε ≤ |f̂(0)ĝ(0)| + max_{a≠0}|f̂(a)|·L, with |f̂(0)ĝ(0)| ≤ 1/q ≤ ε. Hence max_{a≠0}|f̂(a)| ≥ (2ε − 1/q)/L ≥ ε/L = η. This needs ε ≥ 1/q, and that condition is sharp for this inequality.
- **Transport.** f₁(x) = f₀(kx), and substituting u = kx gives f̂₁(b) = f̂₀(b·k⁻¹). Both lists are guaranteed to contain a and ka. Verifying kG = Q is exact, so false pairs, including −k from conjugate frequencies, are rejected. This correctly uses the same B_G for both searches.

## 2. Estimator: checked, correct

- **Unbiasedness.** |f̂(a)|² = q⁻² Σ_{x,y} f(x)f(x−y)e(−ay/q). Summing over a ∈ I gives E_I = q⁻¹ Σ_y E_x[f(x)f(x−y)]·D_I(−y). The importance weight 1/(q·p(y)) therefore makes E[Z_I] = E_I, and taking the real part keeps it unbiased because E_I is real.
- **Bin count.** {0} plus shells j = 0…⌊log₂((q−1)/2)⌋ gives ⌊log₂(q−1)⌋ + 1 = ⌈log₂ q⌉ = H bins, with none empty. This covers q = 3, Fermat primes, and the truncated last shell.
- **|Z| ≤ H.**
  - For y ≠ 0: shell size ≤ 2^{j+1} and |D| ≤ q/(2·2^j), so |Z| ≤ H·2^{j+1}·q/(2^{j+1}·q) = H.
  - For y = 0: |Z| ≤ H|I|/q < H.
- **Hoeffding.** The range width is 2H, so P(error > η²/8) ≤ 2·exp(−mη⁴/128H²) = δ_s/(2·Ntests). This matches the stated m exactly.
- **Adaptive union bound.** Fresh samples are drawn for each test, so each test is conditionally independent of the history. A union bound over test indices up to the enforced cap is valid. Total failure probability is ≤ δ/2, so it is conservative.
- **Thresholds.** Retaining when the estimate is ≥ η²/2, with error ≤ η²/4:
  - every |f̂| ≥ η survives;
  - every retained interval has energy ≥ η²/4;
  - Parseval (Σ|f̂|² = E f² ≤ 1) caps retention at 4/η² per level;
  - tests ≤ 1 + 8⌈log₂(q−1)⌉/η² ≤ Ntests.
- **Caps.** Aborting is reached only on the failure event. Each output list has ≤ 4/η² entries, so there are ≤ 16η⁻⁴ pairs.

## 3. Root's orientation question: confirmed, narrowly

The triangle argument uses only |E f₀g| ≥ 2ε, and replacing f by −f leaves every |f̂| unchanged. So a known or positive orientation is **not** needed for this algorithm.

The correct sufficient condition is weaker still: there exists a ≠ 0 with |f̂₀(a)| ≥ η, and cost depends only on η. What remains required:

- B_G is fixed and stateless, and nothing depends on the target (no B_Q, no per-target selector).
- The domain and exclusion rule are fixed before seeing data. Exclusions are set to B = 0, and full-domain correlation is N/q.
- A real magnitude guarantee holds for this base G.
- ε is known. Otherwise, use a doubling schedule over ε with an explicit floor or cap. Without one, the algorithm has no termination guarantee.

I confirmed from `eds_diagnostic.py` that A1's label is `(-1)^k` for k in `range(q)`, so g is the correct predicate. A1's signs and tiny-q magnitudes say nothing about scaling.

## 4. Repairs needed

**R1. Certified precision (resolves objection 2).**
- Reduce every exponent t modulo q exactly as an integer.
- Compute D_I(−y) as e(−sy/q)·(e(−ℓy/q) − 1)/(e(−y/q) − 1), using approximations of e(t/q) with absolute error ρ.
- The denominator satisfies |e(y/q) − 1| ≥ 4|y|_q/q, so it is never near zero for y ≠ 0. For y = 0, use D = |I| exactly.
- The weight error is ≤ 2Hρq/|y|_q ≤ 2Hρq, so ρ ≤ η²/(16Hq) keeps it within the η²/8 numerical budget.
- That needs b ≈ log₂ q + 2·log₂(1/η) + log₂ H + 4 working bits, which is O(log q) because η ≥ 1/(qL).
- Evaluate sin/cos with a certified series and a b-bit π. This costs polylog(q) bit operations per weight, and the bin probabilities are exact rationals.

**R2. Use L = 2 + ln q,** per section 1.

**R3. Randomised predictors.** The target is the mean function f = E_coins[B]. A y = 0 sample must make two independent calls; squaring a single call estimates E[B²] instead. The correlation hypothesis must be stated for the mean function. Do not use the AGS-style majority vote here.

**R4. Optional sample reuse (not required).** One sample set per search can serve every node of the fixed dyadic tree: union-bound over ≤ 2q nodes, with log(4q/δ) inside m. This is valid under adaptivity because the candidate family is fixed in advance. It cuts predictor calls to Õ(ε⁻⁴), but estimator arithmetic stays Õ(ε⁻⁶), so the full-work exponent is unchanged.

**R5. Amortisation.** The f₀ search does not depend on the target and can be amortised across targets. Still charge it in full for a single target.

## 5. Explicit work bound

Predictor calls ≤ 4·Ntests·m ≈ 4096·H³·L⁶·ε⁻⁶·ln(8·Ntests/δ), plus lower-order terms.

The full work W adds three terms:

- the calls × (O(H) group operations per point + C_B + C_est), with C_est polylog by R1;
- ≤ 16·L⁴·ε⁻⁴ inversions and verifications;
- O(η⁻²) storage.

So W = O(H³ L⁶ ε⁻⁶ log(H L/(εδ)) · polylog) = q^{6β+o(1)} for ε = q^{−β}. It beats √q asymptotically exactly when β < 1/12, assuming C_B is polylog; whether A1's φ evaluation is polylog must still be shown.

Indicative constants at H = 256, ε = 1, δ = ½ (these belong to the companion cost review):

| L | Predictor calls |
| --- | --- |
| 4H+4 | ≈ 2^100.6·ε⁻⁶ |
| 2+ln q | ≈ 2^85.6·ε⁻⁶ |

These are before group, predicate and estimator costs, so there is no finite-size speed guarantee. At A1 sizes (q ≈ 139) the procedure is pointless next to exhaustive search.

## 6. Scope

The method looks like standard sparse-Fourier interval filtering in the AGS family. I verified no primary-source exponent for it or for later work, so it should carry no novelty or optimality claim. The ε⁻¹¹ route stays unverified, and the generic noisy-oracle Fano bound is still not a universal lower bound.

I found no counterexample: every step holds under the stated hypotheses, with R1–R3 added. The claim fails outside them, for example if the predictor is stateful or target-dependent, ε < 1/q, the correlation is measured on a non-uniform or eligible-only domain without the N/q conversion, or a randomised predictor reuses coins.
