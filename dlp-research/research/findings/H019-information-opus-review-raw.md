Provider: claudeAgent / claude-opus-5-5
TaskId: node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h019-information-probability-review-opus-20261008-r1
Status: completed; no pending children. Review raw; memory-only references and further root qualifications remain explicit.

# H019 information-lens report: review of the probability and Fourier claims

**Bottom line:** the report's main closure claims do not hold as stated. A1's information floor is wrong outside a narrow noisy-oracle model. The constant in C1 is false as stated. A3, A4 and C2 depend on A1. A few narrow lemmas survive with repairs, listed in section 2. No new experiment is justified. Verified gain stays NONE.

This was a paper review only: I made no edits, runs, fetches or child agents. External theorems below that I did not read in a source are marked "memory".

## 1. Corrections

**A1 (information floor): rejected as decoder-independent.**
- **The "≤ 3ε² bits per query" claim is false in general.** It is the binary-symmetric-channel value, 1 − h(½ − ε) ≈ 2.885ε². Root's counterexample is correct. Take X uniform, P(Y=1|X=1) = 2ε and P(Y=1|X=0) = 0. Accuracy is ½·2ε + ½·1 = ½ + ε, and I(X;Y) = h(ε) − ½h(2ε) = ε + O(ε²) bits.
  - The general bound for a binary output with best advantage ε is about I ≤ TV = 2ε. Information arguments then give only n ≳ log q / ε queries, which is vacuous at the q^{-1/4} level.
- **It bounds the wrong quantity.**
  - A real predictor's output is a deterministic function of k and the public data, so I(k; Y_i) = H(Y_i), which can approach 1 bit. Advantage on τ(k) does not control I(k; Y_i).
  - Queries on different predicates τ(c_i k + t_i) are not covered either. Neither are conditional terms I(k; Y_i | Y_<i) under adaptive or correlated errors.
  - The raw observable, e.g. x([c]Q + [t]G), carries all of log q bits.
- **Narrow survivor (model-scoped):** suppose each answer is τ(query) XOR fresh independent noise with crossover exactly ½ − ε, possibly adaptive. Then the chain rule and Fano give n ≥ ((1 − P_e)·log₂q − 1) / (1 − h(½ − ε)). Without the symmetric-noise assumption, the denominator becomes 2ε.
- The "ε√m combining" claim and the "β < 1/4 necessary, whatever the decoder" claim are both rejected. The Håstad–Näslund exponent was not read, so the β < 1/4 matching is speculation.

**A2 (Weil-class ceiling): the shape is plausible but the conditions are incomplete.**
- **Centering is needed.** With h = Σ_a ĥ(a)·ψ_a and τ = Σ_b τ̂(b)·e_q(b·), the a = 0, b = 0 term ĥ(0)·conj(τ̂(0)) is not small. The (a = 0, b ≠ 0) terms vanish, because Σ over E of a nontrivial group character is zero. So the bound must be stated for the covariance, or for centered τ.
  - Note that the bit functions B_j generally have nonzero mean on Z_p.
- **Missing conditions:**
  - poles of the pulled-back function, and the k = 0 point O (an O(d/q) correction);
  - the exact effective degree of the pullback, r ∘ (P ↦ [c_i]P + [t_i]G), of order d·max c_i²;
  - a non-Artin–Schreier condition for every nonzero frequency tuple (a_1, …, a_t), not just per feature. Products on different points can cancel; for example P_2 = −P_1 with an odd r. If the effective degree is below p, this reduces to nonconstancy.
- **Source:** the mixed additive bound |Σ_P χ(P)·ψ(f(P))| ≤ 2·deg(f)·√p (Kohel–Shparlinski 2000) is from memory in both the raw report and my check. It must be read in the source with its exact hypotheses before citation. The Chen and Shparlinski–Stange multiplicative-character bounds must not stand in for it.
- **The "closed" table rows are bounded only within this correlation framework.** "Closed by a factor q^{1/4}" uses A1's invalid floor.
  - **What survives:** each correlation of a centered, polylog-L1 coordinate predicate with an additive scalar predicate is Õ(d·q^{-1/2}), given the sourced bound and the conditions above.
  - This does not close nonlinear or multi-query decoders, or methods that use the raw coordinate.
- **Thue–Morse correction.** With normalized coefficients, any |h| ≤ 1 has L1 ≤ √p (Parseval plus Cauchy–Schwarz), so L1 ≈ p^{0.79} is impossible.
  - Gelfond's N^{log3/log4} is a sup-norm bound on an exponential sum, a different quantity.
  - The relevant ∫|Σ(−1)^{s(n)}·e(nα)| dα is about N^{0.40} (Fouvry–Mauduit, memory). That gives a ceiling around p^{-0.1}, which is non-vacuous but far above q^{-1/2}.
  - So F2 being outside A2's useful range still holds, but for a corrected reason.
- **Dropped:** "H018 N2 already states the dichotomy" and the D-item "N2-affine on logs". H018-information-disposition rejected N2 explicitly (correspondence branches need not be homomorphisms), so neither may be cited as accepted.

**A3 (spectral exclusion): mostly reduces to A2 plus A1.**
- **Survives:** for centered h′ and nonzero a, the h-DC term drops out. So |ĥ′(a)| ≤ L1(h)·2d·√p/q, and Parseval forces a flat spectrum with at least about q/(d²·polylog) nonzero coefficients.
- **Rejected:** the required energy q^{-1/2}·log q comes from A1, so "a spectral decoder needs |S| ≥ q^{1/2}" is unsupported. "Flat-spectrum extraction is BSGS" is a slogan, not a theorem.
- **Heuristic only:** estimating one coefficient's phase by i.i.d. sampling of shifts needs about 1/|ĥ′(a)|² ≈ q samples. That is the variance of the natural estimator, not a lower bound on all algorithms.

**A4 (multiplicative-target window):** given the H016 cost m²/ρ² + √(q/m), a gain needs β < ¼ − δ. The window 1/12 ≤ β < ¼ − δ, nonempty when δ < 1/6, is correct arithmetic. "Sole formal gap" and "last Weil-class window" are rejected; they rest on A1 and on A2's restricted class.

**C1 (Fejér screen): the constant is false and the statement needs repair.**
- **The stated inequality fails.** K_L(a) = (1/L)·(sin(πLa/q) / sin(πa/q))². Take L = 2 and a = (q−1)/2. Then K_2 = 2·sin²(π/2q) = 1 − cos(π/q) → 0. With h′ = e_q(a·) itself, correlation is 1 inside the claimed band, yet F_2 → 0.
- **Correct band:** for |a| ≤ q/(2L), K_L(a) ≥ 4L/π² (from sin x ≥ 2x/π).
- **MSB is not bandlimited.** Its coefficients decay like 1/b and its tail beyond B has ℓ₂ norm O(B^{-1/2}). Passing from ε to the heaviest coefficient loses L1(τ).
- **Repaired lemma:** for centered h′ with E|h′|² ≤ 1, and any B, L with L ≤ q/(2B):

  ε ≤ L1(τ)·(π/2)·(F_L / L)^{1/2} + ‖τ̂ restricted to |b| > B‖₂.

  F_L must be computed from centered h′, otherwise the DC term contributes |mean|²·L. The test is label-free: points come from random x-sampling, and E(F_p) is cyclic of prime order.
- **Rejected:** the cost and power claims (std ≈ √(L/N), total work ≈ q) and "reproduces √d·q^{-1/4}". The null value of F_L is about E|h′|², not 0, and no null distribution was derived.

**C2 (learning cost): reframed, not accepted.**
- W·log W / ε² is a sufficient uniform-convergence or ERM bound for suitable classes. It is not a necessary lower bound.
- **Survives:** certifying advantage ε from i.i.d. labelled samples needs Ω(log(1/δ)/ε²) samples. But validation can also be end-to-end, by checking a candidate k against Q, so it need not be paid separately.
- "Gradient = SQ" needs oracle conditions on precision and batch size. Abbe–Sandon (memory) show SGD can escape the SQ model without them.
- **"Small sub-√q circuit exists" is not an open hypothesis.** Nonuniform circuits of about q^{1/3}, with about q^{2/3} precomputation, are known (Bernstein–Lange; generic lower bound S·T² ≳ q by Corrigan-Gibbs–Kogan; both memory). The question is the charged uniform cost of training plus search. The claimed equivalence also depends on a decoder exponent that was not read.

**Smaller items:**
- Genus-2 point counts "inside A2": unsupported. They are multiplicative-character double sums and need their own monodromy-type bound.
- The low-entropy walk "r step counts" claim: unsupported slogan.
- F1's "above the A1 floor ⇒ solver": inherits A1.

## 2. Valid survivors (narrowly scoped)

1. **Bit-L1 lemma: checked, and correct.**
   - Square wave of period T = 2^{j+1}: |Ŝ(r)| = 2/(T·|sin(πr/T)|) at odd r, 0 at even r. The r = 0 term vanishes because the wave has mean 0 over a full period.
   - Since p is odd, r/T ≠ a/p for r ≠ 0, so the Dirichlet kernels never hit a pole. With |D_p(θ)| ≤ min(1, 1/(2p‖θ‖)), each r contributes at most 3 + ln p ≤ 4 + 2·ln p when summed over a.
   - Result: L1_{Z_p}(B_j) = O((j+1)·log p) = O(log² p). Products of s bits are O(log^{2s} p) by submultiplicativity.
   - Caveat: B_j has nonzero mean on Z_p.
2. **Noisy-oracle Fano bound** from A1, with the symmetric-noise (BSC) or 2ε denominator.
3. **A2 per-correlation bound** for centered features with the listed conditions, once the mixed bound is sourced. Plus the flat-spectrum consequence in A3.
4. **The Fejér-window label-free inequality** in its repaired form, as a necessary-condition screen only.
5. **The i.i.d. validation lower bound** Ω(1/ε²).
6. **The A4 window arithmetic**, as a conditional statement only.

Do not accept closure of coordinate, nonlinear or spectral methods, or "sole opening", from any of these.

## 3. Experiments

None is justified. The repaired C1 is a possible pre-screen only if someone later names a concrete non-algebraic feature with a mechanism. Even then it needs a derived null distribution and centering first. No training, feature sweep or further BM fixture is supported. Verified gain remains NONE.
