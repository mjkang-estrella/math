Provider: claudeAgent / claude-opus-5-5
TaskId: node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h020-residue-shadow-review-opus-20261008-r1
Status: completed; no pending children. Raw independent review, with root qualifications in the disposition. No external primary sources fetched by reviewer.

# H020 review: card 1 signed jump-word shadow

**Bottom line:** verified gain is **NONE**. Card 1's word table and sign algebra are fine as bookkeeping. Its gain rests entirely on a 2-adic "shadow" that the raw report never defines. The raw also asserts that "polynomial formulas mod 2^w are exact on the residue", and that is false for canonical F_p arithmetic. No numerical test is justified, because there is nothing defined to run. This is not a proof that no cheap way to predict the jump words exists.

**Scope and access limits:** I read only H020-memory-grok-raw.md, H019-fullwork-disposition.md and H019-xonly-baseline-screen.md. I made no edits and ran nothing. I did not consult any primary sources this session, including Cheon–Hong–Kim, Bos's thesis §4.6, Bernstein–Lange–Schwabe 2011 and GWZ. The raw's claims about those sources are unverified here.

## 1. Sign-word algebra and table: these hold, with small corrections

- **Unfolding is correct.** With W_t = e_t(W_{t-1} + J_{s_{t-1}}), the result is W_k = ε_tot·W_0 + Σ σ_t J_{s_t}, where σ_t = ∏_{u>t} e_u. Factoring out ε_tot gives W_k = ε_tot(W_0 + D), where D = J_{s_0} + Σ_{t≥1} π_t J_{s_t} and π_t = e_1⋯e_t. So a word costs one addition plus a negation.
- **Table size.** There are r·(2r)^{k-1} distinct keys, which is under the stated bound of (2r)^k. Merging words with equal sums (multisets, or words that cancel) shrinks it further.
- **The even-y rule is sound.** y = 0 cannot occur, because the order q is odd, so there is no 2-torsion. Since p is odd, parity(p−y) = 1 − parity(y).
- **Per-target setup by prefix extension** costs one addition per entry. This holds.
- **Arithmetic slips:**
  - Setup B = 2^20 is below T/4 only once q exceeds about 2^44.4, not 2^42. To be "negligible" it needs a much larger q.
  - The ledger leaves out the cost of looking things up in the table. That table holds about 2^21 field elements (≈64 MiB at 256 bits), plus labels, and is hit once per macro-step. That cost is outside the M-count and needs measuring, not assuming.

## 2. Errors, roughly most severe first

1. **"Polynomial formulas mod 2^w are exact on the residue" is false for the walk.** The walk hashes and canonicalizes on canonical representatives in [0, p). Integer formulas are exact mod 2^w only before reduction. Reducing subtracts ⌊z/p⌋·p, and the low bits of that quotient depend on high bits.
   - Affine addition also needs the F_p inverse Δx⁻¹. That inverse is not a low-degree polynomial: the integer lift of a^{p−2} is astronomically large.
   - Going projective (Jacobian) does not help. The hash and the even-y bit need canonical affine x and y, which brings the inversion back. So the "Jacobian-sized c_m ≈ 12, no inversion" charge does not price the needed outputs.
2. **The primitive is not specified.** "Scale-normalized residue", "common 2-valuation", "w = t + O(k)" and "t" are never defined. A run cannot test an object that is not defined.
3. **The falsifier is broken in three ways:**
   - It is vacuous at (16, 4, 32) on a 16-bit field. There w = 32 ≥ log₂ p, so the "shadow" can hold the entire coordinate, and agreement says nothing about a residue idea.
   - On that fixture the raw's own charge is 12·(32/16)² = 48M per fine step, more than 6M, so the card loses by its own ledger.
   - "A failure kills every size" is false. One failed implementation at one size kills that implementation only.
   - The criterion "median agreement length < 4" is the wrong statistic. What matters is the per-word failure probability ε times the cost of detection and recovery. A median of 4 allows about half of all words to fail.
4. **Collision discovery is underspecified.** The gain needs fine-level collisions to be detected. If two walks merge at a fine point but their phases differ mod k, their materialized points never coincide (short of a cycle). So the shadow must also output the distinguished-point bit for every intermediate fine point; the raw lists only indices and even-y bits.
   - Without that, the macro walk is just an r′-adding walk with a big table. Its collision time is about √(πq/4) macro-steps, which brings back rho's cost and removes the factor k.
5. **Cycle escapes are not all table translations.** "Escapes stay inside the word" works for look-ahead index rules, provided the shadow predicts them. Escapes based on doubling or on the cycle's minimum point require materializing the point. That cost must be charged, although it is probably lower order.
6. **The schoolbook width cost 12(w/log₂ q)² has no floor.** A 32-bit operation still costs at least one machine-word operation with fixed overhead, so the quadratic scaling understates it at small w.
7. **Baseline section:**
   - **The 2.45M + 1S figure at k = ℓ = 8 is invalid.** It sets the inversion cost I to 0 rather than amortizing it. The per-key inversion share is (ℓ+1)/(k(2ℓ+1))·I = (9/136)·I ≈ 0.066·I, which is not negligible for a realistic 256-bit I. H019 handles this by requiring k and ℓ to grow.
   - **Calling 0.62 "proved" overstates it.** H019 accepted it as an arithmetic estimate only, not a runtime result.
   - **The crossover holds.** The band 0.19–1.33 follows from θ + 1/(4θ) < 0.886·6/3.5 ≈ 1.519.
   - **"Best prior art for every budget o(√q)"** is a scoped claim, not an established fact.

## 3. Cheap paper counterexamples to a low-bit shadow

All of these use canonical representatives.

- **Addition parity (root's example):** take p > 2^w + 1, a = 0, a′ = 2^w, b = p − 2^w. Then a + b = p − 2^w is odd, while a′ + b reduces to 0, which is even. a and a′ share their low w bits.
- **Multiplication:** p = 13, w = 2. a = 2 and a′ = 6 share low bits 10. With b = 7: 2·7 ≡ 1 (low bits 01), but 6·7 ≡ 3 (low bits 11).
- **Inversion:** p = 13, w = 2. a = 1 and a′ = 5 share low bits 01. But 1⁻¹ = 1 (01) and 5⁻¹ = 8 (00).
- **Structural fact:**
  - Every additive homomorphism Z/p → Z/2^w is zero, because the orders are coprime. So there is no nonzero ring homomorphism F_p → Z/2^w either, unital or not.
  - Likewise, every homomorphism from E(F_p) of odd prime order q into a group of order coprime to q is trivial. So no shadow can be a homomorphism of field addition or of the point law.

This rules out homomorphic shadows, and raw mod-2^w polynomial simulation of the canonical point law. It does **not** rule out a non-homomorphic predictor of hash, sign and distinguished-point bits that is cheap on average. I am not claiming that one exists or that it is impossible.

## 4. Answer: is there a genuine low-bit EC recurrence?

No. The key primitive is missing. The raw report concedes this, but it then wrongly calls the remaining gap only a width question. The specific obstruction is that canonical x(U+J) depends on the F_p inverse of Δx, and nothing in the raw predicts bits of that inverse from partial data. This is weaker than an impossibility claim: I am not asserting that bits of the inverse are hard to predict.

## 5. Minimal specification before any test is admissible

1. **Explicit algorithm.** Shadow(U, table) → (s_0…s_{k−1}, e_1…e_k, distinguished-point bits d_1…d_k, escape flags). State exactly what it reads from U: full coordinates or w bits.
2. **Correctness mode.** Either:
   - exact agreement with the fine walk, with failure detection that does not compute the intermediate points, and a priced recovery; or
   - a standalone macro walk with a collision-discovery argument at the fine level that deals with phase.
3. **Cycle rule.** Expressible as table translations, or with any materialization priced.
4. **Cost model.** Shadow cost in bit or word operations with a machine-word floor; table memory and lookup; per-target setup; every inversion.
5. **Win condition.** Show ε·recovery + shadow + (5+s)/k + lookup < 5+s with a stated margin, at a stated (q, memory) point, against matched baselines. That means rho at the same memory: the table is memory, and 2^20 < 0.19√q, so the comparator is rho, not BSGS.
6. **Paper pre-check.** The algorithm must handle the inversion counterexample above, with an argument for how it gets the low or high bits of Δx⁻¹.
7. **Test fixture, if any.** log₂ p well above w (for example p ≫ 2^{2w}). Admit it as a kill test of that algorithm only, with a predeclared ε threshold and no feature sweep.

## 6. Cards 2–4 (brief; not the focus)

The raw scopes these sensibly and they add no gain claim. Card 2's coverage constant c(0) = 6 from GWZ Table 4 is unverified here. Card 3 is conditional on the bit-count model, and its own conclusion is that the crossover moves by only a constant factor. Card 4 explicitly prices only that one detector.

**Verdict:** no surviving gain, and no numerical test justified now. Card 1 is a word-table framing whose only gain-bearing part, the shadow, is undefined, and the version the raw states (mod-2^w polynomials on the residue) is refuted on paper by the examples above.
