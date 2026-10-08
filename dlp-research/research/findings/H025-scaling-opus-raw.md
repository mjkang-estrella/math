# H025 Opus scaling report — raw, not accepted wholesale

TaskId: node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h025-layout-scaling-opus-20261008-r1

Root notes: independence/resonance/phase-torus assertions and hand integration are
unverified heuristics. The broad negative verdict is not adopted. First-moment
coverage coefficients do not convert directly to mean-work ratios. See the
separate root reconciliation before using any conclusion.

# H025 B review: asymptotic coverage geometry and prior art

**Verdict:** B is not a credible route to a constant that stays below the empirical ~0.9 of the negated grumpy-giants method. The fingerprint and chart argument works at the wrong scale. Under a generic-phase model, B's best possible constant comes out at about 0.90. The finite 5% pass fits early first-moment gains plus small-prime effects. I can't rule out a lucky systematic phase lock, but nothing in the design produces one for every q. Verified improvement: none.

I did no numerical runs, imported no probes and wrote no files. The integrals below are hand calculations (Simpson's rule, h = 0.25, about ±0.01).

## Setup and assumptions

- q is prime and tends to infinity. M = ⌊√(q/2)⌋. All four families use equal centered prefixes of length L = λ√q, so t = 4L and τ = t/√q = 4λ.
- The block size B is polylog in q, so block drift is O(B/√q). The fallback is ignored because its reach probability is tiny at τ = 3.
- Same-family negatives, infinity and the public inputs add O(t) coverage, which is negligible against t².
- The strides can be written s_i = σ_i(M + τ_i), with σ = (+,−,+,−) and τ = (0,1,2,3). Replace the indices by J = σ_i·j and R = σ_l·r. Then channel (i, l, ε) has numerator

  N = ΔD + εR·(M+τ_l) − J·(M+τ_i) = ΔD + u(M+τ_l) + d_il·J,

  where u = εR − J and d_il = τ_l − τ_i. This does not depend on ε.
- So each channel is a 2D arithmetic progression. Each cell u has length about M and holds L − |u| points with step d. The local duty is ρ(u) = (L − |u|)/M, which peaks at L/M = √2·λ.
- B has 12 channels. Their |e| values by family pair:
  - (0,1): 1, 3 (d = 1)
  - (0,2): 3, 5 (d = 2)
  - (0,3): 7, 9 (d = 3)
  - (1,2): 2, 6 (d = 1)
  - (1,3): 6, 10 (d = 2)
  - (2,3): 4, 12 (d = 1)

## 1. Obstruction: the chart argument has no force at critical prefixes

At critical prefixes, |v| ≈ LM = λq/√2. The accepted error bound (|Δ| + |v|)/(|e|q) is therefore Θ(1), not o(1). Each channel's support is |e| windows, each of width √2·λ/|e| in k/q, so each channel covers macroscopic measure √2·λ ≈ 0.354τ.

Over 12 channels the total is about 4.24τ. That exceeds 1 once τ > 0.24, well before the critical range. At τ ≈ 0.9 the average point lies inside about 3.8 channel windows.

So different fingerprints mod 73 only separate window centres. Disjointness, if any, has to come from micro-structure. The 73-fingerprint rationale is asymptotically vacuous as a separation mechanism.

## 2. Within-channel gcd and wrap (exact conditions)

The channel generators are M + τ_i and M + τ_l. Their gcd g divides d.

- **Duplicates over the integers** appear once L − 1 ≥ (M + τ)/g, i.e. τ ≳ 2√2/g. The same thing happens when step-d runs from adjacent cells land on the same residue class.
- **Which pairs are affected:**
  - Pair (0,3), both signs: g = 3 exactly when 3 | M. Onset at τ ≈ 0.94, right in the critical range, so the constant depends on M mod 3.
  - Pairs (0,2) and (1,3): g = 2 for exactly one of them for every M (the first when M is even, the second when M is odd). Onset at τ ≈ 1.41, which is tail only.
  - When g < d, runs from adjacent cells interleave harmlessly.
- **Modular wrap:** no wrap while 2LM < q, i.e. τ < 2√2 ≈ 2.83. The cap at 3⌈√q⌉ goes slightly past this, so wrap matters only in the last stretch.

## 3. Generic-phase anchors (calculable)

Restricted to one chart and macroscopic region, a channel's k-set is a run pattern with period (M + τ)/|e| and duty ρ ≤ √2·λ. For two channels, overlap density = ρ₁ρ₂ + resonant terms. Resonances occur only at harmonics (n₁, n₂) = m·(e₂/g, e₁/g).

For d = 1 runs, the resonant correction is bounded by

  |K| ≤ 2·Σ_m min(ρ₁, 1/(π·m·n₁)) · min(ρ₂, 1/(π·m·n₂)).

- Pairs with reduced indices of 3 or less can in principle be fully anti-correlated. These are the equal-|e| pairs (3,3) and (6,6), and ratios 2 and 3.
- Pairs like (5,7) or (7, anything) have |K| ≲ 0.1·ρρ′, so they behave as effectively independent.

With independent micro-phases, survival at a point is Π_c(1 − ρ_c). Because log(1 − ρ) is concave, survival is at least exp(−s·g(ρ_max)), where g(ρ) = −ln(1 − ρ)/ρ, s = 0.75τ² and ρ_max = 0.354τ. This gives three anchors:

| Model | E[T]/√q |
|---|---|
| Perfect disjointness (H024 floor) | 0.770 |
| Independent phases, *ideal* macro layout (not attainable with triangular profiles) | ≈ 0.90 |
| Independent phases, random macro placement: ½·√(π/0.75) | ≈ 1.02 |

Even the unattainable ideal-layout bound only matches GWZ's ~0.9. A persistent constant below 0.9 therefore *requires* systematic anti-correlation between channels.

## 4. B's micro-phases are not controlled across q

All offsets are multiples of the single quantity D = ⌊q/73⌋. The relative phases therefore lie on the line (n_c·ψ) with ψ = (D/M) mod 1, plus a second parameter (q mod M)/M. Both sweep over their range as q varies (heuristically, ψ through a full cycle every Δq ≈ 73M). The phase also drifts within each region by about 2.83·λ·Δτ cycles, which averages things further towards independence.

So the "constant" is a function F(ψ, r) on a 2-torus, not a limit. q = 509 and q = 1009 are two phase samples.

- **Rounding of ⌊q/73⌋:** this changes macro centres by θΔ/q. That is about 0.15 at q = 509, and about 0.06 for the largest |Δ| at q = 1009. So the tested primes don't even realise the 73-fingerprint geometry.
- **No scale separation at tested sizes:** M/|e| is about 1.25 at q = 509 and about 1.9 at q = 1009 for e = 12. Separation would need roughly q ≳ 3·10⁴–10⁵.
- **Drifting centres:** asymptotically irrelevant at O(B/√q), but finite here, at about 0.13 and 0.095.

## 5. Reading the finite pass

| | q = 509 | q = 1009 |
|---|---|---|
| B, E/√q | ≈ 0.944 | ≈ 0.928 |
| Control, E/√q | ≈ 1.061 | ≈ 1.013 |
| Ratio B/control | 0.889 | 0.916 |

Four families give a 1/0.889 first-moment advantage (0.75τ² against 0.667τ²) while overlaps are still sparse. The control is far above its asymptotic ~0.9 because of finite overhead. The ratio rising across the two primes fits erosion, but two points can't establish a trend.

## Positive criterion to check before any expansion

The persistent constant is below 0.9 only if the union coverage at τ ≈ 0.8–1.2 is clearly better than the independent-phase prediction 1 − Π_c(1 − ρ_c(x)), computed from the known triangular macro profiles. That must hold on average (and ideally at the worst point) over the phase torus (ψ, r).

- Sample primes spanning at least one 73M-wide window of q, at sizes where M/12 ≫ 1.
- Measure the pairwise excess |S_c ∩ S_c′| − Σ_x ρ_cρ_c′ separately for the resonant pairs listed in section 3.
- If union ≈ product prediction, or the excess changes sign with ψ, reject B as an asymptotic route.

This needs only the integer channel sets, no EC arithmetic. I've left the sizing to the cost-design role.

## Prior-art relation

B is essentially the negated, baby-free version of the four-giant stride rule M, −(M+1), M+2, −(M+3) from GWZ 2017 Appendix B, with quadratic offsets added. Tying offsets to M so that the phase is fixed is exactly the shift optimisation in Bernstein–Lange §6 (four giants, optimised shifts). Neither is a discovery. I'm relying on the local findings' reading of these sources and did not reopen them:

- Bernstein–Lange: https://mathweb.ucsd.edu/~kedlaya/ants10/bernstein/paper.pdf
- GWZ 2017: https://pdfs.semanticscholar.org/5753/7e7d4d08b6de01aa79717c4bb849e694958f.pdf

## What remains uncertain

- The independence model and the resonance bound are heuristics, not theorems.
- I have not excluded lucky locking that holds on a set of ψ with positive measure.
- No novelty, optimality or lower-bound claim is made, and nothing here bears on ECDLP hardness.
