# H004 independent compact-algebra initial proposals (raw, unverified)

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h004-compact-algebra-opus-20261008-r1`
Provider/model: Claude Opus 5.5. No edits/experiments/children reported.
Root has NOT adopted the screening lemmas, new epsilon exponent, priors, novelty,
or huge proposed experiment budgets. Native Astra skeptical review is live.

# H004 idea wave: compact high-degree functions and structured divisor products

**Result: verified improvement NONE.** I propose two concrete mechanisms (M1, M2). There are also two screening results, one recovery bridge they share, and one closure of an earlier route. I found no third mechanism that wasn't a variant of these, so I haven't padded the list. All derivations below are my own on paper. None has been independently reviewed or run.

I read H002-first-synthesis, H003-eds-character-collapse, H003-noisy-recovery, H003-norm-generator and H002-predicate-and-circuit-gates. I did not read any other H004 proposal or the p-adic review material. I made no edits, ran no experiments and launched no child agents.

---

## L0 (screening lemma): only odd-multiplicity support survives

**Lemma.** Let F be defined over F_p and let D = div F. Assume D's odd-multiplicity part, together with the class arithmetic below, stays inside a group where 2 is invertible. That holds when the support is in E(F_p) = ⟨G⟩ with q odd and cofactor 1. More generally it holds for any Galois-stable D, because Pic⁰(E/F_p) ≅ E(F_p) has odd order.

Then on ⟨G⟩ away from the supports, χ(F) = χ(c)·χ(g), where:
- D_odd is the set of points of odd multiplicity;
- D₁ = D_odd − deg(D_odd)(O);
- T = [2⁻¹](sum of D₁);
- g has divisor D₁ − 2(T) + 2(O).

So the relevant "degree" is the size of the odd support plus 2, not deg F.

**Proof sketch.** D − div g has degree 0 and lies in 2·Div. Its sum is O. Halving its class in the odd group shows it equals 2·div u.

**Consequences:**
- Every Miller function f_{n,P}, every EDS or elliptic-net term taken as a function of the multiple, and every product of lines or verticals through points of ⟨G⟩ has odd support of at most a few points. It collapses to a character of degree ≤ 5.
- Example: f_{q,G} has divisor q(G) − q(O). So χ(f_{q,G}(S)) = χ(c)·χ(ℓ_{−H}(S)), where ℓ_{−H} is the tangent line at −H and H = [1/2]G. This closes the "Weil reciprocity / mod-squares Tate pairing" route without new data: χ(f_{q,Q}(D)) = χ(f_{q,G}(D))^k·χ(h_k(D)) is a tautology after the collapse.
- Escaping the Chen bound needs a compactly evaluable F with odd support ≫ √p. I know only two such families:
  - (a) pullbacks along an endomorphism or isogeny (support on torsion points), which gives M1;
  - (b) products over translates in a window, evaluated with the √élu resultant (rational support), which gives M2.

## R2 (shared bridge): consecutive-shift phase estimation

This is a conditional bridge with c = 2, improving on the accepted ε^{-6} (or ε^{-4}) reduction.

**Assumptions:** a real predictor B on ⟨H⟩, a known heavy frequency a ≠ 0 with |B̂(a)| ≥ ε, and evaluation of B along cosets P, P+H, P+2H, … at O(1) or polylog cost per step.

**Procedure.** For j = 0..⌈log₂ q⌉:
1. Pick a random r.
2. Compute Z_j = Σ_{i<m} B([2^j]Q + [r+i]H)·e(−ai/q).
3. Then E[Z_j] = m·B̂(a)·e(a(2^j k + r)/q) plus leakage weighted by the Dirichlet kernel.
4. Averaged over r, the noise energy is Σ_{b≠a} |B̂(b)|²·|D_m(b−a)|², which is about m if the spectrum near a is flat. So m ≈ ε^{-2}·log log q gives each phase of 2^j·ak/q to within 1/8.
5. Read off the bits of θ = ak/q, set k = θq·a⁻¹, and verify [k]G = Q.

**Cost:** Õ(log q·(C_start + ε^{-2}·C_step)) + S(ε) + verification. Here C_start is the cost of starting a block and S(ε) is the cost of finding a for the base, which is single-target precomputation and must be paid. ε^{-2} is the information-theoretic minimum, so this is optimal in ε.

**Unproved parts:** local spectral flatness near a, the leakage analysis when several coefficients are heavy, and S(ε). On its own R2 is **not a gain**. It only moves the gain threshold to ε ≫ q^{-1/4}, compared with q^{-1/12} under the accepted reduction.

---

## M1: dilation-product characters (large-n division-polynomial characters)

**Procedure.** Let a(S) = χ(y(S)) and B_n(S) = a(S)·a([n]S) for a fixed n with n² ≫ √p. Equivalent forms:
- B_n(S) = χ(−1)·χ(x([n+1]S) − x([n−1]S)), from x(P+Q) − x(P−Q) = −4y_P·y_Q/(x_P − x_Q)².
- B_n(S) = χ(y·y∘[n]) = χ(ω_n·ψ_n)(x), using H002's normalisation φ(nP) = φ(P)^{n²}·W(n) and H003's halving collapse. So M1 is exactly the Shparlinski–Stange division-polynomial character family in the regime n > p^{1/4}, where their degree bound is vacuous.

Variants:
- An odd predictor ∏_{i≤3} a([n_i]S) with distinct dilation classes.
- A cross-curve version a(S)·b(Φ(S)) with Φ a chain of ℓ-isogenies of degree ℓ^L.
- Order-L characters for smooth L | p−1. Each costs one exponentiation plus a Pohlig–Hellman discrete log, about Σe_i(log p + √ℓ_i). That buys up to L−1 candidate predictors per evaluation, but the per-character bound is unchanged.

**Bridge.** R2 with steps P → P+H and [n]P → [n]P + [n]H: two additions and two characters per sample, so C_start = O(log q).

**Gain and barrier.** The graph of [n] is a genus-1 curve. The function has about 3n² odd-support points, so the Chen/Weil bound is trivial. L0 and the Fejér argument in M2 do not apply, because additive lags of B_n remain dilation products. The minimal endomorphism acting as n on ⟨G⟩ has degree about min(n², ~p^{3/2}): π acts as 1, and nonscalar elements have norm ≳ |D|/4 ≈ p. So no small-degree endomorphism rescues the bound.

Against this, the barrier is heuristic but strong. Averaging over n, Σ_n |B̂_n(a)|² ≈ 1, so a typical n gives ε ≈ q^{-1/2}. Any gain needs a structured n-rule.

**Complexity.** Õ(log q·ε^{-2}) + S(ε). Memory is polylog. No preprocessing beyond S(ε). Success probability is constant, with verification. This is a gain only if ε ≥ q^{-1/4+δ} under R2, or ε ≥ q^{-1/12} under the accepted reduction. If ε ≈ q^{-1/2}, the cost is about q, which is worse than the baseline.

**Prior art distinction.** Chen 2008, Shparlinski–Stange and Kohel–Shparlinski bound only low degree. Shparlinski's bilinear sums over E with multiplicative structure Σα_u·β_v·ψ(f(uvG)) (citation to verify) control averages over n, not a single fixed n. Lange–Shparlinski power-generator sums concern orbits e^j·G. As far as I know, no source bounds a single large-n correlation.

**Main unproved assumption.** Some explicit n-rule (for example n ≈ q^{1/2}, n of special multiplicative order, or a cycle eigenvalue) gives max_{a≠0} |B̂_n(a)| ≥ q^{-1/4+δ}.

**Cheapest decisive falsifier (not run).**
- Compute the array a_k for all k (q additions and q Legendre symbols per curve). Then B_n(k) = a_k·a_{nk mod q} needs no further curve work. FFT each B_n.
- Sizes q ≈ 2^12 to 2^20, with p ≈ q, on 3 random prime-order ordinary curves per size.
- At 2^12 and 2^14, sweep all n modulo ±. At larger sizes, use about 256 random n plus structured n.
- Budget: about 2·10^11 flops in total, dominated by roughly 300 FFTs at 2^20 and the full sweep at 2^14 (about 3·10^10 flops).
- Kill condition: across sizes, max over a≠0 and n stays within 2× the random null √(2 ln(|N|q)/q), with log-slope ≈ −1/2.
- Escalate only if a pre-declared n-rule exceeds q^{-1/4} at the largest size and replicates on held-out curves.

## M2: large interval-window products via √élu

**Procedure.** Let F_s(S) = ∏_{j=1}^{s} (x(S) − x(jH)), with s = q^σ and σ > 1/2 so the Chen bound is vacuous. Evaluate it in Õ(√s) using Bernstein–De Feo–Leroux–Smith biquadratic resultants. A y-window variant is similar, because y(U+V)·y(U−V) is even in both arguments. Then:
- An exact increment identity (my derivation; check it): div(F_s(S+H)/F_s(S)) ≡ (sH) + (−(s+1)H) − (−H) − (O) mod 2. So B_s(k+1) = B_s(k)·χ(c_s)·χ(ℓ_s(kH)·(x(kH) − x_H)), where ℓ_s is the line through sH and −(s+1)H.
- Consecutive steps therefore cost O(1). Starting at a new point costs Õ(√s).
- Bridge: R2. Total cost is Õ(log q·(√s + ε^{-2})) + S(ε).

**New partial obstruction (Fejér / van der Corput, my derivation).** For |L| < M, B(k)·B(k+L) is χ of a function with 2L+2 odd-support points, except at most 2s+3L values of k. Using the positive Fejér kernel, |B̂(a)|² ≤ 1/M + 2·max_{1≤L<M} |A(L)|, with |A(L)| ≤ (C·L·√p + 2s + 3L)/q. Taking M ≈ q^{1/4} gives |B̂_s(a)| ≤ O(q^{-1/8}) uniformly in a, for s ≤ q^{3/4}.

This also extends H003 to growing interval windows. Combined with the cost Õ(√s·ε^{-c}) of random-point reductions, M2 is excluded for every c ≥ 2.5, including the accepted c = 4 and c = 6. It survives only through R2's additive (not multiplicative) cost, and only if ε lies in the band (q^{-1/4+δ}, q^{-1/8}).

**Complexity.** Õ(q^{σ/2} + ε^{-2}), with memory Õ(√s) for the √élu tables. That is below √q only if σ < 1 and ε ≫ q^{-1/4}. Heuristically ε ≈ q^{-1/2}.

**Prior art distinction.** √élu (2020) was built for isogenies. G1 and the Riemann–Roch product tree use these products as membership tests, not as character predictors.

**Main unproved assumption.** Interval-window characters have a coefficient above q^{-1/4}, despite being running products of degree-5 characters.

**Falsifier (not run).**
- Compute B_s by the increment recursion, spot-checked against direct O(s) products at 1,000 random k, then FFT.
- Sizes q = 2^14 to 2^20; σ ∈ {0.55, 0.65, 0.75}; 3 curves each.
- Budget: about 4·10^9 elementary operations.
- Any value above the proved q^{-1/8} cap means a bug.
- Kill if max over a≠0 is ≲ 2× the random null.

**Closure of G1.** √élu supplies G1's missing compact circuit with C_eval = Õ(√T). That makes G1's gate (q/T)·√T = q/√T ≥ √q, so it fails for every T. Multipoint batching, or a binary search on window zero-tests, gives Õ(√q) time and Õ(√q) memory. That matches BSGS and is worse in memory than rho. It is a closure, not a gain.

---

## Overall assessment

Within the grammar "products of fixed low-degree characters at affine views [n_i]Q + [m_i]G" (affine maps are the only ones computable from Q), the picture is:

| Family | Status |
|---|---|
| Same-dilation terms | Collapse (H003 and L0) |
| Additive lags, including large intervals | Fejér cap q^{-1/8} |
| Distinct dilation classes (M1) | Unbounded by these methods; analytically open |

For both mechanisms the prior expectation is ε ≈ q^{-1/2}. Both falsifiers are cheap and would decide the question. In order, the things needing independent review are L0, the Fejér cap, the M2 increment identity, and R2's noise analysis and S(ε). Generic lower bounds were not used as coordinate-aware impossibility claims.
