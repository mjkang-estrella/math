# Iteration 2, arithmetic lane: quasi-RH self-improvement and a combined arithmetic mechanism

Date: 2026-10-08. Upstream: OpenAI/math at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Upstream theorem statements are accepted as true, as instructed; their proofs were not audited. Every deduction made here was checked independently.

**Parent integration status (2026-10-08): candidate, not yet accepted.** The author's claims below await independent proof and novelty review in `../reviews/i02-arithmetic-r2.md`. The parent reproduced the finite checks and verified all 59 pinned source hashes; neither check establishes the asymptotic theorem or novelty. “Unconditional” below always means under the user's accepted-corpus premise. B1 concerns prime moduli only, not Arnold's full integer-modulus problem or an asymptotic formula with its predicted constant. In the opening summary, the density guarantee is c* − η with B depending on η, as in the theorem; a single B attaining c* is not established. The progression-only Artin reduction in §4.4 is also unverified and is not an accepted conditional theorem.

## Outcome in one paragraph

**Route A** tried to improve the quasi-RH half-plane Re s > 7/8. It is stopped, with an exact reason. The 7/8 boundary is the explicit function σ₀ = 11/12 − ℓ/4 of the manuscript's prime-slot length ℓ. The binding high-side certificate leaves only about 1.1×10⁻⁴ of slack. Re-tuning the geometry therefore gains at most about 4×10⁻⁵. A tempting bootstrap, feeding β\* ≤ 7/8 back into Part II, does not loosen that binding case. Even density-hypothesis-quality row counts would leave this architecture stuck above 13/15.

**Route B** combines two independent corpus theorems: the Poisson–Dirichlet law for p−1, and the uniform zero-free half-plane Re s > 1−10⁻⁶ for Kummer-field zeta functions. Together they give **a new unconditional positive-density theorem of near-primitive-root type** (Theorem B below). For any finite set of integers a with |a| ≥ 2, a set of primes of lower relative density at least an absolute constant c\* > 10⁻⁶ has every a of index at most B. Here B depends on the set. As a corollary, the average multiplicative order of a fixed base has the order of magnitude ≍ x predicted under GRH; before, only GRH-conditional lower bounds were known for a fixed base.

This is **not** Artin's conjecture, which needs index exactly 1. The precise obstruction to index 1 is isolated in §4.4. I claim Theorem B as a genuine new theorem, conditional only on the accepted corpus. It is a substantive step in the density direction of a MathDB "celebrated" problem (Artin's conjecture on primitive roots, MathDB #316116), but **not** a resolution or a case of that conjecture as stated.

## 1. Source contracts (immutable; git-blob verified)

All 59 fetched files match their pinned git blob hashes; see `frontier/sources/i02_arithmetic/manifest-artin.json`. The quasi-RH cache also matches its pinned blob (`268c4e32…`).

| Input | Path at pin (blob) | Exact statement used |
|---|---|---|
| QRH | `preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex` (`268c4e32`) | Thm `thm:main`; geometry `old-eq:5.1`; `prop:probe-low` (`old-eq:5.10`, `5.11`); `lem:bin-contour-accounting` (`eq:stage-high-exponent`); `prop:detector-counts`; `lem:balanced-endpoint`; §`sec:selection` (definition of α). Used only for the analysis in Route A. |
| **[PD]** | `preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/build/sections/01-introduction.tex` (`79950676`), `08-poisson-dirichlet.tex` (`43e3be63`) | **Thm `thm:main`.** For each fixed k and bounded continuous F on [0,1]^k, (π(X)−1)⁻¹ Σ_{3≤p≤X} F(V₁(p),…,V_k(p)) → E F(L₁,…,L_k) as X → ∞ through real X. Here V_j(p) = log q_j(p)/log(p−1) for the ranked prime factors of p−1, counted with multiplicity, and (L_j) ~ PD(1). |
| **[HZ]** | `preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/build/sections/01-introduction.tex` (`d3ed0c86`) | **Thm `thm:hecke-zero-free`.** For every cyclotomic F ⊇ μ₁₂ and every finite-order Hecke character η of F, L_F(s,η) has no zero in Re s > 1−10⁻⁶. The width is uniform. |
| [HZ-split] | same manuscript, `07-splitting.tex` (`ee9b3eac`) | Lemma `spl:field-bounds` (descent of [HZ] to ζ_{K_q}, with n_q = q(q−1) and log D_q + n_q ≪_a n_q log 2q) and Lemma `spl:smooth-estimate`. I re-read both proofs. They are short and standard: abelian factorization over Q(μ₁₂q), a unit-window zero count, and a smoothed explicit formula. |
| reduction | same manuscript, `01a-reduction.tex` (`260e5612`) | Lemma `alg:splitting-test` (elementary; re-verified). |

Write δ₀ = 10⁻⁶ and K_q = Q(μ_q, a^{1/q}).

**Derived input (S).** Fix an integer a with |a| ≥ 2. There are q₀(a) and C_a such that, for every prime q ≥ q₀(a) and every x ≥ 2,

  #{x < p ≤ 2x : p splits completely in K_q} ≤ C_a ( x/(q(q−1) log x) + x^{1−δ₀} log(2q)/log x ).

This is the displayed inequality in the proof of `prop:splitting`, before the paper specializes to q ≤ exp(L^{0.3}). Its derivation uses only `spl:field-bounds` (valid for q ≥ q₀(a)) and `spl:smooth-estimate`, whose constant is independent of the field. I checked that no step uses an upper limit on q. (The paper's own restriction only makes log(2q)/L bounded.)

## 2. Route A: self-improving the 7/8 half-plane (stopped, with exact reasons)

### 2.1 The boundary is an explicit function of one geometric parameter

From `old-eq:5.1` the geometry satisfies h = 1 − l_x + ℓ, l_y = l_x + b, and M + ℓ = 1 with M = l_x + l_y. Hence h = (1 + 3ℓ + b)/2.

The low estimate `old-eq:5.10` is Z^{l_x/2 + b/12}. The Mellin exponent `old-eq:5.11` is C(s) = l_x/2 + s − 1 + h/6. The continuation criterion `lem:continuation-criterion` excludes zeros exactly to the right of the σ₀ with C(σ₀) = low exponent. So

  σ₀ = 1 − h/6 + b/12 = **11/12 − ℓ/4**, independent of b.

At ℓ = 0 this is Part I's 11/12; at ℓ = 1/6 it is 7/8. The identity is checked exactly on a rational grid in `frontier/experiments/i02_arithmetic_qrh_geometry.py`. Any improvement must therefore come from a larger compensating prime length ℓ.

### 2.2 How much ℓ the high side tolerates

From `eq:stage-high-exponent` at d = h, with a = (1+δ)/2 and q = xδ, I derived the general exponent

  E(h) = −3/4 − ℓ/4 − b/3 + hR + δ(1+2ℓ)/2 + qℓ.

At ℓ = 1/6, b = 1/8 it reproduces the paper's C₀ = −1/48 form exactly. The row exponent R = R\* from `prop:detector-counts` does not depend on ℓ, except through a supply condition ℓ/h > 7/37 that only gets easier as ℓ grows.

Scanning δ ∈ [1/50, 5/6] and x ∈ [0, 1/2]:

- At the paper's geometry, the worst case has −E ≈ 2.28×10⁻⁴. The paper's certified bound is 49/440640 ≈ 1.11×10⁻⁴. The binding point is interior: δ ≈ 0.39, x = 1/2.
- The largest admissible ℓ is ≈ 0.166838, giving σ₀ ≈ 0.874957, a gain of about **4×10⁻⁵**. Varying b does not help: the best value found was b ≈ 0.1225, with the same gain.

This optimistic gain also ignores constraints that are hard-coded at 7/8: H_η is holomorphic only on Re s > 7/8, and `lem:bin-contour-accounting` requires σ₀ ∈ [7/8, 1). Even the 4×10⁻⁵ would need those rechecked. It is not a substantive theorem, and I did not pursue it.

### 2.3 The tempting bootstrap is invalid

Part II uses Part I (β\* ≤ 11/12) only through Δ ≤ 1/24, the bin ceiling δ ≤ κ ≤ 5/6, and the capacity κ = 2β\* − 1. It is tempting to rerun Part II with β\* ≤ 7/8 as input, which would give "α = 3/4".

But α = 5/6 in `prop:detector-counts` is **not** the bin ceiling. It is "the fixed slope from sixth-power amplification": e(r) = max{1, (1+5r)/6} (`eq:no-slot-inverse-count`). The binding certificate point δ ≈ 0.39 lies far below any ceiling. A smaller κ only removes the +Δ/4 capacity loss, and that loss is already absorbed by the Δ-margin. So feeding 7/8 back does not move the boundary.

### 2.4 The architecture's ceiling

Suppose the row counts were density-hypothesis quality: R = 1 − δ and q = δ/2. Then E(h) = −1/4 + 5ℓ/4 + b/6 − bδ/2. At small δ, which is the floor bin where every row is counted, this forces ℓ < 1/5 − 2b/15, hence σ₀ ≥ 13/15.

So 13/15 is a hard floor for this two-representation scheme, independent of any new zero-density input. Getting past it requires a new low estimate or a different probe, not better counting. **Stopping point:** any real improvement must change the low estimate's Gram loss P_a^{1/6} or the floor-bin count. I found no available input that does either.

## 3. Route C (screened, stopped): Euler's idoneal numbers

Weinberger proved the 65-term list complete under GRH. With [QRH] (no real zero in (7/8, 1)), I derived two things:

- The classical positivity argument with ζ(s)L(s,χ), shifting the contour far left, gives an explicit L(1,χ) ≫ q^{−1/16−ε}.
- n idoneal implies (−n/p) ≠ 1 for every odd prime p < √n with p ∤ n: a reduced form (p, b, c) with p < √n can be ambiguous only if p | 4n.

Together these give an explicit N₀ beyond which no idoneal numbers exist. N₀ is astronomically large (≈ e^{170} via the least-split-prime route), or depends on unoptimized constants (via the L(1,χ) route). Closing the gap would require a pseudosquare-type sieve computation far beyond this pass. The problem is also not on MathDB's high-importance list. **Stopped:** the remaining step is an explicit constant computation plus a large verified sieve search, which I did not do.

## 4. Route B: the main result

### 4.1 Statement

For a prime p ∤ a, write i_p(a) = (p−1)/ord_p(a) for the index of ⟨a mod p⟩ in F_p^×.

> **Theorem B (bounded index for a positive proportion of primes).** Let c\* = log(1/(1−δ₀)) with δ₀ = 10⁻⁶; numerically c\* > 10⁻⁶. Let 𝒜 be a finite set of integers with |a| ≥ 2 for every a ∈ 𝒜, and let η > 0. Then there are B = B(𝒜, η) and x₀ = x₀(𝒜, η) such that, for every real x ≥ x₀,
>
>   #{ x < p ≤ 2x : p ∤ ∏_{a∈𝒜} a, and i_p(a) ≤ B for every a ∈ 𝒜 } ≥ (c\* − η)(π(2x) − π(x)).

> **Corollary B1 (average order over prime moduli, under the accepted corpus).** For every integer a with |a| ≥ 2,
>
>   Σ_{p≤x, p∤a} ord_p(a) ≍_a x²/log x,  and  liminf_{x→∞} π(x)⁻¹ Σ_{p≤x, p∤a} ord_p(a)/(p−1) > 0.

The upper bound in B1 is trivial (ord_p(a) ≤ p − 1). For the lower bound, apply Theorem B on (x/2, x] with 𝒜 = {a} and η = c\*/2: the good primes contribute at least (c\*/2B)(x/2 − 1)(π(x) − π(x/2)) ≫ x²/log x.

Quantifier order: 𝒜 and η are fixed first; then θ, Y₀ and B are chosen; then x → ∞. The density constant c\* is absolute, independent of 𝒜, and only B depends on 𝒜.

### 4.2 Proof

Fix 𝒜 and η, and put k = |𝒜| and L = log x.

**Parameter choices.**
- θ ∈ (0, δ₀) with log(1/(1−θ)) > c\* − η/4.
- Y₀ ≥ max_{a∈𝒜} q₀(a) with 2kC/Y₀ < η/4, where C = max_a C_a is the constant of (S).
- For each prime q ≤ Y₀, an integer k_q ≥ 2 with Σ_{q≤Y₀} 1/φ(q^{k_q}) < η/4.
- B = ∏_{q≤Y₀} q^{k_q − 1}.

**Step 1 (the PD event).** Let G = {x < p ≤ 2x : P⁺(p−1) > x^{1−θ}}. Pick 0 < η′ < θ/4 and a continuous F with 1_{[1−θ+2η′, 1]} ≤ F ≤ 1_{(1−θ+η′, 1]}.

For x < p ≤ 2x and x large, V₁(p) > 1 − θ + η′ implies P⁺(p−1) > (p−1)^{1−θ+η′} > x^{1−θ}. Applying [PD] with k = 1 at 2x and at x, and subtracting (both limits exist, and π(2x) − π(x) ≍ π(x)), gives

  #G ≥ (E F(L₁) − o(1))(π(2x) − π(x)).

For PD(1), L₁ has density 1/t on [1/2, 1]. So E F(L₁) ≥ P(L₁ ≥ 1 − θ + 2η′) = log(1/(1 − θ + 2η′)). Let η′ → 0 to get #G ≥ (log(1/(1−θ)) − η/4 − o(1))(π(2x) − π(x)).

**Step 2 (structure).** For p ∈ G write p − 1 = mQ, where Q = P⁺(p−1) > x^{1−θ} is prime and m < 2x^θ. Then Q ∤ m, since otherwise Q ≤ m < 2x^θ < x^{1−θ}. Fix a ∈ 𝒜 with p ∤ a, and let q be a prime dividing i_p(a). Then q | p − 1, so q = Q or q | m. In the second case, either q ≤ Y₀ or Y₀ < q < 2x^θ.

**Step 3 (three exceptional sets).**
- *E₁(a)*: p ∈ G with Q | i_p(a). Then ord_p(a) | m, so p divides a^j − 1 for some 1 ≤ j < 2x^θ, and a^j ≠ 1 because |a| ≥ 2. A prime p > x dividing |a^j − 1| ≤ (|a|+1)^j contributes at least L to its logarithm. So #E₁(a) ≤ Σ_{j<2x^θ} j log(|a|+1)/L ≪_a x^{2θ}/L = o(x/L).
- *E₂(a)*: primes in (x, 2x] that split completely in K_q for some prime Y₀ < q < 2x^θ. If q | i_p(a) with p ∤ aq, then Lemma `alg:splitting-test` shows p splits completely in K_q; the at most two primes p dividing q are negligible. By (S),

  #E₂(a) ≤ C Σ_{q>Y₀} x/(q(q−1)L) + C Σ_{q<2x^θ} x^{1−δ₀} log(2q)/L ≤ 2C x/(Y₀ L) + O(x^{1−δ₀+θ}).

  The last term is o(x/L) because θ < δ₀.
- *E₃*: primes with q^{k_q} | p − 1 for some q ≤ Y₀. By the union bound and the prime number theorem for the finitely many fixed moduli q^{k_q}, #E₃ ≤ (Σ_q 1/φ(q^{k_q}) + o(1))(π(2x) − π(x)).

**Step 4 (conclusion).** Take p ∈ G outside E₃ and outside E₁(a) ∪ E₂(a) for every a ∈ 𝒜, with p ∤ ∏a. By Step 2, every prime divisor q of i_p(a) satisfies q ≤ Y₀. Moreover v_q(i_p(a)) ≤ v_q(p−1) ≤ k_q − 1. Hence i_p(a) | B, so i_p(a) ≤ B.

Using π(2x) − π(x) ~ x/L, the count of such p is at least (c\* − η/4 − η/4 − 2kC/Y₀ − η/4 − o(1))(π(2x) − π(x)), which is at least (c\* − η)(π(2x) − π(x)) for large x. ∎

### 4.3 Validation and adversarial checks

- **Where each input is essential.**
  - The PD event G is a Chen/twin-prime-type event (p − 1 = mQ with m < x^θ) for an exponent 1 − θ > 1 − 10⁻⁶. The best pre-corpus positive-proportion exponent was about 0.668 (Fouvry); Baker–Harman's 0.677 is for infinitely many primes. So the parity barrier is overcome only by [PD].
  - The range (log x)^C < q ≤ x^θ needs a Chebotarev error that stays uniform in q. Lagarias–Odlyzko/Siegel-type regions cannot supply it there; [HZ] makes the error x^{1−δ₀}. Removing either input breaks the proof.
- **No circularity.** [PD] and [HZ] are separate upstream theorems. Neither is derived here from the conclusion.
- **Constant and edge-case checks.**
  - (S) is used for q up to 2x^θ ≤ x, where log(2q)/L ≤ 2. The constant of `spl:smooth-estimate` is stated, and verified in its proof, to be independent of the field.
  - Prime powers need only the trivial inclusion {q^k | i_p} ⊆ {q^k | p − 1}.
  - Squares and perfect powers are allowed: the index is then bounded but not 1. a = −1 and a = ±1 are excluded by |a| ≥ 2, which is also used to get a^j ≠ 1.
- **Finite sanity test.** `frontier/experiments/i02_arithmetic_index_decomposition_check.py` checks the deterministic implication of Steps 2–4 for a ∈ {2, −3, 12} up to 4×10⁵, with θ = 0.35 and Y₀ = 30: every prime in G outside the exceptional sets has every prime factor of its index ≤ Y₀ and the index ≤ B. There were zero violations. This checks only the finite logic, not any asymptotic or density claim.

### 4.4 Novelty, limits, and the exact obstruction to Artin

**Prior art.** Kurlberg–Pomerance (Algebra & Number Theory 7 (2013)) state that the lower bound in their average-order theorem uses GRH. Unconditional versions exist only after also averaging over the base (Luca–Shparlinski; arXiv 1509.03768). Goldmakher–Martin–Péringuey (arXiv 2502.19601, §8) give unconditional **upper** bounds for densities of small index, and unconditional lower bounds only for the expected number of prime factors of the index. I found no unconditional positive-proportion bounded-index theorem for a fixed base. Within the corpus, the primitive-root paper proves ≫ x/log²x primes with index 1, and its companion gives a conditional result for simultaneous primitive roots; neither states Theorem B. The literature search was targeted, not exhaustive.

**Significance, honestly.** Theorem B upgrades the corpus count from x/log²x to a positive proportion, at the price of bounded rather than trivial index, and with tiny density (about 10⁻⁶). Corollary B1 gives the GRH-predicted order of magnitude for Arnold's average-order problem, unconditionally given the corpus. Neither is Artin's conjecture.

**Exact obstruction to index 1 at positive density.** The small primes q ≤ Y₀ require the joint distribution of
- the Frobenius of p in the fixed field Q(μ_N, a^{1/N}), and
- the PD event for p − 1.

[PD] is stated only for all primes, not for primes in a progression or Chebotarev class. With a progression version — liminf P(G | p ≡ u mod M) > 0 for fixed admissible M, u — the argument in §4.2 gives **positive lower density of primes with primitive root a**, for every admissible a. The reason is that E₂ can be bounded inside the progression via ζ_{K_q(μ_M)}, which is covered by the same descent. This would be a conditional reduction, and I do not claim it.

I also tried deriving it with upper-bound sieves. That fails by a factor of at least 2, because of the parity loss in twin-type upper bounds against the q = 2 density of 1/2.

## 5. Files

- Report: `frontier/iterations/i02-arithmetic.md` (this file).
- Sources: `frontier/sources/i02_arithmetic/` (59 pinned files and `manifest-artin.json` with blob checks).
- Experiments:
  - `frontier/experiments/i02_arithmetic_qrh_geometry.py`: exact geometry identity, slack scan, and ceiling.
  - `frontier/experiments/i02_arithmetic_index_decomposition_check.py`: finite logic check.
- Nothing was staged or committed, and no shared index was edited.
