# SUMMARY — pi-weighted-clt-source-hypothesis-r313 (MathDB 368302, arXiv:2505.03210)

Checkpoint type: source-first qualification + coefficient audit + decisive calculations.
Verdict: record faithful; r311's proposed refutation mechanism FAILS at its first step
(mis-audited coefficient); the conjecture reduces to a sharp, checkable weight condition
(∫w̄² = 3) plus a classical-but-unwritten uniform remainder estimate. Strong numerical
evidence the conjecture is TRUE for an explicit admissible weight; no complete proof
delivered; residuals precisely stated. NOT a claim of acceptance, novelty clearance, or
proof. Counts unchanged (9 additional / 39 total).

## 1. Exact source statement and quantifiers

Primary body read this session (v3, 23 Jan 2026; also published Math. Annalen 294, Paper
18, Feb 2026). Conjecture 1.1, verbatim in primary/source-excerpt.md:

Quantifier order: ∃ w̄ ∈ C_0^∞([0,1]) with ∫₀¹w̄ = 1; ∃ universal constant C₃ > 0; such
that FOR ALL iid centered X with EX₁=0, EX₁²=1, EX₁³=0, E|X₁|⁵<∞, FOR ALL N,
sup_{x∈ℝ} |P((1/√Ā_N)Σ_{n=1}^{N-1}√(w̄(n/N)) Xₙ ≤ x) − 𝒢(x)| ≤ C₃ E|X₁|⁵ / N^{3/2},
where Ā_N = Σ_{n=0}^{N-1} w̄(n/N) and
𝒢(x) = Φ(x) − (E|X₁|⁴−3)/(8√(2π) N) (x³−3x) e^{−x²/2}.

Scope notes fixed by the source itself: (a) the sum runs n=1..N−1 while Ā_N sums
n=0..N−1; (b) √w̄ forces w̄(n/N) ≥ 0 on the grid (the source's exemplar w_{p,q} > 0 on
(0,1)); (c) the source's C_0^∞([0,1]) means smooth and flat at the endpoints — its own
exemplar satisfies w̄(0)=w̄(1)=0 to infinite order. 𝒢 depends on the law of X only
through κ₄ := EX⁴ − 3 (E|X|⁴ = EX⁴). The record mathdb-368302.json is a faithful
transcription (checked field by field); the triage lane's "Cauchy–Schwarz/Edgeworth
objection is unverified" flag was warranted — see §3.

## 2. The relevant cumulant identity (audited; exact)

Let b_n = √(w̄(n/N)/Ā_N), S_N = Σ_{n=1}^{N-1} b_n X_n. Since w̄(0)=0, Var(S_N) =
Σ_{n=1}^{N-1} w̄(n/N)/Ā_N = 1 EXACTLY. Cumulants: κ_j(S_N) = κ_j(X)·Σ b_n^j. With
EX³=0: κ₃(S_N)=0. Euler–Maclaurin with flat endpoints (bounded variation suffices):
Σ_{n=1}^{N-1} w̄(n/N)² = N∫₀¹w̄² + O(1), Ā_N = N + O(1), so
  Σ b_n⁴ = c_w/N + O(N^{-2}),  c_w := ∫₀¹ w̄² dx,  Σ b_n⁵ = Θ(N^{-3/2}).
Characteristic-function inversion (log φ_{S_N}(t) = −t²/2 + (κ₄ c_w/24N) t⁴ + O(N^{-2}t⁶)
in the Taylor regime; standard smoothing inequality for the tail) gives the uniform
order-N^{-1} expansion
  F_N(x) = Φ(x) − (κ₄ c_w / 24N) φ(x) H₃(x) + remainder,
with φ H₃ = (x³−3x)e^{−x²/2}/√(2π). Numerical cross-check (X_ε witness, §5): measured
D_vs_Φ·N → 0.0692 vs predicted κ₄c_wM₃/24 = 0.0688 (M₃ = sup|φH₃| = 0.55059 at
x=±0.7420). The identity and the 1/24 coefficient are confirmed.

## 3. The r311 proposal's obstruction FAILS (documented failure)

r311 claimed: Cauchy–Schwarz gives c_w ≥ 1 with equality iff w̄ const, hence "the
coefficient 1 in 𝒢 is unattainable", so Rademacher refutes. This mis-audits 𝒢: its H₃φ
coefficient is κ₄/(8N) = κ₄·(3/24)/N, NOT κ₄·(1/24)·1/N·3... precisely, the conjecture's
𝒢 corresponds to c_w = 3, not c_w = 1. c_w = 3 is NOT forbidden: it only requires
∫w̄² = 3 with ∫w̄ = 1 (a plateau of height 3 on measure 1/3). The source's 1/8 is
exactly the typical-spherical-weight value Σθ⁴ → 3/N ([Bob20]), so it is deliberately
chosen. Consequently the proposed Rademacher refutation route is dead as stated, and
with it the "coefficient mismatch" mechanism. No credit is claimable via that route.

## 4. What the conjecture reduces to (sharp form)

For a FIXED admissible w̄ (w̄ ≥ 0, flat endpoints, ∫w̄=1): the conjectured bound for all
admissible X holds iff
  (A) c_w = ∫₀¹w̄² = 3 exactly, and
  (B) the uniform remainder after the order-N^{-1} term is O(E|X|⁵ N^{-3/2}) with an
      X-independent constant (the κ₅-term −(κ₅/120)∫w̄^{5/2} N^{-3/2} φH₄ is Θ(N^{-3/2})
      and is absorbed by C₃; for the constructed w̄ ∫w̄^{5/2} = 5.4847 < ∞).
Necessity of (A): if c_w ≠ 3, take X_ε (§5) with κ₄ = ε ≠ 0: the mismatch term
(κ₄/24N)(c_w−3)φH₃ is Θ(1/N) ≫ N^{-3/2}. Sufficiency reduces to (B), a classical
weighted-sum Edgeworth remainder estimate — long but ordinary; NOT written here.

## 5. Explicit weight and decisive calculations (analysis/decisive_results.json)

Construction: w̄_s(x) = exp(−s/(x(1−x)))/Z_s on (0,1), 0 at endpoints; w̄_s > 0, flat at
0,1, ∫w̄_s = 1; c_w(s) strictly increasing 1 → ∞, so by IVT ∃s* with c_w = 3 EXACTLY.
Computed s* = 2.99481358477531 (bracket width 5e-16; c_w(s*) = 3 ± 5e-16; Simpson
convergence-verified). Collision-free/nonlattice weights: for each sign vector the
relation Σ±b_n = 0 is a non-degenerate real-analytic equation in a second tuning
parameter; the bad parameter set is countable, so a w̄ with c_w = 3 AND all 2^{N-1}
sign sums distinct exists (residual: write this cleanly; for algebraic s one can
alternatively invoke Lindemann–Weierstrass on b_n ∝ e^{−s u_n/2}, u_n ∈ ℚ distinct).

Witnesses and exact/high-precision tests (guard: 512MiB AS, ≤102 MB peak group RSS,
4.8 s wall):
- X_ε: density φ(x)(1+H₄(x)/24) — EX=0, EX²=1, EX³=0, κ₄=+1 (since ∫x²H₄φ=0,
  ∫x⁴H₄φ=24), all moments finite, φ_X(t) = e^{−t²/2}(1+t⁴/24). Gil–Pelaez CDF, N =
  60/120/240: sup|F_N − 𝒢| · N = 1.81e-3, 9.15e-4, 4.59e-4 → 0 like ~N^{-2}:
  the N^{-1} term is cancelled (c_w=3) and D ≤ 0.014·N^{-3/2} empirically.
  Against plain Φ: D·N → 0.0692 = predicted κ₄c_wM₃/24 ✓ (audit confirmation).
- Rademacher X (lattice, κ₄=−2, E|ε|⁵=1): EXACT 2^{N-1}-atom PMF, N = 8..23:
  c_w=3 weight: D·N = 0.572, 0.437, 0.203, 0.085, 0.054 → 0 (no jump obstruction:
  with distinct b_n the atoms are 2^{-(N-1)}); c_w=1.3 weight: D·N → 0.082 →
  asymptote |c_w−3|·|κ₄|M₃/24 = 0.0780 (predicted) ✓. Lattice X does NOT obstruct:
  the sum Σ b_n ε_n is nonlattice with exponentially small atoms for collision-free
  profiles; tail decay Π|cos(b_n t)| ≤ e^{−cN} holds because only o(N) indices satisfy
  |b_n t| < δ or dist(b_n t, πℤ) < ε₀ (top-cluster count o(N), endpoint count
  N·(log t)^{-1/p} = o(N)).
No numerical evidence is treated as proof; these are decisive consistency checks of the
audited identities and of the absence of the proposed obstructions.

## 6. Bounded prior coverage (explicitly incomplete)

- Source status: conjecture stated as open in v1 (May 2025), v2, v3 (Jan 2026) and in
  the published Math. Annalen version (Feb 2026). The source itself says "we do not
  know whether our weights ... belong to such almost full measure sets".
- Adjacent prior art located (NOT read in full): [KS12] (typical θ ∈ S^{N-1}, O(1/N),
  fourth moment); [Bob20, Thm 5.1.1] (almost-full-measure θ ∈ S^{N-1}, O(N^{-3/2}),
  fifth moment, corrected normal with coefficient 3/24); Bobkov, "Khinchine's theorem
  and Edgeworth approximations for weighted sums" (Ann. Appl. Probab./AOS, deterministic
  weights, Diophantine metric conditions — closest known prior art for deterministic
  profiles; scope comparison NOT performed); arXiv:2312.14696 (multivariate extension of
  Bobkov 2020); arXiv:2011.09237 (Poincaré-inequality approach, random weights).
- No source visibly resolves the existence of a deterministic C_0^∞ profile with the
  exact quantifiers/𝒢 above. This is a bounded search (one query set), not a registry
  sweep; MathDB access is under the 429 hold so no MathDB requests were made, and cached
  open labels are not novelty evidence.

## 7. Residuals (what a complete resolution still needs)

R1. Write the uniform remainder theorem (B): for S_N = Σ b_n X_n with max b_n = O(N^{-1/2}),
    Σ b_n⁵ = Θ(N^{-3/2}), nonlattice (collision-free profile), covering ALL admissible X
    (nonlattice via limsup_{|t|→∞}|φ_X| < 1 — provable from the symmetrization
    X−X′ argument; lattice via the product-decay count in §5; singular continuous
    included), remainder O(E|X|⁵ N^{-3/2}) with X-independent constant, uniform in x.
    Tools: smoothing (Sadikova/Esseen-type lemma — exact statement to be pinned),
    cumulant Taylor bound |log φ_X(u) + u²/2 − κ₄u⁴/24| ≤ C E min(|uX|⁵, (uX)²) with the
    min-truncation handling large E|X|⁵ uniformly, Euler–Maclaurin (flat endpoints not
    needed beyond bounded variation), product-decay lemma. Estimated 8–15 pages.
R2. Rigorous existence write-up for w̄ with c_w = 3 exactly + collision-free b_n
    (two-parameter IVT + countable-bad-set argument, or LW for algebraic parameters),
    including w̄(0)=0 (exact variance 1) and w̄ ≥ 0.
R3. Verify small-N absorbability: sup_{N ≤ N₀}|F_N − 𝒢| ≤ C·E|X|⁵ with X-independent C
    (Berry–Esseen for weighted sums + |κ₄| ≤ C E|X|⁵), so a single C₃ covers all N.
R4. Optional: independent re-derivation of the κ₅ absorption constant and of ∫w̄^{5/2}
    bounds for the constructed family.

## 8. Strongest classical-adaptation objection (answered)

"Is this just the classical Edgeworth/KS12/Bobkov machinery?" No: those give typical or
measure-theoretic statements over random θ ∈ S^{N-1}; the conjecture demands ONE
deterministic smooth profile working for ALL admissible X simultaneously, with 𝒢's
coefficient fixed at 3/24·κ₄. The content is (A)+(B) above; (A) is a genuine design
constraint (c_w = 3 exactly) that no generic-weight theorem delivers, and (B) for
lattice X with deterministic profile weights is not in the cited literature in this
form. Conversely it is not routine: (B) is a real uniform remainder estimate. A positive
resolution would be a small substantive certificate (explicit w̄ + remainder theorem);
a negative one is currently NOT supported by any obstruction found — every classical
obstruction route (lattice jumps, commensurable weights, κ₅ terms, variance mismatch,
endpoint mass) was checked and fails for the constructed profile.

## 9. Recommendation

PARK as "reduced-and-verified, proof-unwritten": the lane's assigned hypothesis is
source-qualified, the r311 mechanism is dead (documented), the decisive reduction and
numerics are complete, and the remaining work is a single bounded writing task (R1+R2,
~2 sessions). Not recommended for immediate re-delegation as a fresh hypothesis; if
reopened, assign exactly R1+R2+R3 with the artifacts in this lane as frozen inputs.
No acceptance claim; counts remain 9 additional / 39 total / next40.

## 10. Artifacts (hash-bound in MANIFEST.json; manifest excludes itself and receipt)

- inputs/mathdb-368302.json (frozen record; sha256 40694539…)
- inputs/r311-proposal-368302.json (frozen r311 proposal entry)
- inputs/hashes.txt
- primary/source-excerpt.md (verbatim statement, retrieval provenance, fidelity check)
- analysis/decisive_calcs.py, analysis/decisive_results.json
- SUMMARY.md (this file)
