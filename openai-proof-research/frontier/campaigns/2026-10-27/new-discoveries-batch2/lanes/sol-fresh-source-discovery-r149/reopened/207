# Independent adversarial review — parent-sendov proposed C*-algebraic Sendov counterexample

Reviewer: pi-sendov-preliminary-review (solo, no children). Date: 2026-10-26.
Reviewed: `NEW/lanes/parent-sendov/PROOF.md` and bound checks/sources at commit
`3c62435432014fc62be9482d0aaf2fb44585cbd3`. Provenance binding **verified**:
the four lane files at that commit are byte-identical (git `git show` sha256) to the
working-tree files, and their sha256 values match `provenance.json` exactly.

## Verdicts (per gate)

| Gate | Verdict |
|---|---|
| SOURCE (exact statement, live state) | **PASS** |
| MATH (independent full derivation + own checker) | **PASS** |
| NOVELTY (serious bounded search) | **PASS** (with stated access limits) |
| ELIGIBILITY (exact-statement fit; 353908 scoping) | **PASS** |
| Overall | **Accept as proposed refutation candidate** (credit0, no priority claim, formalization pending — no formal PASS claimed) |

Decisive objections: **none found.**

---

## 1. SOURCE gate — PASS

Independently fetched and hashed both PDFs (both sha256 match `provenance.json`),
rendered the relevant pages to images and **visually inspected** them (files in `evidence/`):

- `krishna-published-p59.png` — Theorem 1 (Gauss–Lucas) with **Equation (1)**
  `z = Σ ω_{z_j} a_j, Σ ω_{z_j} = 1` (positive `ω ∈ A`), and Definition 2:
  `D*(a,r) := {z ∈ A : (z−a)(z−a)* ≤ √r·1}`.
- `krishna-published-p60.png` — **Conjecture 3** (C*-algebraic Sendov) and
  **Conjecture 4** (fully-split-derivative variant, no convex-weight hypothesis),
  exactly as the proposal states; degree-2 Theorem 2 only.
- `preprint-2203.06916-p3-...png` — Definition 2.3, Conjecture 2.4, **Conjecture 2.5**
  (= published Conjecture 3 = MathDB 353909), Theorem 2.6.

Live MathDB (fetched 2026-10-26, HTML saved in `evidence/`):
- **353909**: `open`, Solutions 0, no comments/tries, progress "Nothing recorded yet".
- **353908**: `open`, Solutions 0.

Hypothesis-fit against the exact published text (n = 3):
- a_j ∈ D*(0,1): norms 9/10, 27/40, 27/40 — strictly inside. ✔
- "p′ admits roots b₁,…,b_{n−1} ∈ D*(0,1)": exactly two roots B±, both of norm
  ≤ 0.3(1+√43/4) ≈ 0.7918 < 1. ✔
- "each b_k can be written in the form of Equation (1)": explicit strictly positive
  continuous ω_j = r_j/Σr_i, r_j = |B−a_j|^{-2}, constructed below. ✔
- Conclusion fails for a₀: **both** zeros of p′ have sup-distance 3/5+3√43/40 ≈ 1.0918 > 1. ✔
- Conjecture 4 hypotheses also hold (p′ completely factors) and its conclusion fails
  identically — the Conj-4 refutation is free with the Conj-3 one.

**Findings (non-blocking):**
1. **√r nuance.** The published/preprint Definition uses `(z−a)(z−a)* ≤ √r·1` — the
   text-layer extraction in the parent's `.txt` files drops the radical. Immaterial at
   r = 1 (both readings give the pointwise `|z(t)−a(t)| ≤ 1` condition), but the
   formalization must state the definition exactly.
2. **Commutativity is silently used** in "P′(B)=0 and P(B) invertible ⟹
   Σ_j (B−a_j)^{-1} = 0" (in a noncommutative algebra the reordering identity fails).
   Valid here — A = C([0,1],C) is commutative. The source's own Theorem 1 is likewise
   stated only for commutative A, so there is no source gap; just make it explicit when
   formalizing.

## 2. MATH gate — PASS

I wrote an independent checker from scratch (`evidence/independent_check.py`,
result in `independent-check-result.json`) with a different structure from the
parent's (generic-variables symbolic identities, exact case analysis, 2001-point
80-dps scan vs. parent's 401-point 70-dps). All checks pass:

- **Exact identities:** deleted sum = formal derivative; `P′(z) = 3(z−B⁺)(z−B⁻)` as a
  polynomial identity mod `q² − 1 − 27/16·u²`; `q(t)² = 1 + 27/16·u(t)²` with
  `|q²| ∈ [11/16, 43/16]` exactly, so `q ≠ 0` pointwise and `|q| ≤ √43/4 < 2`;
  hence `‖B±‖ ≤ 0.3(1+√43/4) < 0.8 < 1` (max over scan: 0.79180788…).
- **Every critical element classified.** If P′(b) = 0, pointwise
  `3(b−B⁺)(b−B⁻) = 0`, so b(t) ∈ {B⁺(t), B⁻(t)}; `f = (3b/ρ−1)/q` is continuous with
  `f² = 1` on the **connected** interval [0,1], hence constant: b = B⁺ or b = B⁻.
  This step is essential and correct — C([0,1],C) has zero divisors, so the algebraic
  factorization alone does not classify; connectedness does. (On a disconnected base
  the example would fail — the parent's choice is load-bearing, not incidental.)
- **B never equals any a_j** — all six cases ruled out **exactly**: B± = a₁ or a₂ force
  `u = ±4/3`, contradicting |u| = 1; B± = a₀ forces |q| = 2, contradicting
  |q| ≤ √43/4 < 2. Hence B−a_j invertible (nowhere zero continuous), consistent with
  all three scalar roots of each fiber polynomial being simple (pairwise differences
  ρ(1−su), ρ(1+su), 2ρsu all pointwise nonzero).
- **Convex weights:** in the commutative algebra
  P′(B) = P(B)·Σ_j(B−a_j)^{-1} = 0 ⟹ Σ(B−a_j)^{-1} = 0; conjugating gives
  Σ r_j(B−a_j) = 0, so B = Σ ω_j a_j with ω_j = r_j/Σr_i > 0, Σω_j = 1 — exactly the
  source's own construction ((z−a_j)(z−a_j)*)^{-1} normalized. Scan: weight residual
  < 4.3e-81, min weight 2.92e-3 > 0.
- **Endpoint distances exact:** `|a₀ − B⁻|(0) = |a₀ − B⁺|(1) = 3/5 + 3√43/40 ≈ 1.0918`,
  an exact algebraic number > 21/20 > 1; the other branch at each endpoint is at
  distance ≈ 0.1082 < 1.
- **Numerics:** 2001 points, 80 dps, max identity residual 1.7e-80.

**Classical Sendov not contradicted:** each fiber P_t is a scalar cubic with all roots
in |z| ≤ 0.9; classical Sendov supplies a per-fiber near critical point, but the near
branch switches B⁺ → B⁻ across [0,1] and no single continuous element can follow it.
No conflict with the 2026 proof of the classical conjecture (consistent with Tao's
Aug-2026 "digestion" post and the Lean `teorth/sendov` formalization).

## 3. NOVELTY gate — PASS (bounded, honest limits)

Independently executed probes:
- **OpenAlex** (`W4226164614`): cited_by_count = 4; **all four are Krishna's own 2022
  "C*-algebraic Bieberbach…" preprint** (OSF / Autodidact / Preprints.org / SSRN
  duplicates). No external citation; no resolution cited anywhere.
- **arXiv full abstract sweep** `abs:Sendov` (37 entries, export API): only 2203.06916
  is operator-algebraic; **no counterexample or disproof of any C*-algebraic Sendov
  variant**. Follow-ups by the author are Schoenberg (2206.06653) and Smale
  mean-value (2206.08154), degree-2 only.
- **MathDB live**: both entries open, zero solutions/comments (see §1).
- **pubdb sendov tag** (5 entries): no counterexamples; classical Sendov recently
  *proved* (Mazur), consistent with the proposal's framing.
- **Subsumption check**: no known "no continuous selection of critical points" or
  monodromy-obstruction result in the Sendov setting was found; the closest literature
  (continuous selections of polynomial functions, arXiv 2007.03952) does not touch
  Sendov proximity. No immediately subsuming negative result located.

As the proposal itself states, the branch-switching/monodromy mechanism is classical
topology and receives **no novelty credit**; the contribution is the complete
instantiation satisfying *all* source hypotheses (strict interior roots, fully split
derivative, genuine positive A-valued convex weights, uniform >1 failure for every
critical element).

**Access limits (honest):** Google Scholar and Semantic Scholar unreachable (403/429);
zbMATH/MathSciNet not directly queried; Russian-language venues not searched; MathDB
per-entry version history not enumerated (HTML shows no edits; "Never refreshed").
Novelty verdict is bounded by these limits — no absolute priority claim is made.

## 4. ELIGIBILITY gate — PASS

- Target is MathDB **353909** exactly, whose literal statement has **no** density or
  commutativity hypothesis; the example lives in the unital C*-algebra C([0,1],C).
  Refutation of the literal statement is valid.
- **353908 scoping:** I independently verified G(C([0,1],C)) **is** dense (elementary
  patching: on each component of {|f| < ε} replace f by a path in the annulus
  {ε/2 ≤ |w| ≤ ε} matching the boundary values). So the same example mathematically
  refutes the commutative version too — but I concur with the parent's decision **not**
  to claim formal 353908 now: density is an additional unformalized obligation and does
  not block 353909.
- One proposed refutation (Conj 3 and Conj 4 fall together); credit 0; no counts touched.

## Deliverables in this lane

- `review.md` (this file)
- `provenance.json` (verdicts, hashes, source receipts)
- `evidence/independent_check.py`, `evidence/independent-check-result.json`
- `evidence/krishna-published-p59.png`, `evidence/krishna-published-p60.png`
- `evidence/preprint-2203.06916-p3-def2.3-conj2.4-2.5.png`
- `evidence/mathdb353909.html`, `evidence/mathdb353908.html` (live fetches 2026-10-26)

No files outside this lane were created or modified; nothing staged or committed.
