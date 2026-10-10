# Iteration 2, arithmetic lane: quasi-RH self-improvement and a combined arithmetic mechanism

Date: 2026-10-08. Upstream: OpenAI/math at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Upstream theorem statements are accepted as true, as instructed; their proofs were not audited. The independently validated main deduction is recorded in R004; the stopped side proposals retain the limitations below.

**Parent integration status (2026-10-08): repaired B/B1 accepted as deductions, novelty unverified.** The independent [round-2 audit](../reviews/i02-arithmetic-r2.md) passes the corrected proof. [R004](../findings/R004-simultaneous-bounded-index.md) is the authoritative theorem, complete proof, validation and scope record. It preserves B(A,η), fixes the exceptional-set bound and strict error margins, and handles the empty set. The original progression-only Artin argument was incomplete and is withdrawn. Route A/C below remain stopped proposals with the review's limitations; they are not validated global optimization or idoneal-classification theorems.

## Outcome in one paragraph

**Route A** tried to improve the quasi-RH half-plane Re s > 7/8. It is stopped, with an exact reason. The 7/8 boundary is the explicit function σ₀ = 11/12 − ℓ/4 of the manuscript's prime-slot length ℓ. The binding high-side certificate leaves only about 1.1×10⁻⁴ of slack. A coarse numerical re-tuning found gains of about 4×10⁻⁵; it did not certify a global maximum. A tempting bootstrap, feeding β\* ≤ 7/8 back into Part II, does not loosen that binding case. The retained formulas with stipulated ideal row counts give a formal 13/15 floor, not a universal obstruction.

**Route B** combines the accepted PD(p−1) law and uniform Hecke zero-free region to prove simultaneous bounded residual index on a positive proportion of primes. For every finite set A of integer bases |a|≥2 and every η>0, one fixed B(A,η) works on at least a c*−η proportion in every sufficiently large dyadic interval, where c*=−log(1−10⁻⁶). The prime-average multiplicative order consequently has the expected order of magnitude. The complete corrected statement is [R004](../findings/R004-simultaneous-bounded-index.md).

No exact duplicate was located in the targeted literature screen, but worldwide novelty and a nonroutine new mechanism are unestablished. This is neither Artin's conjecture nor Arnold's full integer-modulus problem, and it does not close the frontier objective.

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

A coarse numerical scan, not a continuous global optimization certificate, over δ ∈ [1/50, 5/6] and x ∈ [0, 1/2] gives:

- At the paper's geometry, the worst case has −E ≈ 2.28×10⁻⁴. The paper's certified bound is 49/440640 ≈ 1.11×10⁻⁴. The binding point is interior: δ ≈ 0.39, x = 1/2.
- The largest admissible ℓ is ≈ 0.166838, giving σ₀ ≈ 0.874957, a gain of about **4×10⁻⁵**. Varying b does not help: the best value found was b ≈ 0.1225, with the same gain.

This optimistic gain also ignores constraints that are hard-coded at 7/8: H_η is holomorphic only on Re s > 7/8, and `lem:bin-contour-accounting` requires σ₀ ∈ [7/8, 1). Even the 4×10⁻⁵ would need those rechecked. It is not a substantive theorem, and I did not pursue it.

### 2.3 The tempting bootstrap is invalid

Part II uses Part I (β\* ≤ 11/12) only through Δ ≤ 1/24, the bin ceiling δ ≤ κ ≤ 5/6, and the capacity κ = 2β\* − 1. It is tempting to rerun Part II with β\* ≤ 7/8 as input, which would give "α = 3/4".

But α = 5/6 in `prop:detector-counts` is **not** the bin ceiling. It is "the fixed slope from sixth-power amplification": e(r) = max{1, (1+5r)/6} (`eq:no-slot-inverse-count`). The binding certificate point δ ≈ 0.39 lies far below any ceiling. A smaller κ only removes the +Δ/4 capacity loss, and that loss is already absorbed by the Δ-margin. So feeding 7/8 back does not move the boundary.

### 2.4 The architecture's ceiling

Suppose the row counts were density-hypothesis quality: R = 1 − δ and q = δ/2. Then E(h) = −1/4 + 5ℓ/4 + b/6 − bδ/2. At small δ, which is the floor bin where every row is counted, this forces ℓ < 1/5 − 2b/15, hence σ₀ ≥ 13/15.

Thus 13/15 is a formal floor within these retained formulas and stipulated ideal counts, not a universal impossibility theorem for every variant of the method. Escaping this calculation requires changing a retained estimate or parameter restriction. **Stopping point:** any real improvement must change the low estimate's Gram loss P_a^{1/6} or the floor-bin count. I found no available input that does either.

## 3. Route C (screened, stopped): Euler's idoneal numbers

Weinberger proved the 65-term list complete under GRH. With [QRH] (no real zero in (7/8, 1)), I derived two things:

- The classical positivity argument with ζ(s)L(s,χ), shifting the contour far left, gives an explicit L(1,χ) ≫ q^{−1/16−ε}.
- n idoneal implies (−n/p) ≠ 1 for every odd prime p < √n with p ∤ n: a reduced form (p, b, c) with p < √n can be ambiguous only if p | 4n.

These were proposed routes to a finite cutoff, not a certified computation of one. The independent review did not validate the claimed L(1,χ) constant, the tentative e^{170} scale, or a complete cutoff/search. It did justify the local reduced-form obstruction under the standard class-group characterization. **Stopped:** no idoneal classification is established; explicit constants and a verified exhaustive search remain missing.

## 4. Route B: corrected disposition

The complete repaired theorem, corollary and proof are in [R004](../findings/R004-simultaneous-bounded-index.md); the detailed independent field/uniformity audit and repaired conditional Artin reduction are in [the round-2 review](../reviews/i02-arithmetic-r2.md).

Corrections to the original discovery draft:

- The density is c*−η with B depending on η, not c* for one B(A).
- The small-prime-power union has an upper bound by the sum of progression densities, not equality. Strict error margins and the empty-set case are now explicit.
- No p=q exception occurs for an index divisor q, since q divides p−1.
- Baker–Harman's 0.677 input already yields a positive proportion, as Kurlberg–Pomerance Lemmas 19–20 explicitly state; the earlier “infinitely many only” comparison was false.
- arXiv:1509.03768 is Sungjin Kim's paper, not a Luca–Shparlinski paper. It concerns base/modulus averaging and is not a fixed-base prime-average lower bound.
- Complete splitting in K_q(μ_M) does not enforce an arbitrary residue class modulo M. The old proof of the progression-only Artin reduction is withdrawn. The review repairs it under full fixed-progression PD, an extra hypothesis not proved by the marginal PD theorem.
- The finite original bound B exceeded every tested p−1, so its numerical bounded-index check was vacuous. The independent B=12 check gives nonvacuous finite logic validation, not asymptotic evidence.

No new high-importance MathDB problem or substantial new case has been declared solved. The next arithmetic round investigates the missing fixed-progression reservoir.

## 5. Files

- Report: `frontier/iterations/i02-arithmetic.md` (this file).
- Sources: `frontier/sources/i02_arithmetic/` (59 pinned files and `manifest-artin.json` with blob checks).
- Experiments:
  - `frontier/experiments/i02_arithmetic_qrh_geometry.py`: exact geometry identity, slack scan, and ceiling.
  - `frontier/experiments/i02_arithmetic_index_decomposition_check.py`: finite logic check.
- Nothing was staged or committed, and no shared index was edited.
