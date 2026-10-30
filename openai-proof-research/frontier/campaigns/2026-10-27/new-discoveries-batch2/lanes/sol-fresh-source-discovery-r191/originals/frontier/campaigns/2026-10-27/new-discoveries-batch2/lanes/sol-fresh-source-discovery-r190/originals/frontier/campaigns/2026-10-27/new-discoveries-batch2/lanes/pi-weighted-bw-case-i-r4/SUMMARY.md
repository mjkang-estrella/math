# Lane report: CASE (i) of Mayumi–Kimura–Ohno–Chruściński, Eq. (14) — pi-weighted-bw-case-i-r4

**Date:** 2026-10-28 (session 13:00–14:30 local)
**Agent:** pi (GLM-5.3-Flash), solo, no delegated children.
**Verdict: NOT PROVEN. No counterexample found. Substantial new structure established; precise remaining gap identified (§5).**

---

## 1. Claim under test

Conjecture 1, Eq. (14) of arXiv:2403.04199v2 (LAA 700 (2024) 35–49): for every n ≥ 2, positive-definite
ω with eigenvalues 0 < λ₁ ≤ λ₂ ≤ … ≤ λₙ, and all A, B ∈ M_n(ℂ):

    ‖AB − BA‖_ω ≤ sqrt((λ₁+λ₂)/(λ₁λ₂)) · ‖A‖_ω · ‖B‖_ω,     ‖A‖_ω² = tr(A*Aω).

Status cross-checked against (a) the pinned trureturing dev-branch record
(`sources/trureturing-bw-ii-dev-20261028.md`, sha256 6aab5f66…; its line 79 states case (i) open in general
dimension), (b) live MathDB 362175 (open, zero solutions, zero Lean formalizations), (c) the paper's own v2 HTML
(saved: `sources/2403.04199v2.html`). CASE (ii) (Eq. 15) was **not** touched — it is already settled
(root lane `root-weighted-bw-screen-r22/public-case-ii.md`, hash-identical record). Eq. (16) is a corollary
family of (14), not credited separately. Fang–Cheng (LAA 718 (2025), DOI 10.1016/j.laa.2025.03.015) body was
NOT read (ScienceDirect returned HTTP 403 on one attempt; recorded, no retry/bypass); it remains a novelty gate —
no subsumption was inferred from its title/abstract.

## 2. Reduction used throughout (equivalent forms)

With W = ω^(−1/2) = diag(w₁ ≥ w₂ ≥ … > 0), X = A√ω, Y = B√ω, Eq. (14) becomes

    (F)   ‖XWY − YWX‖_F ≤ sqrt(w₁² + w₂²) · ‖X‖_F ‖Y‖_F.

Set c² = w₁² + w₂². Three equivalent restatements established and used:

1. **Shear-invariant form.** T(X,Y) := XWY − YWX is alternating (T(Y,Y) = 0) and T(W⁻¹, Y) = 0, so T is
   invariant under X → X + aY + bW⁻¹. Hence (F) ⟺ (F) restricted to pairs with ⟨X,Y⟩_F = 0, and the
   "sharpened" inequality ‖T‖² + c²|⟨X,Y⟩|² ≤ c²‖X‖²‖Y‖² is *exactly equivalent* to (F) (it is (F) written in
   deficit form; nothing extra is being proven). The sharpened form was nevertheless verified numerically as an
   independent check (§4).

2. **Wedge-chain form (new, exact).** T(X,Y)_{ij} = Σₖ wₖ (X∧Y)_{(ik),(kj)}, where (X∧Y)_{(ik),(kj)} =
   X_{ik}Y_{kj} − X_{kj}Y_{ik} are coordinates of the decomposable wedge X∧Y ∈ ∧²(HS). So (F) ⟺

       ‖Λ(X∧Y)‖² ≤ c² ‖X∧Y‖²   for all *decomposable* ξ = X∧Y,

   where Λ: ∧²HS → HS is the weighted chain contraction Λ(ξ)_{ij} = Σₖ wₖ ξ_{(ik),(kj)}.
   Verified exactly (floating point, 50 random trials, n = 4): `scripts/verify_wedge.py`.

3. **Per-entry Lagrange decomposition (exact identity).** For each fixed (i,j), with μₖ := (X∧Y)_{(ik),(kj)}:

       c² Σₖ|μₖ|² − |Σₖ wₖμₖ|² = Σ_{k<l} |w_l μₖ − wₖ μ_l|² − (Σ_{k≥3} wₖ²) Σₖ |μₖ|²,

   so the whole conjecture reduces to absorbing the negative term by the non-chain wedge coordinates
   Σ_{nonchain} |μ_{αβ}|² via the decomposability (Plücker) constraints. This is the crux (§5).

## 3. New results obtained this session (all verified, none sufficient alone)

- **(R1) Full-exterior norm is strictly larger (decomposability is essential).** On the *full* exterior square,
  ‖Λ‖² = 98 > c² = 97 for n = 3, w = (9,4,1); ‖Λ‖² = 102 > 97 for n = 4,5, w = (9,4,2,1)
  (`scripts/lambda_norm.py`). Hence any proof must use decomposability; "bound Λ on all of ∧²" provably fails,
  confirming the batch hint.
- **(R2) n = 2 exact identity.** For n = 2, ‖T‖² = c²(‖X‖²‖Y‖² − |⟨X,Y⟩|²) *identically* — the conjecture is an
  equality on all of M₂. Verified symbolically (24-monomial expansion, `scripts/symb_n2c.py`) and numerically
  (~1e-13). This refines the paper's identity (19) (which was stated for centered pairs) to all pairs.
- **(R3) Rank-one X: complete explicit SOS.** For X = E_pq (p ≠ q) the deficit
  D(X,Y) = c²‖X∧Y‖² − ‖T‖² as a Hermitian form in Y is *exactly*
      D = |w_p Y_qp + w_q Y_pp|² + (c² − w_p² − w_q²)(|Y_pp|² + |Y_qq|² + |Y_qp|²)
          + (c² − w_p²) Σ_{i∉{p,q}} |Y_ip|² + (c² − w_q²) Σ_{j∉{p,q}} |Y_qj|²,
  all coefficients ≥ 0. Hence ‖T_{E_pq}‖² = w_p² + w_q², maximized at {p,q} = {1,2} — the extremal is exactly
  the top-2 coordinate block, with equality at Y ∝ w_p E_qp + w_q E_pp direction (e.g. X = E₁₂, Y = E₂₁).
- **(R4) Structured 2-sparse families: explicit SOS.** Symbolic n = 3 computation (`scripts/symb_n3.py`) gives,
  e.g., for X = E₁₂ + aE₁₃, Y = E₂₁ + bE₃₁:
      D = |w₂X₁₃ − w₃ Ȳ₃₁|² + (w₂² − w₃²)(|Y₃₁|² + |X₁₃Y₃₁|²) + w₁²  ≥ 0,
  and for X = E₁₂ + aE₂₃, Y = E₂₁ + bE₃₂:
      D = |w₁X₂₃ + w₃ Ȳ₃₂|² + w₂²|X₂₃|² + (w₁² + w₂² − w₃²)|Y₃₂|² + (w₁² − w₃²)|X₂₃Y₃₂|².
  The pattern: per-(i,j) Lagrange pieces |w_l μₖ − wₖ μ_l|² plus (w_p² − w_q²)·(bilinear)² terms. A general
  closed SOS was **not** found (§5).
- **(R5) Numerical verification, adversarial families.** `scripts/final_sweep.py`: over n = 6, 8, 12 with
  random / near-extremal top-2-leak / wedge-aligned / sparse families (300 trials each), the ratio
  ‖T‖²/(c²‖X∧Y‖²) never exceeded 0.849; the worst cases are precisely the top-2-block-plus-small-leak family,
  whose ratio → 1 as the leak → 0. Together with the prior lane's >6000 trials and this session's
  `verify_sharpened.py` (400 structured X, n ≤ 6, min eigenvalue of c²‖X‖²I − c²|x⟩⟨x| − T*T ≥ −2e-12),
  the conjecture stands under everything thrown at it.
- **(R6) Paper's n = 2 identity (19) re-verified** on 200 random centered pairs (rel. err ~2e-14).

## 4. Failed routes this session (beyond the prior lane's five)

- Block-embedding into the classical (case-ii-type) sharpened BW inequality: always leaves uncontrolled extra
  terms (‖YW‖², ‖(XY−YX)W‖²) — never sharp.
- Per-(i,j) Cauchy–Schwarz on the chain coordinates: gives Σₖ wₖ², not c²; and the per-(i,j) constant c² is
  *false* — the chain coordinate vector (μₖ) can be aligned with w (explicit example: X = row-of-ones, Y with
  Y_k2 = w_k), so the global constraint is unavoidable.
- Induction by splitting W = w₁P + W̃: the rank-one channel and the rest are not orthogonal; triangle loss 2w₁.
- Naive union bounds via Plücker: every non-chain wedge coordinate participates in n different (i,j)-terms,
  so coefficient bookkeeping loses a factor n; cannot reach the sharp constant.

## 5. Precise remaining gap

Prove: for all decomposable ξ = X∧Y ∈ ∧²(M_n), Σ_{ij} |Σₖ wₖ ξ_{(ik),(kj)}|² ≤ (w₁²+w₂²) Σ_{α<β} |ξ_{αβ}|².

Equivalently, using the exact identity in §2.3, absorb
   −(Σ_{k≥3} wₖ²) Σ_chains |ξ|²
into c² Σ_{nonchains} |ξ|² plus the positive Lagrange pieces Σ_{ij,k<l} |w_l ξ_{(ik),(kj)} − wₖ ξ_{(il),(lj)}|²,
using the Plücker relations satisfied by decomposable ξ. The obstruction found: the Plücker identity for
decomposable ξ, ξ_{αβ}ξ_{γδ} − ξ_{αγ}ξ_{βδ} + ξ_{αδ}ξ_{βγ} = 0, applied to chain coordinates
ξ_{(ik),(kj)} ξ_{(il),(lj)} = ξ_{(ik),(il)}ξ_{(kj),(lj)} − ξ_{(ik),(lj)}ξ_{(kj),(il)}, converts each negative
cross-term into products of *four* distinct non-chain coordinates, and the coefficient bookkeeping across the
n values of the free index loses a factor n against the budget c² per coordinate. The sharp inequality must
exploit simultaneous cancellation across all (i,j) — an exact SOS (Gram) decomposition in the bilinear-monomial
basis is the natural next tool (numerical SDP at n = 3, then rational rounding, then general n) and was **not
completed in this session**.

## 6. What would settle it

1. Numerical SDP: fix rational w (e.g. (9,4,2,1)), n = 3 or 4; search a PSD Gram matrix G on the bilinear
   monomial vector (X_pq Y_rs, X_pq Ȳ_rs, and conjugates, 2·2·n⁴ real dimensions) matching the quartic
   deficit's coefficients. If feasible with rational solution, extract the SOS pattern.
2. Generalize the R3/R4 pattern: conjectured shape
   D = Σ_{ij,k<l} |w_l ξ_{(ik),(kj)} − wₖ ξ_{(il),(lj)}|² · (correction) + Σ_{p<q} (w_p² − w_q²) |Φ_{pq}|²
   with Φ_{pq} explicit bilinear forms — to be pinned down from the SDP.
3. Lean bridge only after a human-checkable proof exists (per batch rules).

## 7. Deliverables in this lane

- `sources/` — pinned evidence (hashes in `provenance.json`).
- `scripts/` — symb_n2{,b,c}.py (n=2 identity), symb_n3.py (structured SOS), verify_sharpened.py
  (operator-inequality check), verify_wedge.py (chain formula), lambda_norm.py (full-exterior norm),
  final_sweep.py (adversarial sweep).
- `discovery.md`, `progress.md` — session narrative and findings.
- No `PROOF.md` (nothing proven end-to-end); no Lean artifacts (nothing to bridge yet).

## 8. Honesty notes

- No credit taken for CASE (ii) or Eq. (16); the pinned record and MathDB were re-fetched and cited, not
  re-derived.
- Fang–Cheng was not read (403, single attempt, logged). All R1–R6 above are this session's own derivations;
  if Fang–Cheng's rank-one-pair scope overlaps R3, priority is theirs — R3 is presented as verification, not
  priority claim.
- Every numeric claim above is reproducible from the scripts in this lane with fixed seeds.
