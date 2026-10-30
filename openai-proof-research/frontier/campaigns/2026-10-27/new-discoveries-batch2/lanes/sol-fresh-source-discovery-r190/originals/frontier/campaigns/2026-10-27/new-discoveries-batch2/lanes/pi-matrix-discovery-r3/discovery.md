# Discovery report — lane pi-matrix-discovery-r3 (batch 2, solo Pi, no children)

**Campaign:** 2026-10-27/new-discoveries-batch2. **Verdict: NO DISCOVERY CLAIMED.**
Additional count stays 0/30 (root counts; this lane requests credit 0).

Deep investigation of one matrix-analysis target, plus one important negative
structural finding on a second target. All primary sources read directly; access
limits recorded; all scripts and receipts in this lane only.

---

## 1. Primary target: MathDB 362175 — tight weighted Frobenius commutator bounds

### 1.1 Exact source statement (read from the actual paper)

Source: Aina Mayumi, Gen Kimura, Hiromichi Ohno, Dariusz Chruściński,
*Böttcher–Wenzel inequality for weighted Frobenius norms and its application to
quantum physics*, arXiv:2403.04199 (v1 7 Mar 2024, v2) = **Linear Algebra Appl.
700 (2024) 35–49**, DOI 10.1016/j.laa.2024.07.013. Cached: `sources/2403.04199.txt`
(from the astra-algebra-matrix-r2 lane cache; arXiv HTML v1/v2 cross-checked live).

For positive definite ω ∈ M_n(ℂ), eigenvalues λ₁ ≤ ⋯ ≤ λ_n (λ_m=λ₁, λ_sm=λ₂,
λ_M=λ_n), ‖A‖_ω² := tr(A*Aω), the paper's **Conjecture 1** (their eqs. (14)–(16),
pp. 6–7) asks, for all A,B, the **tight** bounds

- (14) ‖[A,B]‖_ω ≤ √((λ_m+λ_sm)/(λ_m λ_sm)) ‖A‖_ω ‖B‖_ω
- (15) ‖[A,B]‖_ω ≤ √((λ_m+λ_M)/λ_m) ‖A‖_ω ‖B‖
- (16) ‖[A,B]‖  ≤ √((λ_m+λ_sm)/(λ_m² λ_sm)) ‖A‖_ω ‖B‖_ω,

each with nonzero attainors (given in the source). Proven there: n = 2 completely;
special cases (A normal commuting with ω; B commuting with ω for (15); B = |λ₁⟩⟨λ_n|
for (15)). The record MathDB 362175 (fetched live, `sources/mathdb-362175.json`,
status open, solutions []) states exactly these three bounds.

### 1.2 Follow-up literature (critical novelty gate)

Fang & Cheng, *On some conjectures concerning the Böttcher–Wenzel inequality for
weighted Frobenius norms*, **Linear Algebra Appl. 718 (2025) 1–13**,
DOI 10.1016/j.laa.2025.03.015. The article body is CLOSED ACCESS (no arXiv
version; Semantic Scholar `openAccessPdf: CLOSED`; OpenAlex `oa_status: closed`;
no repository copy found on 2026-10-27) — I did **not** access the body.

The **zbMATH review 1564.15017** (reviewer Tin Yau Tam; retrieved live from
api.zbmath.org, saved as `sources/zbm-fangcheng.json`) states their results:
they prove the conjectured inequalities **for all rank-one X and Y**, the constants
in (14)/(15) being optimal, and leave a sharp constant question for (16) open.
So after Fang–Cheng (2025) the **general all-matrix case of (14) and (15) remains
open**; no proof or refutation of the general case is located anywhere (bounded
search: zbMATH, OpenAlex, Semantic Scholar, arXiv API, INSPIRE, MaRDI; receipts in
`sources/`). **Remaining novelty gap:** the Fang–Cheng body itself is unread; its
title and review indicate "some conjectures", and I cannot exclude that it contains
additional partial results beyond the rank-one case. This is an explicit
access-limited gap, not cleared by the review alone.

### 1.3 Exact reduction (this lane's derivation, verified)

Let W := ω^(−1/2) = diag(w₁ ≥ w₂ ≥ ⋯ ≥ w_n > 0) (so w_i = 1/√λ_i, w₁ largest) and
substitute X := A√ω, Y := B√ω. Then ‖A‖_ω = ‖X‖_F, ‖B‖_ω = ‖Y‖_F and
[A,B]√ω = XWY − YWX. Hence

- **(14) ⟺ (★)** ‖XWY − YWX‖_F ≤ √(w₁²+w₂²) ‖X‖_F ‖Y‖_F for all X,Y.
- **(15) ⟺** ‖XWY − YWX‖_F ≤ √(1+w₁²/w_n²) ‖X‖_F ‖YW‖_F for all X,Y.
- (16) follows from (14) via ‖[A,B]‖_F ≤ λ₁^(−1/2)‖[A,B]‖_ω.

So the whole record reduces to two inequalities; (★) is the core. For rank-one
X = E_pq one computes exactly ‖L_{XW} − R_{WX}‖ = √(w_p²+w_q²) (maximized at
{p,q} = {1,2}), reproducing Fang–Cheng's sharp rank-one case and the paper's
attainors — the conjecture says this rank-one value is the **global** supremum.

### 1.4 Numerical evidence (this lane)

Exact-operator alternating maximization (each half-step is a top singular-value
problem; the bilinear map is linear in each argument) over complex X, Y:

- Random trials (6000, n ≤ 6, random diagonal ω): ratios vs the conjectured
  constants never exceeded 1 (max 0.961 for (14), 0.925 for (15)).
- Optimization sweep `scripts/final_sweep.py` (n = 3..8, five spectrum families,
  12 starts × 35 iterations each): the supremum of ‖T_X‖²/‖X‖²_F converged to
  c² = w₁²+w₂² to ~8 digits in every case (`verification/sweep14.json`).
- **Structural finding:** the optimizers always converge to X supported (up to
  ~1e−20 Frobenius mass) on the top-left 2×2 coordinate block, rank ≤ 2 —
  consistently with: *the global sup is attained on the {1,2}-block, where the
  statement is exactly the authors' proven n = 2 theorem.*

So the record's conjecture is very likely TRUE; no counterexample was found.

### 1.5 Proof attempts and why they do not close (documented honestly)

1. **Convexity/extreme-point reduction:** ‖T_X‖ is convex in X; the Frobenius ball
   is strictly convex (all boundary points extreme), so no rank-one reduction.
   The nuclear-norm ball does have rank-one extreme points and yields
   sup_{‖X‖_*≤1}‖T_X‖ = √(w₁²+w₂²) exactly — but that ball is *smaller* than the
   Frobenius ball, giving only the known lower bound.
2. **HS-norm control:** ‖T_X‖²_HS = n(‖XW‖²_F+‖WX‖²_F)−2|tr XW|² ≫ op-norm²;
   useless (superoperator rank ~2n).
3. **Shift/triangle route:** T_X = L_{XW−λI} − R_{WX−λI} (exact, since L_I = R_I);
   the needed bound min_λ(‖XW−λI‖_op+‖WX−λI‖_op) ≤ √(w₁²+w₂²)‖X‖_F fails to be
   provable by the normal-matrix heuristic and the extremal shows the triangle
   inequality must be exactly tight there — unproved.
4. **Peeling/induction on n:** the block computation of XWY − YWX w.r.t. the last
   coordinate produces w_n-terms entering the (1,1) block coherently with the
   W̃-commutator; no slack control found.
5. **Gram-matrix route:** XWY − YWX = Σ_k w_k (x⁽ᵏ⁾y₍ₖ₎ − y⁽ᵏ⁾x₍ₖ₎); the needed
   Gram-matrix inequality wᵀGw ≤ (w₁²+w₂²)‖X‖²_F‖Y‖²_F on the sorted cone (extreme
   rays χ_k = 1+⋯+1) reduces to bounds on ‖XD_kY − YD_kX‖ for prefix projections
   D_k; no closing estimate found.

**Conclusion on 362175:** deep, likely-true, open conjecture; a complete proof is a
genuine research problem (two expert papers could not close it). No credit claimed;
no partial formalization is useful for the record (the endpoint is the full
inequality). Remaining gaps: Fang–Cheng body unread (closed access); the general
proof of (★) and of (15) open.

---

## 2. Secondary target: MathDB 343202 — inverse-eigenvector product (IMPORTANT negative finding)

Source read: G. Ambrus, *Analytic and Probabilistic Problems in Discrete Geometry*
(thesis), arXiv:1907.05379, Definition 1.17, Conjectures 1.18/1.19 (pp. 31–33).
Cached: `sources/1907.05379.txt/pdf`.

**Finding (this lane's derivation): Conjecture 1.18 — the statement recorded in
MathDB 343202 — is EQUIVALENT to the classical real polarization problem** (the
famous open problem that for every unit u₁,…,u_n ∈ ℝⁿ there is a unit v with
∏|⟨u_i,v⟩| ≥ n^(−n/2)).

Proof sketch of the equivalence. For a Gram matrix M = (⟨u_i,u_j⟩) with unit u_i:
α is an inverse eigenvector (Mα = α⁻¹) iff, writing v := Σα_iu_i, one has
α_i⟨u_i,v⟩ = 1 and v = Σα_iu_i; then v is a critical point of g(v) = ∏⟨u_i,v⟩ on
{‖v‖² = n} (Euler's identity ⟨v,∇g⟩ = n·g forces the Lagrange multiplier to match
automatically), and |∏α_i| = 1/|g(v)|. Conversely any critical point v of the
absolute product with sign pattern s yields an inverse eigenvector of S M S
(S = diag s), and S-transfers back to M preserving |∏α_i|. Hence "∃ inverse
eigenvector with |∏α_i| ≤ 1" ⟺ "the maximum of ∏|⟨u_i,v⟩| on the √n-sphere is ≥ 1"
⟺ (v = √n θ) the real polarization problem. The maximum is attained at a smooth
point (the zero set of the product is a finite union of great subspheres), so no
degeneracy escapes the argument.

Consequences: (a) 343202 is exactly as hard as a famous open problem — not a
viable session target in either direction; (b) any literature check of the real
polarization problem's status doubles as a check of 343202 (bounded search here
found no resolution; the complex analogue is Ball's Theorem 1.20, credited).
This equivalence is elementary but was not stated in the thesis (which only notes
one implication); it is recorded here as an uncounted structural clarification.

**377365 (primitive powers of integer matrices)** was left after a literature
glance: the scalar analogue is a hard open problem in Diophantine approximation
(S-unit/subspace-theorem territory); no viable session path. Not investigated
further; no claims.

Other targets screened and rejected for duplication/staleness per prior lanes:
352327 (active in pi-algebra-matrix-r1), 332493 (active formal review), 372905,
371031, 332939, 372787, 372585, 352819, 372716, 369147, 332318, 322910, 371345–47,
375999, 361692–96 (LW conjectures: equivalent to the fundamental LW conjecture —
deep open geometry; also the survey's norm on X is the Frobenius norm, so the
naive diag(1,−1) "refutation" fails the intended hypotheses — checked in the
survey text), 361461 (Bourin–Lee multivariable: deep, no traction), 373707
(implies the open weak balls conjecture; special case tight, no session path),
369189 (8714-config search in prior lane found nothing).

---

## 3. Provenance, hashes, access limits

See `provenance.json`. All sources fetched read-only (arXiv, zbMATH API, OpenAlex,
Semantic Scholar, MathDB public API, publisher landing pages). The Fang–Cheng LAA
718 article body was NOT accessed (closed; no lawful open copy located) — recorded
as a hard novelty gate for any future claim on 362175. No external messages,
uploads, git operations, or other-lane writes.

## 4. Strongest objection to any future claim here

For 362175: the closed-access Fang–Cheng paper could contain more than the
zbMATH review reports (its title says "some conjectures"); any acceptance needs
its actual body. For a *proof* claim, the remaining gap is mathematical: (★) and
(15) for all matrices. For a *refutation* claim: five independent searches
(4000+ random trials, structured sweeps n ≤ 8) found the conjectured constant
exactly; a counterexample is unlikely to be findable by local optimization.
