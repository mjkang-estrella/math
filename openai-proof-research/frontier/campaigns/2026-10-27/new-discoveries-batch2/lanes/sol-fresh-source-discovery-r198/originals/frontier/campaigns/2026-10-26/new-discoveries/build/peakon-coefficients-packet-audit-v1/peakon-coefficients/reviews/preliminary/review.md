# Independent preliminary review — full all-order peakon coefficient solution (MathDB 372008)

Reviewer: pi-peakon-preliminary-review (solo sub-agent). Date: 2026-10-27.
Candidate: lanes/parent-peakon-coefficients frozen at commit `e4bccde43b`
(PROOF.md `b3c80164…`, STATUS.md, support-build.json, formal/{RankTwo,NilpotentCollapse,UpperFamily}.lean + Checks.log, all 13 hashes verified; working tree clean vs the commit for both candidate lanes). Evidence lane: parent-fresh-screen-r12 (all 38 source hashes in its provenance.json verified).

Scope honored: no parent/shared edits, no staging/commits, no tally/acceptance changes (tally 25/30, credit 0 untouched), no contacts/posts. No children; own checker written from scratch (not a rerun of the parent's). The parent's formal directory additionally contains ~19 modules stamped after the frozen commit (10:01–10:07 today); per instructions I did **not** review or poll that live work — this review covers only the frozen candidate.

## Verdicts (preliminary; not acceptance)

| Gate | Verdict |
|---|---|
| G1 Exact source fidelity | **PASS** |
| G2 Complete mathematics (all-order determination) | **PASS** (mathematical completeness; formal gate separately pending) |
| G3 Bounded novelty / subsumption | **PASS, bounded** (no subsumption found; no absolute priority claim possible) |
| G4 Substantive eligibility (genuinely new, not immediate corollary) | **PASS (preliminary)** |

Overall: the proposed formula a_j(k_1,…,k_j) = m·(j−1)! / (∏_i k_i · ∏_s r_s!) is **correct and complete** for the literal source conjecture, by a derivation I reproduced end-to-end with independent exact evidence. Remaining bridges are the formal gate and a necessarily wider novelty screen; they are recorded below and none is a mathematical obstacle found by this review.

## G1 — Exact source: PASS

I read the actual published body (J. Phys. A 59 (2026) 245202, DOI 10.1088/1751-8121/ae7683; PDF retrieved 200, hash-bound in R12) myself, in text and visually (rendered pages):

- Eq 2.1–2.3 (A, T, S with √(p_i p_j) entries, s_ij = sgn(q_i−q_j), convention s_ii=0; Remark 4.3 fixes sgn(0)=0). Verified.
- Eq 2.8/3.1–3.3/4.8: L(z) = S + ΛT + ξA with Λ=(z²−1)/(2z+γ), ξ=(z²+γz+1)/(2z+γ) (Eq 5.4). **Subtlety found and resolved:** plain-text extraction of Eq 4.8 garbles the h±/exponential pairing; the rendered PDF p.8 reads L_ij(z) = √(p_i p_j)(h⁺_ij e^{+ν|q_ij|/2} + h⁻_ij e^{−ν|q_ij|/2}), h± = ½(±1 + Λ ± s_ij ξ). This pairing is exactly the one consistent with L(z)=S+ΛT+ξA; I verified the entry-level identity symbolically (evidence review-check.py, T2 "Eq(4.8) entry"). The candidate's math does not depend on the garbled reading; no defect in PROOF.md.
- Prop 5.1 / Eq 5.17–5.19 (h^(m) = m·tr[(T+½γA)(S+A)^{m−1}], degree-0/degree-1 terms), Eq 5.18 (ξ²=Λ²+γΛ+1 — I re-derived it symbolically), Conjecture 5.2 / Eq 5.20–5.21, Appendix C (τ_4..τ_7). All verified; arXiv:2512.11066v3 (peakons2025.txt, which is that arXiv version) agrees with the published body at every checked point.

**Square-root convention audit (requested, critical).** The source writes √(p_i p_j) and uses T_ii = p_i (Eq 5.6: h^(1)=Σp_i; also Prop 5.1 asserts τ_m is homogeneous symmetric of degree m in p). Three readings exist: (a) coherent per-particle roots √(p_i p_j) := s_i s_j, s_i²=p_i; (b) principal root of the product (real p_i, giving T_ii=|p_i| for p_i<0); (c) independent formal symbols per ordered pair. Only (a) reproduces the source's own h^(1)=Σp_i, h^(2) (Eq 5.10), and the homogeneity/factorization behind "τ_m is a homogeneous symmetric function of degree m" — under (b) T_ii=|p_i|≠p_i for negative momenta and the factorization fails; (c) contradicts the source outright. So the coherent reading is **forced by the source itself**; the positive-p principal reading is merely its special case, and the candidate's final coefficients are polynomial in the p_i (each trace term is a cycle product ∏√(p_{i_l}p_{i_{l+1}}) = ∏ p_{i_l}), so **no silent narrowing occurs and none is needed**. My checker tests negative and zero p_i explicitly. PROOF.md's instruction to an independent reviewer to confirm the amplitude domain is thereby discharged.

Other domain items: ties of q give s_ij=0 and B_ij=0 (no obstacle; tested, including shared-symbol ties); spectral poles 2z+γ=0 affect only the rational parametrization, not the curve relation ξ²=Λ²+γΛ+1 which holds identically (verified) and is all the proof uses; γ=±2 degeneration tested explicitly (checker T3 and literal cases at γ=±2); all N, all m (including m>N via h^(k)=0 for k>N), and no fixed-N algebraic-independence assumption anywhere in the derivation (the source's §5.5 uses independence only for its separate cyclic-variable remark, not for the conjecture).

## G2 — Complete mathematics: PASS

I re-derived every step independently and wrote my own exact checker (`evidence/review-check.py`, 247 checks, all PASS, `review-check.json`/`full-run.log`):

1. **Abstract determinant lemma** (B strictly upper, B−B^T = uv^T−vu^T, L = B + a·uv^T + b·vu^T, a=(λ+ξ−1)/2, b=(λ−ξ+1)/2, a+b=λ, ab=(ξ−1)/2−γλ/4): rank-2 determinant lemma gives det(I−tL)=1−t(aP+bQ)+t²abC with P=v^TRu, Q=u^TRv, C=PQ−(v^TRv)(u^TRu), R=(I−tB)^{-1}=Σ_{k<N}t^kB^k; the resolvent skew identity R−R^T=tR(B−B^T)R^T (re-derived) gives P−Q=tC; the curve condition kills all ξ-dependence, leaving det(I−tL)=1−λt[(P+Q)/2+γ(P−Q)/4] = 1−λt·tr((T+γA/2)R) = 1−λΣ_k(h^(k)/k)t^k. Verified **fully symbolically** in u,v,λ,ξ,γ,t (N=3, reduced mod the curve) and numerically-exactly at assorted rational points; also at the degenerate curves γ=±2.
2. **Literal source bridge**: with u_i=s_i w_i, v_i=s_i/w_i, w_i=e^{νq_i/2} as symbols, the literal Eq 2.1–2.3 matrices satisfy A=(uv^T−vu^T)/2, T=(uv^T+vu^T)/2, T_ii=p_i, B=S+A strictly upper (for any ordering of the q's, ties included), B−B^T=uv^T−vu^T, and the Eq 4.8 entries equal (S+ΛT+ξA)_ij — all as exact identities in the Laurent ring Q[w_1^{±1},…]. h^(1)=Σp_i (5.6) and h^(2)=¼Σp_ip_j(2γ−S_ij) (5.10 with S_ij from 4.10) both verified against the trace formula.
3. **All-order extraction**: tr L(z)^m = Σ_j Λ^j Σ_partitions a_j ∏h^(k_i) with a_j = m(j−1)!/(∏k_i·∏r_s!) verified as an exact symbolic identity for the literal matrices for all m ≤ 8 at N=1..5 (six literal instances: ties, negative/zero p, γ=±2), plus a relabeled-unsorted-q instance via the explicit permutation route of the source's Prop 5.1 proof. The partition counting (j!/∏r_s! ordered compositions, ×m/j) was checked against brute-force composition enumeration for m ≤ 8, and both Eq 5.21 families follow exactly (the source's j<m−1 upper restriction is explained by its separate all-ones family, as PROOF.md says).
4. **Source data**: every coefficient readable in Eq 5.9, 5.13 and Appendix C (C.1–C.4, m=4..7, 33 partition coefficients) matches the formula.
5. **Lean replay** (own copy, absolute packages, Lean 4.34.1/mathlib): 21 declarations in 3 modules compile clean, exit 0; my replay log is **byte-identical** to the frozen Checks.log (b561d60f…); all axiom reports are standard-3 only (propext, Classical.choice, Quot.sound); `algebraicLax_det_collapse` carries only the genuine spectral-curve hypothesis. This supports the abstract collapse only — correctly **not** claimed as a literal source endpoint, and I do not treat it as one.

The mathematics is complete as a proof of Conjecture 5.2 for the literal source family: nothing in the chain is assumed from the source except its definitions (which I read), the classical rank-2 determinant lemma and trace-log identity (characteristic-0, both sides polynomial), and the proved collapse. Sanity anchors: λ=0 members give L=B resp. B^T with det(I−tL)=1; the Λ¹ coefficient reproduces Prop 5.1's h^(m); the Λ^m coefficient is h^(1)^m.

## G3 — Bounded novelty / subsumption: PASS, bounded

- **2023 predecessor** (SciPost Phys. 15, 228): I read §2.3 and §4.1–4.3 myself. Conserved quantities are standard traces τ_n = Tr L̄(a,ā)^n of the full matrix T+āS+aA; §4.1–4.3 is a commuting-traces/r-matrix argument; §2.3 is the Lax presentation. **No determinant collapse, no expansion coefficients, and its one-parameter family is not even the 2026 halved family** (there Λ multiplies T, not S).
- **Ragnisco–Bruschi 1995** (Physica A 228, 150): Lax matrix is the full symmetric peakon matrix with invariants tr L^k; the only log-det is the classical Toda/PL `ln det Λ` for Flaschka variables (Eq 3.4) — a different object. No collapse of any peakon transfer matrix.
- **2022 companion** (SciPost Phys. 13, 044, fetched from HAL and searched): standard h^(k)=tr L^k; no expansion, no conjecture.
- **MathDB 372008**: status open; comments/solutions/model_attempts/human_solves/replies all empty (cached record; live page confirmed to exist via search). The exact statement matches Eq 5.20–5.21.
- **MathDB grouping artifacts**: the record groups 4 other papers (2508.18731, 2503.11912, 2001.11599, 1808.01008) as "stating this conjecture". I fetched all four: graph-factor enumeration, degenerate Painlevé III asymptotics, zonal polynomials, seaweed subalgebra compositions — **all decisively unrelated**; matcher artifacts, excluded.
- **Author/title/registry web screen** (bounded, DuckDuckGo after provider rate limits): no resolutions, no author follow-ups, no citing works found. OpenAlex W4417515821 (0 citers) not treated as evidence, per instructions.
- The general tools (rank-k determinant lemma, trace-log/Newton, Cayley–Hamilton) are classical and correctly not claimed. The proposed bridge is the **specific, curve-conditioned collapse** det(λI−L(z)) = λ^N − Λ(z)·Σ_k(h^(k)/k)λ^{N−k} for the rank-2-skew family — an unusual rigidity statement. I found no prior instance of it, including in semiseparable/Toda-molecule-adjacent structures surfaced by the screen. **Residual risk**: an unexamined body (full Kostant–Toda characteristic-polynomial literature, peakon spectral-curve papers, semiseparable-matrix determinant identities) could contain it; this screen is bounded and no absolute priority is claimed.

## G4 — Substantive eligibility: PASS (preliminary)

Under the strict standard: the result is not an immediate corollary of any prior body found. The two coefficient families alone do not determine the rest; the new content is the source-specific collapse plus its use to determine **every** coefficient — a complete resolution of an open conjecture from a June-2026 publication, with a genuinely new (if elementary-tool) mechanism. The bridge is more than bookkeeping: it hinges on the non-obvious curve-conditioned cancellation of all ξ-dependence. Substantive. Final eligibility belongs to the parent's acceptance process; I claim no tally change.

## Strongest objections / remaining bridges (exact list)

1. **Formal gate (explicitly pending).** No formalized literal-source endpoint: the frozen Lean proves the abstract collapse; the literal exp/sinh bridge, permutation argument, trace-generator normalization (h^(k) = k·tr[(T+γA/2)B^{k−1}] vs the source's 5.17), trace-log/Newton coefficient step, and the universal partition theorem are unformalized. The parent itself flags a candidate Mathlib bridge (derivative_det_one_add_X_smul). Do **not** record a formal PASS from the current 21 declarations.
2. **Novelty is bounded.** No absolute priority; the residual subsumption surface above should be swept (author follow-ups, peakon spectral-curve and full-Kostant–Toda literature, semiseparable determinant identities) before any acceptance-grade novelty claim.
3. **Post-freeze formal work exists but is out of scope.** The parent's formal directory contains modules stamped after the frozen commit; nothing from them is reviewed or credited here, and the frozen hash set must remain the review target.
4. Minor: PROOF.md's "both sides are actually polynomials" phrasing is fine over K(t), but the formal trace-log step still needs a pinned Mathlib theorem (parent notes this) — consistent objection 1.
5. No mathematical defect found. The only source-fidelity trap encountered (Eq 4.8's h±/exponential pairing in text extraction) resolves in the candidate's favor and is documented with the rendered page in `evidence/peakon-published-p8-eq4.8.png`.

## Evidence in this lane

- `evidence/review-check.py` — independent checker (written from scratch; different design from the parent's: literal source matrices, symbolic exponentials, ties, relabeling, degenerate curves, appendix-C data). SHA256 a6f9ad77…
- `evidence/review-check.json`, `evidence/full-run.log` — 247 checks, all PASS (989044bd…).
- `evidence/lean-replay.log` — byte-identical replay of the frozen formal support (b561d60f…).
- `evidence/peakon-published-p8-eq4.8.png` — rendered published p.8 Eq 4.8 used for the pairing audit.
- `provenance.json` — hashes, fetches, verdicts.
