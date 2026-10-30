# Preliminary independent review — connection vs Dirac spectral dominance, dimension ≤ 1

Reviewer: pi (adversarial review sub-agent), 2026-10-26. Work performed solo; no children, no git, no external posts. Scope: this lane only.

Reviewed object: `../parent-connection-graph/PROOF.md` (proposal: every nonempty finite 1-dimensional abstract simplicial complex — equivalently any finite simple graph as vertex-and-edge complex, isolates/disconnected allowed, no clique filling — satisfies S_k(L) − S_k(D) ≥ √2 − 1 > 0 for all 1 ≤ k ≤ v+m, sorted eigenvalue sums, with literal source matrices L (connection) and D (Dirac)).

## GATE VERDICTS

| Gate | Verdict | Summary |
|---|---|---|
| SOURCE | **PASS** | Actual arXiv:2601.18071 v2 (29 Jul 2026) PDF+TXT on disk, SHA-256 verified against provenance. Conjecture 1, §1.6, §1.7, §2.5–2.6, §3 (Thm 3), §5.1–5.5, §10 read in the actual text. Proposal's characterization is accurate. MathDB 372758 entry open, 0 formalizations. |
| MATHEMATICS | **PASS** | Every proof step independently re-derived (see §2). Independent numerics: 132 graphs (12 structured + 120 seeded random, v ≤ 12, all k = 1..N) built from the literal face-intersection definition, plus a 3000-graph × 2-orientation probe. All claims and all intermediate lemmas hold; min gap ≈ 1.0 (single edge, k=1). |
| NOVELTY / ELIGIBILITY | **PASS (bounded)** | No prior or companion body found supplying the all-k L-vs-D signed-Dirac comparison for the graph case. Bounded-search caveats recorded; no absolute priority claimed. |

**Overall eligibility recommendation: ELIGIBLE** as ONE prospective general infinite-class theorem (the full dimension-≤-1 case of MathDB 372758 / 2601.18071v2 Conjecture 1, proved with a uniform strict gap the conjecture itself does not ask for). Credit 0 stays until the campaign's full Lean/paper/packet standard is met, per the task framing.

---

## 1. SOURCE gate (PASS)

- Files `sources/2601.18071-current.{pdf,txt}`, `sources/1803.01464-current.{pdf,txt}`, `sources/372758-live.json` present; SHA-256 of all five recomputed by me and matching `provenance.json` exactly.
- §1.6: "We suspect that L ≥ D in a weak Loewner sense … These are open questions." §5.3: "Experiments suggest … but we can not prove it yet", followed by Conjecture 1 in the exact sorted-array form S_k(L) ≥ S_k(D) for 1 ≤ k ≤ n (n = number of faces). The prose in §5.3 loosely says "is L − D positive in a weak Loewner order", but the formal target (Conjecture 1) is the S_k array statement; the proposal's reading is correct and it never claims the loose phrasing.
- §1.7 confirms the 1-dimensional hydrogen identity is used by the source only for spectral-radius estimation of |H|/H — not for any L-vs-D comparison.
- §10 (v2, incl. the 18 July 2026 update): questions A/B/C; the Robert J. George 2-skeleton-of-K5 counterexample kills question C (spectral radius of g) and, as the parent notes, also refutes the g weak-dominance direction in that example. It does **not** touch L-vs-D (question A). Correctly excluded from credit. The repeated maximal eigenvalue of g for K_n 1-skeleta follows from the old hydrogen identity; also correctly excluded.
- The proposed graph model is source-faithful: for a 1-dimensional complex, literal L(x,y)=1{x∩y≠∅} gives blocks [[I, U],[Uᵀ, UᵀU−I]] (edge-edge diagonal 1 via x=x, adjacent distinct edges share exactly one vertex in a simple graph); literal D = d+d* gives [[0,C],[Cᵀ,0]] with C any oriented incidence; orientations differ by diagonal ±1 conjugation. I verified numerically (300 random graphs) that spectra of the literal face-intersection/boundary matrices equal the block-form spectra in every case. "Faces of cardinality ≤ 2" is the boundary 1-complex of the graph, not the filled clique complex (e.g. a 3-cycle stays a triangle boundary) — matches the source's simplex set semantics.
- MathDB 372758 (live JSON on disk): status open, lean_formalization_count 0, statement matches the S_k array form.

## 2. MATHEMATICS gate (PASS)

I re-derived every step; all check out. Detailed verification notes:

1. **Spectrum of L.** For unit Q-eigenvector u, Qu=qu>0, w=Uᵀu/√q: L(u,0)=(u,√q·w), L(0,w)=(√q·u,(q−1)w) — block [[1,√q],[√q,q−1]], eigenvalues φ(q)=(q+√(q²+4))/2>0 and −1/φ(q)<0 (product −1 ✓). Cross-orthogonality of the 2-planes from distinct Q-eigenvectors follows from u₁ᵀQu₂=0 (repeated eigenvalues: choose an orthogonal basis). Vertex kernel (q=0): eigenvalue 1; edge kernel (Uw=0): eigenvalue −1. Counting: r 2-planes + (v−r) + (m−r) ⇒ exactly v positive, m negative, positive spectrum = φ(q₁),…,φ(q_v). Signature v−m = χ(G) also matches source §2.2. Verified numerically (exact φ-match, exact counts).
2. **D spectrum and top-k formula (k ≤ v).** D=[[0,C],[Cᵀ,0]] has eigenvalues ±√(ℓ_i), i ≤ r = rank C, zeros N−2r. Since r ≤ min(v,m): r ≤ v and N−2r = v+m−2r ≥ v−r, so the first v sorted entries of D's spectrum are exactly √ℓ₁,…,√ℓ_v (zeros at positions r+1..v). Hence S_k(D)=Σ_{i≤k}√ℓ_i for k ≤ v. Verified numerically; my only failures here were my own checker's sqrt-amplification of 1e-16 noise at the zero positions (threshold artifact, not math).
3. **Loewner H ≤ 2Δ.** (z_i−z_j)² ≤ 2z_i²+2z_j² summed over edges gives zᵀHz ≤ 2Σδ_i z_i²; eigenvalue monotonicity under Loewner order gives ℓ_i ≤ 2δ_i↓ individually. Verified numerically per graph.
4. **Ky Fan / Schur–Horn.** diag(Q)=degree vector; sorted diagonal is majorized by sorted eigenvalues ⇒ Σ_{i≤k} q_i ≥ T_k. Standard; correctly applied.
5. **Scalar chain.** φ(t) ≥ 1+t/2 with excess e(t)=√(t²+4)/2−1 ≥ 0, e increasing; S_k(L) ≥ k+T_k/2+e(q₁); (k+T/2)²−2kT = (k−T/2)² ≥ 0 ⇒ k+T/2 ≥ √(2kT); hence S_k(L)−S_k(D) ≥ e(q₁). Rayleigh with z=e_i+e_j on an edge: ‖Uᵀz‖²=4, ‖z‖²=2 ⇒ q₁ ≥ 2 ⇒ e(q₁) ≥ √2−1. All correct. m=0 case: L=I_v, D=0, gap k ≥ 1. Verified.
6. **k ≥ v branch.** S_k(L) = Σ_positives + (top k−v negatives) ≥ Σ_positives + Σ_all negatives = tr L = v+2m−m = N. S_k(D) = Σ_{i≤r}√ℓ_i ≤ Σ_{i≤v}(ℓ_i+1)/2 = (2m+v)/2 = m+v/2. Gap ≥ v/2 ≥ 1/2 > √2−1. Correct; verified numerically for all k > v.
7. **Edge cases probed:** v=1 (single vertex), m=0, isolated vertices, disconnected unions, K_n, paths, stars, cycles, K_{3,3}/K_{3,4}, dense/sparse random; and (extra, beyond the source's definition) even non-boundary "broken" ±1 orientations — the gap never dropped below ≈1.0 in ~3100 graphs. The proven constant √2−1 ≈ 0.414 is **not tight**: observed infimum is 1.0 (single edge, k=1: S₁(L)=2, S₁(D)=1). This is a strengthening opportunity (a gap ≥ 1 statement looks plausible but is not proven by the current AM-GM argument, which is loose there), not a flaw.

No hole found. The proof is complete for the stated hypotheses (nonempty complex ⇒ v ≥ 1; every 1 ≤ k ≤ N; no connectivity/rank hypothesis left implicit — the m=0 and r<v degeneracies are each handled explicitly).

## 3. NOVELTY / ELIGIBILITY gate (PASS, bounded confidence)

Searches performed (this reviewer, independent of the parent's): author followup scan of Knill's graphgeometry papers page (latest items: Mar/May/Jul/Sep 2026 — none touch the conjecture; 2601.18071v2 is the latest word and still open); targeted queries for any proof of the graph case, for weak-Loewner/incidence/Dirac spectral-sum comparisons in the literature, and for the quantumcalculus.org blog "Connection and Dirac Matrix" (which only restates the experimental observation, no proof).

Closest prior bodies inspected, none supplies the theorem:
- **2601.18071 (v1 Jan 2026, v2 Jul 2026, 0 citations):** states the conjecture as open; its attempts (§5.4–5.5: Fan's theorem, Schur on L±D) provably do not resolve even the graph case; its own theorems give only individual eigenvalue upper bounds λ_j(L) ≤ d_j (Thm 1) and λ_j(D) ≤ d_j (Thm 3) — no partial-sum comparison.
- **1803.01464 (hydrogen identity):** Theorem 1 |H| = L−L⁻¹ and §2.16–2.18 concern L's own spectrum (Schur bounds, radius estimates for H₀); no signed-D comparison anywhere.
- **1802.01238, 1804.08211, 1306.2166, 2508.07550 and companions:** similarity/spectral-determination and Dirac-operator material; no weak-Loewner L-vs-D statement.
- **External spectral graph theory** (Ky Fan norms of signless Laplacian, oriented incidence energy, spectral-sum maxima): no theorem comparing Σφ(q_i) against Σ√ℓ_i or L against D.

Eligibility analysis against the campaign standard:
- **Not an already-known corollary:** the source itself leaves the graph case open through v2 (July 2026), with 0 citations and 0 formalizations; no prior theorem found that states or immediately implies S_k(L) ≥ S_k(D) for graphs.
- **Not immediately subsumed:** the hydrogen identity alone compares L with the *sign-less* |H|, not with the *signed* D; bridging to D needs the new Loewner H ≤ 2Δ + Ky Fan + scalar chain, which is exactly the proposed contribution. No single known theorem plus routine manipulation yields it.
- **Not a finite check:** infinite class (all finite simple graphs / 1-dimensional complexes), all k, with a uniform constant.
- **Not a mere reformalization:** it is strictly stronger than the conjecture's graph case (positive uniform gap √2−1 vs plain dominance), and the gap statement is new relative to the source.
- **Correctly not overclaimed:** explicitly only the dimension-≤-1 case; higher dimensions untouched; the g/spectral-radius exclusions respected.

Bounded-novelty caveats (candid): search coverage is finite — unindexed venues, very recent postings, or private notes cannot be excluded; I found no independent citation graph beyond the source (0 citations limits tracing); no absolute priority is claimed or needed for the campaign standard.

## Decisive objections

None decisive. Non-blocking notes:
1. The constant √2−1 is provably loose (numerics suggest true infimum 1, attained by the single edge at k=1). If the parent wants the strongest statement, a gap ≥ 1 variant should be investigated separately — it does not follow from the current argument and must not be claimed.
2. The m=0 degenerate case and the r<v zero-structure of D's spectrum are load-bearing; any Lean bridge must formalize the zero-multiplicity counting (N−2r ≥ v−r) explicitly, not just the inequalities.
3. The proposal's φ(q)-spectrum claim relies on choosing an orthonormal Q-eigenbasis in each repeated-eigenspace; the Lean bridge should do the block reduction via the L−L⁻¹ = diag(Q, UᵀU) hydrogen route (credited) or a direct 2-plane span argument, not by hand-waving orthogonality.

## Suggested Lean bridge (out of scope for credit; optional)

Mathlib has: `Matrix.IsHermitian.eigenvalues`, Ky Fan via `Matrix.sqSingularValue`-free majorization may be missing — realistic path: (1) define L, D for `SimpleGraph` finsets; (2) prove the 2-plane lemma for a single Q-eigenvector; (3) get the positive spectrum of L by relating charpoly of L to prod (x²−q x−1) via block determinant/`Matrix.charPoly_fromBlocks`; (4) Ky Fan step via Schur–Horn (`Matrix.Eigenvalues` majorization exists in recent Mathlib?) or via the elementary Rayleigh/induction route; (5) Loewner ℓ_i ≤ 2δ_i via Courant–Fischer on the explicit quadratic-form inequality. Estimated: a real formalization effort, not a bridge; recommend the packet record the five steps above as the formal plan.

## Verification artifacts in this lane

- `review_verify.py` — independent literal-definition construction (not the parent's block construction), structured+seeded random graphs, all k, all intermediate lemmas, orientation-robustness probe, literal-vs-block spectrum equality probe. All pass.
- Console result: min gap ≈ 0.9999999999999996 (isolates+edge, k=1); 0 literal-vs-block mismatches in 300 graphs.

## Gate tally contribution

This review contributes 3 gate evaluations (SOURCE, MATHEMATICS, NOVELTY) — all PASS. Combined with the parent's standing tally of 13/30, the parent should update the tally per its own rules; this lane does not edit shared indexes.
