# Independent review — candidate `cstar-novak` (frozen c1917cde2a)

Reviewer: pi review sub-agent, GLM-5.3-Flash, standard speed, no children, own lane only.
All six frozen hashes recomputed and matched byte-for-byte (`provenance.json`). `paper.pdf` == `build/main.pdf`.

## Gate 1 — Exact source: PASS

- **Publisher PDF refetched by me** from https://pdf.medrang.co.kr/JKMS/2022/059/JKMS-59-4-789-804.pdf → SHA256 `5f53313d…b8a5d6`, byte-identical to parent's `published2022.pdf`.
- **arXiv v1 refetched** → `db6b0162…b7eb06`, identical.
- **p799 inspected personally** (rendered image read): Definition 6 defines cos x = (e^{ix}+e^{−ix})/2 for a unital C*-algebra. Conjecture 4.2: [∏_{l=1}^d (1+cos(x_{j,l}−x_{k,l}))/2 − (1/n)·1]_{1≤j,k≤n} is positive for all n,d ≥ 2 and **all** choices x_j ∈ A_sa^d. **No commutation, distinctness, or any other side hypothesis.**
- **p800 inspected**: Theorem 4.3 solves only the commutative case. **arXiv v1 Conjecture 4.3** (read from refetched PDF) has identical content and hypotheses; no extra hypothesis in either version.
- **MathDB 351633 refetched live** → `655dc698…20ae0d`, identical to frozen snapshot. I inspected **every** field: status "open", progress null, post_type "conjecture", solutions [], model_attempts [], human_solves [], replies [], comments [], formulations [], attachments [], lean_formalization_count 0, has_bounty false, vote_count 0. No resolution posted anywhere.
- Quantifier check: A = M₂(C) is a unital C*-algebra, n=4 ≥ 2, d=2 ≥ 2, all eight inputs self-adjoint ⇒ the conjecture as literally stated applies to this input tuple. The matrix lives in M₄(M₂(C)) ≅ M₈(C); positivity = PSD of the flattened 8×8 complex matrix. No loophole found.

## Gate 2 — Mathematics, independent derivation: PASS

I re-derived everything with a different code path (`independent_check.py`, sympy exact + numpy 50-digit eigendecomposition; not the parent's script):

- Exact: U² = V² = 4π²I, (U+V)² = π²I, (U−V)² = 15π²I (symbolically verified; also UV ≠ VU, so inputs are genuinely noncommutative — the commutative theorem does not apply).
- All 16 entries of the cosine table verified by eigendecomposition of the actual 2×2 differences (cos U = cos V = I, cos(U+V) = −I, cos(U−V) = cos(π√15)·I, cos 0 = I). The lemma M² = r²I, r>0 ⇒ cos M = (cos r)I was re-derived by hand via the intertwining identity (rI±M)M = ±r(rI±M); it is elementary and correctly proved in the paper.
- Kernel: uncentered K = [[1,1,0,1],[1,1,1,t],[0,1,1,1],[1,t,1,1]]⊗I₂, t=(1+c)/2, c = cos(π√15) ≈ 0.921436514468170. Witness y=(1,−1,1,−1)⊗e₁: yᵀ(K−J₄/4⊗I₂)y = c−3 ≈ **−2.07856348553183** (exact symbolic equality re-derived), and the uncentered kernel fails on the same vector (J-part vanishes since Σyᵢ=0).
- Literal 8×8 matrix: spectrum {−0.59467893 (×2), 0.03928174 (×2), 1 (×2), 2.55539719 (×2)} — matches parent's `numerical-check.json` exactly; min eig < 0 ⇒ not PSD. All entries central ⇒ ordered/Jordan-product ambiguity immaterial.
- During my check I initially made two errors of my own (wrong flattening, wrong witness indexing), caught and corrected them; the corrected results agree with the candidate and the parent's replay JSON.

## Gate 3 — Formal, fresh isolated replay: PASS

- Copied the frozen candidate into `replay/cstar-novak` (hashes re-verified on the copy) and ran `verification/verify_candidate.py` with the pinned Lean 4.34.1 binary and the 2026-10-14 packages. **PASS, 36 declarations (7+14+15)**, only propext/Classical.choice/Quot.sound. My replayed `audit.json` is byte-identical (SHA `636a9fd3…c3f26`) to the frozen one.
- Read all 36 declaration types in `Checks.log`. Scrutiny results:
  - The exponential is Mathlib's genuine `NormedSpace.exp` on M₂ (confirmed by the recorded type of `Novak.exp_scalar`); for finite-dimensional matrices this is the usual power-series exponential, norm-independent. `operatorCos` is literally (exp(iA)+exp(−iA))/2 — matches Definition 6.
  - `sourceBlock` is the literal conjecture entry: product of the two coordinate factors minus 1/4; the second-coordinate factor is proved = 1 (`source_block`); `sourceMatrix` flattens Fin 4 × Fin 2 → 8×8 over ℂ, exactly B⊗I₂ with B the scalar block — my independent spectral check of that flattening agrees.
  - Endpoint `Novak.source_counterexample_351633 : (∀ i l, (inputs i l).IsHermitian) ∧ (sourceMatrix inputs).IsHermitian ∧ ¬(sourceMatrix inputs).PosSemidef` — closed, **no residual premises**, no assumed source bridge. `quadratic_form` states the exact value c−3; `not_posSemidef` derives the contradiction from Mathlib's `PosSemidef.dotProduct_mulVec_nonneg`. The verifier itself forbids `sorry`/`axiom`/`native_decide` and checks dependency revisions/cleanliness.
- No fake source bridge: the endpoint does not reference any "source conjecture" predicate; it directly proves the literal matrix facts.

## Gate 4 — Bounded novelty: ACCEPT-with-limits

Searches I ran (angles distinct from parent's): direct conjecture+counterexample queries, scalar-Novak/Vybíral lineage, citing-corpus of the source (Semantic Scholar API: exactly 2 citations, both inspected — 2402.06399 uses only Krishna's *commutative* Schur theorem as its Thm 6.7; 2207.12799 has no Novak content), Hinrichs–Vybíral counterexample literature, MathOverflow/MSE, exact constant cos(π√15), Krishna's later papers.

- **Vybíral Adv. Math. 368 (2020), 107140** (read abstract/statement via 1909.11726): proves the scalar/commutative Novak conjecture. Our counterexample does **not** contradict it — inputs are noncommutative 2×2 matrices (UV ≠ VU verified exactly). No loophole.
- **Vybíral arXiv:2609.21733 / J. Complexity 2026** (abstract and body-summary read): explicit counterexample to the *Hinrichs–Vybíral* conjecture about arbitrary nonnegative positive-definite functions — a different statement, scalar/commutative, does not mention Novak or this kernel. Nearest in spirit (explicit kernel-counterexample folklore) but not a prior refutation.
- **Krishna 2026 Gauss-Lucas/Sendov paper (krasec.ru PDF, read in full)**: only a bibliographic citation of the 2022 paper; no Novak content. This was the parent's one unread source; it is now read.
- **No source anywhere** states or implies a refutation of the C*-algebraic Novak conjecture; MathDB record is open with zero progress/solutions; the exact constant cos(π√15) appears nowhere.
- **Limits (candid)**: this is a bounded search, not a full zbMATH/Scopus/MathSciNet citing-corpus sweep; OpenAlex was unavailable from this environment; Semantic Scholar may undercount; non-English literature not systematically covered; unpublished folklore or private communications cannot be excluded. I make **no absolute priority claim**. The candidate itself claims only one literal refutation, no new general matrix-cosine/radial-kernel theorem — that bounded claim is appropriately scoped and, to the searched literature, unposted.

## Gate 5 — Manuscript: PASS (no authoring changes)

Rendered both pages of the frozen `paper.pdf` myself (pdftoppm, both images inspected).
- Page 1: source conjecture displayed exactly as published (product, −1/n, quantifiers), correct numbering note (4.3 preprint / 4.2 published), MathDB mention, all inputs self-adjoint, squares identity, no overclaiming.
- Page 2: Lemma proof (intertwining, no diagonalization) correct as written; kernel K matches my independent derivation; proof of Theorem 1 (yᵀ(K−J₄/4)y = −4+2t = c−3 ≤ −2, Hermitian, not PSD; uncentered also fails) correct; formal scope paragraph accurate (NormedSpace.exp, 36 declarations, pinned revision d13f23b7…, 3 axioms); both references bibliographically correct.
- No math/typo/rendering defects found. Both pages clean.

## Verdict

| Gate | Verdict |
|---|---|
| 1 Source | PASS |
| 2 Mathematics | PASS |
| 3 Formal replay | PASS |
| 4 Bounded novelty | PASS (bounded; no prior refutation found; limits disclosed above) |
| 5 Manuscript | PASS |

**Decisive objections: none.** The one full source-conjecture refutation is genuine, formally certified, and — within the searched corpus — unposted. The candidate is **eligible** as one genuine new discovery under the strict 9→10 standard, subject to the parent's final acceptance decision. I did not change the count or any shared state; my originals are preserved in this lane (`replay/cstar-novak/`, `independent_check.py`, `independent-check-output.txt`, `replay-run.txt`, `provenance.json`).
