# Preliminary review: proposed uniform maximal-index proof h(d)=2d−5 (d≥5)

**Reviewer lane:** `pi-maxindex-review` · **Date:** 2026-10-26 · **Artifact reviewed:** parent lane `parent-maxindex` at commit `7c84a2009c` (PROOF.md read completely; check_bounds.py; exact-bound-check.json; formal/ScalarBounds.lean + Checks.lean + Checks.log; sources incl. actual PDF p.18 inspected visually).

**Scope of this review.** This is a PRELIMINARY source/mathematical/serious-bounded-novelty review only. Only four scalar Lean ingredients exist; the finite-array theorem, manuscript, and proof packet are absent and will be formalized/gated separately by the parent. **No claim of final acceptance is made here. Tally unchanged at 11/30; this lead remains credit 0.**

---

## 1. SOURCE verdict: **PASS** (conjecture correctly transcribed; genuinely open in every channel checked)

I independently downloaded and verified every mandated source:

1. **arXiv 2009.06666v3** — downloaded fresh; SHA-256 `7f1fe71f…50947a` **matches the parent's hash exactly**. Abs page submission history read: v1 2020-09-14, v2 2021-03-08, v3 2022-10-30 (latest; no later version). Page 18 **inspected visually** (parent's PNG plus my own text extraction): Conjecture 4.19 states, for p ∈ ℝ^d≥0 with Σpᵢ=1, a_ij=(pᵢ+p_j)/2, g_ij=√(pᵢp_j), A = Σ_{k=1}^{h(d)} a_k↓, G = Σ_{k=1}^{h(d)} g_k↓ (k-th largest entries, ordered d² entries, both sums of the SAME length h(d)), and conjectures the maximal h(d) with A+G ≤ d for every p is 2d−5. This matches the parent's transcription and the proposed theorem's target exactly. Remark 4.18 gives the Ky Fan / singular-value motivation; the following text explicitly says "we cannot prove yet" — the source claims no proof.
2. **Published body J. Math. Phys. 62, 042203 (2021), DOI 10.1063/5.0031760** — I read the actual published copy as embedded (with AIP "Cite as" header) in the primary TUM thesis `mediatum.ub.tum.de/doc/1634443/1634443.pdf` (SHA `09f704a6…23ba8903`, extracted full text). Published **Conjecture IV.19 is verbatim identical** to the arXiv v3 statement, followed by the same "we have tested this conjecture numerically … If we were able to prove this conjecture…" passage and Remark IV.20 with "which we cannot prove yet". **No proof, restriction, or resolution anywhere in the published body.**
3. **Author's MSE question 3968126** — retrieved via the official StackExchange API (direct HTTP is 403; recorded). Asked 2020-12-31 by IMathYou (Matthias C. Caro). **answer_count = 0, is_answered = false.** Exactly two comments: rrogers asking whether the matrix formulation adds anything, and the author's reply. The question restates the same problem, the authors' provable bound h = ⌊2d−2√(2d)+1⌋, the extremal facts A-alone ⇒ 2d−2 and G-alone ⇒ d², the cap h ≤ 2d−2, and the numerical conjecture 2d−5. **No answers, no follow-up questions found** (site-wide excerpt search returned only this question).
4. **MathDB post 347947 (live)** — fetched fresh; SHA matches parent. `status: "open"`, `progress: null`, and **all** of `solutions`, `model_attempts`, `human_solves`, `formulations`, `comments`, `replies` are **empty arrays**; the stored statement matches the source conjecture exactly.

**Decisive source objections: none.**

---

## 2. MATHEMATICAL verdict: **PASS (proposed)** — I independently re-derived every bound and found no gap; one presentational strength and formalization items below

### 2.1 Combinatorial coefficient facts — verified exhaustively

For a k-element set S of ordered pairs with k=2m+1 and cᵢ=(rowcount+colcount)/2:
- Σ_{(i,j)∈S} a_ij = Σᵢ cᵢpᵢ ✓ (direct).
- cᵢ ≤ (k+1)/2 = m+1: row+col count ≤ k+1 (only the loop is double-counted) ✓.
- cᵢ+c_j ≤ (k+4)/2 = m+5/2 for i≠j: internal ordered pairs (at most 4) contribute 2 each, others ≤1 ✓.

I verified these **exhaustively over all 753,054 masks** (d ≤ 5, k ≤ 7, all k-element subsets of ordered pairs) with zero excess — see `evidence/independent_check.json` §A. No symmetry or common-ordering assumption is used anywhere; the argument applies to arbitrary masks, which is the right level of generality.

### 2.2 Sufficiency at k=2d−5 — re-derived, correct

- **Low branch (p ≤ 2/3):** Σcᵢpᵢ ≤ a·pᵤ + b(1−pᵤ) ≤ a·p + b(1−p) ≤ (2a+b)/3 ≤ ((m+1)+(m+5/2))/3 = **(4m+7)/6** ✓ (a≥b justifies monotonicity in p). With the coarse G_k ≤ √k (from Σ_all g² = (Σpᵢ)² = 1 and Cauchy): (4m+7)/6 + √(2m+1) < m+3 ⟺ 36(2m+1) < (2m+11)² ⟺ 0 < 4m²−28m+85 = (2m−7)²+36 ✓ for all m.
- **High branch (p > 2/3):** entries outside row/col u are ≤ 1−p < p/2; the baseline p/2 + extras decomposition (loop extra p/2 once; each tail pᵢ at most twice via (u,i),(i,u)) gives **A_k ≤ 1+mp** ✓. The largest geometric entry g_uu = p can be forced into a maximizing mask (standard exchange among tied maxima), and Cauchy on the remaining 2m entries against the residual square-mass 1−p² gives **G_k ≤ p + √(2m)·√(1−p²)** ✓. Two-dimensional Cauchy: A+G ≤ 1+√((m+1)²+2m) = 1+√(m²+4m+1) < m+3 = d (gap (m+2)²−(m²+4m+1) = 3) ✓. The max is unique when p > 2/3 (two entries = p would force p ≤ 1/2), so no tie subtlety harms this branch.
- Both branches are strict; case split is exhaustive; k=2d−5 ≤ d² for d ≥ 3. The four scalar inequalities are exactly the four Lean theorems, which compile with **only the three standard axioms** (Checks.log). I could not re-run Lean (no toolchain in this environment — recorded), but the log statements match ScalarBounds.lean verbatim and the .olean header embeds 4.34.1.

### 2.3 Sharpness family — re-derived exactly; actual sorted sums match

p = (r², 1^m, 0, 0)/(r²+m), r=2m, d=m+3 ≥ 5, k′=2m+2. Both exhibited masks are genuine sets of k′ **distinct** ordered pairs (counts check: 1+2m+1). Exact selected sums A_sel = ((m+3/2)r²+m)/D, G_sel = (r²+2mr+1)/D, D=r²+m, and total −(m+3) = (m−1)²/(4m²+m) > 0 for m ≥ 2 — all re-derived symbolically by me and **confirmed against actual independently sorted top-(2m+2) sums for every m ∈ [2,60]** (§C). Spot check d=5: p=(16,1,1,0,0)/18, A=29/9, G=11/6, total 91/18 = 5 + 1/18 ✓. Monotonicity of top-k sums then kills every k > 2d−5. Combined with §2.2 this yields h(d)=2d−5 exactly for d ≥ 5.

### 2.4 Small-d classification — re-derived; consistent, and notably CONTRADICTS the literal conjecture at d=3,4

- h(1)=0 (A₁+G₁=2>1), h(2)=1 (k=1: 2p₁≤2; k=2 witness 5/2>2, exact).
- h(3)=2: A₂+G₂ = (5/2)p₁+p₂/2+x₁x₂ ≤ 3p₁+p₂ ≤ 3 for all p (uses (p₁+p₂)/2 ≥ p₂ and x₁x₂ ≥ p₂, both from p₁ ≥ p₂ — correct); k=3 witness 17/5 > 3, exact.
- h(4)=4: A₄ = 2p₁+p₂+max(p₂,(p₁+p₃)/2) and G₄ = p₁+2x₁x₂+max(p₂,x₁x₃) — **both closed forms brute-force verified against full sorting on 20,000 random cases** (§E; the "next two are the two (1,2) orientations" step is correct since (p₁+p₂)/2 ≥ p₂ and x₁x₂ ≥ p₂). All four SOS branch expressions re-expanded by hand and each equals 4−(A₄+G₄) in its branch; each is nonnegative unconditionally, so no case analysis beyond the realized maxima is needed ✓. k=5 witness 22/5 > 4 exact. 200,000 exact samples: zero violations of d4-k4 and d3-k2 (§D).
- **Observation the manuscript should own:** h(3)=2 ≠ 1 and h(4)=4 ≠ 3, so the source conjecture **as literally stated is false at d = 3,4**; the parent's scoping (equality exactly for d ≥ 5, with h = (0,1,2,4,2d−5) overall) is the correct theorem and a small refinement of the source's claim. The parent already frames it this way; good.

### 2.5 Objections

**Decisive: none.** I looked specifically for: dimension slips (k=2d−5 vs d−3 offset — consistent), cardinality errors in both sharpness masks (none), zero-probability and tie handling (handled; high-p uniqueness even simplifies it), ordered vs unordered loop double-counting (handled by the k+1 / k+4 counting), assumed common ordering of a and g (none assumed), largest-geometric-inclusion failure (exchange argument valid; flagged by the parent itself for formalization), and monotonicity loopholes in the converse (downward-closed valid set; witness at 2d−4 suffices).

**Nondecisive (must be closed at the formal gate, not blockers at this stage):**
1. The finite-array endpoint — top-k semantics, mask cardinalities, the cᵢ counting lemmas, Σ_ij g² = (Σp)², and the exchange lemma for including g_uu — is unformalized. The parent says so; agreed.
2. check_bounds.py only samples square-weight parametrizations (w²/D). This is w.l.o.g. complete (any p is w=√p), but my independent check used general 10⁻¹²-grid weights with sparse/peaked/uniform families and found no violations either (10,800 vectors, d=3..11).
3. The numerical observation "max at odd k matches (d+√(d²−8))/2" is correctly not claimed; the proved bounds are looser but sufficient.
4. Checks.log does not state the toolchain version; PROOF.md claims Lean 4.34.1, corroborated by the .olean header. Re-running the build in the formal gate is advisable.

**Verdict: the proposed argument is a complete and correct proof at the mathematical level, pending formalization. No fatal gap found.**

---

## 3. BOUNDED NOVELTY verdict: **no prior resolution found** (serious but bounded search; open label correctly not treated as evidence)

- **Citation corpus (Semantic Scholar API):** exactly **3 citations**, retrieved: Sadri et al. *Accessible Maps…* (2201.12524), *Quantum and classical dynamical semigroups of superchannels…* (2109.03847, J.Math.Phys 63, 072204), *Construction of propagators for divisible dynamical maps* (2004.09264). I read all three abstracts via the arXiv API: **none addresses the conjecture**. Second S2 call hit **HTTP 429** (recorded; no empty-corpus inference).
- **Authors' trajectories:** Caro's subsequent work is quantum learning theory/cryptography (personal site + arXiv listing checked); Graswald's 2022 dissertation is *Mathematical Analysis of Electronic Structure Models* — different field; it embeds the same paper without resolution. **No erratum or addendum** to JMP 62, 042203 found (arXiv titling search).
- **Problem-specific channels:** MSE 3968126 (0 answers, benign comments), MathDB 347947 (all arrays empty) — both read live by me.
- **Closest general literature:** top-k/Ky-Fan majorization tools (e.g., Bapat's max-convolution survey) and mixed AG-mean inequalities (Holland/Kedlaya type) exist, but **nothing subsuming** the specific pair (a_ij, g_ij) with common index h(d) was found. The source's own provable bound ⌊2d−2√(2d)+1⌋ is far weaker than the proposed 2d−5 for large d, so no trivial subsumption.
- Ten recorded queries in `provenance.json`. No MathSciNet/zbMATH access presumed. **Bounded-novelty conclusion: no published or posted proof or subsuming theorem found; discovery credit is not excluded by anything I could locate.** (This can never rise to proof of worldwide priority; full formal gate still pending.)

---

## 4. Suggested Lean bridge (suggestions only; not authoring Lean)

1. Model top-k sums as a **sup over Finsets**: `A k p = ⨆ (S : {S : Finset (Fin d × Fin d) // S.card = k}), ∑ e ∈ S, a p e` (or via an existentially attained maximizer). This avoids literal sorted-`take` tie semantics entirely; monotonicity in k is then `mono` over sup domains.
2. The cᵢ extraction is cleanly `c i = ((S.filter (·.1 = i)).card + (S.filter (·.2 = i)).card : ℚ)/2`; the two counting lemmas reduce to `Finset.card_filter_le` plus the loop/interior double-count argument — modest but real combinatorial work.
3. `∑ i, ∑ j, (p i * p j) = (∑ i, p i)^2` via `Finset.sum_mul_sum`; keep probabilities in ℝ with `0 ≤ p i`, `∑ p i = 1`.
4. Exchange lemma: "a maximizer mask may be chosen to contain an index attaining the entrywise maximum" — a `Finset` replacement (`S \ {x} ∪ {uu}`) with monotonicity of the sum.
5. The four existing scalar theorems slot in as the terminal numeric steps; the sharpness side needs only `le_sup` from two explicit Finsets plus `field_simp` computations (already mirrored by `sharpness_selected_sum`).

## 5. Overall

| Gate | Verdict |
|---|---|
| Source (Conjecture 4.19 / IV.19, actual PDF + published body + MSE + MathDB) | **PASS** |
| Mathematics (all bounds + sharpness + small-d independently re-derived) | **PASS (proposed)** — no fatal gap |
| Bounded novelty (corpus, citations, follow-ups) | **No prior resolution found** |
| Formal (finite-array Lean endpoint) | **PENDING** — absent, correctly declared |
| Manuscript / packet / independent formal review | **PENDING** |

**Recommendation:** promote to the parent for separate formalization of the finite-array endpoint; tally remains 11/30, credit 0. This review does not constitute final acceptance.
