# MathDB 324342: refutation of the Etzion–Vardy–Yaakobi conference-matrix MDS conjecture

**Status: DRAFT.** This was prepared with AI assistance (Claude Opus 5.5) and has not been peer reviewed. No human authorship is claimed and no priority is claimed. Accepted credit is zero; only the project root can accept.

## 1. Target statement

**MathDB record.** The record is 324342, "Conference-matrix MDS code conjecture". It is cached in corpus chunk 0002 at line 3870, bound in `mathdb/mathdb-binding.json`. Its statement field reads:

> Let $p$ be a prime, and let ${\mathbb C}$ be a code of length $p+1$ constructed from a generator matrix that is a conference matrix. **Conference-matrix MDS conjecture.** The code ${\mathbb C}$ is an MDS code of dimension $\frac{p+1}{2}$ and minimum Hamming distance $\frac{p+3}{2}$. This would give an MDS code with parameters determined by the rank of a conference matrix over ${\mathbb Z}_p$; the source provides no resolution of the claim.

Hashes of the raw line:
- sha256 without the trailing newline: `73a0bb420a99d35212e9d73c002d9d5721c69c7f2f1f62c48d2f78218b281342`. This is the hash recorded by conference-fidelity-review-r1.
- sha256 with the trailing newline: `12a701a2d4ba91a49c026f0c772537d3029ffe17dda34fbbfe8fdb86b087c55f`. This is the hash recorded by held-reopen-r1.

Both hashes are of the same bytes, and the raw line is byte-identical to the copy in held-reopen-r1.

**Source.** T. Etzion, A. Vardy and E. Yaakobi, "Coding for the Lee and Manhattan metrics with weighing matrices". The conjecture appears in four versions, all with the same parameters:

| Version | Location |
|---|---|
| arXiv:1210.5725 v1 (21 Oct 2012) | Conjecture 5, p. 4 |
| arXiv:1210.5725 v2 (11 Dec 2012) | Conjecture 5, p. 6 |
| ISIT 2013 | Conjecture 1, p. 3 |
| IEEE Trans. Inform. Theory 59(10) (2013), pp. 6712–6723, doi:10.1109/TIT.2013.2268156 | Conjecture 1, p. 6715; open problem 2, p. 6722 |

The journal version was read from an author-posted copy of the IEEE typeset article, rendered page by page in `sources/tit2013-rendering/`.

Journal wording, checked against the rendered p. 6715:

> Conjecture 1: If ℂ is a code of length p + 1 constructed from a generator matrix which is a conference matrix then ℂ is a maximum distance separable (MDS) code of dimension (p+1)/2 and minimum Hamming distance (p+3)/2.

**Source definitions** (arXiv v2 p. 4; journal p. 6713):
- A weighing matrix W_{n,w} is an n × n matrix over {0, 1, −1} with exactly w nonzero entries in every row and column and W Wᵀ = w I_n.
- A conference matrix is a weighing matrix with w = n − 1.
- The source does not require a zero diagonal, symmetry or skewness.
- Theorem 1 reduces the lattice Λ(W) to a code over ℤ_w. For a conference matrix of order p + 1, w = p.
- Theorem 4: if W is a conference matrix of order n = p + 1 with p prime, then its rank over ℤ_p = 𝔽_p is (p + 1)/2.

**Scope.** The claim is universal: for every prime p and every conference matrix W of order p + 1, the 𝔽_p-code C(W) is MDS, has dimension (p + 1)/2, and has minimum Hamming distance (p + 3)/2. The source's remark about Paley matrices up to n = 23 describes the evidence; it is not a hypothesis. A single counterexample refutes the statement.

**The code.** C(W) is the image of Λ(W) = ℤ-span(rows of W) under coordinatewise reduction mod p. Reduction is additive and maps ℤ onto 𝔽_p, so C(W) equals the 𝔽_p-span of the reduced rows. Lean proves this as `latticeCode_eq_rowCode`, for every p, n and W.

## 2. Ordinary proof

Rows and columns are indexed 0, …, 19.

**Matrix.** Take the ±1 sequences
- a = (1, 1, 1, −1, −1);
- b = c = (1, 1, 1, 1, −1);
- d = (1, 1, −1, 1, −1).

Let A, B, C, D be their 5 × 5 circulants, let R be the back-diagonal permutation, and let H be the Goethals–Seidel array:

[A, BR, CR, DR; −BR, A, DᵀR, −CᵀR; −CR, −DᵀR, A, BᵀR; −DR, CᵀR, −BᵀR, A].

Put W = H − I. W is printed in full in the paper and in `data/witness-check.json` (`matrix_W`), and it is identical to `Wrows` in the Lean file.

**Proposition 1: W is a skew conference matrix.** W has zero diagonal, ±1 entries off the diagonal, Wᵀ = −W and W Wᵀ = 19 I. Hence every row and every column has 19 nonzero entries, so W is a weighing matrix W_{20,19}, which is a conference matrix in the source's sense.

*Proof.*
1. The periodic autocorrelations are:

   | Sequence | Shift 1 | Shift 2 |
   |---|---|---|
   | a | 1 | −3 |
   | b | 1 | 1 |
   | c | 1 | 1 |
   | d | −3 | 1 |

   P(t) = P(5 − t), so the four autocorrelations sum to 0 at every nonzero shift. Therefore Σ XXᵀ = 20 I.
2. Circulants commute, and XR = RXᵀ is symmetric. Block multiplication then gives HHᵀ = 20 I. For example, block rows 1 and 2 give −ABR + BAR + CD − DC = 0.
3. Since a is skew-type, A + Aᵀ = 2I. Each off-diagonal block of H is symmetric and is the negative of its mirror block, so H + Hᵀ = 2I.
4. Hence Wᵀ = I − H = −W, and W Wᵀ = HHᵀ − H − Hᵀ + I = 19 I.

The finite facts are also verified entry by entry, by Lean (`decide +kernel`) and by `tools/check_witness.py`. ∎

**Proposition 2: dim C = 10.**

*Proof.*
- **Upper bound.** W Wᵀ ≡ 0 (mod 19), so C ⊆ C^⊥ and 2 dim C ≤ 20.
- **Lower bound.** Let A₀ be the block of rows 0–9 and columns 0–9. The printed 10 × 10 matrix B₀ satisfies A₀B₀ = B₀A₀ = I over 𝔽₁₉, so rows 0–9 are independent.
- **Cross-check.** Lean uses an explicit 20 × 10 matrix D expressing every row as a combination of rows 0–9. Fresh Gaussian elimination in `check_witness.py` also gives rank 10. ∎

**Proposition 3: a weight-9 codeword.** Let

x = (5, 7, 13, 9, 0, 15, 14, 2, 8, 18, 0, …, 0).

The integer vector xW is

(−38, −38, −38, −38, −19, 34, 57, 19, −9, 1, 37, 57, 9, 19, 37, −43, −33, −23, −19, −19).

Reducing mod 19 gives

c = (0, 0, 0, 0, 0, 15, 0, 0, 10, 1, 18, 0, 9, 0, 18, 14, 5, 15, 0, 0) ∈ C.

Its support is {5, 8, 9, 10, 12, 14, 15, 16, 17}, so its weight is 9. ∎

**Theorem.** The conjecture is false.

*Proof.* Take p = 19 and the matrix W.
- C is a [20, 10] code.
- d(C) ≤ wt(c) = 9.
- 9 < 11 = 20 − 10 + 1 = (p + 3)/2.

So C is not MDS, and d(C) ≠ (p + 3)/2. The dimension clause, which is the source's Theorem 4, holds. ∎

**Normal form.** The source normalizes the first row to zeroes followed by +1's. Negating columns 3, 4, 5, 10, 15 and 17 achieves this here. That is a monomial change, so weights are preserved and the image of c still has weight 9 (`normal_form_word_weight` in `data/witness-check.json`).

## 3. What is credited and what is not

**Credited scope**, per conference-significance-adjudication-r2 and the root rulings: an explicit order-20 conference matrix whose 𝔽₁₉ row code contains a nonzero word of weight ≤ 9. This refutes the conjecture in its exact universal scope.

**Not credited.** The following are ordinary supporting computation or known background only:
- d = 9 exactly, and the 180 projective weight-9 words (r4 enumeration over all 184,756 ten-column sets; recomputed by conference-significance-review-r1);
- the fact that Paley matrices give doubly extended Reed–Solomon (MDS) codes;
- the order-20 two-class dichotomy, which rests on a secondary classification table;
- minimality of p = 19.

**Lean.** Lean proves d ≤ 9, not d = 9.

**Significance.** The adjudication gave a qualified pass at the minimum threshold: a finite refutation with no structural theorem.

## 4. Lean correspondence

The endpoint `ConferenceMDS.conjecture5_false : ¬ ConferenceMDS.Conjecture5` is in `lean/324342-replay-fit-source.zip`:
- ZIP sha256 `c6977a39d3f5aa81122c6ad9c2d374bcadc281dccf577208fbda31eac2e1a00f`;
- module `ConferenceMDS324342.lean`, sha256 `38d5bb48…0a12`.

The source notions map to Lean declarations as follows:

| Source notion | Lean declaration |
|---|---|
| Weighing matrix | `IsWeighingMatrix` |
| Conference matrix | `IsConferenceMatrix` (w = n − 1); textbook variant `IsStdConferenceMatrix` |
| Code from the rows | `rowCode` (ZMod p span of the reduced rows) |
| Code reduced from the lattice | `latticeCode`; equal to `rowCode` by `latticeCode_eq_rowCode` |
| Minimum distance | `minDistance` (via `hammingDist`); variant `minWeight` |
| MDS | `IsMDS` (Singleton equality) |
| Dimension | `Module.finrank` |
| The conjecture | `Conjecture5`, quantified over every prime p and every integer matrix of order p + 1 satisfying `IsConferenceMatrix` |

Companion theorems:
- `counterexample`;
- `conjecture5Std_false`;
- `mds_claim_false`;
- `distance_claim_false`;
- `conjecture5_minWeight_false`;
- `latticeCode_eq_rowCode`.

Control: `Control.paley3_satisfies` shows that the order-4 Paley matrix satisfies every clause.

**Import change.** The packet differs from the frozen r4 module only in its import lines (`lean/324342-imports.diff`). `import Mathlib` was replaced by six specific Mathlib modules. The body after the imports has sha256 `c0b023540ad8fd5325c96f20f34a841ba9aab61d5563015c24a335d0977f414f`, the same in both versions. Audit.lean and Controls.lean are byte-identical. MetadataAudit.lean is new audit code.

**Root replay** (`receipts/root-replay/`).
- Steps: safe extraction, then strict `lean -j1 -M3500 -DwarningAsError=true` builds of all 4 modules, then explicit-module leanchecker on each.
- Outcome: all exit codes 0. Every call stayed under 140 s wall time and 6 GiB. Peak RSS was 2.93 GB.
- Axioms: the endpoint and all companions use only propext, Classical.choice and Quot.sound.
- Audits: the Audit module covers 90 declarations and MetadataAudit covers 116. None is unsafe, partial, implemented_by, extern or _unsafe_rec.

**Trust limits.**
- The Lean kernel and leanchecker are trusted.
- Prebuilt Mathlib objects at the pinned revision (Lean 4.34.1, Mathlib d13f23b7…) are trusted, not rebuilt.
- Statement fidelity is a reviewed human judgment.
- Theorem 4 is not formalized in general.

## 5. Prior-art limits (held-reopen-root-ruling-r1)

**Arasu–Gulliver 2001.** Self-dual codes over F_p and weighing matrices, IEEE TIT 47(5), 2051–2055, doi:10.1109/18.930940.
- The paper is closed access. Its Section 2 remarks and tables were **not read**.
- Its constructions, as described in the read Armario–Frau arXiv:1311.2637 §1.2 (Propositions 1.3–1.4, Table 1), need α² + k ≡ 0 or α² + β² + k ≡ 0 (mod p) with α, β ≠ 0.
- At p = k = 19 these become α² = 0 or α² + β² = 0. Both are impossible, because −1 is not a square mod 19 (`data/witness-check.json`).
- Those constructions give length 2n = 40, not 20.
- A length-n row-code remark in the unread tables is **not excluded**.

**Grassl–Gulliver 2008.** ISIT, doi:10.1109/ISIT.2008.4595330. The body is unread; this is low risk. EVY cite it only for the existence of self-dual MDS codes of length q + 1.

**Other searches.** All are bounded:
- the bodies of 7 citing works were read; the others were checked by title only;
- openai/math head `4eaee875`, by path screen;
- Omega head `342d478c`, by complete D5 and Problems path screens with hit review (2026-11-04);
- the cached MathDB record.

No resolution was found. This is not a worldwide clearance, and no priority is claimed.
