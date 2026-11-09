# Candidate: Hetyei's interval-transform kernel conjecture is false (MathDB 347230), with companion 347231

Lane expanded-corpus-r240 (Claude). Zero accepted credit until root review. No Lean was run in this lane.

## 1. Target and exact statement

* MathDB 347230, "The kernel conjecture for the second-kind interval transform". The corpus line is in
  `raw/347230.jsonl`, with provenance and hashes in `extracted.json`.
* Source: G. Hetyei, *The type B permutohedron and the poset of intervals as a Tchebyshev transform*.
  * arXiv:2007.07362v2 (19 Jul 2020), Conjecture 5.14.
  * Published version: Discrete Comput. Geom. 71(3) (2024) 918–944, doi 10.1007/s00454-023-00490-4, Conjecture 39 (open-access HTML read; `sources/springer-s00454-023-00490-4.html`).
  * The wording is identical in both versions.

> **Conjecture 39.** For each n ≥ 1, the kernel of I₂ : ℚ⟨a,b⟩ₙ → ℚ⟨a,b⟩ₙ₊₁ is A_ℚ⟨a,b⟩ₙ.

The definitions are in Section 6 of the published version (Section 5 of the arXiv version):

* **Words and reversal.** ℚ⟨a,b⟩ₙ is spanned by the ab-words of length n. u ↦ u* reverses words and is extended linearly.
* **Symmetric and antisymmetric parts.** A_ℚ⟨a,b⟩ₙ = {u : u* = −u} and S_ℚ⟨a,b⟩ₙ = {u : u* = u} (Definition 34). Their dimensions are 2ⁿ⁻¹ ∓ 2^⌊(n−1)/2⌋ (Proposition 35).
* **The operator** (Theorem 32):

  I₂(u) = u + u* + Σ_u M(u₍₁₎*, u₍₂₎).

  * Δ is the Ehrenborg–Readdy coproduct, Δ(v₁⋯vₙ) = Σᵢ v₁⋯vᵢ₋₁ ⊗ vᵢ₊₁⋯vₙ.
  * M is the Ehrenborg–Readdy mixing operator (ER, J. Algebraic Combin. 8 (1998), Definition 9.1).
  * Theorem 32 states that Ψ_{Î₂(P)} = I₂(Ψ_P) for every graded poset P. Here Ψ_{Î₂(P)} = Σ_{x∈P} Ψ_{[[x,x],[0̂,1̂]]}, and each such interval is [0̂,x]* × [x,1̂] (Proposition 30).
  * I₂ preserves degree. The codomain "n+1" in the printed conjecture is immaterial for the kernel.
* **Already known.** A ⊆ ker I₂ is Corollary 33. The conjecture asserts equality, i.e. that I₂ is injective on Sₙ.

## 2. Result

**Theorem A.** Let u ∈ ℚ⟨a,b⟩₅ be the integer combination

```
u =  aaaba + aaabb − 2 aabaa − aabba + aabbb + abaaa + abaab − abbaa + abbab − 2 abbba
   − 2 baaab + baaba − baabb + babba + babbb + bbaaa − bbaab − 2 bbabb + bbbaa + bbbab .
```

Then u* = u, u ≠ 0 and I₂(u) = 0. Hence u ∈ ker I₂ but u ∉ A_ℚ⟨a,b⟩₅, since u = −u* = −u would force u = 0. So Conjecture 39 fails at n = 5.

More precisely, the following was computed with exact rational and fraction-free integer elimination:

* rank I₂|₅ = 19 and dim ker I₂|₅ = 13 = dim A₅ + 1, so ker I₂|₅ = A₅ ⊕ ℚu.
* The conjecture holds for n ≤ 4: the kernel dimensions are 0, 1, 2, 6, equal to dim Aₙ.
* For n = 6 and 7 the kernel dimensions are 30 and 63, against dim Aₙ = 28 and 56.
* A mod-p rank computation (p = 1000003) suggests the excess keeps growing: ranks 120 at n = 8 and 229 at n = 9, giving kernel dimension at most 136 and 283 against dim Aₙ = 120 and 240.

**Proof of Theorem A.** This is a finite computation in a 32-dimensional space.

1. u is visibly reversal-invariant. Its 20 words are the 4 palindromes aabaa, abbba, baaab, bbabb (coefficient −2 each) and 8 reversal pairs with equal coefficients, for example aaaba/abaaa and aaabb/bbaaa.
2. I₂ is expanded on each of the 20 words using the definitions above. For each length-5 word w, I₂(w) has coefficient sum 64 = 2⁶.
3. The weighted sum of the 20 expansions, 1280 unit terms in total, cancels on all 32 words of length 5.

The two hand-checkable degree-3 expansions in Section 4 show the mechanics. The full expansion is reproduced by `scripts/hetyei_certificates.py` and `scripts/hetyei_expand.py`. ∎

**Validation of the operator.** Two independent implementations agree on every word of length ≤ 7 (`logs/hetyei_compare_vbu_7.log`):

1. **Poset implementation** (`scripts/hetyei_I2.py`). This works in flag-f coordinates. I₂ is computed as Σ_x (flag f-vector of [0̂,x]* × [x,1̂]), with the product of chain pieces counted by Delannoy lattice paths. It was checked against explicit brute-force interval posets for 20 graded posets, including the Boolean algebras B₁–B₄ and 16 random graded posets of rank ≤ 5, with 0 mismatches (`logs/hetyei_check.log`).
2. **Literal implementation** (`scripts/hetyei_literal_vbu.py`, `scripts/hetyei_certificates.py`). This is Theorem 32 with ER Definition 9.1 and the ER coproduct.

Since both are linear and ab-indices of graded posets span ℚ⟨a,b⟩ₙ, agreement on posets already pins down the operator. (The doubled-chain posets have flag f-vectors 2^{|S∩T|}, a tensor power of an invertible 2×2 matrix.) Corollary 33 (I₂(u*) = I₂(u)) also holds for all words up to length 6.

## 3. Fidelity issue: a misprint in Hetyei's Definition 31

Both versions of Hetyei print M₂,₁,₂(u,v) = u·b·v. Ehrenborg–Readdy's Definition 9.1, which Hetyei cites as the definition (`sources/ER-coproduct.pdf`, p. 20), has M₂,₁(u,v,2) = v·b·u. The printed variant is not the intended operator:

* It gives M(a,1) = aa + 2ab. This is not the ab-index aa + ab + ba of the product of chains of ranks 2 and 1, so ER Theorem 9.2 and Hetyei's Theorem 32 fail for it.
* With the printed M, I₂ is injective on ℚ⟨a,b⟩ₙ for n ≤ 6 (`logs/hetyei_gen_printed_6.log`). That contradicts Hetyei's own Corollary 33.

So the conjecture fails under both readings:

* Under the intended (ER) operator, ker ⊋ A₅. This is the substantive refutation.
* Under the misprinted operator, ker = 0 ≠ Aₙ for n ≥ 2. This is a misprint artefact and claims no credit.

The refutation in Theorem A uses only the cited ER definition and does not depend on any faulty source lemma.

## 4. Companion: MathDB 347231 (Conjecture 40 / 5.15), secondary

> **Conjecture 40.** For each n ≥ 1, a generating set of S_ℚ⟨a,b⟩ₙ consisting of eigenvectors only may be found by taking all possible n-fold compositions of Pyr : u ↦ M(1,u) and L : u ↦ (a−b)u + u(a−b), applied to 1.

**Theorem B.** S_ℚ⟨a,b⟩₃ is not spanned by I₂-eigenvectors that lie in S_ℚ⟨a,b⟩₃. Hence no generating set of S₃ consisting of eigenvectors exists, whichever compositions are taken.

*Proof.* Using ER Definition 9.1:

* M(1,ab) = aab + aba + abb + bab
* M(a,b) = aab + aba + abb + baa + bab + bba
* M(aa,1) = aaa + aab + aba + baa

So

I₂(aab) = aab + baa + M(1,ab) + M(a,b) + M(aa,1) = aaa + 4aab + 3aba + 2abb + 3baa + 2bab + bba.

By Corollary 33, I₂(baa) = I₂(aab). With s₀ = aab + baa ∈ S₃, the image I₂(s₀) has coefficient 8 at aab and 6 at baa, so it is not symmetric.

Let α(v) = v(aab) − v(baa). Then α vanishes on S₃. If g ∈ S₃ and I₂g = c·g, then α(I₂g) = c·α(g) = 0. So every such eigenvector lies in the hyperplane {s ∈ S₃ : α(I₂ s) = 0}, while α(I₂ s₀) = 2 ≠ 0. ∎

Exactly, the eigenvectors in S₃ span 5 of the 6 dimensions: eigenvalue 2 gives 1, eigenvalue 4 gives 2, eigenvalues 8 and 16 give 1 each (`logs/hetyei_certificates-3.log`). The same deficiency holds for n = 4, 5, 6: 7 of 10, 13 of 20, 19 of 36 (`logs/hetyei_spec2_1_6.log`).

Further facts:

* **Hetyei's Lemma 36 is false.** u = Ψ(B₃) = aa + 2ab + 2ba + bb is an eigenvector with eigenvalue 8, but L(u) is not an eigenvector.
* **Compositions fail early.** L∘Pyr∘Pyr(1) is not an eigenvector.
* **No spanning at n = 7.** The 128 compositions span only 71 < 72 = dim S₇.

The refutation of Theorem B does not rely on Lemma 36 being false.

**Significance caveat.** Theorem B is elementary: I₂ does not commute with reversal. It also comes from the same source as 347230, and root may treat the pair as one family. 347230 is the main candidate.

## 5. Prior art and novelty screen (bounded)

* **arXiv.** v1 and v2 read (v2 adds the second edgewise triangulation connection; the conjectures are unchanged). The 2019 Charlotte preprint version has no Section 5.
* **Published version.** DCG 2024 open-access HTML read; Conjectures 39 and 40, the misprint and Lemma 36 are all unchanged.
* **Web searches.** No later treatment of the conjecture found. Searches covered "interval transform of the second kind", Hetyei with kernel/antisymmetric, and the citing work arXiv:2408.07698v2, which uses Hetyei's Tchebyshev work but not this conjecture.
* **Registries** (`outputs/registry-screen.json`). All clean:
  * Lean Pool HEAD 01db1d70: complete tree, no hit.
  * Omega trureturing HEAD 046c7ac2: issue search for 2007.07362 or Hetyei, no relevant hit.
  * OpenAI/math HEAD 4eaee875: cached preprint listing, no hit.
  * GitHub repository and issue searches: 0 hits.
* **Campaign history.** No prior lane treated 347230 or 347231 (`outputs/history-screen.json` hits are hash-substring coincidences).
* **Limits.**
  * Semantic Scholar, Crossref and the arXiv search API are denied, so the citing-works list is not exhaustive.
  * Omega D5/Problems trees were not refetched at the new head.
  * Hetyei's own later papers were checked only by title search.

**Credit-risk assessment against the exclusion precedents:**

* Not a source-formula evaluation: the source gives no formula for the kernel.
* Not a smallest-parameter or endpoint correction: the failure persists and grows for n = 5, 6, 7, 8, 9.
* Not a consequence of a faulty source theorem: Corollary 33 and Theorem 32 are correct for the ER operator.
* Not a modification of a printed example.

The open risk is a significance judgement: the certificate is a modest linear-algebra computation that the author did not run.

## 6. Lean plan (uncompiled draft: `lean-draft/HetyeiIntervalTransform.lean`)

**Definitions.**

* Word := List Bool (false = a, true = b).
* ℚ⟨a,b⟩ is `Word →₀ ℚ`.
* star = `Finsupp.lmapDomain List.reverse`.
* deg n = `Finsupp.supported` on words of length n.
* anti n = deg n ⊓ ker(star + id) and symm n = deg n ⊓ ker(star − id).
* `cop` gives the coproduct pieces and `Mrs r s n u v` gives ER's M_{r,s}(u,v,n), structurally recursive in n, with ER's index-set parity filter.
* `Mw` sums n over 2..|u|+|v|+2. A lemma is needed that higher n vanish: each recursion step consumes one letter.
* `I2w` is Theorem 32 on words, and I2 is the `Finsupp.linearCombination` extension.

**Endpoints.**

* `not_KernelConjecture : ¬ ∀ n ≥ 1, deg n ⊓ ker I2 = anti n`.
* `not_EigenGeneration : ¬ ∀ n ≥ 1, ∃ G ⊆ {eigenvectors in symm n}, span G = symm n`. This is a consequence of Conjecture 40 under any reading of the composition clause.

**Computation.** The kernel checks are `decide` on Bool/Int list computations, with about 1280 unit terms for I2(u). No `native_decide`.

**Remaining lemmas** (marked `sorry` in the draft, all routine):

* (i) `I2_toPoly`: linearity bridge from formal sums to Finsupp.
* (ii) `toPoly_eq_zero_of_coeff`: coefficient extraction.
* (iii) membership of uCert in deg 5, star-invariance and nonvanishing.
* (iv) `alpha_symm`, `s0_symm` and `alpha_I2_s0` (decide).
* Optional fidelity lemma: vanishing of M_{r,s}(u,v,n) for n > |u|+|v|+2.

**Fidelity review must check:**

* that the ER v·b·u base case is the paper's intended operator (Section 3 above);
* that "kernel of I₂ : ℚ⟨a,b⟩ₙ → …" is read as ker of the restriction to degree n.

**Expected Lean cost:** small to moderate. The definitions are short and the certificate is about 32 coordinates.
