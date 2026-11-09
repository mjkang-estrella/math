# Candidate 332037: a counterexample to Smyth's combinatorial injection conjecture

**MathDB 332037**, "The combinatorial injection conjecture for dominance order on compositions".
**Source:** Clifford Smyth, *A Probabilistic Characterization of the Dominance Order on Partitions*, arXiv:1512.04084 (v1, 13 Dec 2015, the only arXiv version), Conjecture 1.5. Published in *Order* 35 (2018) 393–402. The published body was not read because it is paywalled; see §6.

Status: a candidate only. There is no accepted credit, and the Lean source is an **UNCOMPILED draft**.

## 1. Statement (source, verbatim content)

Notation: U^m is the set of maps λ : [m] → ℕ (compositions with m non-negative parts), U^m_n = {λ ∈ U^m : |λ| = n}, and λμ is concatenation. Compositions are ordered by dominance of their non-increasing rearrangements: λ ⊵ μ iff λ_p ⊵ μ_p. For partitions, μ ⊵ λ iff |λ| = |μ| and Σ_{i≤j} λ(i) ≤ Σ_{i≤j} μ(i) for all j (source p. 3, "λ E µ (or µ D λ)").

> **Conjecture 1.5.** For all integers A, a, B, b with A ≥ B ≥ 0 and a ≥ b ≥ 0 there is an injection γ : U^A_b × U^B_a ↪ U^A_a × U^B_b such that for all (λ1, μ1) ∈ U^A_b × U^B_a, (λ2, μ2) = γ((λ1, μ1)) satisfies λ1μ1 ⊵ λ2μ2.

The MathDB record matches this exactly, including the quantifier ranges, the domain and codomain, and the direction of dominance.

**Orientation check.** In the source's proof of Theorem 3.1, the injection must give p_{λ1μ1} ≤ p_{λ2μ2} for TN2 sequences p. By Lemma 2.1(iii), λ ⊵ μ implies p_λ ≤ p_μ. So the source must dominate the image, which is the orientation used here. (The text of Theorem 3.1 has a sign typo, "p_{λ1µ1} ≥ p_{λ2µ2}", immediately followed by the correct "p_{λ1µ1} ≤ p_{λ2µ2}".)

## 2. Theorem (refutation)

For (A, a, B, b) = (3, 20, 2, 19) no such injection exists. Hence Conjecture 1.5 is false.

**Certificate.** Let G be the following set of 8 partitions of 39 into 5 parts:

    (13,12,8,4,2) (13,13,7,3,3) (12,12,8,6,1) (14,12,6,4,3)
    (13,11,7,7,1) (14,11,6,6,2) (15,11,5,5,3) (16,10,5,4,4)

Let D be the set of partitions ν of 39 with g ⊵ ν for some g ∈ G. Define X = U^3_19 × U^2_20 (|X| = 210 · 21 = 4410) and Y = U^3_20 × U^2_19 (|Y| = 231 · 20 = 4620). Let

* S = {(λ, μ) ∈ X : (λμ)_p ∈ D}, with |S| = **1137**;
* T = {(λ, μ) ∈ Y : (λμ)_p ∈ D}, with |T| = **1134**.

**Proof.** Suppose γ is as in the conjecture and take x ∈ S. Then some g ∈ G satisfies g ⊵ (x concatenated)_p, and by hypothesis that concatenation dominates the concatenation of γ(x). Dominance is transitive, because it is defined by sum equality and a family of partial-sum inequalities. So g dominates the concatenation of γ(x), and γ(x) ∈ T. Thus γ maps S into T. Since |S| = 1137 > 1134 = |T|, γ is not injective on S, a contradiction. ∎

The proof needs nothing beyond the two counts and transitivity. Both counts were verified by `verify_certificate.py`, a standalone script using literal definitions: compositions are enumerated by `itertools.product` with a sum filter, and dominance is checked with all partial sums on zero-padded rearrangements. The script records sha256 hashes of the sorted lists S and T and also checks the closure property directly on types.

## 3. Lean statement-correspondence plan (draft `Smyth1512Refutation.lean`, UNCOMPILED)

| Source object | Lean |
|---|---|
| U^m_n | `U m n : Set (Fin m → ℕ) := {f | ∑ i, f i = n}` |
| λ_p (non-increasing rearrangement) | `rearr f := (List.ofFn f).insertionSort (fun x y => y ≤ x)`; it is the sorted permutation (`List.sorted_insertionSort` and `List.perm_insertionSort` give fidelity; the proof uses only the permutation property) |
| partition dominance, all j, padding with zeros | `DomL l₁ l₂ := l₁.sum = l₂.sum ∧ ∀ j, (l₂.take j).sum ≤ (l₁.take j).sum`; taking past the length gives the full sum, which equals zero padding |
| λ ⊵ μ on compositions | `Dom f g := DomL (rearr f) (rearr g)` |
| λμ | `Fin.append` |
| Conjecture 1.5 | `Conjecture15 : ∀ A a B b : ℕ, B ≤ A → b ≤ a → ∃ γ : (U A b × U B a) → (U A a × U B b), Function.Injective γ ∧ ∀ x, Dom (concat x.1.1 x.2.1) (concat (γ x).1.1 (γ x).2.1)` |
| endpoint | `theorem not_conjecture15 : ¬ Conjecture15` |

Kernel work is limited to `SL.length = 1137`, `TL.length = 1134` and `gens` lengths, all by `decide`. These are filters over a structurally recursive enumerator `comps`, with insertion sort and prefix sums on 5-element lists; there is no well-founded `mergeSort`. The bridges are:

* `mem_comps`: membership in `comps m n` iff length m and sum n;
* `nodup_comps`: no duplicates, so `SL.toFinset.card = 1137`;
* `domB_iff`: the Boolean prefix test with j ≤ 5 is exact for length-5 lists;
* `DomL.trans`;
* `rearr_concat`, via `List.ofFn_fin_append`;
* realisation of list pairs as subtype elements (`toFun`, `ofFn_toFun`);
* the counting step `Finset.card_le_card_of_injOn`.

Lemma names may need adjustment for the pinned Mathlib. Watch especially `List.flatMap`, `List.nodup_flatMap`, `List.ofFn_fin_append`, `List.length_insertionSort` and `List.getD_eq_getElem`.

## 4. Search coverage and structure (diagnostics)

* Type-level exact max flow over all (A, B, a, b) with A ≤ 10, a ≤ 10 (b < a) and a + b ≤ 16: no failure (3900 cases). This uses `scripts/smyth.py`: edges depend only on rearranged types, so the max injection equals the max flow on the type network.
* The fast network (`scripts/smyth_fast.py`) uses unit Robin Hood transfer edges, which generate dominance among partitions with at most A + B parts (Muirhead). All (a, b) with a + b ≤ n_max: (A,B) = (3,2) to n = 39 has a single failure, (20,19). (4,2) to 38, (4,3) to 36, (5,2) to 30, (5,3) to 28 and (5,4) to 26 have none. Gap-1 scans: (4,3) and (4,2) to b = 25, (5,4), (5,3) and (5,2) to b = 20, none. (3,2) with gap 2 or 3: none to b = 30.
* **Infinite pattern (not proved):** for (A, B) = (3, 2) and a = b + 1, the maximum injection is short for every b = 19, …, 43, with deficiencies 3, 5, 9, 12, 16, 22, …, 135 (`outputs/smyth-family-3-2.json`). Every b ≤ 18 passes.
* The conjecture holds trivially when A = B (swap) or a = b. For B = 1 there is a short proof: (λ1, (a)) ↦ (λ1 + (a−b)e_1, (b)) is injective, and {λ1(1), a} majorizes {λ1(1)+a−b, b}.
* Natural proof routes were tested and fail: pairwise Robin Hood inside coordinate pairs fails at c = (2,2), and the one-step equal-size lemma (u, v) → (u+1, v−1) fails at B = 2, (2,4) → (3,3). The conjecture survives only in aggregate until n = 39, which is consistent with nobody having noticed.

## 5. Credit-rule checks (for root)

* **Source's own theorems:** Theorem 1.4 (TN2 ⇒ TN2) is proved independently in the source and remains true. The counterexample does not contradict any source statement: Theorem 1.4 concerns only product weights p_λ with p log-concave, and the Hall violator is an indicator of a down-set, which is not of product form. This is not a correction of a source theorem.
* **Cited constructions or generic failure:** none known. The obstruction is a 3-element deficiency at n = 39. It is not a classical extremal object and not a parameter or endpoint convention.
* **Family check:** it is unrelated to the credited 338258 (Riordan *graphs*) and 366371 (ordinal majorization). The ledger has no "Smyth", "1512.04084" or "dominance order".
* **MathDB fidelity:** identical to the source. The domain is ℕ, and both concatenations have the same length A + B and total a + b.

## 6. Prior-art and registry checks (dated 2026-11-04 UTC)

* arXiv abs 1512.04084 lists only v1, with no withdrawal or comment (receipt `sources/abs-1512.04084.receipt.json`).
* Springer page for the published version (Order 35, 393–402, DOI 10.1007/s11083-017-9438-z): HTTP 200, abstract and references only. The abstract does not mention the conjecture. **Gap:** I could not read whether the published body still states Conjecture 1.5, or states it in modified form.
* Semantic Scholar citations of arXiv:1512.04084 (6 papers: Zhu 2026, Hassler 2026 arXiv:2601.20590, Wang–Zhang–Liang 2024, Mao–Mu–Wang 2021 arXiv:2107.08436, Zhu 2020 arXiv:2006.14485, Liang–Zhang–Wang 2024). Titles only; none is about the injection conjecture, and their bodies were not read. Web searches (standard and extended) found no proof or refutation.
* OpenAI/math HEAD 4eaee87548250b2682affda7d05d947c05554bae is unchanged from root's 2026-11-03 value. The cached tree path screen has no match.
* Omega trureturing HEAD **1764a0c7f33be6acf6dcaf4ad4007da021469ae9**, newer than root's 86172888. The full D5 tree (13911 entries, not truncated) and the Problems tree (1717 entries) were fetched live. A path screen for smyth, dominance, majoriz and injection found no item on this conjecture. This is a path screen only, not proof reading.
