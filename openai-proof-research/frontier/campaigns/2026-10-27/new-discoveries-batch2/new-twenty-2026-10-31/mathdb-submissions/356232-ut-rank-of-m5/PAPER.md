# The monoid ⟨a, b | aba = ba⟩ has UT-rank exactly 4

*Claude Opus 5.5 produced the proof, the Lean formalization, and the first review. GPT-6.2 Sol conducted the cross-model review and edited this manuscript. The companion Lean appendix contains the formal proof of Conjecture 2.11. Bracketed names identify Lean declarations.*

## Abstract

C.-F. Nyberg-Brodda conjectured that the one-relation monoid M5 = Mon⟨a, b | aba = ba⟩ embeds as a semigroup in the upper-triangular tropical matrices UT4(ℤ̄), but not in UT3(ℤ̄) or UT2(ℤ̄). Here ℤ̄ = (ℤ ∪ {−∞}, max, +). We prove this conjecture.

- **Upper bound.** We verify the source’s proposed UT4 embedding with B₁₁ = −1. The printed value B₁₁ = 1 yields a collision.
- **Lower bound (the new part).** For every pair A, B ∈ UT3(ℤ̄) with ABA = BA, two distinct normal forms of M5 have the same image under a ↦ A, b ↦ B.
  - The argument uses the diagonal constraints forced by the relation and explicit formulas for powers of 3 × 3 triangular matrices.
  - An integer lattice shift produces two distinct exponent triples with the same image.

The whole statement, including the definitions, is formalized in Lean 4 with Mathlib. The only axioms used are propext, Classical.choice and Quot.sound.

## 1. Source and statement

**Source.** C.-F. Nyberg-Brodda, *Tropical one-relation monoids*, arXiv:2209.12612 (v1, 26 Sep 2022, the only version).

In [NB22, pp. 2–4 and Table 1], ℤ̄ denotes the integers with −∞ adjoined, with addition ⊕ given by maximum and multiplication ⊗ given by ordinary addition extended by absorption at −∞. Tropical matrix multiplication is (AB)ᵢⱼ = ⊕ₖ Aᵢₖ ⊗ Bₖⱼ. Upper triangular matrices have all entries below the diagonal equal to −∞. The UT-rank is the least positive dimension in which there is an injective multiplicative map of the monoid into these matrices.

**Conjecture 2.11 [NB22, p. 11].** The monoid M5 = Mon⟨a, b | aba = ba⟩ has UT-rank exactly 4.

MathDB record 356232 asks for the same rank and describes the dimension-four upper bound as known. Section 3 verifies the upper bound using the corrected matrix of Lemma 2.9.

**Lean definitions** (module `M5Defs`):

```lean
abbrev Zbar := MinTropical (WithTop ℤᵒᵈ)            -- (ℤ ∪ {−∞}, max, +)
def UT (n : ℕ) : Subsemigroup (Matrix (Fin n) (Fin n) Zbar) where
  carrier := {M | ∀ i j, j < i → M i j = 0}           -- 0 of Zbar is −∞
def rel5 : FreeMonoid (Fin 2) → FreeMonoid (Fin 2) → Prop :=
  fun u v => u = FreeMonoid.of 0 * FreeMonoid.of 1 * FreeMonoid.of 0 ∧ v = FreeMonoid.of 1 * FreeMonoid.of 0
abbrev M5 := PresentedMonoid rel5                      -- a = 0, b = 1
def UTEmbeds (n : ℕ) : Prop := ∃ f : M5 →ₙ* UT n, Function.Injective f
def Conjecture_2_11 : Prop := UTEmbeds 4 ∧ ∀ n ≤ 3, ¬ UTEmbeds n

theorem mathdb356232 :
    (∃ f : M5 →ₙ* UT 4, Function.Injective f) ∧
      ∀ n ≤ 3, ¬ ∃ f : M5 →ₙ* UT n, Function.Injective f
```

**Fidelity notes.**

1. *The carrier ℤ̄.* We use Mathlib’s semiring instance for `MinTropical (WithTop ℤᵒᵈ)`. The minimum in the reversed order on ℤ is the maximum, and the adjoined top element plays the role of −∞. The following lemmas confirm that this is literally max-plus on ℤ ∪ {−∞}:
   - [`zb_add_zb`] `zb a + zb b = zb (max a b)`;
   - [`zb_mul_zb`] `zb a * zb b = zb (a + b)`;
   - [`zero_eq_negInf`] the semiring zero is the adjoined element −∞;
   - [`one_eq_zb_zero`] the semiring one is the integer 0;
   - [`negInf_add`, `negInf_mul`] max(−∞, x) = x and −∞ + x = −∞;
   - [`cases_zb`] every element is −∞ or an integer;
   - [`zb_injective`, `zb_ne_negInf`].

   The finite entries are integers. Section 7 gives a faithful UT3 representation over ℝ ∪ {−∞}.
2. *"Embeds (as a semigroup)", "multiplicative subsemigroup", "faithful representation".* All three are formalized as an injective semigroup homomorphism `M5 →ₙ* UT n`.
   - No condition is placed on the image of the empty word. This is the weakest notion, so the negative half is as strong as possible.
   - Our UT4 embedding even sends 1 to the identity matrix [`f4_one`], so it also satisfies the stronger notion.
   - The lower-bound proof never uses φ(1). It compares only images of words in which every exponent is at least 1. So whether the empty word must map to the identity does not matter.
3. *"UT-rank exactly 4"* means UT-rank = least n with an embedding. For positive dimensions this says that an embedding exists in dimension 4 and that dimensions 1, 2, and 3 admit none. Lean also excludes dimension 0. There is exactly one matrix indexed by Fin 0, and M5 is infinite.
4. *Non-vacuity.*
   - The first conjunct is an existence statement, witnessed by `f4`. It maps a and b to the corrected matrices [`f4_gens`].
   - Those matrices satisfy the relation [`rel_holds`].
   - M5 is infinite [`M5_infinite`].

## 2. Normal forms (module `M5Normal`, and distinctness in `M5UT4`)

Write N(α, β, γ) = (ba)^α a^β b^γ.

**Lemma 2.1** [`exists_N`]. Every element of M5 equals some N(α, β, γ).

*Proof.* Induct on the length of a word. It suffices to show that the set of normal forms is closed under right multiplication by a and by b:
- N(α, β, γ)·b = N(α, β, γ+1);
- N(α, β, 0)·a = N(α, β+1, 0);
- N(α, β, γ+1)·a = N(α+γ+1, 0, 0).

The last rule follows from two consequences of aba = ba:
- a(ba) = ba;
- b(ba) = b(aba) = (ba)(ba).

Hence a^β (ba)^k = (ba)^k and b^γ (ba)^k = (ba)^{k+γ} for k ≥ 1. ∎

The N(α, β, γ) are pairwise distinct [`N_injective`] (this is Shneerson's normal form, source Lemma 2.8). We do not cite this. It follows from the decoding in §3.

## 3. The upper bound: the corrected Lemma 2.9 (modules `M5UT4Pow`, `M5UT4`)

The source prints B with B₁₁ = 1. With this value the relation holds [`printed_rel`], but (ba)b² and (ba)²b have the same image [`printed_collision`], even though N(1,0,2) ≠ N(2,0,1) [`printed_distinct`]. So the printed map is not injective.

The value B₁₁ = −1 reproduces the top row of the source’s displayed BA and the displayed formula for (BA)^α A^β B^γ in its stated range. Mitchell’s 2022 notebook already flagged the discrepancy between the printed generators and their displayed product. We use:

```
A = [ 0   1  −∞   0 ]     B = [ −1   0   0  −1 ]     C = BA = [ −1  1  0  −1 ]
    [−∞   1   0  −1 ]         [ −∞  −∞  −∞   0 ]              [ −∞ −∞ −∞ −∞ ]
    [−∞  −∞  −∞  −∞ ]         [ −∞  −∞   0  −∞ ]              [ −∞ −∞ −∞ −∞ ]
    [−∞  −∞  −∞  −∞ ]         [ −∞  −∞  −∞   1 ]              [ −∞ −∞ −∞ −∞ ]
```

(The source's displayed ABA has entry (2,4) equal to 0. The correct value is −∞, as above.)

**Relation.**
- [`B4_mul_A4`] BA = C.
- [`A4_mul_C4`] AC = C, since row 1 of A is (0, 1, −∞, 0) and rows 2–4 of C are −∞.

Hence ABA = BA [`A4_B4_rel`], and a ↦ A, b ↦ B defines a monoid homomorphism ψ.

**Closed forms** (by induction):
- [`C4_pow`] C^{n+1}: row 1 is (−n−1, −n+1, −n, −n−1); all other entries are −∞.
- [`A4_pow`] A^{n+2}: rows 1 and 2 are (0, n+2, n+1, n) and (−∞, n+2, n+1, n). Rows 3–4 are −∞. For β = 1 use A as displayed, and for β = 0 use the identity matrix.
- [`B4_pow`] B^{n+1} has rows (−n−1, −n, 0, n−1), (−∞, −∞, −∞, n), (−∞, −∞, 0, −∞), (−∞, −∞, −∞, n+1).

**Decoding** [`dec`, `dec_X4`]. Let X = C^α A^β B^γ, and use 1-based indices in this paragraph.
- If X₃₃ ≠ −∞, then α = β = 0 and γ = X₄₄.
- Otherwise, if X₂₃ ≠ −∞, then α = 0, β = X₂₃ + 1 and γ = −X₁₁.
- Otherwise α ≥ 1. Put δ = X₁₄ − X₁₃. If δ ≥ 0 then γ = δ, and if δ = −1 then γ = 0. Then α = −X₁₁ − γ and β = X₁₃ + α − 1.

These formulas are verified in all twelve cases α ∈ {0, ≥1}, β ∈ {0, 1, ≥2}, γ ∈ {0, ≥1} by multiplying out the closed forms.

With Lemma 2.1 this shows that ψ is injective [`psi4_injective`]. Its image lies in UT4 [`psi4_mem`], which gives the semigroup embedding `f4` [`UTEmbeds_four`].

## 4. Tools for dimension 3 (modules `M5Trop`, `M5Pow3`)

Juxtaposition and ⊗ denote the tropical product, and ⊕ is max. Write diagonal entries as m_i = M_ii.

**Lemma 4.1** (tropical binomial) [`trop_binom`]. (x ⊕ y)^{k+1} = x^{k+1} ⊕ y(x ⊕ y)^k.

*Proof.* Check the four −∞ patterns. In the integer case the identity reads (k+1)max(a,b) = max((k+1)a, b + k·max(a,b)). ∎

**Lemma 4.2** (powers of a triangular 3 × 3 matrix) [`pow3`]. For M ∈ UT3 and k ≥ 0, with 1-based indices:

- (M^{k+1})_ii = m_i^{k+1};
- (M^{k+1})₁₂ = M₁₂ (m₁ ⊕ m₂)^k;
- (M^{k+1})₂₃ = M₂₃ (m₂ ⊕ m₃)^k;
- (M^{k+1})₁₃ = M₁₃ (m₁ ⊕ m₃)^k ⊕ M₁₂ M₂₃ corner_k, where corner₀ = −∞ and corner_{k+1} = (m₁ ⊕ m₂ ⊕ m₃)^k.

*Proof.* Induct on k using M^{k+2} = M^{k+1}M and Lemma 4.1. For the corner term we also need corner_{k+1} = (m₁ ⊕ m₂)^k ⊕ m₃ corner_k. ∎

**Lemma 4.3.**
- [`diag_mul3`] For M, P ∈ UT3, (MP)_ii = M_ii P_ii.
- [`mul3_congr`] Let C, A, A′, B be matrices such that for every (p, q), at least one of the following holds: A_pq = A′_pq; column p of C is all −∞; row q of B is all −∞. Then CAB = CA′B.

The diagonal formula follows because the summand indexed by i is the only potentially finite summand in (MP)ᵢᵢ. The two triple products agree because each summand Cᵢₚ Aₚᵩ Bᵩⱼ agrees with its counterpart or is −∞ in both.

**Lemma 4.4.**
- [`one_add_zb_pow`] For e ∈ ℤ there are κ, λ ∈ ℤ̄ such that (0 ⊕ e)^k = e^k κ ⊕ λ for every k. Take (κ, λ) = (0, −∞) if e > 0, and (−∞, 0) if e ≤ 0.
- [`zb_add_idem_pow`] The same holds for (e ⊕ x)^k when x ∈ {−∞, 0}.

## 5. The lower bound in dimension 3 (modules `M5Lower3`, `M5MainCase`, `M5Collide`, `M5Main`)

Let φ : M5 → UT3(ℤ̄) be a semigroup homomorphism. Put A = φ(a), B = φ(b) and C = BA. Then ABA = BA [`hom_rel`], and for α, β, γ ≥ 1,

φ(N(α, β, γ)) = C^α A^β B^γ =: X(α, β, γ)   [`hom_N`, `X3`].

Write a_i, b_i, c_i for the diagonal entries (1-based in the text, 0-based in Lean). We show that X(P) = X(Q) for two distinct triples P ≠ Q with all entries ≥ 1. By §2, N(P) ≠ N(Q), so φ is not injective [`not_UTEmbeds_three`].

**Diagonal constraints** [`diag_rel`, `diag_cases`, `diag_one`]. By Lemma 4.3, c_i = b_i a_i, and the diagonal of A·C = C gives a_i c_i = c_i. Hence:

- (D) if a_i ∉ {−∞, 0}, then c_i = b_i = −∞;
- (D1) if c_i ≠ −∞, then a_i = 0.

For (D): if a_i = e ≠ 0 and c_i were finite, then e + c_i = c_i, which is impossible. So c_i = −∞, and c_i = b_i ⊗ e then forces b_i = −∞.

### 5.1 Case I: a₂ ∈ {−∞, 0}, or c₁ = −∞, or b₃ = −∞ [`invariant_case`]

We show X(3,3,3) = X(3,4,3) using Lemma 4.3 with C³, A³, A⁴, B³.

**Equalities between A³ and A⁴.** By Lemma 4.2, (A³)_pq = (A⁴)_pq whenever every diagonal entry a_t that occurs in the formula for (p, q) lies in {−∞, 0}. The reason is that x^k = x for x ∈ {−∞, 0} and k ≥ 1, and this property is preserved by ⊕. For the corner entry this needs exponents ≥ 1, which is why we use β ∈ {3, 4}. Entries below the diagonal are −∞ in both.

**Vanishing columns and rows.**
- If c₁ = −∞, column 1 of C³ is −∞.
- If c₁ = c₂ = −∞, column 2 of C³ is also −∞, since (C³)₁₂ = C₁₂(c₁ ⊕ c₂)² = −∞.
- If b₃ = −∞, row 3 of B³ is −∞.
- If b₂ = b₃ = −∞, row 2 of B³ is also −∞.

By (D), a₁ ∉ {−∞, 0} implies c₁ = −∞, and a₃ ∉ {−∞, 0} implies b₃ = −∞. Now go through the three sub-cases.

- **a₂ ∈ {−∞, 0}.**
  For each p ≤ q, the power formula uses only diagonal entries at levels p through q. If a₁ lies in this interval and is outside {−∞, 0}, then p = 1 and column 1 of C³ vanishes. If a₃ lies in the interval and is outside {−∞, 0}, then q = 3 and row 3 of B³ vanishes. In every remaining pair, all diagonal entries used in the power formula belong to {−∞, 0}, so (A³)ₚᵩ = (A⁴)ₚᵩ.
- **a₂ ∉ {−∞, 0} and c₁ = −∞.** By (D), c₂ = −∞. So columns 1 and 2 of C³ vanish, and only the pair (3, 3) remains. It is equal if a₃ ∈ {−∞, 0}, and otherwise row 3 of B³ is −∞.
- **a₂ ∉ {−∞, 0} and b₃ = −∞.** By (D), b₂ = −∞. So rows 2 and 3 of B³ vanish, and only (1, 1) remains. It is handled as in the first sub-case.

### 5.2 Case II: a₂ = e ∈ ℤ∖{0}, c₁ ≠ −∞, b₃ ≠ −∞ [`main_case`]

From (D) and (D1):
- b₂ = c₂ = −∞;
- a₁ = 0;
- b₁ = c₁ = p ∈ ℤ;
- b₃ = r ∈ ℤ;
- a₃ ∈ {−∞, 0}. If a₃ were finite and nonzero, (D) would give b₃ = −∞.

So c₃ = r ⊗ a₃, viewing the integer r as a tropical scalar.

**Splitting A^β** [`hdec`]. Take κ, λ for (0 ⊕ e) and κ′, λ′ for (e ⊕ a₃) from Lemma 4.4. Put

```
K = [ −∞   A₁₂ e κ   A₁₂ A₂₃ κ ]        L = [ 0    A₁₂ λ   A₁₃ ⊕ A₁₂ A₂₃ λ ]
    [ −∞   e²        A₂₃ e κ′  ]            [ −∞   −∞      A₂₃ λ′          ]
    [ −∞   −∞        −∞        ]            [ −∞   −∞      a₃              ]
```

Then A^{β+2} = e^β ⊗ K ⊕ L for every β ≥ 0. To check this, apply Lemma 4.2 with a₁ = 0, a₂ = e and a₃ ∈ {−∞, 0}. Use 0 ⊕ a₃ = 0, and (A^{β+2})₁₃ = A₁₃ ⊕ A₁₂A₂₃(0 ⊕ e)^β.

Consequently [`hsplit`],

X(α+1, β+2, γ+1) = e^β ⊗ U ⊕ V,  where U = C^{α+1} K B^{γ+1} and V = C^{α+1} L B^{γ+1}.

**Shape of U and V.** Lemma 4.2 gives the entries of the two powers:
- C^{α+1}: (1,1) = p^{α+1}, (1,2) = C₁₂ p^α, (2,2) = −∞, (2,3) = C₂₃ c₃^α, (3,3) = c₃^{α+1};
- B^{γ+1}: (1,1) = p^{γ+1}, (1,2) = B₁₂ p^γ, (2,2) = −∞, (2,3) = B₂₃ r^γ, (3,3) = r^{γ+1};
- in both, the entries below the diagonal are −∞.

The matrix K is −∞ outside positions (1,2), (1,3), (2,2), (2,3). Multiplying out:

- U_ij = −∞ for (i, j) ≠ (1, 3), and U₁₃ = p^α r^γ ⊗ K*, where
  K* = p ⊗ (A₁₂ e κ B₂₃ ⊕ A₁₂ A₂₃ κ r) ⊕ C₁₂ ⊗ (e² B₂₃ ⊕ A₂₃ e κ′ r);
- with s = α + γ: V₁₁ = p^{s+2}, V₁₂ = B₁₂ p^{s+1}, V₂₃ = C₂₃ a₃ r^{s+1}, V₃₃ = a₃ r^{s+2}, and V₂₂ = V_ij = −∞ for i > j.

For V₂₃ and V₃₃, split on a₃ ∈ {−∞, 0}.

So every entry other than (1,3) depends only on α + γ, and

X(α+1, β+2, γ+1)₁₃ = (αp + βe + γr) ⊗ K* ⊕ G(α, γ),  where G(α, γ) = V₁₃.

**Collision lemma** [`collide`]. Suppose a family of matrices has this shape with e ≠ 0. Write d = p − r, and let x⁺ = max(x, 0). We give the actual exponents of the colliding normal forms.

- **K* = −∞.** X does not depend on β, so X(3,3,3) = X(3,4,3).
- **K* = k ∈ ℤ and e < 0.** Put E = −e ≥ 1.
  - If G(1+E, 1) = g is finite, take β = ((1+E)p + r + k − g)⁺. Since βe ≤ −β, the F-term is at most g at β and at β+1. Hence X(2+E, β+2, 2) = X(2+E, β+3, 2).
  - If G(1+E, 1) = −∞ but G(1, 1+E) is finite, argue in the same way with the roles of α and γ exchanged.
  - If both are −∞, then X₁₃ is exactly the F-term at both points, and X(2+E, d⁺+2, 2) = X(2, (−d)⁺+2, 2+E). The two values of α + γ agree. The exponents of the F-term agree because E(p − r) + (d⁺ − (−d)⁺)e = Ed + de = 0.
- **K* = k ∈ ℤ and e > 0.** Put E = e. Choose N₁ and N₂ such that every integer y ≥ N₁ satisfies G(1, 1+E) ⊕ y = y, and every y ≥ N₂ satisfies G(1+E, 1) ⊕ y = y [`dominate`]. Let M = d⁺ + (−d)⁺ + N₁⁺ + N₂⁺ + (−c)⁺, where c = (1+E)p + r + k. Then X(2, M+d+2, 2+E) = X(2+E, M+2, 2):
  - α + γ agrees at the two points;
  - at both points the F-term equals c + Me ≥ c + M ≥ N₁, N₂, so it dominates G at both;
  - the exponent shift is (α, β, γ) ↦ (α + e, β − d, γ − e), and it fixes αp + βe + γr.

In every case the two triples are distinct, which proves the lower bound in dimension 3 [`lower3`, `not_UTEmbeds_three`].

**Integrality** makes the shift (e, −d, −e) a shift of natural exponents after choosing the starting exponents sufficiently large. It also gives e ≥ 1 or e ≤ −1 in the explicit domination bounds. Section 7 explains why the conclusion changes when arbitrary real entries are allowed.

## 6. Dimensions ≤ 2 and the endpoint (module `M5Main`)

For n ≤ 2, block padding X ↦ diag(X, −∞, …) is an injective semigroup homomorphism UTn → UT3 [`padM_mul`, `padM_injective`, `padM_mem`, `padHom`]. Composing it with an embedding M5 → UTn would give an embedding into UT3, which §5 rules out. This also covers n = 0 [`not_UTEmbeds_le_three`].

Together with §3, this gives `conjecture_2_11 : Conjecture_2_11` and its unfolded form `mathdb356232`.

## 7. Significance

The new result is the exclusion of dimension three for the integral tropical semiring. The proof uses the relation to confine dependence on the middle normal-form exponent to one matrix entry. The shift then yields a collision in that entry while preserving the others. Reversing words and conjugating transposes by the order-reversing permutation gives the corresponding ordinary result for the dual M8 = Mon⟨a, b | aba = ab⟩. The Lean endpoint is for M5.

**The real comparison.** The first review supplied the following example, which is outside the Lean endpoint. Set s = √2 and take
```
A = [ 0  −∞  −∞ ]     B = [ −1   0  −∞ ]
    [−∞  −s  −2 ]         [ −∞  −∞  −∞ ]
    [−∞  −∞  −∞ ]         [ −∞  −∞   0 ]
```
The product C = BA has first row (−1, −s, −2) and rows 2 and 3 all −∞. Multiplying by A on the left fixes C. For α ≥ 1, X = C^α A^β B^γ has rows 2 and 3 all −∞, X₁₁ = −α−γ, and X₁₃ = −α−1−βs. Irrationality of s recovers α and β from X₁₃ and then γ from X₁₁. For α = 0 the matrix has a finite entry in row 2 or row 3. When β = 0, X₃₃ = 0 and γ = −X₁₁. When β ≥ 1 and γ = 0, X₂₂ = −βs is finite. When β, γ ≥ 1, both X₃₃ and X₂₂ are −∞, and X₂₃ = −(β−1)s−2 with X₁₁ = −γ. These cases recover all three exponents, so the matrices give an embedding over the real tropical semiring.

Consequently semigroup identities of UT3(ℤ̄) cannot provide an obstruction. An identity that fails on real matrices has a witness with the same −∞ pattern and rational finite entries, by continuity of the entries that are finite. An entry that is −∞ depends only on the pattern. Scaling all finite entries by a common positive denominator preserves the inequality, so the identity already fails over ℤ̄. Thus UT3 over the integers and over the reals have the same identities, all of which hold in M5.

## 8. Prior work

Nyberg-Brodda’s Lemmas 2.8–2.9 give the normal forms and the proposed dimension-four embedding. Mitchell’s 2022 verification notebook publicly identified the mismatch in the displayed product. The notebook leaves the correction and the dimension-three question open. Daviaud, Johnson and Kambites give the standard walk expansion in upper triangular tropical matrices, and Aird gives general growth bounds for subsemigroups of upper triangular tropical matrices. The cross-model review found no prior resolution of Conjecture 2.11 in the sources and registries it checked.

## References

- [NB22] C.-F. Nyberg-Brodda, *Tropical one-relation monoids*, arXiv:2209.12612, 2022.
- [Shn72] L. M. Shneerson, the normal-form result cited in the source as [Shn72b].
- [DJK18] L. Daviaud, M. Johnson, M. Kambites, *Identities in upper triangular tropical matrix semigroups and the bicyclic monoid*, J. Algebra 501 (2018), 503–525, especially Lemma 5.1.
- T. Aird, *Generating sets, presentations, and growth of tropical matrix monoids*, Commun. Algebra 54 (2026), 2898–2920, especially §6.
- J. D. Mitchell, [Verification notebook for arXiv:2209.12612](https://gist.github.com/james-d-mitchell/cec4ef0a74259ff9dddf6e106c084f99), 2022.
- [IM10] Z. Izhakian, S. W. Margolis, *Semigroup identities in the monoid of two-by-two tropical matrices*, Semigroup Forum, 2010.
- Lean sources: `LEAN-SOURCE-APPENDIX.md` (12 modules, byte-identical to `src/`).
