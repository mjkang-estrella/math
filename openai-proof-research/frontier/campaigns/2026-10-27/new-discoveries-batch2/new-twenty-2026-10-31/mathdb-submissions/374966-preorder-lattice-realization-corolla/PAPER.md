# A three-element counterexample to the lattice-realization conjecture for preorder lattice-point posets

**MathDB 374966 — editorial revision following independent manuscript review, 18 November 2026.**

## Abstract

Athanasiadis and Chapoton (arXiv:2605.26916v1, Conjecture 8.1) conjecture that for every preorder
τ of size n there is a finite graded lattice L_τ of rank n with Z(P_τ,t) = Z(L_τ,t) and
M̄_{P_τ}(x,y) = M_{L_τ}(x,y), where P_τ is the poset of lattice points of the preorder polytope.
We show that the conjecture already fails for the corolla t₃: three elements, one maximum and two
incomparable minimal elements. The M-triangle equation alone has no solution. Its diagonal forces
five elements in each of ranks 1 and 2 of L, its x y² coefficient forces thirteen comparable pairs
between those ranks, and in a lattice two distinct rank-1 elements lie below at most one common
rank-2 element. Double counting the pairs makes thirteen impossible. The ordinary proof extends to every corolla with k ≥ 2 leaves. The Lean 4 and Mathlib certificate covers t₃.
A separate checked module derives the canonical rank hypothesis from the source's own definition of
gradedness by maximal chains.

## 1. Definitions and the statement

We use the definitions of Athanasiadis and Chapoton, arXiv:2605.26916v1, dated 27 May 2026. The source comparison uses this retained version.

* **Preorders (§2.2).** A preorder τ on a finite nonempty set E is a reflexive, transitive relation ≤.
  Its *size* is |E|. An *order ideal* is a subset I ⊆ E such that b ∈ I and a ≤ b imply a ∈ I.
* **Preorder polytope (§1, display (2)).** Q_τ ⊂ ℝ^E is cut out by x_e ≥ 0 (e ∈ E) and
  Σ_{e∈I} x_e ≤ |I| for every order ideal I. P_τ = Q_τ ∩ ℤ^E, ordered as a subposet of the product
  order ℕ^E (§1, §3.3). By §3.3, P_τ is an order ideal of ℕ^E with minimum 0, and it is graded with rank
  function the coordinate sum |w|.
* **Graded (§2.3).** For a finite poset P let d be the length (one less than the cardinality) of a
  longest chain. P is *graded* if all maximal chains have length d, and it has *rank* n when d = n.
  Its rank function ρ (see Stanley, *Enumerative Combinatorics*, Volume 1, §3.1) is 0 on minimal elements and satisfies ρ(y) = ρ(x)+1
  whenever y covers x. On a finite poset it is unique when it exists (proved formally as
  `A374966.rankFn_unique`).
* **Möbius function.** μ(a,a) = 1 and Σ_{a ≤ z ≤ b} μ(a,z) = 0 for a < b. Mathlib's
  `IncidenceAlgebra.mu` uses exactly this recursion: μ(a,b) = −Σ_{a ≤ z < b} μ(a,z) for a ≠ b.
* **M-triangle (§8).** For a finite graded poset P with rank function ρ,
  M_P(x,y) = Σ_{a,b ∈ P, a ⪯ b} μ_P(a,b) x^{ρ(a)} y^{ρ(b)}.
* **Transmutation (§8).** For f ∈ ℚ(x,y), f̄(x,y) = f((1−y)/(1−xy), 1−xy).

**Conjecture 8.1 (verbatim).** *For every preorder τ of size n there exists a finite graded lattice L_τ
of rank n such that Z(P_τ,t) = Z(L_τ,t) and (27) M̄_{P_τ}(x,y) = M_{L_τ}(x,y).*

MathDB 374966 retains the same statement ("There exists a finite graded lattice L_τ of rank n such that
𝒵(P_τ,t) = 𝒵(L_τ,t), M̄_{P_τ}(x,y) = M_{L_τ}(x,y)"), with the same transmutation.

**The corolla t₃.** Let E = {r, ℓ₁, ℓ₂} with ℓ₁ < r and ℓ₂ < r, and ℓ₁, ℓ₂ incomparable. This is the arbor
with root r and two leaves. Section 1 of the source regards an arbor as a preorder whose root is the
maximum vertex. All vertices are singletons and the size is n = 3. The order ideals are
∅, {ℓ₁}, {ℓ₂}, {ℓ₁,ℓ₂} and E.

## 2. Main theorem

**Theorem 1.** Let τ = t₃. No finite graded lattice L of rank 3 satisfies M̄_{P_τ}(x,y) = M_L(x,y).
Hence Conjecture 8.1, and MathDB 374966 as stated, are false.

The proof in fact excludes every finite lattice L that carries a strictly increasing map ρ : L → ℕ,
with M_L built from ρ. Gradedness enters only through Lemma 4.

### 2.1 The poset P_τ

Write points as (a, b, c) = (x_r, x_{ℓ₁}, x_{ℓ₂}). The ideal inequalities are a, b, c ≥ 0, b ≤ 1, c ≤ 1,
b + c ≤ 2 (redundant) and a + b + c ≤ 3. The twelve lattice points, by rank |w|, are

| rank | points | count |
|---|---|---|
| 0 | 000 | 1 |
| 1 | 100, 010, 001 | 3 |
| 2 | 200, 110, 101, 011 | 4 |
| 3 | 300, 210, 201, 111 | 4 |

All inequalities are monotone, so P_τ is down-closed in ℕ³. Every interval [v,w] of P_τ is therefore
the full integer box, a product of three chains. The Möbius function is the product of chain Möbius
functions: μ(v,w) = (−1)^{|S|} if w − v = e_S is the 0/1 vector with support S, and μ(v,w) = 0
otherwise.

### 2.2 The coefficient table of M_{P_τ}

By the box formula, [x^i y^j] M_P = (−1)^{j−i} N_{i,j}, where
N_{i,j} = #{(v, S) : |v| = i, |S| = j − i, v + e_S ∈ P_τ}. The counts are:

* i = 0 (v = 000): every e_S lies in P_τ, so N = 1, 3, 3, 1.
* i = 1, one step (S a singleton): 100 → 200, 110, 101; 010 → 110, 011; 001 → 101, 011. So N_{1,2} = 7.
  Two steps: 100 → 210, 201, 111; 010 → 111; 001 → 111. So N_{1,3} = 5.
* i = 2, one step: 200 → 300, 210, 201; 110 → 210, 111; 101 → 201, 111; 011 → 111. So N_{2,3} = 8.
* The diagonal entries count the rank layers: 1, 3, 4, 4.

The table has rows x^i (i = 0..3) and columns y^j (j = 0..3):

| | y⁰ | y¹ | y² | y³ |
|---|---|---|---|---|
| x⁰ | 1 | −3 | 3 | −1 |
| x¹ | 0 | 3 | −7 | 5 |
| x² | 0 | 0 | 4 | −8 |
| x³ | 0 | 0 | 0 | 4 |

So M_{P_τ} = 1 − 3y + 3y² − y³ + 3xy − 7xy² + 5xy³ + 4x²y² − 8x²y³ + 4x³y³.

### 2.3 Transmutation

Every monomial x^i y^j of M_P has j ≥ i. Under the substitution it becomes
((1−y)/(1−xy))^i (1−xy)^j = (1−y)^i (1−xy)^{j−i}, so M̄_P is a polynomial. Grouping by i:

* i = 0: 1 − 3(1−xy) + 3(1−xy)² − (1−xy)³ = (xy)³;
* i = 1: (1−y)(3 − 7(1−xy) + 5(1−xy)²) = (1−y)(1 − 3xy + 5x²y²);
* i = 2: (1−y)²(4 − 8(1−xy)) = (1−y)²(−4 + 8xy);
* i = 3: 4(1−y)³.

Adding the four parts gives

M̄_{P_τ}(x,y) = 1 + (−5 + 5x) y + (8 − 13x + 5x²) y² + (−4 + 8x − 5x² + x³) y³,

with coefficient table (rows x^i, columns y^j)

| | y⁰ | y¹ | y² | y³ |
|---|---|---|---|---|
| x⁰ | 1 | −5 | 8 | −4 |
| x¹ | 0 | 5 | −13 | 8 |
| x² | 0 | 0 | 5 | −5 |
| x³ | 0 | 0 | 0 | 1 |

The coefficients are integers, so equation (27) has the same meaning over ℚ(x,y) and ℝ(x,y). It also
says the same thing as an equality in ℤ[x,y] ⊂ ℚ[x,y] ⊂ ℚ(x,y), because each inclusion is injective.

**Remark (closed form; ordinary).** Every P_τ is an order ideal of ℕ^E (§3.3). Substitute
v = w − e_S with S ⊆ supp(w), and write m(w) = |supp w|. Then for every preorder τ,
M̄_{P_τ}(x,y) = Σ_{w∈P_τ} Σ_{S⊆supp w} (−1)^{|S|}(1−y)^{|w|−|S|}(1−xy)^{|S|}
= Σ_{w∈P_τ} (y(x−1))^{m(w)} (1−y)^{|w|−m(w)}.
Hence [x^k y^k] M̄ = h_k(τ), the number of points with k nonzero coordinates. This matches the source's
remark that the transmuted diagonal is the h-vector; for t₃, h = (1, 5, 5, 1). Also
[x y²] M̄ = Σ_{m(w)=1}(1 − |w|) − 2 h_2(τ). For t₃ the support-one points 100, 200, 300, 010, 001
contribute 0 − 1 − 2 + 0 + 0 = −3, and −2·5 = −10, which gives −13 as in the table.

### 2.4 Reading M_L

**Lemma 2.** Let L be a finite poset and ρ : L → ℕ strictly increasing, and set
M_L = Σ_{a ≤ b} μ(a,b) x^{ρ(a)} y^{ρ(b)}. Then [x^k y^k] M_L = #{a : ρ(a) = k}, and
[x y²] M_L = −#{(a,b) : ρ(a) = 1, ρ(b) = 2, a < b}.

*Proof.* Distinct comparable elements have distinct ranks, so only the pairs a = b contribute to the
diagonal, each with μ = 1. If a < b with ρ(a) = 1 and ρ(b) = 2, nothing lies strictly between them,
since its rank would be strictly between 1 and 2. So [a,b] = {a,b} and μ(a,b) = −1. ∎

### 2.5 Gradedness gives a strictly increasing rank function

**Lemma 3.** Let L be a finite poset and ρ a rank function (0 on minimal elements, +1 on covers).
Then ρ is strictly increasing.

*Proof.* Induct on b along the well-founded order. Given a < b, choose c maximal in
{x : a ≤ x < b}. Then c ⋖ b, so ρ(b) = ρ(c) + 1, and either c = a or ρ(a) < ρ(c) by induction. ∎

**Lemma 4 (native §2.3 ⇒ canonical rank hypothesis).** Let L be a finite bounded poset, all of whose
maximal chains have length n, and let ρ be its rank function. Then ρ is strictly increasing,
increases by one on covers, ρ(0̂) = 0 and ρ(1̂) = n. Conversely, any such ρ is the rank function and
all maximal chains have length n.

*Proof.* A rank function exists under the maximal-chain hypothesis. Fix x ∈ L and a maximal chain
in [x, 1̂]. Joining it to any maximal chain in [0̂, x] gives a maximal chain in L, since the two chains
are saturated and meet at x. All maximal chains in [0̂, x] therefore have the same length. Define ρ(x)
to be that length. For a cover x ⋖ y, adjoining y to a maximal chain in [0̂, x] gives a maximal chain
in [0̂, y], so ρ(y) = ρ(x) + 1. The checked native endpoint takes the rank function used by M_L as
a hypothesis.

Let C be a maximal chain with greatest element t. Its least element m is minimal in L, since
otherwise a smaller element could be inserted into C. So ρ(m) = 0. If x ∈ C has x < t, let d be the
least element of C above x. Then x ⋖ d in L, since any e with x < e < d could be inserted into C. So
ρ(d) = ρ(x) + 1. Hence ρ maps C, injectively by Lemma 3, onto {0, 1, …, ρ(t)}, and |C| = ρ(t) + 1.
In a bounded poset every maximal chain contains 0̂ and 1̂, so |C| = n + 1 forces ρ(1̂) = n. The
converse follows from the same count. ∎

Lemma 4 is formalized at arbitrary n (`A374966.native_iff_isGradedRank`) and applied at n = 3, where
every maximal chain has exactly four elements. Applied to P_τ, the same chain count shows that every
maximal chain of P_τ has four elements and that the coordinate sum is the unique rank function
(`A374966.P_nativeGraded`, `A374966.rk_unique`). So M_{P_τ} above is the native M-triangle, with no
parameter changed.

### 2.6 Proof of Theorem 1

Suppose L is a finite graded lattice of rank 3 with rank function ρ and M_L = M̄_{P_τ}. By Lemma 4, ρ
is strictly increasing, so Lemma 2 applies.

*Lower count.* Comparing the coefficients of xy and x²y², L has five elements of rank 1 and five of
rank 2. Comparing the coefficients of xy², there are exactly 13 comparable pairs (a,c) with ρ(a) = 1
and ρ(c) = 2. For c of rank 2 let d_c be the number of rank-1 elements below c. Then Σ_c d_c = 13,
summed over the five elements of rank 2.

*Upper count.* Let x ≠ y have rank 1, and let c have rank 2 with x, y ≤ c. Then x < x ∨ y ≤ c, since
x ∨ y = x would give y ≤ x, and two comparable elements of the same rank are equal. So
ρ(x ∨ y) ≥ 2 = ρ(c), and therefore x ∨ y = c. Each unordered pair of rank-1 elements thus lies below
at most one rank-2 element, and Σ_c C(d_c, 2) ≤ C(5, 2) = 10.

*Contradiction.* For every integer d ≥ 0, C(d,2) ≥ 2d − 3, because (d−2)(d−3) ≥ 0. So
Σ_c C(d_c,2) ≥ 2·13 − 3·5 = 11 > 10. ∎

## 3. Every corolla with at least two leaves (ordinary; not formalized)

Let τ_k be the preorder with a root r above k ≥ 1 pairwise incomparable leaves, all singletons, of
size n = k + 1. Q_{τ_k} is given by a, b_i ≥ 0, b_i ≤ 1 and a + Σ b_i ≤ k + 1; the other ideal
inequalities are sums of these. P_{τ_k} is down-closed, so the closed form of §2.3 gives:

* h_1 = A = (k + 1) + k = 2k + 1: the points a·e_r with 1 ≤ a ≤ k+1, and the k unit leaf points.
* h_2 = B = k·k + C(k,2) = (3k² − k)/2: root plus one leaf with 1 ≤ a ≤ k, and two leaves.
* −[x y²] M̄ = E = Σ_{a=1}^{k+1}(a − 1) + 0 + 2B = k(k+1)/2 + 3k² − k = (7k² − k)/2.

If M_L = M̄_{P_{τ_k}} for a finite graded lattice L, then the argument of §2.6 gives Σ_c d_c = E over
B elements and Σ_c C(d_c,2) ≤ C(A,2). By Cauchy–Schwarz,
Σ_c C(d_c,2) = ½(Σ d_c² − Σ d_c) ≥ ½(E²/B − E) = E(E − B)/(2B), where E − B = 2k².
The inequality E(E − B)/B > A(A − 1) reads 2k²(7k − 1)/(3k − 1) > 2k(2k + 1), that is
7k² − k > 6k² + k − 1, that is (k − 1)² > 0. So every corolla with k ≥ 2 leaves is a counterexample.
For k = 1 (a two-element chain) the bound is attained and there is no obstruction, consistent with
the source's chain examples. For k = 2: A = B = 5 and E = 13, as in §2.

## 4. Remarks

**Zeta conjunct.** P_τ is down-closed with box intervals. Hence Z(P_τ,2) = 12,
Z(P_τ,3) = Σ_w Π_e(w_e + 1) = 46, and Z(P_τ,4) = Σ_w #{v ≤ w}·#{u ≥ w} = 116, with third difference
13 = 3!·(13/3!), i.e. 13 maximal chains. A rank-3 lattice with the sizes 1, 5, 5, 1 and the 13
rank-1/rank-2 incidences forced above has exactly the same values. So the zeta condition gives no
extra obstruction, and it is not used. The formal endpoints conjoin an arbitrary predicate on the
same lattice in its place. No formal zeta computation is claimed.

**Comparison with the Hochschild and shuffle lattices.** Chapoton's §9 proposes the core-label
order of the Hochschild lattice as the transmuted partner of the root-maximum corolla and reports
computer checks through n = 9. Mühle's Theorem 1.3 identifies that order with the shuffle lattice
Shuf(n−1,1). At n = 3, Mühle's Example 6.5 gives twelve incidences between ranks 1 and 2. The
root-maximum corolla requires thirteen. Reversing the lattice order preserves this incidence count.
As a separate check on the root-maximum calculation, the n = 3 term of Chapoton's generating
function, proved by Liu and Tang in Theorem 2.6, gives the untransmuted table in §2.2.
[Chapoton, §9](https://arxiv.org/abs/2503.04247v2), [Mühle, Theorem 1.3 and Example 6.5](https://arxiv.org/abs/2008.13247v2), [Liu–Tang, Theorem 2.6](https://arxiv.org/abs/2605.08968v1).

For the opposite corolla τ* with the root below both leaves, the transmuted polynomial at n = 3 is

    1 + (−5 + 5x)y + (7 − 12x + 5x²)y² + (−3 + 7x − 5x² + x³)y³.

It agrees with the M-triangle of Shuf(2,1) in Mühle's Example 6.5. This comparison is an ordinary
calculation for n = 3. [Mühle, Example 6.5](https://arxiv.org/abs/2008.13247v2).

## 5. Formal verification (summary)

Lean 4.34.1 with Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612, pinned binaries. Appendix A is the
canonical certificate of five modules (C374966Defs, C374966Corolla, C374966Transmute, C374966Lattice,
C374966Main). It was independently extracted from the frozen appendix into an empty `src/`, compiled
from an empty `build/` and kernel-checked module by module. All five oleans byte-match the author
manifest. Appendix B is the reviewer module A374966NativeBridge, separately labeled. It is not part
of the canonical certificate and does not change it. All 34 canonical and 19 reviewer `#print axioms`
roots depend only on propext, Classical.choice and Quot.sound.

* Canonical endpoint `C374966.conj81_false_at_corolla`: ¬∃ finite lattice L with bounded-order
  structure and ρ : L → ℕ such that `IsGradedRank ρ 3` and transmute(M_{P_τ}) = M_L in ℚ(x,y).
  `IsGradedRank` = strictly increasing, +1 on covers, ρ ⊥ = 0, ρ ⊤ = 3. The `_with_zeta` and
  `_gradeOrder` variants are also checked.
* Reviewer endpoint `A374966.conj81_false_at_corolla_native`: the same negation stated with the
  source's own definitions. Every Mathlib maximal chain (`IsMaxChain (· ≤ ·)`) of L has exactly four
  elements, and ρ is 0 on minimal elements and +1 on covers. No bounded order, `IsGradedRank` or
  `GradeOrder` is assumed. It is derived from the canonical endpoint by `isGradedRank_of_native`.
* Non-vacuity on standard lattices: the four-element chain `Fin 4` and the Boolean lattice
  `Finset (Fin 3)` are shown to satisfy the native hypotheses at rank 3, with maximal chains counted
  through the general lemma rather than assumed (`fin4_*`, `boolean3_*`).

## 6. Scope and limits

* Exact endpoint: the formal theorem is the literal refutation of Conjecture 8.1 at τ = t₃ (n = 3).
  The larger family, the closed form, the zeta values and the opposite-corolla comparison are ordinary
  proofs.
* Formal reading choices: "maximal chain" is Mathlib's `IsMaxChain (· ≤ ·)`, cardinality is
  `Set.ncard`, μ is Mathlib's `IncidenceAlgebra.mu ℚ`, and equation (27) is read in
  ℚ(x,y) = `FractionRing ℚ[x,y]`. All instance arguments (`LocallyFiniteOrder`, decidability) are
  universally quantified.
* Trust: the pinned Lean binaries and the upstream Mathlib oleans are trusted, not rebuilt.
* The source and prior-work comparisons cover the retained primary literature cited here. The
  current registry and later versions of the conjecture source were not verified.

## Appendix A. Canonical Lean certificate (exact; five modules)

Each block below is byte-for-byte the canonical source extracted from the frozen author appendix (`inputs/LEAN-SOURCE-APPENDIX.md`, sha256 91ec50fb1e7ddb14f1f665d930eea36d18eb5dcf1968f31a29a29e5fde6af0b0). Dependency order: Defs → Corolla → Transmute; Defs → Lattice; Transmute, Lattice → Main.

### C374966Defs.lean

source sha256 `950fbefe3285fc9f9cc7ae30e3d56dce5c6f7d12856eded51523038c0c256cd5`; fresh olean sha256 `f979caf39e18ea47297c1c0a3964ae041d54b84eeb609c3f30912c7f4542c7ea`

```lean
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fin.VecNotation

/-!
# MathDB 374966 — shared definitions

Athanasiadis–Chapoton, arXiv:2605.26916v1, Section 8:
`M_P(x,y) = ∑_{a ⪯ b} μ_P(a,b) x^{ρ a} y^{ρ b}` and the transmutation
`f̄(x,y) = f((1-y)/(1-xy), 1-xy)`.  Here `x = X 0`, `y = X 1`, coefficients in `ℚ`,
and `μ` is Mathlib's `IncidenceAlgebra.mu`.
-/

namespace C374966

open Finset MvPolynomial

/-- The polynomial ring `ℚ[x,y]`. -/
abbrev Pxy := MvPolynomial (Fin 2) ℚ

/-- The rational function field `ℚ(x,y)`. -/
abbrev FracXY := FractionRing Pxy

/-- The image of `x` in `ℚ(x,y)`. -/
notation "xF" => algebraMap C374966.Pxy C374966.FracXY (MvPolynomial.X 0)
/-- The image of `y` in `ℚ(x,y)`. -/
notation "yF" => algebraMap C374966.Pxy C374966.FracXY (MvPolynomial.X 1)

/-- Exponent vector of `x^i y^j`. -/
noncomputable abbrev mon (i j : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 j

theorem mon_inj {i j i' j' : ℕ} : mon i j = mon i' j' ↔ i = i' ∧ j = j' := by
  constructor
  · intro h
    have h0 := DFunLike.congr_fun h 0
    have h1 := DFunLike.congr_fun h 1
    simp [mon] at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem CXX (c : ℚ) (i j : ℕ) :
    (C c * X 0 ^ i * X 1 ^ j : Pxy) = monomial (mon i j) c := by
  rw [mul_assoc, X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial, one_mul,
    C_mul_monomial, mul_one]

/-- The M-triangle `M_P(x,y) = ∑_{a ≤ b} μ(a,b) x^{ρ a} y^{ρ b}` of a finite poset with rank map `ρ`. -/
noncomputable def Mtri (α : Type*) [PartialOrder α] [Fintype α] [LocallyFiniteOrder α]
    [DecidableEq α] [DecidableLE α] (ρ : α → ℕ) : Pxy :=
  ∑ a : α, ∑ b ∈ univ.filter (fun b => a ≤ b),
    C (IncidenceAlgebra.mu ℚ a b) * X 0 ^ ρ a * X 1 ^ ρ b

/-- Coefficient table of `Mtri`: `Tab α ρ i j = ∑_{a ≤ b, ρ a = i, ρ b = j} μ(a,b)`. -/
noncomputable def Tab (α : Type*) [PartialOrder α] [Fintype α] [LocallyFiniteOrder α]
    [DecidableEq α] [DecidableLE α] (ρ : α → ℕ) (i j : ℕ) : ℚ :=
  ∑ a : α, ∑ b : α, if ρ a = i ∧ ρ b = j then
    (if a ≤ b then IncidenceAlgebra.mu ℚ a b else 0) else 0

theorem Mtri_eq (α : Type*) [PartialOrder α] [Fintype α] [LocallyFiniteOrder α]
    [DecidableEq α] [DecidableLE α] (ρ : α → ℕ) :
    Mtri α ρ = ∑ a : α, ∑ b : α,
      C (if a ≤ b then IncidenceAlgebra.mu ℚ a b else 0) * X 0 ^ ρ a * X 1 ^ ρ b := by
  unfold Mtri
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : a ≤ b
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h, map_zero, zero_mul, zero_mul]

/-- `[x^i y^j] M_P = Tab α ρ i j`, for every `i j`. -/
theorem coeff_Mtri (α : Type*) [PartialOrder α] [Fintype α] [LocallyFiniteOrder α]
    [DecidableEq α] [DecidableLE α] (ρ : α → ℕ) (i j : ℕ) :
    (Mtri α ρ).coeff (mon i j) = Tab α ρ i j := by
  rw [Mtri_eq, coeff_sum]
  unfold Tab
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [coeff_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [CXX, coeff_monomial]
  by_cases h : ρ a = i ∧ ρ b = j
  · rw [ite_eq_left (mon_inj.2 h), ite_eq_left h]
  · rw [ite_eq_right (show ¬ (mon (ρ a) (ρ b) = mon i j) from fun h' => h (mon_inj.1 h')), ite_eq_right h]

/-- A polynomial of bidegree `≤ (3,3)` given by its coefficient table. -/
noncomputable def tab (t : ℕ → ℕ → ℚ) : Pxy :=
  ∑ i ∈ range 4, ∑ j ∈ range 4, C (t i j) * X 0 ^ i * X 1 ^ j

theorem coeff_tab (t : ℕ → ℕ → ℚ) {i j : ℕ} (hi : i < 4) (hj : j < 4) :
    (tab t).coeff (mon i j) = t i j := by
  unfold tab
  rw [coeff_sum, Finset.sum_eq_single_of_mem i (Finset.mem_range.2 hi)]
  · rw [coeff_sum, Finset.sum_eq_single_of_mem j (Finset.mem_range.2 hj)]
    · rw [CXX, coeff_monomial, ite_eq_left rfl]
    · intro j' _ hj'
      rw [CXX, coeff_monomial,
        ite_eq_right (show ¬ (mon i j' = mon i j) from fun h => hj' (mon_inj.1 h).2)]
  · intro i' _ hi'
    rw [coeff_sum]
    refine Finset.sum_eq_zero fun j' _ => ?_
    rw [CXX, coeff_monomial,
      ite_eq_right (show ¬ (mon i' j' = mon i j) from fun h => hi' (mon_inj.1 h).1)]

theorem tab_congr {t t' : ℕ → ℕ → ℚ} (h : ∀ i < 4, ∀ j < 4, t i j = t' i j) :
    tab t = tab t' := by
  unfold tab
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  rw [h i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj)]

theorem sum_swap4 {ι κ M : Type*} [AddCommMonoid M] (s : Finset ι) (t : Finset κ)
    (G : ι → ι → κ → κ → M) :
    ∑ i ∈ s, ∑ j ∈ s, ∑ a ∈ t, ∑ b ∈ t, G i j a b
      = ∑ a ∈ t, ∑ b ∈ t, ∑ i ∈ s, ∑ j ∈ s, G i j a b := by
  calc ∑ i ∈ s, ∑ j ∈ s, ∑ a ∈ t, ∑ b ∈ t, G i j a b
      = ∑ i ∈ s, ∑ a ∈ t, ∑ j ∈ s, ∑ b ∈ t, G i j a b :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ a ∈ t, ∑ i ∈ s, ∑ j ∈ s, ∑ b ∈ t, G i j a b := Finset.sum_comm
    _ = ∑ a ∈ t, ∑ i ∈ s, ∑ b ∈ t, ∑ j ∈ s, G i j a b :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ a ∈ t, ∑ b ∈ t, ∑ i ∈ s, ∑ j ∈ s, G i j a b :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm

/-- Regrouping a double sum of monomials into its coefficient table. -/
theorem regroup {α : Type*} [Fintype α] (ρ : α → ℕ) (hρ : ∀ a, ρ a < 4) (w : α → α → ℚ) :
    tab (fun i j => ∑ a, ∑ b, if ρ a = i ∧ ρ b = j then w a b else 0)
      = ∑ a, ∑ b, C (w a b) * X 0 ^ ρ a * X 1 ^ ρ b := by
  unfold tab
  simp only [map_sum, Finset.sum_mul]
  rw [sum_swap4]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single_of_mem (ρ a) (Finset.mem_range.2 (hρ a))]
  · rw [Finset.sum_eq_single_of_mem (ρ b) (Finset.mem_range.2 (hρ b))]
    · rw [ite_eq_left (show ρ a = ρ a ∧ ρ b = ρ b from ⟨rfl, rfl⟩)]
    · intro j _ hj
      rw [ite_eq_right (show ¬ (ρ a = ρ a ∧ ρ b = j) from fun h => hj h.2.symm),
        map_zero, zero_mul, zero_mul]
  · intro i _ hi
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [ite_eq_right (show ¬ (ρ a = i ∧ ρ b = j) from fun h => hi h.1.symm),
      map_zero, zero_mul, zero_mul]

/-- Uniqueness of the Möbius function: a function with `f a a = 1` whose interval sums vanish
agrees with Mathlib's `IncidenceAlgebra.mu` on comparable pairs. -/
theorem mu_eq_of_sum {α : Type*} [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α]
    (f : α → α → ℚ) (h1 : ∀ a, f a a = 1)
    (h2 : ∀ a b, a < b → ∑ z ∈ Finset.Icc a b, f a z = 0) (a : α) :
    ∀ b, a ≤ b → IncidenceAlgebra.mu ℚ a b = f a b := by
  suffices H : ∀ n : ℕ, ∀ b, (Finset.Ico a b).card = n → a ≤ b →
      IncidenceAlgebra.mu ℚ a b = f a b from fun b hab => H _ b rfl hab
  intro n
  refine Nat.strong_induction_on
    (p := fun n => ∀ b, (Finset.Ico a b).card = n → a ≤ b →
      IncidenceAlgebra.mu ℚ a b = f a b) n ?_
  intro n ih b hn hab
  rcases eq_or_ne a b with rfl | hne
  · rw [IncidenceAlgebra.mu_apply, ite_eq_left rfl, h1]
  · rw [IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne hne]
    have hs : ∑ x ∈ Finset.Ico a b, IncidenceAlgebra.mu ℚ a x
        = ∑ x ∈ Finset.Ico a b, f a x := by
      refine Finset.sum_congr rfl fun x hx => ?_
      have hx' := Finset.mem_Ico.1 hx
      have hsub : Finset.Ico a x ⊂ Finset.Ico a b :=
        (Finset.ssubset_iff_of_subset (Finset.Ico_subset_Ico_right hx'.2.le)).2
          ⟨x, hx, Finset.right_notMem_Ico⟩
      have hlt : (Finset.Ico a x).card < n := by
        rw [← hn]; exact Finset.card_lt_card hsub
      exact ih _ hlt x rfl hx'.1
    rw [hs]
    have h := h2 a b (lt_of_le_of_ne hab hne)
    rw [← Finset.Ico_insert_right hab, Finset.sum_insert Finset.right_notMem_Ico] at h
    linarith

/-- The literal transmutation substitution `x ↦ (1-y)/(1-xy)`, `y ↦ 1-xy`, landing in `ℚ(x,y)`. -/
noncomputable def transmuteHom : Pxy →+* FracXY :=
  eval₂Hom ((algebraMap Pxy FracXY).comp C) ![(1 - yF) / (1 - xF * yF), 1 - xF * yF]

/-- Transmutation `f̄(x,y) = f((1-y)/(1-xy), 1-xy)` of a polynomial, as an element of `ℚ(x,y)`. -/
noncomputable def transmute (f : Pxy) : FracXY := transmuteHom f

theorem tr_X0 : transmuteHom (X 0) = (1 - yF) / (1 - xF * yF) := by
  simp [transmuteHom]

theorem tr_X1 : transmuteHom (X 1) = 1 - xF * yF := by
  simp [transmuteHom]

/-- `1 - xy ≠ 0` in `ℚ(x,y)`. -/
theorem one_sub_xy_ne : (1 : FracXY) - xF * yF ≠ 0 := by
  intro h
  have h' : algebraMap Pxy FracXY (1 - X 0 * X 1) = algebraMap Pxy FracXY 0 := by
    rw [map_sub, map_one, map_mul, map_zero]
    exact h
  have h'' := IsFractionRing.injective Pxy FracXY h'
  have h3 := congrArg MvPolynomial.constantCoeff h''
  simp at h3

/-- Coercion injectivity `ℚ[x,y] → ℚ(x,y)`. -/
theorem iota_injective : Function.Injective (algebraMap Pxy FracXY) :=
  IsFractionRing.injective Pxy FracXY

end C374966
```

### C374966Corolla.lean

source sha256 `bf2027d0adb9e7516462c46484be519af10fdc9f80569699e4b4c68bd96c7d17`; fresh olean sha256 `5e624c058f4cf1d0efcd72c12b2a80b91cb6e890338ec355bcd8da252f6072ea`

```lean
import C374966Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-!
# MathDB 374966 — the corolla preorder `τ = t₃` and its lattice-point poset `P_τ`

Ground set `E = Fin 3`; vertex `0` is the root, above the two incomparable leaves `1, 2`.
`Q_τ = {x ≥ 0, ∑_{e ∈ I} x_e ≤ |I| for all order ideals I}`; `P_τ` = its integer points,
ordered componentwise, ranked by coordinate sum.
-/

namespace C374966

open Finset MvPolynomial

/-- The corolla preorder: `cor i j` means `i ≤_τ j`. -/
abbrev cor (i j : Fin 3) : Prop := i = j ∨ j = 0

theorem cor_refl (i : Fin 3) : cor i i := Or.inl rfl
theorem cor_trans : ∀ i j k : Fin 3, cor i j → cor j k → cor i k := by decide
theorem cor_antisymm : ∀ i j : Fin 3, cor i j → cor j i → i = j := by decide
theorem cor_shape : cor 1 0 ∧ cor 2 0 ∧ ¬ cor 1 2 ∧ ¬ cor 2 1 ∧ ¬ cor 0 1 ∧ ¬ cor 0 2 := by
  decide

/-- Order ideals of a preorder (source §2.2): `b ∈ I`, `a ≤ b` imply `a ∈ I`. -/
abbrev IsIdeal (I : Finset (Fin 3)) : Prop := ∀ b ∈ I, ∀ a : Fin 3, cor a b → a ∈ I

theorem ideals_iff : ∀ I : Finset (Fin 3),
    IsIdeal I ↔ I = ∅ ∨ I = {1} ∨ I = {2} ∨ I = {1, 2} ∨ I = Finset.univ := by
  decide

theorem ideal_one : IsIdeal {1} := by decide
theorem ideal_two : IsIdeal {2} := by decide
theorem ideal_univ : IsIdeal Finset.univ := by decide

/-- Literal integer points of the preorder polytope `Q_τ`. -/
def Qcor (v : Fin 3 → ℤ) : Prop :=
  (∀ e, 0 ≤ v e) ∧ ∀ I : Finset (Fin 3), IsIdeal I → ∑ e ∈ I, v e ≤ (I.card : ℤ)

/-- The lattice-point poset `P_τ` (subtype order of the componentwise order on `ℤ^3`). -/
abbrev P := {v : Fin 3 → ℤ // Qcor v}

theorem Qcor_iff (v : Fin 3 → ℤ) :
    Qcor v ↔ 0 ≤ v 0 ∧ 0 ≤ v 1 ∧ 0 ≤ v 2 ∧ v 1 ≤ 1 ∧ v 2 ≤ 1 ∧ v 0 + v 1 + v 2 ≤ 3 := by
  constructor
  · rintro ⟨hnn, hI⟩
    have h1 := hI {1} ideal_one
    have h2 := hI {2} ideal_two
    have h3 := hI Finset.univ ideal_univ
    rw [Finset.sum_singleton, Finset.card_singleton, Nat.cast_one] at h1 h2
    rw [Fin.sum_univ_three, Finset.card_univ, Fintype.card_fin] at h3
    exact ⟨hnn 0, hnn 1, hnn 2, h1, h2, by exact_mod_cast h3⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5⟩
    refine ⟨fun e => ?_, fun I hI => ?_⟩
    · fin_cases e
      · exact h0
      · exact h1
      · exact h2
    · rcases (ideals_iff I).1 hI with rfl | rfl | rfl | rfl | rfl
      · simp
      · rw [Finset.sum_singleton, Finset.card_singleton]; omega
      · rw [Finset.sum_singleton, Finset.card_singleton]; omega
      · have hc : ({1, 2} : Finset (Fin 3)).card = 2 := by decide
        rw [Finset.sum_pair (by decide), hc]; omega
      · rw [Fin.sum_univ_three, Finset.card_univ, Fintype.card_fin]; omega

/-- The twelve points (coordinates: root, leaf 1, leaf 2). -/
def ptsL : List (Fin 3 → ℤ) :=
  [![0, 0, 0], ![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![2, 0, 0], ![1, 1, 0], ![1, 0, 1],
   ![0, 1, 1], ![3, 0, 0], ![2, 1, 0], ![2, 0, 1], ![1, 1, 1]]

def pts : Finset (Fin 3 → ℤ) := ⟨ptsL, Multiset.coe_nodup.2 (by decide)⟩

theorem pts_sound : ∀ v ∈ pts,
    0 ≤ v 0 ∧ 0 ≤ v 1 ∧ 0 ≤ v 2 ∧ v 1 ≤ 1 ∧ v 2 ≤ 1 ∧ v 0 + v 1 + v 2 ≤ 3 := by
  decide

/-- The executable twelve-point finset is exactly the literal ideal-inequality domain. -/
theorem mem_pts (v : Fin 3 → ℤ) : v ∈ pts ↔ Qcor v := by
  rw [Qcor_iff]
  constructor
  · exact pts_sound v
  · rintro ⟨h0, h1, h2, h3, h4, h5⟩
    obtain ⟨a, b, c, rfl⟩ : ∃ a b c : ℤ, v = ![a, b, c] :=
      ⟨v 0, v 1, v 2, by funext i; fin_cases i <;> rfl⟩
    change 0 ≤ a at h0
    change 0 ≤ b at h1
    change 0 ≤ c at h2
    change b ≤ 1 at h3
    change c ≤ 1 at h4
    change a + b + c ≤ 3 at h5
    have ha : a ≤ 3 := by omega
    interval_cases a <;> interval_cases b <;> interval_cases c <;> first | decide | omega

instance instFintypeP : Fintype P := Fintype.subtype pts mem_pts

instance instDecLEP : DecidableLE P := fun a b =>
  decidable_of_iff (∀ i, a.1 i ≤ b.1 i) Iff.rfl

noncomputable instance instDecLTP : DecidableLT P := fun _ _ => Classical.dec _

noncomputable instance instLFOP : LocallyFiniteOrder P := Fintype.toLocallyFiniteOrder

theorem card_P : Fintype.card P = 12 :=
  (Fintype.card_of_subtype pts mem_pts).trans (by decide)

/-- Rank on the executable side: coordinate sum. -/
def rkz (v : Fin 3 → ℤ) : ℕ := (v 0 + v 1 + v 2).toNat

/-- The rank function of `P_τ`: coordinate sum. -/
def rk (a : P) : ℕ := rkz a.1

abbrev le3 (v w : Fin 3 → ℤ) : Prop := v 0 ≤ w 0 ∧ v 1 ≤ w 1 ∧ v 2 ≤ w 2

/-- The order of `P_τ` is the componentwise order. -/
theorem le_iff (a b : P) : a ≤ b ↔ le3 a.1 b.1 := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2⟩
  · rintro ⟨h0, h1, h2⟩
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2

/-- `P_τ` is down-closed between its points: the box between two points lies in `Q_τ`. -/
theorem down_closed (a b : P) (w : Fin 3 → ℤ) (h : ∀ i, a.1 i ≤ w i ∧ w i ≤ b.1 i) :
    Qcor w := by
  have ha := (Qcor_iff a.1).1 a.2
  have hb := (Qcor_iff b.1).1 b.2
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  exact (Qcor_iff w).2 ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- Every interval of `P_τ` is the product of its coordinate chains. -/
def intervalIso (a b : P) : Set.Icc a b ≃o ((i : Fin 3) → Set.Icc (a.1 i) (b.1 i)) where
  toFun z i := ⟨z.1.1 i, z.2.1 i, z.2.2 i⟩
  invFun w := ⟨⟨fun i => (w i).1, down_closed a b _ fun i => ⟨(w i).2.1, (w i).2.2⟩⟩,
    fun i => (w i).2.1, fun i => (w i).2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- The bottom point `000`. -/
def botP : P := ⟨![0, 0, 0], (mem_pts _).1 (by decide)⟩

theorem botP_le (a : P) : botP ≤ a := by
  have ha := (Qcor_iff a.1).1 a.2
  exact (le_iff _ _).2 (show (0 : ℤ) ≤ a.1 0 ∧ (0 : ℤ) ≤ a.1 1 ∧ (0 : ℤ) ≤ a.1 2 by omega)

theorem rk_botP : rk botP = 0 := rfl

theorem rk_lt_four (a : P) : rk a < 4 := by
  have h := (Qcor_iff a.1).1 a.2
  unfold rk rkz
  omega

theorem rk_strictMono : StrictMono rk := by
  intro a b hab
  have hle := (le_iff a b).1 hab.le
  have hne : a.1 ≠ b.1 := fun h => hab.ne (Subtype.ext h)
  have ha := (Qcor_iff a.1).1 a.2
  have hb := (Qcor_iff b.1).1 b.2
  have hd : a.1 0 ≠ b.1 0 ∨ a.1 1 ≠ b.1 1 ∨ a.1 2 ≠ b.1 2 := by
    by_contra hc
    apply hne
    funext i
    fin_cases i
    · by_contra h; exact hc (Or.inl h)
    · by_contra h; exact hc (Or.inr (Or.inl h))
    · by_contra h; exact hc (Or.inr (Or.inr h))
  unfold rk rkz
  omega

theorem exists_between {a b : P} (hab : a ≤ b) (hr : rk a + 2 ≤ rk b) :
    ∃ c : P, a < c ∧ c < b := by
  have hle : le3 a.1 b.1 := (le_iff a b).1 hab
  have ha := (Qcor_iff a.1).1 a.2
  have hb := (Qcor_iff b.1).1 b.2
  have hr' : (a.1 0 + a.1 1 + a.1 2).toNat + 2 ≤ (b.1 0 + b.1 1 + b.1 2).toNat := hr
  have key : ∀ x y z : ℤ, a.1 0 ≤ x ∧ a.1 1 ≤ y ∧ a.1 2 ≤ z →
      x ≤ b.1 0 ∧ y ≤ b.1 1 ∧ z ≤ b.1 2 →
      x + y + z = a.1 0 + a.1 1 + a.1 2 + 1 → ∃ c : P, a < c ∧ c < b := by
    intro x y z k1 k2 hs
    have hz : ∀ i, a.1 i ≤ ![x, y, z] i ∧ ![x, y, z] i ≤ b.1 i := by
      intro i
      fin_cases i
      · exact ⟨k1.1, k2.1⟩
      · exact ⟨k1.2.1, k2.2.1⟩
      · exact ⟨k1.2.2, k2.2.2⟩
    refine ⟨⟨![x, y, z], down_closed a b _ hz⟩, lt_of_le_of_ne ?_ ?_, lt_of_le_of_ne ?_ ?_⟩
    · exact (le_iff _ _).2 k1
    · intro h
      have e0 := congrFun (congrArg Subtype.val h) 0
      have e1 := congrFun (congrArg Subtype.val h) 1
      have e2 := congrFun (congrArg Subtype.val h) 2
      change a.1 0 = x at e0
      change a.1 1 = y at e1
      change a.1 2 = z at e2
      omega
    · exact (le_iff _ _).2 k2
    · intro h
      have e0 := congrFun (congrArg Subtype.val h) 0
      have e1 := congrFun (congrArg Subtype.val h) 1
      have e2 := congrFun (congrArg Subtype.val h) 2
      change x = b.1 0 at e0
      change y = b.1 1 at e1
      change z = b.1 2 at e2
      omega
  obtain ⟨h0, h1, h2⟩ := hle
  by_cases c0 : a.1 0 < b.1 0
  · exact key (a.1 0 + 1) (a.1 1) (a.1 2) ⟨by omega, le_refl _, le_refl _⟩
      ⟨by omega, h1, h2⟩ (by omega)
  · by_cases c1 : a.1 1 < b.1 1
    · exact key (a.1 0) (a.1 1 + 1) (a.1 2) ⟨le_refl _, by omega, le_refl _⟩
        ⟨h0, by omega, h2⟩ (by omega)
    · by_cases c2 : a.1 2 < b.1 2
      · exact key (a.1 0) (a.1 1) (a.1 2 + 1) ⟨le_refl _, le_refl _, by omega⟩
          ⟨h0, h1, by omega⟩ (by omega)
      · exfalso
        omega

/-- Grading: covers raise the rank by exactly one. -/
theorem rk_covBy {a b : P} (h : a ⋖ b) : rk b = rk a + 1 := by
  have h1 := rk_strictMono h.lt
  by_contra hne
  obtain ⟨c, hac, hcb⟩ := exists_between h.lt.le (by omega)
  exact h.2 hac hcb

/-- Grading: every maximal element of `P_τ` has rank `3`. -/
theorem rk_of_maximal (a : P) (hmax : ∀ b : P, a ≤ b → b = a) : rk a = 3 := by
  have ha := (Qcor_iff a.1).1 a.2
  by_contra hne
  have hne' : ¬ (a.1 0 + a.1 1 + a.1 2).toNat = 3 := hne
  have hq : Qcor ![a.1 0 + 1, a.1 1, a.1 2] := by
    rw [Qcor_iff]
    show 0 ≤ a.1 0 + 1 ∧ 0 ≤ a.1 1 ∧ 0 ≤ a.1 2 ∧ a.1 1 ≤ 1 ∧ a.1 2 ≤ 1 ∧
      a.1 0 + 1 + a.1 1 + a.1 2 ≤ 3
    omega
  have hb := hmax ⟨_, hq⟩ ((le_iff _ _).2
    (show a.1 0 ≤ a.1 0 + 1 ∧ a.1 1 ≤ a.1 1 ∧ a.1 2 ≤ a.1 2 by omega))
  have e0 := congrFun (congrArg Subtype.val hb) 0
  change a.1 0 + 1 = a.1 0 at e0
  omega

/-! ### Möbius function of `P_τ` (box formula) -/

/-- One-dimensional chain Möbius values. -/
def gz (t : ℤ) : ℤ := if t = 0 then 1 else if t = 1 then -1 else 0

def fz (v w : Fin 3 → ℤ) : ℤ := gz (w 0 - v 0) * gz (w 1 - v 1) * gz (w 2 - v 2)

/-- Candidate Möbius function: product of coordinate chain Möbius values. -/
def fP (a b : P) : ℚ := ∏ i : Fin 3, ((gz (b.1 i - a.1 i) : ℤ) : ℚ)

theorem fP_cast (a b : P) : fP a b = (fz a.1 b.1 : ℚ) := by
  simp only [fP, Fin.prod_univ_three, fz, Int.cast_mul]

theorem fP_self (a : P) : fP a a = 1 := by
  simp [fP, gz]

theorem sum1 (a b : ℤ) (h : a ≤ b) :
    ∑ t ∈ Finset.Icc a b, ((gz (t - a) : ℤ) : ℚ) = if a = b then 1 else 0 := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · rw [Finset.Icc_self, Finset.sum_singleton, sub_self, ite_eq_left rfl]
    norm_num [gz]
  · rw [ite_eq_right (ne_of_lt hlt)]
    rw [Finset.sum_eq_add a (a + 1) (by omega)]
    · rw [sub_self, add_sub_cancel_left]
      norm_num [gz]
    · intro c hc hca
      rw [Finset.mem_Icc] at hc
      obtain ⟨hc1, hc2⟩ := hca
      have e1 : ¬ (c - a = 0) := by omega
      have e2 : ¬ (c - a = 1) := by omega
      rw [gz, ite_eq_right e1, ite_eq_right e2, Int.cast_zero]
    · intro ha
      exact absurd (Finset.mem_Icc.2 ⟨le_refl a, h⟩) ha
    · intro hb
      exact absurd (Finset.mem_Icc.2 ⟨by omega, by omega⟩) hb

theorem sum_Icc_P (a b : P) (F : (Fin 3 → ℤ) → ℚ) :
    ∑ z ∈ Finset.Icc a b, F z.1
      = ∑ w ∈ Fintype.piFinset (fun i => Finset.Icc (a.1 i) (b.1 i)), F w := by
  have hmap : (Finset.Icc a b).map (Function.Embedding.subtype Qcor)
      = Fintype.piFinset (fun i => Finset.Icc (a.1 i) (b.1 i)) := by
    ext w
    simp only [Finset.mem_map, Finset.mem_Icc, Fintype.mem_piFinset]
    constructor
    · rintro ⟨z, ⟨h1, h2⟩, rfl⟩ i
      exact ⟨h1 i, h2 i⟩
    · intro h
      exact ⟨⟨w, down_closed a b w h⟩, ⟨fun i => (h i).1, fun i => (h i).2⟩, rfl⟩
  rw [← hmap]
  exact (Finset.sum_map (Finset.Icc a b) (Function.Embedding.subtype Qcor) F).symm

theorem fP_sum (a b : P) (hab : a < b) : ∑ z ∈ Finset.Icc a b, fP a z = 0 := by
  have h1 : ∑ z ∈ Finset.Icc a b, fP a z
      = ∑ w ∈ Fintype.piFinset (fun i => Finset.Icc (a.1 i) (b.1 i)),
          ∏ i, ((gz (w i - a.1 i) : ℤ) : ℚ) :=
    sum_Icc_P a b (fun w => ∏ i, ((gz (w i - a.1 i) : ℤ) : ℚ))
  have h2 := (Finset.prod_univ_sum (fun i => Finset.Icc (a.1 i) (b.1 i))
      (fun i t => ((gz (t - a.1 i) : ℤ) : ℚ))).symm
  rw [h1, h2]
  have hle : ∀ i, a.1 i ≤ b.1 i := fun i => hab.le i
  obtain ⟨i, hi⟩ : ∃ i, a.1 i ≠ b.1 i := by
    by_contra hcon
    exact hab.ne (Subtype.ext (funext fun i => by by_contra h; exact hcon ⟨i, h⟩))
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [sum1 _ _ (hle i), ite_eq_right hi]

/-- The Möbius function of `P_τ` (pinned Mathlib `IncidenceAlgebra.mu`) is the box formula. -/
theorem mu_P (a b : P) (hab : a ≤ b) : IncidenceAlgebra.mu ℚ a b = (fz a.1 b.1 : ℚ) := by
  rw [mu_eq_of_sum fP fP_self fP_sum a b hab, fP_cast]

/-! ### The M-triangle of `P_τ` -/

theorem sum_P_pts (F : (Fin 3 → ℤ) → (Fin 3 → ℤ) → ℚ) :
    ∑ a : P, ∑ b : P, F a.1 b.1 = ∑ v ∈ pts, ∑ w ∈ pts, F v w := by
  rw [Finset.sum_subtype (F := instFintypeP) pts mem_pts]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_subtype (F := instFintypeP) pts mem_pts]

/-- Explicit integer coefficient sums over the twelve points. -/
def Tz (i j : ℕ) : ℤ := ∑ v ∈ pts, ∑ w ∈ pts,
  if rkz v = i ∧ rkz w = j then (if le3 v w then fz v w else 0) else 0

def tableP : List (List ℤ) := [[1, -3, 3, -1], [0, 3, -7, 5], [0, 0, 4, -8], [0, 0, 0, 4]]

def tPz (i j : ℕ) : ℤ := (tableP.getD i []).getD j 0

def tPq (i j : ℕ) : ℚ := (tPz i j : ℚ)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem Tz_table : ∀ i j : Fin 4, Tz i j = tPz i j := by
  decide

theorem Tab_P (i j : ℕ) : Tab P rk i j = (Tz i j : ℚ) := by
  have hmu : ∀ a b : P,
      (if rk a = i ∧ rk b = j then (if a ≤ b then IncidenceAlgebra.mu ℚ a b else 0) else 0)
        = (((if rkz a.1 = i ∧ rkz b.1 = j then (if le3 a.1 b.1 then fz a.1 b.1 else 0)
            else 0 : ℤ)) : ℚ) := by
    intro a b
    by_cases h1 : rkz a.1 = i ∧ rkz b.1 = j
    · rw [ite_eq_left (show rk a = i ∧ rk b = j from h1), ite_eq_left h1]
      by_cases h2 : le3 a.1 b.1
      · have hab : a ≤ b := (le_iff a b).2 h2
        rw [ite_eq_left hab, ite_eq_left h2, mu_P a b hab]
      · rw [ite_eq_right (fun h => h2 ((le_iff a b).1 h)), ite_eq_right h2, Int.cast_zero]
    · rw [ite_eq_right (show ¬ (rk a = i ∧ rk b = j) from h1), ite_eq_right h1, Int.cast_zero]
  unfold Tab
  simp only [hmu]
  rw [sum_P_pts (fun v w => (((if rkz v = i ∧ rkz w = j then (if le3 v w then fz v w else 0)
      else 0 : ℤ)) : ℚ))]
  simp only [Tz, Int.cast_sum]

/-- `M_{P_τ}` equals the polynomial with the computed coefficient table. -/
theorem MP_eq_tab : Mtri P rk = tab tPq := by
  rw [Mtri_eq, ← regroup rk rk_lt_four
    (fun a b => if a ≤ b then IncidenceAlgebra.mu ℚ a b else 0)]
  apply tab_congr
  intro i hi j hj
  have hT : Tz i j = tPz i j := Tz_table ⟨i, hi⟩ ⟨j, hj⟩
  show Tab P rk i j = tPq i j
  rw [Tab_P, hT, tPq]

theorem tPz_vals : tPz 0 0 = 1 ∧ tPz 0 1 = -3 ∧ tPz 0 2 = 3 ∧ tPz 0 3 = -1 ∧
    tPz 1 0 = 0 ∧ tPz 1 1 = 3 ∧ tPz 1 2 = -7 ∧ tPz 1 3 = 5 ∧
    tPz 2 0 = 0 ∧ tPz 2 1 = 0 ∧ tPz 2 2 = 4 ∧ tPz 2 3 = -8 ∧
    tPz 3 0 = 0 ∧ tPz 3 1 = 0 ∧ tPz 3 2 = 0 ∧ tPz 3 3 = 4 := by
  decide

/-- `1 - 3y + 3y² - y³ + 3xy - 7xy² + 5xy³ + 4x²y² - 8x²y³ + 4x³y³`. -/
noncomputable def MP_lit : Pxy :=
  1 - 3 * X 1 + 3 * X 1 ^ 2 - X 1 ^ 3 + 3 * X 0 * X 1 - 7 * X 0 * X 1 ^ 2
    + 5 * X 0 * X 1 ^ 3 + 4 * X 0 ^ 2 * X 1 ^ 2 - 8 * X 0 ^ 2 * X 1 ^ 3 + 4 * X 0 ^ 3 * X 1 ^ 3

theorem tab_P_lit : tab tPq = MP_lit := by
  obtain ⟨e00, e01, e02, e03, e10, e11, e12, e13, e20, e21, e22, e23, e30, e31, e32, e33⟩ :=
    tPz_vals
  simp only [tab, tPq, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    e00, e01, e02, e03, e10, e11, e12, e13, e20, e21, e22, e23, e30, e31, e32, e33,
    Int.cast_zero, Int.cast_one, Int.cast_neg, Int.cast_ofNat,
    map_zero, map_one, map_neg, map_ofNat, MP_lit]
  ring

/-- The actual M-triangle of `P_τ`. -/
theorem Mtri_P_lit : Mtri P rk = MP_lit := MP_eq_tab.trans tab_P_lit

end C374966
```

### C374966Transmute.lean

source sha256 `9c6029b6b4d1aa2d371fabd0dec916ef90f434eaaa35f88e5aa4a40a7c54d0ec`; fresh olean sha256 `a2b17caf323b994b83d57b8d78124b6f12ab0b1bcb6f325a7604f8b4ae289608`

```lean
import C374966Corolla
import Mathlib.Tactic.FieldSimp

/-!
# MathDB 374966 — transmutation of `M_{P_τ}`

`M̄(x,y) = M((1-y)/(1-xy), 1-xy)` computed in `ℚ(x,y) = FractionRing ℚ[x,y]`, equal to the image
of `1 + (-5+5x)y + (8-13x+5x²)y² + (-4+8x-5x²+x³)y³`.
-/

namespace C374966

open Finset MvPolynomial

def tableM : List (List ℤ) := [[1, -5, 8, -4], [0, 5, -13, 8], [0, 0, 5, -5], [0, 0, 0, 1]]

def tMz (i j : ℕ) : ℤ := (tableM.getD i []).getD j 0

def tMq (i j : ℕ) : ℚ := (tMz i j : ℚ)

theorem tMz_vals : tMz 0 0 = 1 ∧ tMz 0 1 = -5 ∧ tMz 0 2 = 8 ∧ tMz 0 3 = -4 ∧
    tMz 1 0 = 0 ∧ tMz 1 1 = 5 ∧ tMz 1 2 = -13 ∧ tMz 1 3 = 8 ∧
    tMz 2 0 = 0 ∧ tMz 2 1 = 0 ∧ tMz 2 2 = 5 ∧ tMz 2 3 = -5 ∧
    tMz 3 0 = 0 ∧ tMz 3 1 = 0 ∧ tMz 3 2 = 0 ∧ tMz 3 3 = 1 := by
  decide

/-- Hand cross-check form `M̄ = 1+(-5+5x)y+(8-13x+5x²)y²+(-4+8x-5x²+x³)y³`. -/
noncomputable def Mbar_lit : Pxy :=
  1 + (-5 + 5 * X 0) * X 1 + (8 - 13 * X 0 + 5 * X 0 ^ 2) * X 1 ^ 2
    + (-4 + 8 * X 0 - 5 * X 0 ^ 2 + X 0 ^ 3) * X 1 ^ 3

theorem tab_M_lit : tab tMq = Mbar_lit := by
  obtain ⟨e00, e01, e02, e03, e10, e11, e12, e13, e20, e21, e22, e23, e30, e31, e32, e33⟩ :=
    tMz_vals
  simp only [tab, tMq, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    e00, e01, e02, e03, e10, e11, e12, e13, e20, e21, e22, e23, e30, e31, e32, e33,
    Int.cast_zero, Int.cast_one, Int.cast_neg, Int.cast_ofNat,
    map_zero, map_one, map_neg, map_ofNat, Mbar_lit]
  ring

/-- The literal rational transmutation of the explicit `M_{P_τ}`. -/
theorem transmute_MP_lit : transmute MP_lit = algebraMap Pxy FracXY Mbar_lit := by
  have hne : (1 : FracXY) - xF * yF ≠ 0 := one_sub_xy_ne
  simp only [transmute, MP_lit, Mbar_lit, map_add, map_sub, map_mul, map_pow, map_one,
    map_ofNat, map_neg, tr_X0, tr_X1]
  field_simp
  ring

/-- `M̄_{P_τ}` of the actual Möbius M-triangle is the image of the explicit table polynomial. -/
theorem transmute_MP : transmute (Mtri P rk) = algebraMap Pxy FracXY (tab tMq) := by
  rw [Mtri_P_lit, transmute_MP_lit, tab_M_lit]

/-- Checked coefficients of `M̄_{P_τ}`: diagonal `1,5,5,1` and `[x y²] = -13`. -/
theorem Mbar_coeffs :
    (tab tMq).coeff (mon 0 0) = 1 ∧ (tab tMq).coeff (mon 1 1) = 5 ∧
    (tab tMq).coeff (mon 2 2) = 5 ∧ (tab tMq).coeff (mon 3 3) = 1 ∧
    (tab tMq).coeff (mon 1 2) = -13 := by
  obtain ⟨e00, -, -, -, -, e11, e12, -, -, -, e22, -, -, -, -, e33⟩ := tMz_vals
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [coeff_tab tMq (i := 0) (j := 0) (by norm_num) (by norm_num), tMq, e00]
    norm_num
  · rw [coeff_tab tMq (i := 1) (j := 1) (by norm_num) (by norm_num), tMq, e11]
    norm_num
  · rw [coeff_tab tMq (i := 2) (j := 2) (by norm_num) (by norm_num), tMq, e22]
    norm_num
  · rw [coeff_tab tMq (i := 3) (j := 3) (by norm_num) (by norm_num), tMq, e33]
    norm_num
  · rw [coeff_tab tMq (i := 1) (j := 2) (by norm_num) (by norm_num), tMq, e12]
    norm_num

end C374966
```

### C374966Lattice.lean

source sha256 `bae00e9597257c177718da5af8aaab8c22f28026c50113cb332f8a3129e7e54d`; fresh olean sha256 `666b8901a7efc240a71b86e2d2c9c2df0e364fed9a57818cdaef5df7783388d5`

```lean
import C374966Defs
import Mathlib.Order.Grade
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.IntervalCases

/-!
# MathDB 374966 — finite graded lattices cannot have the corolla M-triangle data

For a finite lattice with a strictly monotone rank map `ρ` (in particular any graded lattice):
`[x^k y^k] M_L = #{ρ = k}` and `[x y²] M_L = -∑_{ρ c = 2} d_c` with `d_c = #{a ≤ c, ρ a = 1}`.
Two distinct rank-1 elements below a rank-2 element `c` have join `c`, so
`∑ C(d_c, 2) ≤ C(#{ρ = 1}, 2)`. With counts `5, 5` and `∑ d_c = 13` this is impossible.
-/

namespace C374966

open Finset MvPolynomial

/-- A rank map making a bounded poset graded of rank `n`. -/
structure IsGradedRank {L : Type*} [PartialOrder L] [BoundedOrder L] (ρ : L → ℕ) (n : ℕ) :
    Prop where
  strictMono : StrictMono ρ
  covBy : ∀ a b : L, a ⋖ b → ρ b = ρ a + 1
  bot : ρ ⊥ = 0
  top : ρ ⊤ = n

/-- Binding to Mathlib's standard graded orders. -/
theorem isGradedRank_of_gradeOrder {L : Type*} [PartialOrder L] [BoundedOrder L]
    [GradeOrder ℕ L] {n : ℕ} (hb : grade ℕ (⊥ : L) = 0) (ht : grade ℕ (⊤ : L) = n) :
    IsGradedRank (grade ℕ : L → ℕ) n where
  strictMono := grade_strictMono (𝕆 := ℕ)
  covBy _ _ h := (Nat.covBy_iff_add_one_eq.1 (CovBy.grade (𝕆 := ℕ) h)).symm
  bot := hb
  top := ht

variable {L : Type*}

theorem eq_of_le_of_rank_ge [PartialOrder L] {ρ : L → ℕ} (hρ : StrictMono ρ) {u v : L}
    (h : u ≤ v) (hr : ρ v ≤ ρ u) : u = v := by
  by_contra hne
  have := hρ (lt_of_le_of_ne h hne)
  omega

/-- Comparable points of successive rank form a cover. -/
theorem covBy_of_rank [PartialOrder L] {ρ : L → ℕ} (hρ : StrictMono ρ) {a b : L}
    (hab : a ≤ b) (hr : ρ b = ρ a + 1) : a ⋖ b := by
  refine ⟨lt_of_le_of_ne hab ?_, ?_⟩
  · intro h
    rw [h] at hr
    omega
  · intro c hac hcb
    have h1 := hρ hac
    have h2 := hρ hcb
    omega

/-- In a graded poset the rank-one layer is exactly the set of atoms. -/
theorem rank_one_iff_bot_covBy [PartialOrder L] [BoundedOrder L] {ρ : L → ℕ} {n : ℕ}
    (hg : IsGradedRank ρ n) (a : L) : ρ a = 1 ↔ ⊥ ⋖ a := by
  constructor
  · intro h
    exact covBy_of_rank hg.strictMono bot_le (by have := hg.bot; omega)
  · intro h
    have h1 := hg.covBy _ _ h
    have h2 := hg.bot
    omega

/-- `μ = -1` on comparable pairs of ranks `1 < 2`. -/
theorem mu_cover [PartialOrder L] [LocallyFiniteOrder L] [DecidableEq L] {ρ : L → ℕ}
    (hρ : StrictMono ρ) {a b : L} (ha : ρ a = 1) (hb : ρ b = 2) (hab : a ≤ b) :
    IncidenceAlgebra.mu ℚ a b = -1 := by
  have hne : a ≠ b := by
    intro h
    rw [h] at ha
    omega
  rw [IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne hne]
  have hIco : Finset.Ico a b = {a} := by
    ext x
    rw [Finset.mem_Ico, Finset.mem_singleton]
    constructor
    · rintro ⟨hax, hxb⟩
      by_contra hxa
      have h1 := hρ (lt_of_le_of_ne hax (Ne.symm hxa))
      have h2 := hρ hxb
      omega
    · rintro rfl
      exact ⟨le_rfl, lt_of_le_of_ne hab hne⟩
  rw [hIco, Finset.sum_singleton, IncidenceAlgebra.mu_apply, ite_eq_left rfl]

/-- Diagonal coefficients count rank layers. -/
theorem Tab_diag [PartialOrder L] [Fintype L] [LocallyFiniteOrder L] [DecidableEq L]
    [DecidableLE L] {ρ : L → ℕ} (hρ : StrictMono ρ) (k : ℕ) :
    Tab L ρ k k = ((univ.filter (fun a => ρ a = k)).card : ℚ) := by
  unfold Tab
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : ρ a = k
  · rw [ite_eq_left ha, Nat.cast_one, Finset.sum_eq_single a]
    · rw [ite_eq_left (And.intro ha ha), ite_eq_left le_rfl, IncidenceAlgebra.mu_apply,
        ite_eq_left rfl]
    · intro b _ hb
      by_cases hb' : ρ a = k ∧ ρ b = k
      · rw [ite_eq_left hb', ite_eq_right]
        intro hab
        exact hb (eq_of_le_of_rank_ge hρ hab (le_of_eq (hb'.2.trans hb'.1.symm))).symm
      · rw [ite_eq_right hb']
    · intro h
      exact absurd (Finset.mem_univ a) h
  · rw [ite_eq_right ha, Nat.cast_zero]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [ite_eq_right (show ¬ (ρ a = k ∧ ρ b = k) from fun h => ha h.1)]

/-- The `x y²` coefficient is minus the number of rank-1/rank-2 covers. -/
theorem Tab_cover [PartialOrder L] [Fintype L] [LocallyFiniteOrder L] [DecidableEq L]
    [DecidableLE L] {ρ : L → ℕ} (hρ : StrictMono ρ) :
    Tab L ρ 1 2 = -∑ b ∈ univ.filter (fun b => ρ b = 2),
      ((univ.filter (fun a => ρ a = 1 ∧ a ≤ b)).card : ℚ) := by
  have hterm : ∀ a b : L,
      (if ρ a = 1 ∧ ρ b = 2 then (if a ≤ b then IncidenceAlgebra.mu ℚ a b else 0) else 0)
        = -(if ρ b = 2 then (if ρ a = 1 ∧ a ≤ b then (1 : ℚ) else 0) else 0) := by
    intro a b
    by_cases h1 : ρ a = 1 ∧ ρ b = 2
    · rw [ite_eq_left h1, ite_eq_left h1.2]
      by_cases h2 : a ≤ b
      · rw [ite_eq_left h2, ite_eq_left (And.intro h1.1 h2), mu_cover hρ h1.1 h1.2 h2]
      · rw [ite_eq_right h2, ite_eq_right (show ¬ (ρ a = 1 ∧ a ≤ b) from fun h => h2 h.2),
          neg_zero]
    · rw [ite_eq_right h1]
      by_cases hb : ρ b = 2
      · rw [ite_eq_left hb,
          ite_eq_right (show ¬ (ρ a = 1 ∧ a ≤ b) from fun h => h1 ⟨h.1, hb⟩), neg_zero]
      · rw [ite_eq_right hb, neg_zero]
  calc Tab L ρ 1 2
      = ∑ a, ∑ b, -(if ρ b = 2 then (if ρ a = 1 ∧ a ≤ b then (1 : ℚ) else 0) else 0) := by
        unfold Tab
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hterm a b
    _ = -∑ b, ∑ a, (if ρ b = 2 then (if ρ a = 1 ∧ a ≤ b then (1 : ℚ) else 0) else 0) := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_neg_distrib]
    _ = -∑ b, (if ρ b = 2 then ((univ.filter (fun a => ρ a = 1 ∧ a ≤ b)).card : ℚ) else 0) := by
        congr 1
        refine Finset.sum_congr rfl fun b _ => ?_
        by_cases hb : ρ b = 2
        · simp only [ite_eq_left hb]
          rw [Finset.sum_boole]
        · simp only [ite_eq_right hb, Finset.sum_const_zero]
    _ = -∑ b ∈ univ.filter (fun b => ρ b = 2),
          ((univ.filter (fun a => ρ a = 1 ∧ a ≤ b)).card : ℚ) := by
        rw [Finset.sum_filter]

/-- Two distinct rank-1 elements below a rank-2 element `b` have join `b`. -/
theorem join_eq [Lattice L] {ρ : L → ℕ} (hρ : StrictMono ρ) {x y b : L}
    (hx : ρ x = 1) (hy : ρ y = 1) (hxy : x ≠ y) (hxb : x ≤ b) (hyb : y ≤ b) (hb : ρ b = 2) :
    x ⊔ y = b := by
  have h1 : x < x ⊔ y := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro h
    have hyx : y ≤ x := by
      rw [h]
      exact le_sup_right
    exact hxy (eq_of_le_of_rank_ge hρ hyx (by omega)).symm
  have h2 := hρ h1
  exact eq_of_le_of_rank_ge hρ (sup_le hxb hyb) (by omega)

/-- Double counting of atom pairs under rank-2 elements. -/
theorem count_bound [Lattice L] [Fintype L] [DecidableEq L] [DecidableLE L]
    (ρ : L → ℕ) (hρ : StrictMono ρ) :
    ∑ b ∈ univ.filter (fun b => ρ b = 2), (univ.filter (fun a => ρ a = 1 ∧ a ≤ b)).card.choose 2
      ≤ (univ.filter (fun a => ρ a = 1)).card.choose 2 := by
  have hdisj : ((univ.filter (fun b => ρ b = 2) : Finset L) : Set L).PairwiseDisjoint
      (fun b => (univ.filter (fun a => ρ a = 1 ∧ a ≤ b)).powersetCard 2) := by
    intro b hb b' hb' hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro s hs hs'
    simp only [Finset.mem_powersetCard] at hs hs'
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 hs.2
    have hx := hs.1 (Finset.mem_insert_self x {y})
    have hy := hs.1 (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
    have hx' := hs'.1 (Finset.mem_insert_self x {y})
    have hy' := hs'.1 (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy hx' hy'
    have hb2 : ρ b = 2 := by simpa using hb
    have hb2' : ρ b' = 2 := by simpa using hb'
    apply hne
    rw [← join_eq hρ hx.1 hy.1 hxy hx.2 hy.2 hb2, join_eq hρ hx'.1 hy'.1 hxy hx'.2 hy'.2 hb2']
  calc ∑ b ∈ univ.filter (fun b => ρ b = 2),
          (univ.filter (fun a => ρ a = 1 ∧ a ≤ b)).card.choose 2
      = ∑ b ∈ univ.filter (fun b => ρ b = 2),
          ((univ.filter (fun a => ρ a = 1 ∧ a ≤ b)).powersetCard 2).card := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.card_powersetCard]
    _ = ((univ.filter (fun b => ρ b = 2)).biUnion
          (fun b => (univ.filter (fun a => ρ a = 1 ∧ a ≤ b)).powersetCard 2)).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ ((univ.filter (fun a => ρ a = 1)).powersetCard 2).card := by
        apply Finset.card_le_card
        intro s hs
        rw [Finset.mem_biUnion] at hs
        obtain ⟨b, _, hs⟩ := hs
        refine Finset.powersetCard_mono ?_ hs
        intro a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
        exact ha.1
    _ = (univ.filter (fun a => ρ a = 1)).card.choose 2 := Finset.card_powersetCard 2 _

/-- `C(d,2) + 3 ≥ 2d` for all `d` (equivalently `(d-2)(d-3) ≥ 0`). -/
theorem two_mul_le_choose_two_add_three (d : ℕ) : 2 * d ≤ d.choose 2 + 3 := by
  induction d with
  | zero => decide
  | succ n ih =>
    have e : (n + 1).choose 2 = n.choose 1 + n.choose 2 := Nat.choose_succ_succ' n 1
    rw [e, Nat.choose_one_right]
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> decide
    · omega

/-- Core obstruction: no finite lattice with a strictly monotone rank map has
`[xy]M = 5`, `[x²y²]M = 5` and `[xy²]M = -13`. -/
theorem no_lattice_core [Lattice L] [Fintype L] [LocallyFiniteOrder L] [DecidableEq L]
    [DecidableLE L] (ρ : L → ℕ) (hρ : StrictMono ρ)
    (h11 : (Mtri L ρ).coeff (mon 1 1) = 5) (h22 : (Mtri L ρ).coeff (mon 2 2) = 5)
    (h12 : (Mtri L ρ).coeff (mon 1 2) = -13) : False := by
  rw [coeff_Mtri, Tab_diag hρ] at h11
  rw [coeff_Mtri, Tab_diag hρ] at h22
  rw [coeff_Mtri, Tab_cover hρ] at h12
  have hA : (univ.filter (fun a => ρ a = 1)).card = 5 := by exact_mod_cast h11
  have hB : (univ.filter (fun a => ρ a = 2)).card = 5 := by exact_mod_cast h22
  have hE : ∑ b ∈ univ.filter (fun b => ρ b = 2),
      (univ.filter (fun a => ρ a = 1 ∧ a ≤ b)).card = 13 := by
    have h : ∑ b ∈ univ.filter (fun b => ρ b = 2),
        ((univ.filter (fun a => ρ a = 1 ∧ a ≤ b)).card : ℚ) = 13 := by
      linarith
    exact_mod_cast h
  have hcb := count_bound ρ hρ
  rw [hA] at hcb
  have hsum : ∑ b ∈ univ.filter (fun b => ρ b = 2),
        2 * (univ.filter (fun a => ρ a = 1 ∧ a ≤ b)).card
      ≤ ∑ b ∈ univ.filter (fun b => ρ b = 2),
        ((univ.filter (fun a => ρ a = 1 ∧ a ≤ b)).card.choose 2 + 3) :=
    Finset.sum_le_sum fun b _ => two_mul_le_choose_two_add_three _
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, hB, hE] at hsum
  have h10 : Nat.choose 5 2 = 10 := by decide
  omega

end C374966
```

### C374966Main.lean

source sha256 `6bcce3a950740a9a2bb237e527dfb389ebde4bcff9f5d2581788278ccba9b756`; fresh olean sha256 `bb580acebc6ede177b47218c8f3db42bd25e328a5be6466b50221bef1bbb60d6`

```lean
import C374966Transmute
import C374966Lattice

/-!
# MathDB 374966 — literal refutation endpoint

Conjecture 8.1 of Athanasiadis–Chapoton (arXiv:2605.26916v1): for every preorder `τ` of size `n`
there is a finite graded lattice `L_τ` of rank `n` with `Z(P_τ,t) = Z(L_τ,t)` and
`M̄_{P_τ}(x,y) = M_{L_τ}(x,y)`.  For the corolla `τ = t₃` (`n = 3`) no finite graded lattice of
rank 3 satisfies even the M-equality, so the zeta conjunct is redundant.
-/

namespace C374966

open Finset MvPolynomial

universe u

/-- Lattice points of `Q_τ` for an arbitrary preorder relation `le` on `Fin n` (source §1, (2)). -/
def QPre {n : ℕ} (le : Fin n → Fin n → Prop) (v : Fin n → ℤ) : Prop :=
  (∀ e, 0 ≤ v e) ∧
    ∀ I : Finset (Fin n), (∀ b ∈ I, ∀ a, le a b → a ∈ I) → ∑ e ∈ I, v e ≤ (I.card : ℤ)

/-- The corolla domain is the general preorder-polytope domain at `τ = cor`. -/
theorem Qcor_eq_QPre : Qcor = QPre cor := rfl

/-- No finite graded lattice of rank 3 has `M_L = M̄_{P_τ}` for the corolla `τ = t₃`. -/
theorem corolla_no_M_match (L : Type u) [Lattice L] [BoundedOrder L] [Fintype L]
    [DecidableEq L] [DecidableLE L] [LocallyFiniteOrder L] (ρ : L → ℕ)
    (hg : IsGradedRank ρ 3) :
    transmute (Mtri P rk) ≠ algebraMap Pxy FracXY (Mtri L ρ) := by
  intro h
  rw [transmute_MP] at h
  have h2 : tab tMq = Mtri L ρ := iota_injective h
  obtain ⟨-, c11, c22, -, c12⟩ := Mbar_coeffs
  rw [h2] at c11 c22 c12
  exact no_lattice_core ρ hg.strictMono c11 c22 c12

/-- **Literal endpoint.** Conjecture 8.1 fails at the corolla `τ = t₃` (`n = 3`). -/
theorem conj81_false_at_corolla :
    ¬ ∃ (L : Type u) (_ : Lattice L) (_ : BoundedOrder L) (_ : Fintype L) (_ : DecidableEq L)
      (_ : DecidableLE L) (_ : LocallyFiniteOrder L) (ρ : L → ℕ),
      IsGradedRank ρ 3 ∧ transmute (Mtri P rk) = algebraMap Pxy FracXY (Mtri L ρ) := by
  rintro ⟨L, _, _, _, _, _, _, ρ, hg, h⟩
  exact corolla_no_M_match L ρ hg h

/-- **Literal endpoint with the zeta conjunct.** For any predicate `Zeta` standing for
`Z(P_τ,t) = Z(L,t)` on the same lattice, the full conjunction of Conjecture 8.1 fails. -/
theorem conj81_false_at_corolla_with_zeta
    (Zeta : ∀ (L : Type u) [Lattice L] [Fintype L], Prop) :
    ¬ ∃ (L : Type u) (_ : Lattice L) (_ : BoundedOrder L) (_ : Fintype L) (_ : DecidableEq L)
      (_ : DecidableLE L) (_ : LocallyFiniteOrder L) (ρ : L → ℕ),
      IsGradedRank ρ 3 ∧ Zeta L ∧ transmute (Mtri P rk) = algebraMap Pxy FracXY (Mtri L ρ) := by
  rintro ⟨L, _, _, _, _, _, _, ρ, hg, -, h⟩
  exact corolla_no_M_match L ρ hg h

/-- The same endpoint for Mathlib's standard graded orders `GradeOrder ℕ L`. -/
theorem conj81_false_at_corolla_gradeOrder (L : Type u) [Lattice L] [BoundedOrder L]
    [Fintype L] [DecidableEq L] [DecidableLE L] [LocallyFiniteOrder L] [GradeOrder ℕ L]
    (hb : grade ℕ (⊥ : L) = 0) (ht : grade ℕ (⊤ : L) = 3) :
    transmute (Mtri P rk) ≠ algebraMap Pxy FracXY (Mtri L (grade ℕ)) :=
  corolla_no_M_match L (grade ℕ) (isGradedRank_of_gradeOrder hb ht)

#print axioms conj81_false_at_corolla
#print axioms conj81_false_at_corolla_with_zeta
#print axioms conj81_false_at_corolla_gradeOrder
#print axioms corolla_no_M_match
#print axioms Qcor_eq_QPre
#print axioms ideals_iff
#print axioms Qcor_iff
#print axioms mem_pts
#print axioms card_P
#print axioms le_iff
#print axioms intervalIso
#print axioms rk_strictMono
#print axioms rk_covBy
#print axioms rk_of_maximal
#print axioms botP_le
#print axioms mu_eq_of_sum
#print axioms mu_P
#print axioms Tz_table
#print axioms Mtri_P_lit
#print axioms one_sub_xy_ne
#print axioms iota_injective
#print axioms transmute_MP_lit
#print axioms transmute_MP
#print axioms Mbar_coeffs
#print axioms isGradedRank_of_gradeOrder
#print axioms rank_one_iff_bot_covBy
#print axioms covBy_of_rank
#print axioms mu_cover
#print axioms Tab_diag
#print axioms Tab_cover
#print axioms join_eq
#print axioms count_bound
#print axioms two_mul_le_choose_two_add_three
#print axioms no_lattice_core

end C374966
```

## Appendix B. Reviewer audit module (separately labeled; NOT part of the canonical certificate)

Imports the canonical `C374966Main`; adds no canonical declarations and changes none.

### A374966NativeBridge.lean

source sha256 `6a250e896193665cfdbca9e45894737edf12f3a13e13a7d4137ec917486bde0b`; olean sha256 `5160f7e474745b6d6651a5bfdb6a9556fe00855c999660b5cfa1586b3d0ea46e`

```lean
import C374966Main
import Mathlib.Order.Zorn
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Finset.Grade

/-!
# MathDB 374966 — independent reviewer audit module (NOT one of the five canonical modules)

Binds the native definitions of Athanasiadis–Chapoton, arXiv:2605.26916v1, to the canonical
replayed endpoint `C374966.conj81_false_at_corolla`:

* §2.3: a finite poset is *graded* if all maximal chains have the same length `d` (length is one
  less than cardinality); "rank `n`" means `d = n`.  Maximal chains are Mathlib's literal
  `IsMaxChain (· ≤ ·)` (a chain not strictly contained in another chain).
* the rank function of a graded poset (Stanley EC1 §3.1, cited as [Sta11]): `0` on minimal
  elements and `+1` along every cover relation (§8 writes `ρ : P → ℕ`).

No `BoundedOrder`, `IsGradedRank` or `GradeOrder` is assumed in the native endpoint.
-/

namespace A374966

open C374966

universe u v

/-- Native §2.3 at rank `n`: every maximal chain has length `n`, i.e. exactly `n + 1` elements. -/
def NativeGradedRank (α : Type v) [PartialOrder α] (n : ℕ) : Prop :=
  ∀ s : Set α, IsMaxChain (· ≤ ·) s → s.ncard = n + 1

/-- Rank function of a graded poset: `0` on minimal elements, `+1` along covers. -/
structure IsNativeRankFn {α : Type v} [PartialOrder α] (ρ : α → ℕ) : Prop where
  min_zero : ∀ a : α, IsMin a → ρ a = 0
  cover_succ : ∀ a b : α, a ⋖ b → ρ b = ρ a + 1

/-- In a finite poset every cover-additive map is strictly monotone. -/
theorem strictMono_of_cover {α : Type v} [PartialOrder α] [Finite α] {ρ : α → ℕ}
    (hc : ∀ a b : α, a ⋖ b → ρ b = ρ a + 1) : StrictMono ρ := by
  have key : ∀ b : α, ∀ a : α, a < b → ρ a < ρ b := by
    intro b
    induction b using WellFoundedLT.induction with
    | ind b ih =>
      intro a hab
      obtain ⟨c, ⟨hac, hcb⟩, hmax⟩ :=
        (wellFounded_gt (α := α)).has_min {x | a ≤ x ∧ x < b}
          ⟨a, show a ≤ a ∧ a < b from ⟨le_rfl, hab⟩⟩
      have hcov : c ⋖ b := by
        refine ⟨hcb, ?_⟩
        intro d hcd hdb
        exact hmax d ⟨hac.trans hcd.le, hdb⟩ hcd
      rw [hc c b hcov]
      rcases eq_or_lt_of_le hac with rfl | hlt
      · omega
      · have := ih c hcb a hlt
        omega
  exact fun a b h => key b a h

/-- Uniqueness of the rank function on a finite poset. -/
theorem rankFn_unique {α : Type v} [PartialOrder α] [Finite α] {ρ ρ' : α → ℕ}
    (h : IsNativeRankFn ρ) (h' : IsNativeRankFn ρ') : ρ = ρ' := by
  funext a
  induction a using WellFoundedLT.induction with
  | ind a ih =>
    by_cases hmin : IsMin a
    · rw [h.min_zero a hmin, h'.min_zero a hmin]
    · obtain ⟨b, hb⟩ := not_isMin_iff.1 hmin
      obtain ⟨c, ⟨hbc, hca⟩, hmax⟩ :=
        (wellFounded_gt (α := α)).has_min {x | b ≤ x ∧ x < a}
          ⟨b, show b ≤ b ∧ b < a from ⟨le_rfl, hb⟩⟩
      have hcov : c ⋖ a := by
        refine ⟨hca, ?_⟩
        intro d hcd hda
        exact hmax d ⟨hbc.trans hcd.le, hda⟩ hcd
      rw [h.cover_succ c a hcov, h'.cover_succ c a hcov, ih c hca]

/-- A nonempty finite chain has a greatest element. -/
theorem chain_exists_greatest {α : Type v} [PartialOrder α] [Finite α] {s : Set α}
    (hs : IsChain (· ≤ ·) s) (hne : s.Nonempty) : ∃ t ∈ s, ∀ y ∈ s, y ≤ t := by
  obtain ⟨t, ht, hmax⟩ := (wellFounded_gt (α := α)).has_min s hne
  refine ⟨t, ht, fun y hy => ?_⟩
  by_contra h
  exact hmax y hy ((hs.not_le hy ht).1 h)

/-- The greatest element of a maximal chain is a maximal element of the poset. -/
theorem isMax_of_greatest {α : Type v} [PartialOrder α] {s : Set α}
    (hs : IsMaxChain (· ≤ ·) s) {t : α} (htop : ∀ y ∈ s, y ≤ t) : IsMax t := by
  intro z hz
  have hch : IsChain (· ≤ ·) (insert z s) :=
    hs.1.insert fun b hb _ => Or.inr ((htop b hb).trans hz)
  have e1 := hs.2 hch (Set.subset_insert z s)
  have hzs : z ∈ s := by
    rw [e1]
    exact Set.mem_insert z s
  exact htop z hzs

/-- Counting a maximal chain with a rank function: if `t` is the greatest element of the
maximal chain `s`, then `#s = ρ t + 1` (the chain meets every rank `0, …, ρ t` exactly once). -/
theorem ncard_maxChain {α : Type v} [PartialOrder α] [Finite α] {ρ : α → ℕ}
    (hr : IsNativeRankFn ρ) {s : Set α} (hs : IsMaxChain (· ≤ ·) s) {t : α} (ht : t ∈ s)
    (htop : ∀ y ∈ s, y ≤ t) : s.ncard = ρ t + 1 := by
  have hmono : StrictMono ρ := strictMono_of_cover hr.cover_succ
  have hinj : Set.InjOn ρ s := by
    intro x hx y hy hxy
    by_contra hne
    rcases hs.1 hx hy hne with h | h
    · have := hmono (lt_of_le_of_ne h hne)
      omega
    · have := hmono (lt_of_le_of_ne h (Ne.symm hne))
      omega
  obtain ⟨m, hm, hmmin⟩ := (wellFounded_lt (α := α)).has_min s ⟨t, ht⟩
  have hmle : ∀ y ∈ s, m ≤ y := fun y hy => by
    by_contra h
    exact hmmin y hy ((hs.1.not_le hm hy).1 h)
  have hmisMin : IsMin m := by
    intro z hz
    by_contra hmz
    have hzm : z < m := lt_of_le_of_ne hz (fun h => hmz (le_of_eq h.symm))
    have hch : IsChain (· ≤ ·) (insert z s) :=
      hs.1.insert fun b hb _ => Or.inl (hz.trans (hmle b hb))
    have e1 := hs.2 hch (Set.subset_insert z s)
    have hzs : z ∈ s := by
      rw [e1]
      exact Set.mem_insert z s
    exact hmmin z hzs hzm
  have hsurj : ∀ k, k ≤ ρ t → ∃ x ∈ s, ρ x = k := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨m, hm, hr.min_zero m hmisMin⟩
    | succ k ih =>
      intro hk
      obtain ⟨x, hx, hxk⟩ := ih (by omega)
      have hxt : x < t := lt_of_le_of_ne (htop x hx) (by rintro rfl; omega)
      obtain ⟨d, ⟨hds, hxd⟩, hdmin⟩ :=
        (wellFounded_lt (α := α)).has_min {y | y ∈ s ∧ x < y}
          ⟨t, show t ∈ s ∧ x < t from ⟨ht, hxt⟩⟩
      have hdle : ∀ b ∈ s, x < b → d ≤ b := fun b hb hxb => by
        by_contra h
        exact hdmin b ⟨hb, hxb⟩ ((hs.1.not_le hds hb).1 h)
      have hcov : x ⋖ d := by
        refine ⟨hxd, ?_⟩
        intro e hxe hed
        have hch : IsChain (· ≤ ·) (insert e s) := by
          refine hs.1.insert fun b hb _ => ?_
          by_cases hbx : b ≤ x
          · exact Or.inr (hbx.trans hxe.le)
          · exact Or.inl (hed.le.trans (hdle b hb ((hs.1.not_le hb hx).1 hbx)))
        have e1 := hs.2 hch (Set.subset_insert e s)
        have hes : e ∈ s := by
          rw [e1]
          exact Set.mem_insert e s
        exact hdmin e ⟨hes, hxe⟩ hed
      exact ⟨d, hds, by rw [hr.cover_succ x d hcov, hxk]⟩
  have himg : ρ '' s = ((Finset.range (ρ t + 1) : Finset ℕ) : Set ℕ) := by
    ext k
    simp only [Set.mem_image, Finset.mem_coe, Finset.mem_range]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have := hmono.monotone (htop x hx)
      omega
    · intro hk
      exact hsurj k (by omega)
  rw [← hinj.ncard_image, himg, Set.ncard_coe_finset, Finset.card_range]

/-- **Bridge.** Native §2.3 gradedness of rank `n` with its rank function gives the canonical
`IsGradedRank ρ n` (for any bounded-order structure on the same order). -/
theorem isGradedRank_of_native {α : Type v} [PartialOrder α] [Finite α] [BoundedOrder α]
    {ρ : α → ℕ} {n : ℕ} (hg : NativeGradedRank α n) (hr : IsNativeRankFn ρ) :
    IsGradedRank ρ n where
  strictMono := strictMono_of_cover hr.cover_succ
  covBy := hr.cover_succ
  bot := hr.min_zero ⊥ isMin_bot
  top := by
    obtain ⟨M, hM, -⟩ := (IsChain.empty : IsChain (α := α) (· ≤ ·) ∅).exists_maxChain
    have h1 := hg M hM
    have h2 := ncard_maxChain hr hM hM.top_mem (fun y _ => le_top)
    omega

/-- **Converse bridge.** The canonical `IsGradedRank ρ n` gives native gradedness and the
native rank function. -/
theorem native_of_isGradedRank {α : Type v} [PartialOrder α] [Finite α] [BoundedOrder α]
    {ρ : α → ℕ} {n : ℕ} (hg : IsGradedRank ρ n) :
    NativeGradedRank α n ∧ IsNativeRankFn ρ := by
  have hr : IsNativeRankFn ρ :=
    ⟨fun a ha => by rw [isMin_iff_eq_bot.1 ha]; exact hg.bot, hg.covBy⟩
  refine ⟨fun s hs => ?_, hr⟩
  rw [ncard_maxChain hr hs hs.top_mem (fun y _ => le_top), hg.top]

theorem native_iff_isGradedRank {α : Type v} [PartialOrder α] [Finite α] [BoundedOrder α]
    {ρ : α → ℕ} {n : ℕ} : (NativeGradedRank α n ∧ IsNativeRankFn ρ) ↔ IsGradedRank ρ n :=
  ⟨fun h => isGradedRank_of_native h.1 h.2, native_of_isGradedRank⟩

/-! ### The corolla side: `P_τ` is natively graded of rank 3 with rank function `rk` -/

theorem rk_isNativeRankFn : IsNativeRankFn rk where
  min_zero a ha := by
    have h1 : a = botP := le_antisymm (ha (botP_le a)) (botP_le a)
    rw [h1]
    exact rk_botP
  cover_succ _ _ h := rk_covBy h

/-- `rk` is the only rank function of `P_τ`, so `Mtri P rk` is the native `M_{P_τ}`. -/
theorem rk_unique (ρ : P → ℕ) (h : IsNativeRankFn ρ) : ρ = rk :=
  rankFn_unique h rk_isNativeRankFn

/-- Every maximal chain of `P_τ` has exactly four elements (native §2.3, rank 3). -/
theorem P_nativeGraded : NativeGradedRank P 3 := by
  intro s hs
  have hb : botP ∈ s := by
    have hch : IsChain (· ≤ ·) (insert botP s) := hs.1.insert fun b _ _ => Or.inl (botP_le b)
    have e1 := hs.2 hch (Set.subset_insert botP s)
    rw [e1]
    exact Set.mem_insert botP s
  obtain ⟨t, ht, htop⟩ := chain_exists_greatest hs.1 ⟨botP, hb⟩
  rw [ncard_maxChain rk_isNativeRankFn hs ht htop,
    rk_of_maximal t (fun b hb' => le_antisymm (isMax_of_greatest hs htop hb') hb')]

/-! ### Native literal endpoints -/

/-- **Native literal endpoint.** Conjecture 8.1 fails at the corolla `t₃` (`n = 3`) with the
source's own §2.3 gradedness (all maximal chains have four elements) and rank function; no
bounded order, `IsGradedRank` or `GradeOrder` is assumed.  Derived from the canonical
endpoint `C374966.conj81_false_at_corolla` through the bridge. -/
theorem conj81_false_at_corolla_native :
    ¬ ∃ (L : Type u) (_ : Lattice L) (_ : Fintype L) (_ : DecidableEq L) (_ : DecidableLE L)
      (_ : LocallyFiniteOrder L) (ρ : L → ℕ),
      NativeGradedRank L 3 ∧ IsNativeRankFn ρ ∧
        transmute (Mtri P rk) = algebraMap Pxy FracXY (Mtri L ρ) := by
  rintro ⟨L, _, _, _, _, _, ρ, hg, hr, h⟩
  obtain ⟨M, hM, -⟩ := (IsChain.empty : IsChain (α := L) (· ≤ ·) ∅).exists_maxChain
  have hM4 : M.ncard = 3 + 1 := hg M hM
  obtain ⟨x, -⟩ := Set.nonempty_of_ncard_ne_zero (s := M) (by omega)
  have : Nonempty L := ⟨x⟩
  let _ : BoundedOrder L := Fintype.toBoundedOrder L
  exact conj81_false_at_corolla
    ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, ρ, isGradedRank_of_native hg hr, h⟩

/-- The native endpoint with the (unused) zeta conjunct on the same lattice. -/
theorem conj81_false_at_corolla_native_with_zeta
    (Zeta : ∀ (L : Type u) [Lattice L] [Fintype L], Prop) :
    ¬ ∃ (L : Type u) (_ : Lattice L) (_ : Fintype L) (_ : DecidableEq L) (_ : DecidableLE L)
      (_ : LocallyFiniteOrder L) (ρ : L → ℕ),
      NativeGradedRank L 3 ∧ IsNativeRankFn ρ ∧ Zeta L ∧
        transmute (Mtri P rk) = algebraMap Pxy FracXY (Mtri L ρ) := by
  rintro ⟨L, _, _, _, _, _, ρ, hg, hr, -, h⟩
  exact conj81_false_at_corolla_native
    ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ρ, hg, hr, h⟩

/-! ### Non-vacuity on standard finite lattices (hypotheses derived, not assumed) -/

/-- The four-element chain `Fin 4` with rank `Fin.val`. -/
theorem fin4_rankFn : IsNativeRankFn (fun a : Fin 4 => (a : ℕ)) where
  min_zero a ha := by
    have h0 : a = ⊥ := isMin_iff_eq_bot.1 ha
    subst h0
    rfl
  cover_succ a b h := by
    show (b : ℕ) = (a : ℕ) + 1
    have h1 : (a : ℕ) < b := h.1
    have hb4 : (b : ℕ) < 4 := b.2
    by_contra hne
    have h2 : (a : ℕ) + 1 < b := by omega
    have hc4 : (a : ℕ) + 1 < 4 := by omega
    exact h.2 (show a < (⟨(a : ℕ) + 1, hc4⟩ : Fin 4) from Nat.lt_succ_self _)
      (show (⟨(a : ℕ) + 1, hc4⟩ : Fin 4) < b from h2)

theorem fin4_nativeGraded : NativeGradedRank (Fin 4) 3 := fun s hs => by
  rw [ncard_maxChain fin4_rankFn hs hs.top_mem (fun y _ => le_top)]
  rfl

theorem fin4_isGradedRank : IsGradedRank (fun a : Fin 4 => (a : ℕ)) 3 :=
  isGradedRank_of_native fin4_nativeGraded fin4_rankFn

/-- The Boolean lattice `B₃ = Finset (Fin 3)` with rank `card`. -/
theorem boolean3_rankFn : IsNativeRankFn (fun s : Finset (Fin 3) => s.card) where
  min_zero s hs := by
    have h0 : s = ⊥ := isMin_iff_eq_bot.1 hs
    subst h0
    rfl
  cover_succ s t h := by
    obtain ⟨a, ha, rfl⟩ := Finset.covBy_iff_exists_insert.1 h
    exact Finset.card_insert_of_notMem ha

theorem boolean3_nativeGraded : NativeGradedRank (Finset (Fin 3)) 3 := fun s hs => by
  rw [ncard_maxChain boolean3_rankFn hs hs.top_mem (fun y _ => le_top)]
  decide

theorem boolean3_isGradedRank : IsGradedRank (fun s : Finset (Fin 3) => s.card) 3 :=
  isGradedRank_of_native boolean3_nativeGraded boolean3_rankFn

#print axioms conj81_false_at_corolla_native
#print axioms conj81_false_at_corolla_native_with_zeta
#print axioms isGradedRank_of_native
#print axioms native_of_isGradedRank
#print axioms native_iff_isGradedRank
#print axioms ncard_maxChain
#print axioms strictMono_of_cover
#print axioms rankFn_unique
#print axioms chain_exists_greatest
#print axioms isMax_of_greatest
#print axioms rk_isNativeRankFn
#print axioms rk_unique
#print axioms P_nativeGraded
#print axioms fin4_rankFn
#print axioms fin4_nativeGraded
#print axioms fin4_isGradedRank
#print axioms boolean3_rankFn
#print axioms boolean3_nativeGraded
#print axioms boolean3_isGradedRank

end A374966
```

## Appendix C. Declaration and source crosswalk

Every declaration named below was machine-checked to be declared in the listed module(s) at assembly time.

| Paper item | Source (arXiv:2605.26916v1) | Lean declarations (namespace C374966 or A374966) | Module |
|---|---|---|---|
| Corolla t3 preorder (ℓ ≤ r) | §1 (arbor root = maximum), §2.2 | `cor`, `cor_refl`, `cor_trans`, `cor_antisymm`, `cor_shape` | C374966Corolla |
| Order ideals | §2.2 | `IsIdeal`, `ideals_iff` | C374966Corolla |
| Q_τ ideal inequalities (2), general τ | §1 display (2) | `QPre`, `Qcor_eq_QPre` | C374966Main |
| Q_τ ∩ ℤ³ for t3, twelve points | §1, §3.3 | `Qcor`, `Qcor_iff`, `pts`, `mem_pts`, `card_P` | C374966Corolla |
| Product order on P_τ | §1, §3.3 | `P`, `le_iff` | C374966Corolla |
| Box intervals, down-closure | §3.3 | `down_closed`, `intervalIso` | C374966Corolla |
| Rank = coordinate sum, graded | §3.3 | `rk`, `rk_strictMono`, `rk_covBy`, `rk_of_maximal`, `botP_le` | C374966Corolla |
| P_τ natively graded of rank 3; unique rank function | §2.3, §3.3 | `rk_isNativeRankFn`, `rk_unique`, `P_nativeGraded` | A374966NativeBridge |
| Möbius function (Mathlib μ), box formula | §8 (μ_P) | `mu_eq_of_sum`, `fP_sum`, `mu_P` | C374966Defs, C374966Corolla |
| M-triangle M_P and coefficient table (§2.2 of paper) | §8 | `Mtri`, `Tab`, `coeff_Mtri`, `Tz`, `Tz_table`, `MP_eq_tab`, `Mtri_P_lit` | C374966Defs, C374966Corolla |
| Transmutation in ℚ(x,y) | §8 | `transmuteHom`, `transmute`, `tr_X0`, `tr_X1`, `one_sub_xy_ne` | C374966Defs |
| M̄_P computed (§2.3 of paper) | §8 | `transmute_MP_lit`, `transmute_MP`, `Mbar_coeffs`, `tab_M_lit` | C374966Transmute |
| Injection ℚ[x,y] → ℚ(x,y) | §8 (27) | `iota_injective` | C374966Defs |
| Lemma 2 (reading M_L) | §8 | `Tab_diag`, `mu_cover`, `Tab_cover` | C374966Lattice |
| Upper count (distinct-atom join) | — | `join_eq`, `count_bound` | C374966Lattice |
| C(d,2) ≥ 2d−3 and contradiction | — | `two_mul_le_choose_two_add_three`, `no_lattice_core` | C374966Lattice |
| Canonical rank hypothesis | — | `IsGradedRank`, `isGradedRank_of_gradeOrder` | C374966Lattice |
| Lemma 3 | §2.3 | `strictMono_of_cover` | A374966NativeBridge |
| Lemma 4 (native graded ⇔ IsGradedRank) | §2.3 | `NativeGradedRank`, `IsNativeRankFn`, `ncard_maxChain`, `chain_exists_greatest`, `isMax_of_greatest`, `isGradedRank_of_native`, `native_of_isGradedRank`, `native_iff_isGradedRank`, `rankFn_unique` | A374966NativeBridge |
| Theorem 1, canonical endpoints | Conjecture 8.1 | `corolla_no_M_match`, `conj81_false_at_corolla`, `conj81_false_at_corolla_with_zeta`, `conj81_false_at_corolla_gradeOrder` | C374966Main |
| Theorem 1, native endpoints | Conjecture 8.1, §2.3 | `conj81_false_at_corolla_native`, `conj81_false_at_corolla_native_with_zeta` | A374966NativeBridge |
| Non-vacuity on standard lattices | §2.3 | `fin4_rankFn`, `fin4_nativeGraded`, `fin4_isGradedRank`, `boolean3_rankFn`, `boolean3_nativeGraded`, `boolean3_isGradedRank` | A374966NativeBridge |
