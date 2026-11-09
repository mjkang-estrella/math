/-
UNCOMPILED DRAFT (Claude lane expanded-corpus-r160, 2026-11-04). Not run through Lean in this lane
(lane restriction). Root / a Sol worker must compile with the pinned toolchain (Lean 4.34.1, mathlib
d13f23b723b8a846827a245b89c10fc7d3f11612), fix any API drift, and audit `#print axioms`.

MathDB 353800 = Naslund, "Paley graphs and Sarkozy's theorem in function fields",
arXiv:2203.01293v3 (Q. J. Math. 2022), Conjecture 13 (Section 3, "Limits of the Method"):
  Let k >= 2, gcd(k, q-1) > 1, n = 0 (mod 2k). Any A ⊆ P_{q,n} (polynomials over F_q of degree < n)
  containing no k-th power difference (distinct u, v in A with u - v = b^k, b in F_q[T]) satisfies
  |A| <= q^{n(1 - 1/k^2)}.
We prove the literal negation with q = 5, k = 2, n = 4 and an explicit set A of 160 polynomials
(> 5^3 = 125), the q = 5 case of the uniform construction in CANDIDATE-353800.md (Theorem U). A = { c0 + c1 T + c2 T^2 + c3 T^3 : (c0,c1,c2) in `slice`, c3 in F_5 }.
-/
import Mathlib

open Polynomial

namespace MathDB353800

/-- Literal statement of the conjecture (all finite fields, all admissible k, n). -/
def Conjecture : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (k n : ℕ),
    2 ≤ k → 1 < Nat.gcd k (Fintype.card F - 1) → n % (2 * k) = 0 →
    ∀ A : Finset F[X],
      (∀ f ∈ A, f.degree < (n : WithBot ℕ)) →
      (∀ u ∈ A, ∀ v ∈ A, u ≠ v → ∀ b : F[X], u - v ≠ b ^ k) →
      (A.card : ℝ) ≤ (Fintype.card F : ℝ) ^ ((n : ℝ) * (1 - 1 / (k : ℝ) ^ 2))

instance fact5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

abbrev F5 := ZMod 5

/-- 32 coefficient triples (c0, c1, c2) over F_5: the 20 solutions of 4*c0*c2 - c1^2 = 2 (a nonsquare)
together with the 12 points t*(a^2, 2ab, b^2), t in {1, 4}, [a:b] in PG(1,5). Independently re-verified. -/
def slice : List (F5 × F5 × F5) :=
  [(0, 0, 1),
   (0, 0, 4),
   (1, 0, 0),
   (1, 0, 3),
   (1, 1, 2),
   (1, 1, 4),
   (1, 2, 1),
   (1, 2, 4),
   (1, 3, 1),
   (1, 3, 4),
   (1, 4, 2),
   (1, 4, 4),
   (2, 0, 4),
   (2, 1, 1),
   (2, 2, 2),
   (2, 3, 2),
   (2, 4, 1),
   (3, 0, 1),
   (3, 1, 4),
   (3, 2, 3),
   (3, 3, 3),
   (3, 4, 4),
   (4, 0, 0),
   (4, 0, 2),
   (4, 1, 1),
   (4, 1, 3),
   (4, 2, 1),
   (4, 2, 4),
   (4, 3, 1),
   (4, 3, 4),
   (4, 4, 1),
   (4, 4, 3)]

/-- (c0,c1,c2), c3  ↦  c0 + c1 T + c2 T^2 + c3 T^3. -/
noncomputable def toPoly (t : (F5 × F5 × F5) × F5) : F5[X] :=
  C t.1.1 + C t.1.2.1 * X + C t.1.2.2 * X ^ 2 + C t.2 * X ^ 3

noncomputable def A : Finset F5[X] :=
  (slice.toFinset ×ˢ (Finset.univ : Finset F5)).image toPoly

lemma coeff_toPoly (t : (F5 × F5 × F5) × F5) :
    (toPoly t).coeff 0 = t.1.1 ∧ (toPoly t).coeff 1 = t.1.2.1 ∧
    (toPoly t).coeff 2 = t.1.2.2 ∧ (toPoly t).coeff 3 = t.2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [toPoly, coeff_X_pow, coeff_X, coeff_C]

lemma toPoly_injective : Function.Injective toPoly := by
  intro s t h
  obtain ⟨s0, s1, s2, s3⟩ := coeff_toPoly s
  obtain ⟨t0, t1, t2, t3⟩ := coeff_toPoly t
  have e0 : s.1.1 = t.1.1 := by rw [← s0, ← t0, h]
  have e1 : s.1.2.1 = t.1.2.1 := by rw [← s1, ← t1, h]
  have e2 : s.1.2.2 = t.1.2.2 := by rw [← s2, ← t2, h]
  have e3 : s.2 = t.2 := by rw [← s3, ← t3, h]
  exact Prod.ext (Prod.ext e0 (Prod.ext e1 e2)) e3

lemma natDegree_toPoly_le (t : (F5 × F5 × F5) × F5) : (toPoly t).natDegree ≤ 3 := by
  unfold toPoly
  compute_degree

lemma degree_toPoly_lt (t : (F5 × F5 × F5) × F5) : (toPoly t).degree < ((4 : ℕ) : WithBot ℕ) := by
  have h := natDegree_toPoly_le t
  exact lt_of_le_of_lt (degree_le_of_natDegree_le h) (WithBot.coe_lt_coe.mpr (by norm_num))

lemma slice_nodup : slice.Nodup := by decide

lemma card_A : A.card = 160 := by
  rw [A, Finset.card_image_of_injective _ toPoly_injective, Finset.card_product,
    List.toFinset_card_of_nodup slice_nodup, Finset.card_univ, ZMod.card]
  rfl

/-- The finite core: no difference of two slice points is (b0^2, 2 b0 b1, b1^2) unless b0 = b1 = 0.
Kernel-checkable; if plain `decide` is too slow use `decide +kernel` (no native_decide). -/
lemma slice_check : ∀ x ∈ slice, ∀ y ∈ slice, ∀ b0 b1 : F5,
    x.1 - y.1 = b0 ^ 2 → x.2.1 - y.2.1 = 2 * b0 * b1 → x.2.2 - y.2.2 = b1 ^ 2 →
      b0 = 0 ∧ b1 = 0 := by
  decide

lemma sq_lin (b0 b1 : F5) :
    (C b1 * X + C b0) ^ 2 = C (b0 ^ 2) + C (2 * b0 * b1) * X + C (b1 ^ 2) * X ^ 2 := by
  simp only [map_pow, map_mul, map_ofNat]
  ring

lemma coeff_sq_lin (b0 b1 : F5) :
    ((C b1 * X + C b0) ^ 2).coeff 0 = b0 ^ 2 ∧ ((C b1 * X + C b0) ^ 2).coeff 1 = 2 * b0 * b1 ∧
    ((C b1 * X + C b0) ^ 2).coeff 2 = b1 ^ 2 := by
  rw [sq_lin]
  refine ⟨?_, ?_, ?_⟩ <;> simp [coeff_X_pow, coeff_X, coeff_C]

theorem no_square_difference : ∀ u ∈ A, ∀ v ∈ A, u ≠ v → ∀ b : F5[X], u - v ≠ b ^ 2 := by
  intro u hu v hv huv b hb
  simp only [A, Finset.mem_image, Finset.mem_product, List.mem_toFinset] at hu hv
  obtain ⟨s, ⟨hs, -⟩, rfl⟩ := hu
  obtain ⟨t, ⟨ht, -⟩, rfl⟩ := hv
  have hdeg : (b ^ 2).natDegree ≤ 3 := by
    rw [← hb]
    exact (natDegree_sub_le _ _).trans (max_le (natDegree_toPoly_le s) (natDegree_toPoly_le t))
  rw [Polynomial.natDegree_pow] at hdeg
  have hb1 : b.natDegree ≤ 1 := by omega
  have hbX := eq_X_add_C_of_natDegree_le_one hb1
  obtain ⟨s0, s1, s2, -⟩ := coeff_toPoly s
  obtain ⟨t0, t1, t2, -⟩ := coeff_toPoly t
  obtain ⟨q0, q1, q2⟩ := coeff_sq_lin (b.coeff 0) (b.coeff 1)
  have e0 : (toPoly s - toPoly t).coeff 0 = (b ^ 2).coeff 0 := by rw [hb]
  have e1 : (toPoly s - toPoly t).coeff 1 = (b ^ 2).coeff 1 := by rw [hb]
  have e2 : (toPoly s - toPoly t).coeff 2 = (b ^ 2).coeff 2 := by rw [hb]
  rw [coeff_sub, s0, t0] at e0
  rw [coeff_sub, s1, t1] at e1
  rw [coeff_sub, s2, t2] at e2
  rw [hbX] at e0 e1 e2
  rw [q0] at e0; rw [q1] at e1; rw [q2] at e2
  obtain ⟨z0, z1⟩ := slice_check s.1 hs t.1 ht (b.coeff 0) (b.coeff 1) e0 e1 e2
  have hb0 : b = 0 := by rw [hbX, z0, z1]; simp
  apply huv
  have : toPoly s - toPoly t = 0 := by rw [hb, hb0]; simp
  exact sub_eq_zero.mp this

theorem not_conjecture : ¬ Conjecture := by
  intro h
  have hgcd : 1 < Nat.gcd 2 (Fintype.card F5 - 1) := by rw [ZMod.card]; decide
  have H := h F5 2 4 le_rfl hgcd (by decide) A
    (fun f hf => by
      simp only [A, Finset.mem_image] at hf
      obtain ⟨t, -, rfl⟩ := hf
      exact degree_toPoly_lt t)
    no_square_difference
  rw [card_A, ZMod.card] at H
  have e : ((4 : ℕ) : ℝ) * (1 - 1 / ((2 : ℕ) : ℝ) ^ 2) = ((3 : ℕ) : ℝ) := by norm_num
  rw [e, Real.rpow_natCast] at H
  norm_num at H

end MathDB353800
