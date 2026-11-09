import Mathlib

open Finset

namespace BergmanConvolution

/-- The source's triangular coefficients, zero beyond the support. -/
def triangle (m r : ℕ) : ℕ := if r < m then r + 1 else 2 * m - 1 - r

/-- Ordered pairs of indices in the finite geometric sum with prescribed sum. -/
def pairFiber (m r : ℕ) : Finset (ℕ × ℕ) :=
  ((range m) ×ˢ (range m)).filter (fun p => p.1 + p.2 = r)

lemma card_pairFiber (m r : ℕ) (hm : 0 < m) :
    (pairFiber m r).card = triangle m r := by
  have hb : (pairFiber m r).card = (Ico (r + 1 - m) (min m (r + 1))).card := by
    apply Finset.card_bij (fun p _ => p.1)
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hp, he⟩
      rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
      simp only [mem_range] at hp1 hp2
      simp only [mem_Ico, lt_min_iff]
      omega
    · intro p hp q hq he
      have hp' := (Finset.mem_filter.mp hp).2
      have hq' := (Finset.mem_filter.mp hq).2
      apply Prod.ext
      · exact he
      · omega
    · intro p hp
      simp only [mem_Ico, lt_min_iff] at hp
      refine ⟨(p, r - p), ?_, rfl⟩
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        constructor <;> apply Finset.mem_range.mpr <;> omega
      · omega
  rw [hb, Nat.card_Ico]
  unfold triangle
  split_ifs <;> omega

/-- Grouping the square of a geometric sum by its triangular multiplicities. -/
theorem triangle_sum {R : Type*} [AddCommMonoid R] (m : ℕ) (hm : 0 < m)
    (F : ℕ → R) :
    (∑ r ∈ range (2 * m - 1), triangle m r • F r) =
      ∑ p ∈ range m, ∑ q ∈ range m, F (p + q) := by
  calc
    (∑ r ∈ range (2 * m - 1), triangle m r • F r) =
        ∑ r ∈ range (2 * m - 1), ∑ p ∈ pairFiber m r, F (p.1 + p.2) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [← card_pairFiber m r hm, ← Finset.sum_const]
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]
    _ = ∑ p ∈ (range m) ×ˢ (range m), F (p.1 + p.2) := by
      apply Finset.sum_fiberwise_of_maps_to
      intro p hp
      rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
      simp only [mem_range] at hp1 hp2 ⊢
      omega
    _ = ∑ p ∈ range m, ∑ q ∈ range m, F (p + q) := by
      rw [Finset.sum_product]

/-- Two independent triangular convolutions, with no multiplicities omitted. -/
theorem triangle_sum_two {R : Type*} [AddCommMonoid R] (m : ℕ) (hm : 0 < m)
    (F : ℕ → ℕ → R) :
    (∑ r ∈ range (2 * m - 1), ∑ q ∈ range (2 * m - 1),
      (triangle m r * triangle m q) • F r q) =
      ∑ p ∈ range m, ∑ p' ∈ range m, ∑ q ∈ range m, ∑ q' ∈ range m,
        F (p + p') (q + q') := by
  calc
    _ = ∑ r ∈ range (2 * m - 1),
        triangle m r • (∑ q ∈ range (2 * m - 1), triangle m q • F r q) := by
      simp_rw [mul_smul, Finset.sum_nsmul]
    _ = ∑ r ∈ range (2 * m - 1),
        triangle m r • (∑ q ∈ range m, ∑ q' ∈ range m, F r (q + q')) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [triangle_sum m hm]
    _ = _ := triangle_sum m hm _

/-- Complementing the second member of each ordered pair is a finite reindexing. -/
theorem reflect_quadruple_sum {R : Type*} [AddCommMonoid R] (m : ℕ)
    (F : ℕ → ℕ → R) :
    (∑ p ∈ range m, ∑ p' ∈ range m, ∑ q ∈ range m, ∑ q' ∈ range m,
      F (p + (m - 1 - p')) (q + (m - 1 - q'))) =
      ∑ p ∈ range m, ∑ p' ∈ range m, ∑ q ∈ range m, ∑ q' ∈ range m,
        F (p + p') (q + q') := by
  apply Finset.sum_congr rfl
  intro p _
  calc
    _ = ∑ p' ∈ range m, ∑ q ∈ range m, ∑ q' ∈ range m,
        F (p + (m - 1 - p')) (q + q') := by
      apply Finset.sum_congr rfl
      intro p' _
      apply Finset.sum_congr rfl
      intro q _
      exact Finset.sum_range_reflect (fun q' => F (p + (m - 1 - p')) (q + q')) m
    _ = _ := Finset.sum_range_reflect
      (fun p' => ∑ q ∈ range m, ∑ q' ∈ range m, F (p + p') (q + q')) m

/-- The two-factor triangular sum expressed directly through complemented pairs. -/
theorem triangle_sum_reflected {R : Type*} [AddCommMonoid R] (m : ℕ) (hm : 0 < m)
    (F : ℕ → ℕ → R) :
    (∑ r ∈ range (2 * m - 1), ∑ q ∈ range (2 * m - 1),
      (triangle m r * triangle m q) • F r q) =
      ∑ p ∈ range m, ∑ p' ∈ range m, ∑ q ∈ range m, ∑ q' ∈ range m,
        F (p + (m - 1 - p')) (q + (m - 1 - q')) := by
  rw [reflect_quadruple_sum]
  exact triangle_sum_two m hm F

end BergmanConvolution
