import Mathlib

namespace GraphNormalization
open scoped BigOperators
open Matrix

/-- Weighted Young inequality, summed using symmetry of the kernel. -/
theorem symmetric_energy_le {ι : Type*} [Fintype ι]
    (B : ι → ι → ℝ) (hB : ∀ i j, 0 ≤ B i j)
    (hs : ∀ i j, B i j = B j i) (x a : ι → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (∑ i, ∑ j, B i j * (x i * a i) * (x j * a j)) ≤
      ∑ i, x i * (a i)^2 * (∑ j, B i j * x j) := by
  have hp : (∑ i, ∑ j, 2 * (B i j * (x i * a i) * (x j * a j))) ≤
      ∑ i, ∑ j, B i j * x i * x j * ((a i)^2 + (a j)^2) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    have hb := mul_nonneg (mul_nonneg (hB i j) (hx i)) (hx j)
    have ht := mul_nonneg hb (sq_nonneg (a i - a j))
    nlinarith
  have he : (∑ i, ∑ j, B i j * x i * x j * ((a i)^2 + (a j)^2)) =
      2 * (∑ i, x i * (a i)^2 * (∑ j, B i j * x j)) := by
    simp_rw [mul_add, Finset.sum_add_distrib]
    have ha : (∑ i, ∑ j, B i j * x i * x j * (a i)^2) =
        ∑ i, x i * (a i)^2 * (∑ j, B i j * x j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hb : (∑ i, ∑ j, B i j * x i * x j * (a j)^2) =
        ∑ i, x i * (a i)^2 * (∑ j, B i j * x j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [hs i j]
      ring
    rw [ha, hb]
    ring
  rw [he] at hp
  simp_rw [← Finset.mul_sum] at hp
  linarith

/-- Normalization inequality for every nonnegative symmetric matrix with positive row action. -/
theorem normalized_energy_le {ι : Type*} [Fintype ι]
    (B : ι → ι → ℝ) (hB : ∀ i j, 0 ≤ B i j)
    (hs : ∀ i j, B i j = B j i) (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hrow : ∀ i, 0 < ∑ j, B i j * x j) :
    let y := fun i => x i / (∑ j, B i j * x j)
    (∑ i, ∑ j, B i j * y i * y j) ≤ ∑ i, y i := by
  dsimp only
  have he := symmetric_energy_le B hB hs x (fun i => (∑ j, B i j * x j)⁻¹) hx
  simp only [← div_eq_mul_inv] at he
  convert he using 1
  apply Finset.sum_congr rfl
  intro i _
  have hn := ne_of_gt (hrow i)
  field_simp

noncomputable def closedKernel {ι : Type*} (G : SimpleGraph ι) : ι → ι → ℝ :=
  by
    classical
    exact fun i j => if i = j ∨ G.Adj i j then 1 else 0

theorem closedKernel_nonneg {ι : Type*} (G : SimpleGraph ι) (i j : ι) :
    0 ≤ closedKernel G i j := by
  classical
  unfold closedKernel
  split_ifs <;> norm_num

theorem closedKernel_symm {ι : Type*} (G : SimpleGraph ι) (i j : ι) :
    closedKernel G i j = closedKernel G j i := by
  classical
  simp only [closedKernel]
  congr 1
  exact propext (or_congr eq_comm (G.adj_comm i j))

/-- This is the source's adjacency matrix plus the identity matrix. -/
theorem closedKernel_eq_adj_add_one {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) [DecidableRel G.Adj] :
    closedKernel G = G.adjMatrix ℝ + (1 : Matrix ι ι ℝ) := by
  ext i j
  by_cases h : i = j
  · subst j; simp [closedKernel, SimpleGraph.adjMatrix]
  · simp [closedKernel, SimpleGraph.adjMatrix, h]

/-- Full Conjecture 8.1; in fact no connectivity assumption is needed. -/
theorem graph_normalization_inequality {ι : Type*} [Fintype ι]
    (G : SimpleGraph ι) (x : ι → ℝ) (hx : ∀ i, 0 < x i) :
    let B := closedKernel G
    let y := fun i => x i / (∑ j, B i j * x j)
    (∑ i, ∑ j, B i j * y i * y j) ≤ ∑ i, |y i| := by
  classical
  have hrow : ∀ i, 0 < ∑ j, closedKernel G i j * x j := by
    intro i
    have he : x i ≤ ∑ j, closedKernel G i j * x j := by
      have h := Finset.single_le_sum (f := fun j => closedKernel G i j * x j)
        (fun j _ => mul_nonneg (closedKernel_nonneg G i j) (le_of_lt (hx j)))
        (Finset.mem_univ i)
      simpa [closedKernel] using h
    exact lt_of_lt_of_le (hx i) he
  dsimp only
  have he := normalized_energy_le (closedKernel G) (closedKernel_nonneg G)
    (closedKernel_symm G) x (fun i => le_of_lt (hx i)) hrow
  convert he using 1
  apply Finset.sum_congr rfl
  intro i _
  exact abs_of_pos (div_pos (hx i) (hrow i))

/-- The original assertion written with mathlib adjacency matrices and matrix products. -/
theorem mathdb349070 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [DecidableRel G.Adj] (x : ι → ℝ) (hx : ∀ i, 0 < x i) :
    let B := G.adjMatrix ℝ + (1 : Matrix ι ι ℝ)
    let y := fun i => x i / (B *ᵥ x) i
    dotProduct y (B *ᵥ y) ≤ ∑ i, |y i| := by
  dsimp only
  rw [← closedKernel_eq_adj_add_one G]
  simpa only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc,
    mul_left_comm, mul_comm] using graph_normalization_inequality G x hx

end GraphNormalization
