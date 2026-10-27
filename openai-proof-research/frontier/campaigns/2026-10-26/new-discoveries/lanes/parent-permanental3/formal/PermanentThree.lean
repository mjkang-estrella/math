import Mathlib

namespace PermanentalThree

open Matrix

abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℝ

/-- Strict positivity of every nonempty minor of a real 3 by 3 matrix. -/
def StrictTP3 (A : Mat3) : Prop :=
  (∀ i j, 0 < A i j) ∧
  (∀ i j k l, i < j → k < l → 0 < A i k * A j l - A i l * A j k) ∧
  0 < A.det

def per3 (A : Mat3) : ℝ :=
  A 0 0 * A 1 1 * A 2 2 + A 0 0 * A 1 2 * A 2 1 +
  A 0 1 * A 1 0 * A 2 2 + A 0 1 * A 1 2 * A 2 0 +
  A 0 2 * A 1 0 * A 2 1 + A 0 2 * A 1 1 * A 2 0

def per2 (A : Mat3) (i j : Fin 3) : ℝ :=
  A i i * A j j + A i j * A j i

def numerator (A : Mat3) : ℝ := per2 A 0 1 * per2 A 1 2

def denominator (A : Mat3) : ℝ := per3 A * A 1 1

noncomputable def ratio (A : Mat3) : ℝ := numerator A / denominator A

theorem per3_eq_permanent (A : Mat3) : per3 A = A.permanent := by
  have hu : (Finset.univ : Finset (Equiv.Perm (Fin 3))) =
      {1, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2,
        Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.swap 1 2 * Equiv.swap 0 1} := by
    decide +kernel
  rw [Matrix.permanent, hu]
  repeat rw [Finset.sum_insert (by decide)]
  simp [Fin.prod_univ_succ, Equiv.Perm.mul_apply, Equiv.swap_apply_def, per3]
  ring

theorem per3_pos {A : Mat3} (h : ∀ i j, 0 < A i j) : 0 < per3 A := by
  unfold per3
  repeat first | apply add_pos | apply mul_pos | exact h _ _

theorem denominator_pos {A : Mat3} (h : StrictTP3 A) : 0 < denominator A :=
  mul_pos (per3_pos h.1) (h.1 1 1)

theorem per2_eq_permanent (A : Mat3) (i j : Fin 3) :
    per2 A i j = (A.submatrix ![i,j] ![i,j]).permanent := by
  have hu : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by
    decide +kernel
  rw [Matrix.permanent, hu]
  repeat rw [Finset.sum_insert (by decide)]
  simp [Fin.prod_univ_succ, Matrix.submatrix_apply, per2]
  ring

noncomputable def sourceRatio (A : Mat3) : ℝ :=
  (A.submatrix ![0,1] ![0,1]).permanent *
  (A.submatrix ![1,2] ![1,2]).permanent / (A.permanent * A 1 1)

theorem ratio_eq_sourceRatio (A : Mat3) : ratio A = sourceRatio A := by
  unfold ratio numerator denominator sourceRatio
  rw [per3_eq_permanent, per2_eq_permanent, per2_eq_permanent]

end PermanentalThree
