import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic

/-! Algebraic support for the kinetic path theorem. These statements do not
formalize the collision history construction, measure estimates or path limit. -/

namespace KineticSupport
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def leftVelocity (v w n : E) : E :=
  v - (inner ℝ (v - w) n) • n

noncomputable def rightVelocity (v w n : E) : E :=
  w - (inner ℝ (v - w) n) • n

theorem collision_momentum (v w n : E) :
    leftVelocity v w n + rightVelocity v w n = v + w := by
  unfold leftVelocity rightVelocity
  abel

theorem collision_energy (v w n : E) (hn : inner ℝ n n = 1) :
    ‖leftVelocity v w n‖ ^ 2 + ‖rightVelocity v w n‖ ^ 2 =
      ‖v‖ ^ 2 + ‖w‖ ^ 2 := by
  simp only [← real_inner_self_eq_norm_sq, leftVelocity, rightVelocity,
    inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, hn]
  rw [real_inner_comm n v, real_inner_comm n w]
  ring

/-- Shifting affine origins by minus shift times velocity translates time. -/
theorem affine_time_shift (a v : E) (t shift : ℝ) :
    (a - shift • v) + t • v = a + (t - shift) • v := by
  rw [sub_smul]
  abel

/-- Relative affine origins have exactly the relative-velocity shear. -/
theorem relative_origin_shift (a b v w : E) (shift : ℝ) :
    (b - shift • w) - (a - shift • v) =
      (b - a) - shift • (w - v) := by
  rw [smul_sub]
  abel

/-- This covers a determined contact once its time translates by shift. -/
theorem contact_time_shift (a b v w : E) (t shift : ℝ) :
    ((a - shift • v) + (t + shift) • v) -
      ((b - shift • w) + (t + shift) • w) =
      (a + t • v) - (b + t • w) := by
  simp only [add_smul]
  abel

/-- The common time shift is a group action on an affine origin. -/
theorem affine_shift_compose (a v : E) (s t : ℝ) :
    (a - s • v) - t • v = a - (s + t) • v := by
  rw [add_smul]
  abel

omit [InnerProductSpace ℝ E] in
/-- Replacing two coordinates with equal total squared norm conserves all-line
energy, regardless of the number or values of the other coordinates. -/
theorem total_energy_of_pair_replacement {I : Type*} [Fintype I]
    [DecidableEq I] (u u' : I → E) (i j : I) (hij : i ≠ j)
    (hout : ∀ k, k ≠ i → k ≠ j → u' k = u k)
    (hpair : ‖u' i‖ ^ 2 + ‖u' j‖ ^ 2 = ‖u i‖ ^ 2 + ‖u j‖ ^ 2) :
    ∑ k, ‖u' k‖ ^ 2 = ∑ k, ‖u k‖ ^ 2 := by
  classical
  have hi : i ∈ (Finset.univ : Finset I) := Finset.mem_univ i
  have hj : j ∈ (Finset.univ : Finset I).erase i :=
    Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩
  have hrest : ∑ k ∈ ((Finset.univ : Finset I).erase i).erase j, ‖u' k‖ ^ 2 =
      ∑ k ∈ ((Finset.univ : Finset I).erase i).erase j, ‖u k‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro k hk
    have hki := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    have hkj := (Finset.mem_erase.mp hk).1
    rw [hout k hki hkj]
  have h1 := Finset.sum_erase_add _ (fun k => ‖u' k‖ ^ 2) hi
  have h2 := Finset.sum_erase_add _ (fun k => ‖u k‖ ^ 2) hi
  have h3 := Finset.sum_erase_add _ (fun k => ‖u' k‖ ^ 2) hj
  have h4 := Finset.sum_erase_add _ (fun k => ‖u k‖ ^ 2) hj
  linarith

/-- Simultaneous update using the two old velocities. -/
noncomputable def pairVelocity {I : Type*} [DecidableEq I]
    (u : I → E) (i j : I) (n : E) : I → E :=
  Function.update (Function.update u i (leftVelocity (u i) (u j) n))
    j (rightVelocity (u i) (u j) n)

/-- One elastic event conserves the energy of the entire finite population. -/
theorem total_collision_energy {I : Type*} [Fintype I] [DecidableEq I]
    (u : I → E) (i j : I) (hij : i ≠ j) (n : E)
    (hn : inner ℝ n n = 1) :
    ∑ k, ‖pairVelocity u i j n k‖ ^ 2 = ∑ k, ‖u k‖ ^ 2 := by
  apply total_energy_of_pair_replacement u (pairVelocity u i j n) i j hij
  · intro k hki hkj
    simp [pairVelocity, Function.update_of_ne hki, Function.update_of_ne hkj]
  · simpa [pairVelocity, Function.update_of_ne hij] using
      collision_energy (u i) (u j) n hn

/-- Exact arithmetic in the centering-transfer and chaining exponents. -/
theorem exponent_budget :
    (-1 : ℚ) + (21 / 20) * (21 / 22) = 1 / 440 ∧
    (-1 : ℚ) + (3 / 2) * (4 / 8) = -1 / 4 ∧
    (1 : ℚ) + 4 * (1 / 8) ≤ 2 := by
  norm_num

end KineticSupport
