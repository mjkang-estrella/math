/- Independent semantic controls, Myeongjin Kang. MIT. -/
import CM275
open scoped BigOperators ComplexConjugate
open RCLike

namespace ReviewControls

-- The centered interval must fit modulo q; otherwise actual aliases occur.
theorem centered_alias_counterexample :
    ¬Function.Injective (fun i : Fin 5 => (i.val : ZMod 3) - (2 : ZMod 3)) := by
  intro h
  have hi : (0 : Fin 5) = 3 := h (by decide)
  norm_num at hi

-- Sharp endpoint: five centered frequencies do fit in a five-point grid.
theorem centered_endpoint_valid :
    Function.Injective (fun i : Fin 5 => (i.val : ZMod 5) - (2 : ZMod 5)) := by
  exact CM275.centered_modes_injective (K := 2) (by norm_num)

-- A two-element frequency index sent to one character sums amplitudes, not energies.
theorem duplicate_character_sample (x : ZMod 1) :
    CM275.sample (fun _ : Fin 2 => CM275.mode (0 : ZMod 1)) (fun _ => 1) x = 2 := by
  norm_num [CM275.sample, CM275.mode, Fin.sum_univ_two]

theorem duplicate_character_energy :
    ⟪CM275.sample (fun _ : Fin 2 => CM275.mode (0 : ZMod 1)) (fun _ => 1),
      CM275.sample (fun _ : Fin 2 => CM275.mode (0 : ZMod 1)) (fun _ => 1)⟫ₙ_[ℂ] = 4 := by
  have h : CM275.sample (fun _ : Fin 2 => CM275.mode (0 : ZMod 1)) (fun _ => 1) =
      fun _ => (2 : ℂ) := funext duplicate_character_sample
  rw [h, wInner_cWeight_eq_expect]
  norm_num [RCLike.inner_apply]

theorem duplicate_character_invalid_parseval :
    ⟪CM275.sample (fun _ : Fin 2 => CM275.mode (0 : ZMod 1)) (fun _ => 1),
      CM275.sample (fun _ : Fin 2 => CM275.mode (0 : ZMod 1)) (fun _ => 1)⟫ₙ_[ℂ] ≠
      ∑ _ : Fin 2, star (1 : ℂ) * 1 := by
  rw [duplicate_character_energy]
  norm_num

-- Unit modulus is material even for a singleton frequency index.
theorem singleton_frequency_injective :
    Function.Injective (fun _ : Unit => CM275.mode (0 : ZMod 3)) := by
  intro a b _
  exact Subsingleton.elim a b

theorem nonunit_phase_energy :
    ⟪CM275.sample (fun _ : Unit => CM275.mode (0 : ZMod 3)) (fun _ => 2),
      CM275.sample (fun _ : Unit => CM275.mode (0 : ZMod 3)) (fun _ => 2)⟫ₙ_[ℂ] = 4 := by
  rw [CM275.character_parseval _ singleton_frequency_injective]
  norm_num

theorem nonunit_phase_not_isometry :
    ⟪CM275.sample (fun _ : Unit => CM275.mode (0 : ZMod 3)) (fun _ => 2),
      CM275.sample (fun _ : Unit => CM275.mode (0 : ZMod 3)) (fun _ => 2)⟫ₙ_[ℂ] ≠
    ⟪CM275.sample (fun _ : Unit => CM275.mode (0 : ZMod 3)) (fun _ => 1),
      CM275.sample (fun _ : Unit => CM275.mode (0 : ZMod 3)) (fun _ => 1)⟫ₙ_[ℂ] := by
  rw [nonunit_phase_energy, CM275.character_parseval _ singleton_frequency_injective]
  norm_num

-- A genuine representation with the trivial character is fixed by averaging.
theorem trivial_representation_fixed (v : ℂ) :
    CM275.characterProjector (Representation.trivial ℂ (Equiv.Perm (Fin 2)) ℂ) 1 v = v := by
  apply CM275.characterProjector_fixes
  intro g
  simp [Representation.trivial_apply]

-- The sign sector of the trivial action of S_2 is zero.
theorem trivial_action_sign_zero :
    CM275.characterProjector (Representation.trivial ℂ (Equiv.Perm (Fin 2)) ℂ)
      CM275.complexSign (1 : ℂ) = 0 := by
  have h := CM275.signProjector_eigen
    (Representation.trivial ℂ (Equiv.Perm (Fin 2)) ℂ) (1 : ℂ)
    (Equiv.swap (0 : Fin 2) 1)
  norm_num [Representation.trivial_apply] at h
  linear_combination (1 / 2 : ℂ) * h

end ReviewControls
