import Certificate
import SpectralShift
import SourceStatement

open scoped Matrix.Norms.Operator ComplexOrder MatrixOrder
open Matrix
namespace LinMajorization

theorem R_posSemidef : R.PosSemidef :=
  (A_posDef.posSemidef.pow 2).add (D_posSemidef.pow 3)

theorem trace_eq_sum_ordered {M : M3} (hM : M.IsHermitian) :
    M.trace.re = hM.eigenvalues₀ 0 + hM.eigenvalues₀ 1 + hM.eigenvalues₀ 2 := by
  have ht := congrArg (RCLike.re : ℂ →+ ℝ) hM.trace_eq_sum_eigenvalues
  simp only [map_sum, RCLike.ofReal_re] at ht
  rw [← (Fintype.equivOfCardEq (Fintype.card_fin _)).sum_comp hM.eigenvalues] at ht
  simp only [Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply,
    RCLike.re_eq_complex_re] at ht
  let e : Fin 3 ≃ Fin (Fintype.card (Fin 3)) :=
    (Fin.castOrderIso (Fintype.card_fin 3).symm).toEquiv
  have he0 : e 0 = 0 := by
    apply Fin.ext; norm_num [e, Fin.castOrderIso, Fintype.card_fin]
  have he1 : e 1 = 1 := by
    apply Fin.ext; norm_num [e, Fin.castOrderIso, Fintype.card_fin]
  have he2 : e 2 = 2 := by
    apply Fin.ext; norm_num [e, Fin.castOrderIso, Fintype.card_fin]
  rw [← e.sum_comp hM.eigenvalues₀] at ht
  simpa [Fin.sum_univ_succ, he0, he1, he2] using ht

theorem eigenTopSum_two {M : M3} (hM : M.IsHermitian) :
    eigenTopSum hM 2 = hM.eigenvalues₀ 0 + hM.eigenvalues₀ 1 := by
  simp [eigenTopSum, Fintype.card_fin, List.ofFn_succ]
  congr 1
  apply Fin.ext
  norm_num [Fintype.card_fin]

theorem L_smallest_gt : tau < L_posSemidef.isHermitian.eigenvalues₀ 2 := by
  have h := eigenvalues_gt_of_shift_posDef L_posSemidef.isHermitian tau L_shift_posDef
    ((Fintype.equivOfCardEq (Fintype.card_fin _)) (2 : Fin (Fintype.card (Fin 3))))
  simpa [Matrix.IsHermitian.eigenvalues] using h

theorem R_smallest_lt : R_posSemidef.isHermitian.eigenvalues₀ 2 < tau := by
  obtain ⟨i, hi⟩ := exists_eigenvalue_lt_of_shift_not_posSemidef
    R_posSemidef.isHermitian tau R_shift_not_posSemidef
  let j := (Fintype.equivOfCardEq (Fintype.card_fin _)).symm i
  have hj : j ≤ (2 : Fin (Fintype.card (Fin 3))) := by
    have h := j.isLt
    norm_num at h
    exact_mod_cast (show j.val ≤ 2 by omega)
  exact lt_of_le_of_lt (R_posSemidef.isHermitian.eigenvalues₀_antitone hj) hi

theorem top_two_strict_reversed :
    eigenTopSum L_posSemidef.isHermitian 2 < eigenTopSum R_posSemidef.isHermitian 2 := by
  have hl := trace_eq_sum_ordered L_posSemidef.isHermitian
  have hr := trace_eq_sum_ordered R_posSemidef.isHermitian
  have ht := congrArg Complex.re trace_eq
  have hm := lt_trans R_smallest_lt L_smallest_gt
  rw [eigenTopSum_two, eigenTopSum_two]
  linarith

theorem not_majorizes : ¬EigenMajorizes L_posSemidef.isHermitian R_posSemidef.isHermitian := by
  intro h
  exact (not_le_of_gt top_two_strict_reversed) (h.1 2 (by decide))

theorem source_counterexample_332939 : ¬SourceConjecture332939 := by
  intro h
  have hm := h 3 A B A_posDef.posSemidef B_posSemidef 3 (by norm_num)
  have heL := sourceLeft_three
  have heR := sourceRight_three
  apply not_majorizes
  simpa only [heL, heR] using hm

end LinMajorization
