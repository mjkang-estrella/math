import TraceGenerator

set_option autoImplicit false
set_option warningAsError true

namespace PeakonCoefficients

open Matrix

variable {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]

noncomputable def derivativeJet (D : Derivation A R R) : R →+* TrivSqZeroExt R R where
  toFun x := TrivSqZeroExt.inl x + TrivSqZeroExt.inr (D x)
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp [D.map_one_eq_zero]
  map_add' x y := by apply TrivSqZeroExt.ext <;> simp
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · simp
    · simp [D.leibniz, smul_eq_mul, mul_comm]

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem det_dual_perturbation (M N Q : Matrix n n R) (hMQ : M * Q = 1) :
    ((M.map (TrivSqZeroExt.inlHom R R) +
      (TrivSqZeroExt.inr (1 : R) : TrivSqZeroExt R R) •
        N.map (TrivSqZeroExt.inlHom R R)).det).snd =
      M.det * Matrix.trace (Q * N) := by
  let f := TrivSqZeroExt.inlHom R R
  let e : TrivSqZeroExt R R := TrivSqZeroExt.inr 1
  have he : e ^ 2 = 0 := by
    rw [pow_two]
    exact TrivSqZeroExt.inr_mul_inr R 1 1
  have hf : M.map f * (1 + e • (Q * N).map f) = M.map f + e • N.map f := by
    rw [Matrix.mul_add, Matrix.mul_one]
    congr 1
    have hmul : M.map f * (e • (Q * N).map f) = e • (M.map f * (Q * N).map f) := by
      apply Matrix.ext
      intro i j
      simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [hmul, ← Matrix.map_mul, ← Matrix.mul_assoc, hMQ, Matrix.one_mul]
  have hd : (1 + e • (Q * N).map f).det =
      1 + Matrix.trace ((Q * N).map f) * e := by
    rw [Matrix.det_one_add_smul, he, mul_zero, add_zero]
  change ((M.map f + e • N.map f).det).snd = _
  rw [← hf, Matrix.det_mul, hd]
  have hm : (M.map f).det = f M.det := (f.map_det M).symm
  rw [hm]
  have ht : Matrix.trace ((Q * N).map f) = f (Matrix.trace (Q * N)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
  rw [ht]
  simp [f, e, smul_eq_mul]


theorem derivation_det_of_inverse (D : Derivation A R R) (M Q : Matrix n n R)
    (hMQ : M * Q = 1) :
    D M.det = M.det * Matrix.trace (Q * M.map D) := by
  let f := TrivSqZeroExt.inlHom R R
  let e : TrivSqZeroExt R R := TrivSqZeroExt.inr 1
  have hm : M.map (derivativeJet D) = M.map f + e • (M.map D).map f := by
    apply Matrix.ext
    intro i j
    apply TrivSqZeroExt.ext <;> simp [derivativeJet, f, e, smul_eq_mul]
  have hd := congrArg TrivSqZeroExt.snd ((derivativeJet D).map_det M)
  have hleft : ((derivativeJet D) M.det).snd = D M.det := by simp [derivativeJet]
  rw [hleft] at hd
  change D M.det = (M.map (derivativeJet D)).det.snd at hd
  rw [hm] at hd
  exact hd.trans (det_dual_perturbation M (M.map D) Q hMQ)

end PeakonCoefficients
