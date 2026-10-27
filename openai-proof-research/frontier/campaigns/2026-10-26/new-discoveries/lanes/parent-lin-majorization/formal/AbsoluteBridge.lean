import Witness

open scoped Matrix.Norms.Operator ComplexOrder MatrixOrder
open Matrix
namespace LinMajorization

theorem D_posSemidef : D.PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num [Complex.nonneg_iff]

theorem D_star : star D = D := by
  exact D_posSemidef.isHermitian.eq

theorem QDQ_posSemidef : (Q*D*star Q).PosSemidef := by
  simpa only [Matrix.star_eq_conjTranspose] using
    D_posSemidef.mul_mul_conjTranspose_same Q

theorem abs_AB : CFC.abs (A*B) = D := by
  change CFC.sqrt (star (A*B)*(A*B)) = D
  apply (CFC.sqrt_eq_iff _ _ (star_mul_self_nonneg _) D_posSemidef.nonneg).mpr
  rw [AB_eq, star_mul, D_star]
  calc
    D*D = D*(star Q*Q)*D := by rw [Q_star_mul]; simp
    _ = D*star Q*(Q*D) := by noncomm_ring

theorem abs_BA : CFC.abs (B*A) = Q*D*star Q := by
  change CFC.sqrt (star (B*A)*(B*A)) = Q*D*star Q
  apply (CFC.sqrt_eq_iff _ _ (star_mul_self_nonneg _) QDQ_posSemidef.nonneg).mpr
  rw [BA_eq, star_mul, star_star, D_star]
  calc
    (Q*D*star Q)*(Q*D*star Q) = Q*D*(star Q*Q)*D*star Q := by noncomm_ring
    _ = Q*D*(D*star Q) := by rw [Q_star_mul]; noncomm_ring

theorem QDQ_cube : (Q*D*star Q)^3 = Q*D^3*star Q := by
  have h : (Q*D*star Q)^2 = Q*D^2*star Q := by
    calc
      (Q*D*star Q)^2 = Q*D*(star Q*Q)*D*star Q := by noncomm_ring
      _ = Q*D^2*star Q := by rw [Q_star_mul]; noncomm_ring
  rw [pow_succ, h]
  calc
    Q*D^2*star Q*(Q*D*star Q) = Q*D^2*(star Q*Q)*D*star Q := by noncomm_ring
    _ = Q*D^3*star Q := by rw [Q_star_mul]; noncomm_ring

theorem sourceLeft_three : sourceLeft A B 3 = L := by
  unfold sourceLeft
  rw [abs_BA]
  rw [show CFC.rpow (Q*D*star Q) 3 = (Q*D*star Q)^3 from
    CFC.rpow_natCast _ 3 QDQ_posSemidef.nonneg, QDQ_cube]
  rfl

theorem sourceRight_three : sourceRight A B 3 = R := by
  unfold sourceRight
  rw [abs_AB]
  rw [show CFC.rpow D 3 = D^3 from CFC.rpow_natCast _ 3 D_posSemidef.nonneg]
  rfl

end LinMajorization
